#lang racket
(provide kont-append
         kont-snoc
         lookup ρlookup σlookup σlookups
         bind
         σextend σextend* σupdate extend
         alloc
         abort-targets first-preprocess
         unwrap-call/cc
         capture-upto capture-upto/cc
         lookup-err hash-set* hash-extend*)
(require redex "fyff-grammar.rkt" racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tunable

;; Changes for concrete vs abstract (current: concrete)
(define-metafunction L
  [(σupdate σ a v) ,(hash-set (term σ) (term a) (set (term v)))])
(define-metafunction L
  [(alloc label ς) (label ,(gensym))]
  [(alloc (alloc-point ...) ς) ,(for/list ([y (in-list (term (alloc-point ...)))]) `(,y ,(gensym)))]
  [(alloc any_0 any_1) ,(error 'alloc "~a ~a" (term any_0) (term any_1))])
(define-metafunction L
  [(concretely-one? v) #t]
  [(concretely-one? a) #t])
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction L
  [(concretely-equal? v v) (concretely-one? v)]
  [(concretely-equal? any_0 any_1) #f])

(define-metafunction L
  [(kont-append mt κ) κ]
  [(kont-append (f κ) κ_tail) (f (kont-append κ κ_tail))])

(define-metafunction L
  [(kont-revappend mt κ) κ]
  [(kont-revappend (f κ) κ_tail) (kont-revappend κ (f κ_tail))])

(define-metafunction L
  [(kont-reverse κ) (kont-revappend κ mt)])

(define-metafunction L
  [(kont-snoc κ f) (kont-append κ (f mt))])

(define (hash-set* ρ xs as)
  (for/fold ([ρ ρ]) ([x (in-list xs)]
                     [a (in-list as)])
    (hash-set ρ x a)))

(define ((lookup-err tag key)) (error tag "Lookup failed at ~a" key))

(define (hash-extend* σ as vs)
  (for/fold ([σ* σ]) ([a (in-list as)]
                     [v (in-list vs)])
    (hash-set σ* a (set-add (hash-ref σ a (set)) v))))

(define-metafunction L
  [(ρlookup ρ x) ,(hash-ref (term ρ) (term x) (lookup-err 'ρlookup (term x)))])
(define-metafunction L
  [(σlookups σ a) ,(hash-ref (term σ) (term a) (lookup-err 'σlookups (term a)))])
(define-metafunction L
  [(σlookup σ a) ,(set->list (term (σlookups σ a)))])
(define-metafunction L
  [(lookup σ ρ x) ,(let ([a (term (ρlookup ρ x))])
                     (set->list (hash-ref (term σ) a (lookup-err 'lookup a))))])
(define-metafunction L
  [(bind σ ρ (x ...) (a ...) (v ...))
   (,(hash-set* (term ρ) (term (x ...)) (term (a ...)))
    ,(hash-extend* (term σ) (term (a ...)) (term (v ...))))])

(define-metafunction L
  [(extend ρ x a) ,(hash-set (term ρ) (term x) (term a))])
(define-metafunction L
  [(σextend σ a vs) ,(hash-set (term σ) (term a) (set-union (term vs) (hash-ref (term σ) (term a) (set))))])
(define-metafunction L
  [(σextend* σ (a ..._i) (v ..._i)) ,(hash-extend* (term σ) (term (a ...)) (term (v ...)))])

(define-metafunction L
  [(add-to any any_v) ,(set-add (term any) (term any_v))])
(define-metafunction L
  [(join-to any any_v) ,(set-union (term any) (term any_v))])

(define-metafunction L
  capture-upto-accumulate : κ tag κ ks -> ks
  [(capture-upto-accumulate (name κ ((prompt tag_0 v) κ_0)) tag_1 κ_acc ks)
   (add-to ks (κ_acc κ))
   (side-condition (term (concretely-equal? tag_0 tag_1)))]
  ;; Can't determine tags are concretely equal? Then say current κ is possible and keep searching.
  [(capture-upto-accumulate (name κ ((prompt tag v) κ_0)) tag κ_acc ks)
   (capture-upto-accumulate κ_0 tag (kont-snoc κ_acc (prompt tag v)) (add-to ks (κ_acc κ)))]
  [(capture-upto-accumulate (f κ) tag κ_acc ks)
   (capture-upto-accumulate κ tag (kont-snoc κ_acc f) ks)]
  [(capture-upto-accumulate mt tag κ_acc ks) ks])

(define (cc/tag ks tag) (for/set ([κ×κ (in-set ks)]) `(cont ,tag ,(first κ×κ))))
(define (comp-of ks) (for/set ([κ×κ (in-set ks)]) `(comp ,(first κ×κ))))

(define-metafunction L
  [(capture-upto/cc κ tag) ,(cc/tag (term (capture-upto-accumulate κ tag mt ,(set))) (term tag))])
(define-metafunction L
  [(capture-upto κ tag) ,(comp-of (term (capture-upto-accumulate κ tag mt ,(set))))])

(define-metafunction L
  [(abort-targets κ tag σ)
   ,(set->list (term (first-tagged-or-postcondition κ tag ,(set))))])
(define-metafunction L
  [(first-tagged-or-postcondition mt tag ks) ks]
  [(first-tagged-or-postcondition ((dw a v_pre v_post) κ) tag ks)
   (add-to ks (v_post κ))]
  [(first-tagged-or-postcondition ((prompt tag_0 v) κ) tag_1 ks)
   (add-to ks (v κ))
   (side-condition (term (concretely-equal? tag_0 tag_1)))]
  [(first-tagged-or-postcondition ((prompt tag v) κ) tag ks)
   (first-tagged-or-postcondition κ tag (add-to ks (v κ)))]
  [(first-tagged-or-postcondition (f κ) tag ks)
   (first-tagged-or-postcondition κ tag ks)])

;; True if the two given continuations do not share the same
;; gensyms for any dw frames.
;; False otherwise.
(define-metafunction L
  [(noShared κ_0 κ_1) ,(compare-sets (list->set (term (all-dws κ_0 ())))
                                     (list->set (term (all-dws κ_1 ()))))])
;; Is as0 concretely disjoint from as1?
(define (compare-sets as0 as1)
  (define concretely? #f)
  (define maybe? #f)
  (for ([a (in-set (set-intersect as0 as1))])
    (if (term (concretely-one? ,a))
        (set! concretely? #t)
        (set! maybe? #t)))
  (cond [concretely? '(#f)]
        [maybe? '(#t #f)]
        [else '(#t)]))

(define-metafunction L
  [(all-dws ((dw a v_0 v_1) κ) (a_acc ...)) (all-dws κ (a a_acc ...))]
  [(all-dws (f κ) any) (all-dws κ any)]
  [(all-dws mt any) any])

(define-metafunction L
  [(sameDWs κ_0 κ_1) (concretely-same? (all-dws κ_0 ()) (all-dws κ_1 ()) #t)])
(define-metafunction L
  [(concretely-same? () () #f) (#t #f)]
  [(concretely-same? () () #t) (#t)]
  [(concretely-same? (a a_rest0 ...) (a a_rest1 ...) boolean)
   (concretely-same? (a_rest0 ...) (a_rest1 ...) ,(and (term boolean) (term (concretely-one? a))))]
  [(concretely-same? any_0 any_1 any_2) (#f)])

;; Split up κ₀ and κ₁ into maximal matching prefix / non-overlapping suffix
(define (match-prefixes κ₀ κ₁)
  (define (split-at-dw κ)
    (let revloop ([κ κ] [pre 'mt])
      (match κ
        ['mt (values pre 'mt)]
        [`(,(and dwf `(dw ,a ,v-pre ,v-post)) ,κ*)
         (values pre κ)]
        [`(,f ,κ*) (revloop κ* `(,f ,pre))])))
  (define (add-dw dwf dws)
    (match dwf
      [`(dw ,a ,v-pre ,v-post) (set-add dws a)]
      [#f dws]))
  ;; Walk down both κ₀ and κ₁ building up their dw-delimited sections that aren't
  ;; shared, and then confirm that the rest (may be) equal.
  (let loop ([κ₀ κ₀] [κ₁ κ₁] [no-share₀ 'mt] [no-share₁ 'mt] [dws₀ (set)] [dws₁ (set)])
    (define (done)
      (set (list κ₀ (term (kont-reverse ,no-share₀))
                 κ₁ (term (kont-reverse ,no-share₁)))))
    (cond
     [(and (eq? κ₀ 'mt) (eq? κ₁ 'mt))
      (done)]
     [else
      (define-values (κ₀-pre κ₀-post) (split-at-dw κ₀))
      (define-values (κ₁-pre κ₁-post) (split-at-dw κ₁))
      (match* (κ₀-pre κ₁-pre)
        [('mt 'mt)
         (if (memv #t (term (sameDWs ,κ₀-post ,κ₁-post)))
             (set (list κ₀ (term (kont-reverse ,no-share₀))
                        κ₁ (term (kont-reverse ,no-share₁))))
             (set-union
              (match κ₀-post
                [`(,(and dwf₀ `(dw ,a0 ,v-pre0 ,v-post0)) ,κ₀*)
                 (define dws₀* (set-add dws₀ a0))
                 (define cmp₀ (compare-sets dws₀* dws₁))
                 (cond
                  [(memv #t cmp₀) ;; try a dw of κ₀
                   (loop κ₀* κ₁ (term (,dwf₀ ,no-share₀)) no-share₁ dws₀* dws₁)]
                  [(memv #f cmp₀) ;; overlap started due to κ₀. See if there is overlap in κ₁.
                   (match κ₁-post
                     [`(,(and dwf₁ `(dw ,a1 ,v-pre1 ,v-post1)) ,κ₁*)
                      (define dws₁* (set-add dws₁ a1))
                      (define cmp₁ (compare-sets dws₀ dws₁*))
                      (cond
                       [(and (memv #t cmp₁)) ;; keep going down κ₁
                        (loop κ₀ κ₁* no-share₀ (term (,dwf₁ ,no-share₁)) dws₀ dws₁*)]
                       [(memv #f cmp₁) ;; totally done.
                        (done)])]
                     [_ (set)])])]
                [_ (set)])
              (match κ₁-post
                [`(,(and dwf₁ `(dw ,a1 ,v-pre1 ,v-post1)) ,κ₁*)
                 (define dws₁* (set-add dws₁ a1))
                 (define cmp₁ (compare-sets dws₀ dws₁*))
                 (cond
                  [(memv #t cmp₁) ;; try a dw of κ₁
                   (loop κ₀ κ₁* no-share₀ (term (,dwf₁ ,no-share₁)) dws₀ dws₁*)]
                  [(memv #f cmp₁) ;; overlap started due to κ₁. See if there is overlap in κ₀
                   (match κ₀-post
                     [`(,(and dwf₁ `(dw ,a1 ,v-pre1 ,v-post1)) ,κ₁*)
                      (define dws₁* (set-add dws₁ a1))
                      (define cmp₁ (compare-sets dws₀ dws₁*))
                      (cond
                       [(memv #t cmp₁) ;; keep going down κ₁
                        (loop κ₀ κ₁* no-share₀ (term (,dwf₁ ,no-share₁)) dws₀ dws₁*)]
                       [(memv #f cmp₁)
                        (done)])]
                     ;; already checked for sameDWs. Stuck.
                     [_ (set)])])]
                [_ (set)])))]
        [(_ _)
         (loop κ₀-post κ₁-post
               (term (kont-append ,κ₀-pre ,no-share₀))
               (term (kont-append ,κ₁-pre ,no-share₁))
               dws₀ dws₁)])])))

(module+ test
 (require rackunit)
 (define tail
   '((dw
      (3 g2038)
      ((λ () (4 print 2)) #hash((a . a) (do-a? . do-a?)))
      ((λ () (7 print 3)) #hash((a . a) (do-a? . do-a?))))
     ((bgn
       ((8
         dynamic-wind
         (λ () (9 print 4))
         (λ ()
            (if do-a?
                (begin (set! do-a? #f) (10 a (λ () 11)))
                (begin (set! a #f) 12)))
         (λ ()
            (begin
              (11 print 5)
              (12
               call/comp
               (λ (k)
                  (13
                   call-with-continuation-prompt
                   (λ () (14 k 10))
                   0
                   (λ (x) x)))
               0))))
        #hash((a . a) (do-a? . do-a?))))
      ((dw
        (1 g2035)
        ((λ () (2 print 1)) #hash((a . a) (do-a? . do-a?)))
        ((λ () (15 print 6)) #hash((a . a) (do-a? . do-a?))))
       mt))))
 (check equal?
        (match-prefixes
         tail
         `((ev 5 () () #hash((a . a) (do-a? . do-a?)))
           ,tail))
        (set (list tail 'mt
                   tail `((ev 5 () () #hash((a . a) (do-a? . do-a?))) mt)))))

;; Truncate a continuation at the innermost dw (first found dw)
(define/match (innermost-dw κ)
  [('mt) #f]
  [(`((dw ,a ,v-pre ,v-post) ,κ*)) κ]
  [(`(,f ,κ*)) (innermost-dw κ*)])
(define (outermost-dw/last-dw-κ κ option-κ)
  (match κ
   ['mt option-κ]
   [`((dw ,a ,v-pre ,v-post) ,κ*) (outermost-dw/last-dw-κ κ* κ)]
   [`(,f ,κ*) (outermost-dw/last-dw-κ κ* option-κ)]))
(define (outermost-dw κ) (outermost-dw/last-dw-κ κ #f))


;; The following metafunction is one of the most complicated.
;; It finds the applicability of the cont-pre, cont-post and cont rules.

(define-metafunction L
  [(unwrap-call/cc κ_call tag κ)
   ,(set->list (calling-cont (term κ_call) (term tag) (term κ)))])

(define (calling-cont κ-call tag κ)
  (define chopped (term (capture-upto-accumulate ,κ ,tag mt ,(set))))
  (for/fold ([out (set)]) ([inside×outside (in-set chopped)])
    (match-define (list inside outside) inside×outside)
    (define prefix-splits (match-prefixes inside κ-call))
    (for/fold ([out out]) ([split (in-set prefix-splits)])
      (match-define (list D₂ in-D₂ D₆ in-D₆) split)
      ;; If E₃ contains a dw, then we are in [cont-post].
      (match (innermost-dw in-D₂)
        [#f ;; in-D₂ is W₃
         ;; Otherwise, if E₄ contains a dw, then we are in [cont-pre].
         (match (outermost-dw in-D₆)
           ;; else, we are in [cont].           
           [#f ;; in-D₆ is W₄
            (set-add out (term (kont-append ,κ-call ,outside)))]
           [`((dw ,a ,v-pre ,v-post) ,W₄)
            (set-add out (term (pre ,a ,v-pre ,v-post (kont-append ,W₄ (kont-append ,D₆ ,outside)))))])]
        [`((dw ,a ,v-pre ,v-post) ,E₃)
         (set-add out (term (post ,v-post (kont-append ,E₃ (kont-append ,D₂ ,outside)))))]))))

#|
(calling-cont
  '((ev 5 () () #hash((a . a) (do-a? . do-a?)))
    ((dw
      (3 g2038)
      ((λ () (4 print 2)) #hash((a . a) (do-a? . do-a?)))
      ((λ () (7 print 3)) #hash((a . a) (do-a? . do-a?))))
     ((bgn
       ((8
         dynamic-wind
         (λ () (9 print 4))
         (λ ()
           (if do-a?
             (begin (set! do-a? #f) (10 a (λ () 11)))
             (begin (set! a #f) 12)))
         (λ ()
           (begin
             (11 print 5)
             (12
              call/comp
              (λ (k)
                (13
                 call-with-continuation-prompt
                 (λ () (14 k 10))
                 0
                 (λ (x) x)))
              0))))
        #hash((a . a) (do-a? . do-a?))))
      ((dw
        (1 g2035)
        ((λ () (2 print 1)) #hash((a . a) (do-a? . do-a?)))
        ((λ () (15 print 6)) #hash((a . a) (do-a? . do-a?))))
       mt))))
  0
  '((dw
     (3 g2038)
     ((λ () (4 print 2)) #hash((a . a) (do-a? . do-a?)))
     ((λ () (7 print 3)) #hash((a . a) (do-a? . do-a?))))
    ((bgn
      ((8
        dynamic-wind
        (λ () (9 print 4))
        (λ ()
          (if do-a?
            (begin (set! do-a? #f) (10 a (λ () 11)))
            (begin (set! a #f) 12)))
        (λ ()
          (begin
            (11 print 5)
            (12
             call/comp
             (λ (k)
               (13 call-with-continuation-prompt (λ () (14 k 10)) 0 (λ (x) x)))
             0))))
       #hash((a . a) (do-a? . do-a?))))
     ((dw
       (1 g2035)
       ((λ () (2 print 1)) #hash((a . a) (do-a? . do-a?)))
       ((λ () (15 print 6)) #hash((a . a) (do-a? . do-a?))))
      ((prompt 0 ((λ (x) x) #hash((a . a) (do-a? . do-a?)))) mt)))))
|#
(trace calling-cont match-prefixes)

;; continuations are in reverse order than W[v] notation.
(define-metafunction L
  [(first-preprocess κ) (last-preprocess κ #f mt)])
;; As we recur down k (inside-out for W[v]), we accumulate the stack up to where we currently are,
;; and when we hit a dw, we copy that stack over to the accumulator that stands for the last seen dw.
(define-metafunction L
  [(last-preprocess mt any κ_build) any]
  [(last-preprocess ((name f (dw a v_pre v_post)) κ) any κ_build)
   (last-preprocess κ (a v_pre v_post κ_build) (kont-snoc κ_build f))]
  [(last-preprocess (f κ) any κ_build)
   (last-preprocess κ any (kont-snoc κ_build f))])
