#lang racket
(provide kont-append
         kont-snoc
         lookup ρlookup σlookup σlookups
         bind
         σextend σextend* σupdate
         alloc
         abort-targets first-preprocess
         unwrap-call/cc
         capture-upto capture-upto/cc)
(require redex "fyff-grammar.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tunable

;; Changes for concrete vs abstract (current: concrete)
(define-metafunction L
  [(σupdate σ a v) ,(hash-set (term σ) (term a) (set (term v)))])
(define-metafunction L
  [(alloc label ς) (label ,(gensym))]
  [(alloc (x ...) ς) ,(for/list ([y (in-list (term (x ...)))]) `(,y ,(gensym)))])
(define-metafunction L
  [(concretely-equal? tag tag) #t]
  [(concretely-equal? any_0 any_1) #f])
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction L
  [(kont-append mt k) k]
  [(kont-append (f k) k_tail) (f (kont-append k k_tail))])

(define-metafunction L
  [(kont-snoc k f) (kont-append k (f mt))])

(define (hash-set* ρ xs as)
  (for/fold ([ρ ρ]) ([x (in-list xs)]
                     [a (in-list as)])
    (hash-set ρ x a)))

(define (hash-extend* σ as vs)
  (for/fold ([σ σ]) ([a (in-list as)]
                     [v (in-list vs)])
    (hash-set σ a (set-add (hash-ref σ a (set)) v))))

(define-metafunction L
  [(ρlookup ρ x) ,(hash-ref (term ρ) (term x))])
(define-metafunction L
  [(σlookups σ a) ,(hash-ref (term σ) (term a))])
(define-metafunction L
  [(σlookup σ a) ,(set->list (term (σlookups σ a)))])
(define-metafunction L
  [(lookup σ ρ x) ,(set->list (hash-ref (term σ) (term (ρlookup ρ x))))])
(define-metafunction L
  [(bind σ ρ (x ...) (a ...) (v ...))
   (,(hash-set* (term ρ) (term (x ...)) (term (a ...)))
    ,(hash-extend* (term σ) (term (a ...)) (term (v ...))))])

(define-metafunction L
  [(σextend σ a vs) ,(hash-set (term σ) (term a) (set-union (term vs) (hash-ref (term σ) (term a) (set))))])
(define-metafunction L
  [(σextend* σ (a ..._i) (v ..._i)) ,(hash-extend* (term σ) (term (a ...)) (term (v ...)))])

(define-metafunction L
  [(add-to any any_v) ,(set-add (term any) (term any_v))])
(define-metafunction L
  [(join-to any any_v) ,(set-union (term any) (term any_v))])

(define-metafunction L
  capture-upto/cc-accumulate : k tag k ks -> ks
  [(capture-upto/cc-accumulate (name k ((prompt tag_0 v) k_0)) tag_1 k_acc ks)
   (add-to ks ((cont tag_1 k_acc) k))
   (side-condition (term (concretely-equal? tag_0 tag_1)))]
  ;; Can't determine tags are concretely equal? Then say current cont is possible and keep searching.
  [(capture-upto/cc-accumulate (name k ((prompt tag v) k_0)) tag k_acc ks)
   (capture-upto/cc-accumulate k_0 tag (kont-snoc k_acc (prompt tag v)) (add-to ks (cont tag k_acc)))]
  [(capture-upto/cc-accumulate (f k) tag k_acc ks)
   (capture-upto/cc-accumulate k tag (kont-snoc k_acc f) ks)]
  [(capture-upto/cc-accumulate mt tag k_acc ks) ks])

(define-metafunction L
  capture-upto-accumulate : k tag k ks -> ks
  [(capture-upto-accumulate (name k ((prompt tag_0 v) k_0)) tag_1 k_acc ks)
   (add-to ks ((cont tag_1 k_acc) k))
   (side-condition (term (concretely-equal? tag_0 tag_1)))]
  [(capture-upto-accumulate (name k ((prompt tag v) k_0)) tag k_acc ks)
   ;; only line different from previous definition
   (capture-upto-accumulate k_0 tag (kont-snoc k_acc (prompt tag v)) (add-to ks (comp k_acc)))]
  [(capture-upto-accumulate (f k) tag k_acc ks)
   (capture-upto-accumulate k tag (kont-snoc k_acc f) ks)]
  [(capture-upto-accumulate mt tag k_acc ks) ks])

(define-metafunction L
  [(capture-upto/cc k tag) (capture-upto/cc-accumulate k tag mt ,(set))])
(define-metafunction L
  [(capture-upto k tag) (capture-upto-accumulate k tag mt ,(set))])

(define-metafunction L
  [(abort-targets k tag σ) (get-abort-targets k tag σ mt ,(set))])
(define-metafunction L
  [(get-abort-targets mt tag σ k_build ks) ,(set->list (term ks))]
  [(get-abort-targets ((dw a v_pre v_post) k) tag k_build ks)
   ,(set->list (term (add-to ks (v_pre k_build))))]
  [(get-abort-targets ((prompt tag_0 v) k) tag_1 k_build ks)
   ,(set->list (term (add-to ks (v k_build))))
   (side-condition (term (concretely-equal? tag_0 tag_1)))]
  [(get-abort-targets ((prompt tag v) k) tag k_build ks)
   (get-abort-targets k tag (kont-snoc k_build) (add-to ks (v k_build)))]
  [(get-abort-targets (f k) tag k_build ks)
   (get-abort-targets k tag (kont-snoc k_build f) ks)])

(define-metafunction L
  [(unwrap-call/cc k_call tag k) ???])

;; continuations are in reverse order than W[v] notation.
(define-metafunction L
  [(first-preprocess k) (last-preprocess k #f mt mt)])
;; As we recur down k (inside-out for W[v]), we accumulate the stack up to where we currently are,
;; and when we hit a dw, we copy that stack over to the accumulator that stands for the last seen dw.
(define-metafunction L
  [(last-preprocess mt any k_build) any]
  [(last-preprocess ((name f (dw a v_pre v_post)) k) any k_build)
   (last-preprocess k (v_pre k_build) (kont-snoc k_build f))]
  [(last-preprocess (f k) any k_build)
   (last-preprocess k any (kont-snoc k_build f))])
