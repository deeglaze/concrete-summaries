#lang racket

(provide L R)
(require redex racket/trace)
(define-language L
  [e x (label e e ...) (λ (x ...) e) (shift x e) (reset e) prims]
  [prims number + <= #t #f]
  [label natural]
  [(σ ρ χ Ξ M σ-token χ-token) any]
  [f (ev label (e ...) (v ...) ρ)]
  [a any]
  [(ks vs as) (side-condition (name vs any) (set? (term vs)))]  
  [v (clos (λ (x ...) e) ρ) prims]
  [x variable-not-otherwise-mentioned])

(define-syntax-rule (for/union guards body ...) (for/fold ([acc (set)]) guards (set-union acc (let () body ...))))
(define-syntax-rule (for*/union guards body ...) (for*/fold ([acc (set)]) guards (set-union acc (let () body ...))))

(define (hash-join σ a vs) (hash-set σ a (set-union (hash-ref σ a (set)) vs)))
(define (hash-set-many ρ xs as)
 (for/fold ([ρ ρ]) ([x (in-list xs)]
                    [a (in-list as)])
   (hash-set ρ x a)))
(define (hash-join-many σ as vs)
  (for/fold ([σ σ]) ([a (in-list as)]
                     [v (in-list vs)])
    (hash-join σ a (set v))))

(define-metafunction L [(σlookup σ a) ,(set->list (hash-ref (term σ) (term a)))])
(define-metafunction L [(ρlookup ρ x) ,(hash-ref (term ρ) (term x) (λ () (error 'ρlookup "unbound var ~a" (term x))))])
(define-metafunction L
  [(alloc (x ...) any)
   ,(for/list ([xi (in-list (term (x ...)))])
      (term (,xi ,(begin (gensym) #f))))])

(define-extended-language L-SR L
  [κ mt (f κ)]
  [C (∘ κ C) mt]
  [p (e ρ) v]
  [v .... (comp κ)]
  [ς (p σ κ C)
     (do-call label v (v ...) σ κ C)])

(define-metafunction L-SR
  [(bind σ ρ (x ..._1) (a ..._1) (v ..._1))
   (,(hash-set-many (term ρ) (term (x ...)) (term (a ...)))
    ,(for/fold ([σ* (term σ)]) ([a* (in-list (term (a ...)))]
                                [v* (in-list (term (v ...)))])
       (hash-join σ* a* (set v*))))])
(define R
  (reduction-relation L-SR
    [--> ((prims ρ) σ κ C) (prims σ κ C)]
    [--> (((reset e) ρ) σ κ C)
         ((e ρ) σ mt (∘ κ C))]
    [--> (((λ (x ...) e) ρ) σ κ C)
         ((clos (λ (x ...) e) ρ) σ κ C)]
    [--> (name ς (((shift x e) ρ) σ κ C))
         ((e ρ_1) σ_1 mt C)
         (where (a) (alloc (x) ς))
         (where (ρ_1 σ_1) (bind σ ρ (x) (a) ((comp κ))))]
    [--> ((x ρ) σ κ C)
         (v σ κ C)
         (where (any_0 ... v any_1 ...) (σlookup σ (ρlookup ρ x)))]
    [--> (((label e_0 e_rest ...) ρ) σ κ C)
         ((e_0 ρ) σ ((ev label (e_rest ...) () ρ) κ) C)]
    [--> (v σ ((ev label (e e_rest ...) (v_done ...) ρ) κ) C)
         ((e ρ) σ ((ev label (e_rest ...) (v_done ... v) ρ) κ) C)]
    [--> (v σ ((ev label () () ρ) κ) C)
         (do-call label v () σ κ C)]
    [--> (v σ ((ev label () (v_fn v_args ...) ρ) κ) C)
         (do-call label v_fn (v_args ... v) σ κ C)]
    [--> (name ς (do-call label (clos (λ (x ..._i) e) ρ) (v ..._i) σ κ C))
         ((e ρ_1) σ_1 κ C)
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σ_1) (bind σ ρ (x ...) (a ...) (v ...)))]
    [--> (do-call label (comp κ_call) (v) σ κ C)
         (v σ κ_call (∘ κ C))]
    [--> (do-call label + (number ...) σ κ C)
         (,(apply + (term (number ...))) σ κ C)]
    [--> (do-call label <= (number ...) σ κ C)
         (,(apply <= (term (number ...))) σ κ C)]
    [--> (v σ mt (∘ κ C))
         (v σ κ C)]))

(define-extended-language L-SRT L
  [κ mt (rt ctx) (f κ)]
  [C (prompt ctx) mt]
  [p (e ρ) v]
  [v .... (comp κ)]
  [ctx ((e ρ) σ χ) (v v σ χ)
       ((e ρ) a)]
  [(Σ F σΔ χΔ ΞΔ MΔ) any]
  [pre-ς (p κ C)
         (do-call label v (v ...) κ C)]
  [simple-ς pre-ς
            (pre-ς σ χ Ξ M)]
  [ς simple-ς (Δs simple-ς σΔ χΔ ΞΔ MΔ)])

(define-metafunction L-SRT
  [(bindΔ σ ρ (x ..._1) (a ..._1) (v ..._1))
   (,(hash-set-many (term ρ) (term (x ...)) (term (a ...)))
    ((a v) ...))])

(define (update h Δ)
  (for/fold ([h h]) ([kv (in-list Δ)])
    (hash-join h (first kv) (set (second kv)))))

(define ((changes?-base who combine) σ Δ)
  (let loop ([Δ Δ] [same? #t])
    (match Δ
      ['() (not same?)]
      [(cons (list k v) Δ)
       (define old (hash-ref σ k (set)))
       (define new (combine old v))
       (if (= (set-count new) (set-count old))
           (loop Δ same?)
           (loop Δ #f))]
      [bad (error who "bad ~a" bad)])))
(define changes? (changes?-base 'changes? set-add))
(define changes*? (changes?-base 'changes*? set-union))

(define ((update/same-base who combine) σ Δ)
  (let loop ([σ σ] [Δ Δ] [same? #t])
    (match Δ
      ['() (values σ same?)]
      [(cons (list k v) Δ)
       (define old (hash-ref σ k (set)))
       (define new (combine old v))
       (if (= (set-count new) (set-count old))
           (loop σ Δ same?)
           (loop (hash-set σ k new) Δ #f))]
      [bad (error who "bad ~a" bad)])))
(define update/same (update/same-base 'update/same set-add))
(define update*/same (update/same-base 'update*/same set-union))

(define (Ξupdate h Δ)
  (for/fold ([h h]) ([kv (in-list Δ)])
    (define-values (k χ-token v)
      (match kv
        [`(((,e ,ρ) ,σ-token ,χ-token) ,κ) (values `((,e ,ρ) ,σ-token) χ-token κ)]
        [`(((comp ,κ) ,v ,σ-token ,χ-token) ,κC) (values `((comp ,κ) ,v ,σ-token) χ-token κC)]))
    (define χmap (hash-ref h k #hash()))
    (hash-set h k (hash-join χmap χ-token (set v)))))

;; for wide. (Narrow is (v σ χ))
(define (Mupdate h χ χ-token Ξ Δ)
  (match Δ
    ['() h]
    [`((,(and k (or `((,_ ,_) ,_ ,_)
                    `((comp ,_) ,_ ,_ ,_)))
        (,v ,_ ,_)) . ,rest)
     (Mupdate (hash-join h k (set v)) χ χ-token Ξ rest)]
    [`((((,e ,ρ) ,a) (,v ,_ ,_)) . ,rest)
     (define vs (set v))
     (Mupdate (for*/fold ([M h]) ([σ-token (in-set (hash-ref χ a))]
                                  [χ-token* (in-hash-keys (hash-ref Ξ `((,e ,ρ) ,σ-token)))])
                (hash-join M `((,e ,ρ) ,σ-token ,χ-token*) vs))
              χ χ-token Ξ rest)]
    [_ (error 'Mupdate "bad ~a" Δ)]))

(define-metafunction L-SRT
  [(Ξlookup Ξ χ χ-token ctx)
   ,(set->list
     ((term-match/single L-SRT
        [((e ρ) a)
         (for*/union ([σ-token (in-set (hash-ref (term χ) (term a) (set)))]
                      [(χ-token* σs) (in-hash (hash-ref (term Ξ) (term ((e ρ) ,σ-token))))]
                      #:when (<= χ-token* (term χ-token)))
           σs)]
        [((e ρ) σ-token χ-token)
         (hash-ref (hash-ref (term Ξ) (term ((e ρ) σ-token))) (term χ-token))]
        [((comp κ) v σ-token χ-token)
         (hash-ref (hash-ref (term Ξ) (term ((comp κ) v σ-token))) (term χ-token))])
      (term ctx)))])
(define-metafunction L-SRT
  [(Mlookup M ctx σ χ) ,(for/list ([vσχ (in-set (hash-ref (term M) (term ctx) (set)))])
                          (list vσχ (term σ) (term χ)))]) ;; for wide. (Narrow is just vσ)
(define-metafunction L-SRT
  [(approximate χ (rt ((e ρ) σ-token χ-token)) a)
   (((a ,(set (term σ-token)))) ;; FIXME: wat do? Everything less than χ-token?
    (rt ((e ρ) a)))]
  [(approximate χ (rt ((e ρ) a_0)) a)
   (((a ,(hash-ref (term χ) (term a_0))))
    (rt ((e ρ) a)))]
  [(approximate χ (f κ) a)
   (χΔ (f κ_1))
   (where (χΔ κ_1) (approximate χ κ a))]
  [(approximate χ mt a) (() mt)])

(define W
  (reduction-relation L-SRT
    [--> (Σ F σ χ σ-token χ-token Ξ M)
         ,(step-system (term Σ) (term F) (term σ) (term χ)
                       (term σ-token) (term χ-token)
                       (term Ξ) (term M))]))

(define (R-table σ χ σΔ? χΔ? σ-token χ-token Ξ M)
  (define-metafunction L-SRT
    [(σtoken ()) ,σ-token]
    [(σtoken any) ,(cond [(or σΔ? (not (changes? σ (term any)))) σ-token]
                         [else (add1 σ-token)])])
  (define-metafunction L-SRT
    [(χtoken ()) ,χ-token]
    [(χtoken any) ,(cond [(or χΔ? (not (changes*? χ (term any)))) χ-token]
                         [else (add1 χ-token)])])
  ;; for narrow
  #;#;
  (define-metafunction L-SRT
    [(σtoken any) ,(update σ (term any))])
  (define-metafunction L-SRT
    [(χtoken any) ,(update χ (term any))])

  (reduction-relation L-SRT
    [--> ((prims ρ) κ C) (prims κ C)]
    [--> (((λ (x ...) e) ρ) κ C)
         ((clos (λ (x ...) e) ρ) κ C)]
    ;; Actually do prompt
    [--> (((reset e) ρ) κ C)
         (Δs (((e ρ) mt (prompt ctx)) ,σ ,χ ,Ξ ,M) () () ((ctx (κ C))) ())
         (where ctx ((e ρ) (σtoken ()) (χtoken ())))
         (side-condition (not (hash-has-key? M (term ctx))))]
    ;; Use memo for prompt
    [--> (((reset e) ρ) κ C)
         (Δs ((v κ C) σ_out χ_out ,Ξ ,M) () () ((ctx (κ C))) ())
         (where ctx ((e ρ) (σtoken ()) (χtoken ())))
         (where (any_0 ... (v σ_out χ_out) any_1 ...) (Mlookup ,M ctx ,σ ,χ))]
    [--> (name ς (((shift x e) ρ) κ C))
         (Δs (((e ρ_1) mt C) ,σ ,χ ,Ξ ,M) σΔ χΔ () ())
         (where (a) (alloc (x) ς))
         (where ctx ((e ρ) (σtoken ()) (χtoken ())))
         (where (χΔ κ_1) (approximate ,χ κ a))
         (where (ρ_1 σΔ) (bindΔ ,σ ρ (x) (a) ((comp κ_1))))]
    [--> ((x ρ) κ C) (v κ C)
         (where (any_0 ... v any_1 ...) (σlookup ,σ (ρlookup ρ x)))]
    [--> (((label e_0 e_rest ...) ρ) κ C)
         ((e_0 ρ) ((ev label (e_rest ...) () ρ) κ) C)]
    [--> (v ((ev label (e e_rest ...) (v_done ...) ρ) κ) C)
         ((e ρ) ((ev label (e_rest ...) (v_done ... v) ρ) κ) C)]
    [--> (v ((ev label () (v_fn v_args ...) ρ) κ) C)
         (do-call label v_fn (v_args ... v) κ C)]
    [--> (v ((ev label () () ρ) κ) C)
         (do-call label v () κ C)]
    ;; actually do call
    [--> (name ς (do-call label (clos (λ (x ..._i) e) ρ) (v ..._i) κ C))
         (Δs (((e ρ_1) (rt ctx) C) ,σ ,χ ,Ξ ,M) σΔ () ((ctx κ)) ())
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σΔ) (bindΔ ,σ ρ (x ...) (a ...) (v ...)))
         (where ctx ((e ρ_1) (σtoken σΔ) (χtoken ())))
         (side-condition (not (hash-has-key? M (term ctx))))]
    ;; Use memo table
    [--> (name ς (do-call label (clos (λ (x ..._i) e) ρ) (v ..._i) κ C))
         (Δs ((v_result κ C) σ_out χ_out ,Ξ ,M) () () ((ctx κ)) ())
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σΔ) (bindΔ ,σ ρ (x ...) (a ...) (v ...)))
         (where ctx ((e ρ_1) (σtoken σΔ) (χtoken ())))
         (where (any_0 ... (v_result σ_out χ_out) any_1 ...) (Mlookup ,M ctx ,σ ,χ))] ;; FIXME: Narrow should use updated σ
    ;; Actually do cont-invocation
    [--> (do-call label (comp κ_call) (v) κ C)
         (Δs ((v κ_call (prompt ctx_1)) ,σ ,χ ,Ξ ,M) () () ((ctx_1 (κ C))) ())
         (where ctx_1 ((comp κ_call) v (σtoken ()) (χtoken ())))
         (side-condition (not (hash-has-key? M (term ctx_1))))]
    ;; Use memo table
    [--> (do-call label (comp κ_call) (v) κ C)
         (Δs ((v_result κ C) σ_out χ_out ,Ξ ,M) () () ((ctx_1 (κ C))) ())
         (where ctx_1 ((comp κ_call) v (σtoken ()) (χtoken ())))
         (where (any_0 ... (v_result σ_out χ_out) any_1 ...) (Mlookup ,M ctx_1 ,σ ,χ))]
    ;; needs further abstracting for a fully terminating analysis. Only here for testing.
    [--> (do-call label + (number ...) κ C)
         (,(apply + (term (number ...))) κ C)]
    [--> (do-call label <= (number ...) κ C)
         (,(apply <= (term (number ...))) κ C)]
    [--> (v (rt ctx) C)
         (Δs ((v κ C) ,σ ,χ ,Ξ ,M) () () () ((ctx (v ,σ ,χ))))
         (where (any_0 ... κ any_1 ...) (Ξlookup ,Ξ ,χ ,χ-token ctx))]
    [--> (v mt (prompt ctx))
         (Δs ((v κ C) ,σ ,χ ,Ξ ,M) () () () ((ctx (v ,σ ,χ))))
         (where (any_0 ... (κ C) any_1 ...) (Ξlookup ,Ξ ,χ ,χ-token ctx))]))

(define Narrow
  (reduction-relation L-SRT
    [--> (name ς (pre-ς σ χ Ξ M))
         (simple-ς_1 ,(update (term σ_1) (term σΔ))
                     ,(update (term χ_1) (term χΔ))
                     ,(update (term Ξ_1) (term ΞΔ))
                     ,(update (term M_1) (term MΔ)))
         (where (any_0 ... (Δs (simple-ς_1 σ_1 χ_1 Ξ_1 M_1) σΔ χΔ ΞΔ MΔ) any_1 ...)
                ,(apply-reduction-relation (R-table (term σ) (term χ) #f #f (term σ) (term χ) (term Ξ) (term M)) (term ς)))]
    [--> (name ς (pre-ς σ χ Ξ M))
         (pre-ς_1 σ χ Ξ M)
         (where (any_0 ... pre-ς_1 any_1 ...)
                ,(apply-reduction-relation (R-table (term σ) (term χ) #f #f (term σ) (term χ) (term Ξ) (term M)) (term ς)))]))

(define (step-system Σ F σ χ σ-token χ-token Ξ M)
  (define-values (Σ* F* σ* χ* σ-token* χ-token* Ξ* M* σΔ? χΔ?)
    (for*/fold ([Σ* Σ] [F* (set)] [σ* σ] [χ* χ] [σ-token σ-token] [χ-token χ-token] [Ξ* Ξ] [M* M] [σΔ? #f] [χΔ? #f])
        ([simple-ς (in-set F)]
         [ςσχΞM (in-list (let ([reds (apply-reduction-relation (R-table σ χ σΔ? χΔ? σ-token χ-token Ξ M) simple-ς)])
                           (when (empty? reds)
                             (printf "Irreducible ~a~%~%" (term (,simple-ς ,σ ,χ ,Ξ ,M))))
                           reds))])
      (match ςσχΞM
        [`(Δs (,simple-ς ,_ ,_ ,_ ,_) ,σΔ ,χΔ ,ΞΔ ,MΔ)
         (define-values (next-σ σsame?) (update/same σ* σΔ))
         (define-values (next-χ χsame?) (update*/same χ* χΔ))
         (define next-Ξ (Ξupdate Ξ* ΞΔ))
         (define next-M (Mupdate M* χ* χ-token Ξ* MΔ))
         (define next-σ-token (cond [(or σΔ? σsame?) σ-token]
                                    [else (add1 σ-token)]))
         (define next-χ-token (cond [(or χΔ? χsame?) χ-token]
                                    [else (add1 χ-token)]))
         (define-values (Σ-next F-next)
           (match (hash-ref Σ* simple-ς #f)
             [(list (== next-σ-token) (== next-χ-token)) (values Σ* F*)]
             [_ (values (hash-set Σ* simple-ς (list next-σ-token next-χ-token)) (set-add F* simple-ς))]))
         (values Σ-next F-next next-σ next-χ next-σ-token next-χ-token next-Ξ next-M σΔ? χΔ?)]
        [simple-ς
         (define-values (Σ-next F-next)
           (match (hash-ref Σ* simple-ς #f)
             [(list (== σ-token) (== χ-token)) (values Σ* F*)]
             [_ (values (hash-set Σ* simple-ς (list σ-token χ-token)) (set-add F* simple-ς))]))
         (values Σ-next F-next σ* χ* σ-token χ-token Ξ* M* σΔ? χΔ?)])))
  (if (set-empty? F*)
      (term (,(for/set ([(ς _) (in-hash Σ*)]
                        #:when (redex-match L (v mt mt) ς))
                (first ς))
             ,σ*))
      (term (,Σ* ,F* ,σ* ,χ* ,σ-token* ,χ-token* ,Ξ* ,M*))))
;;(trace step-system)

(define (injectW e)
  (define ς (term ((,(add-labels e) #hash()) mt mt)))
  ;; Σ F σ χ σ-token χ-token Ξ M
  (term (,(hash ς 0) ,(set ς) #hash() #hash() 0 0 #hash() #hash())))

(define example1
  (term (reset (+ (shift k (+ 10 (k 100)))
                  (shift k* 1)))))

(define example2
  (term ((λ (id)
              ((λ (f)
                  ((λ (g)
                      (<= (g 0) (g 1)))
                   (λ (z) (reset (id (f z))))))
               (λ (y) (shift k (k (k y))))))
           (λ (x) x))))

(define example3
  (term ((λ (id)
            ((λ (f)
                ((λ (g) (g 0 (λ (g0v) (g 1 (λ (g1v) (<= g0v g1v))))))
                 (λ (z h) (h (f z (λ (fv) (id fv (λ (i) i))))))))
             (λ (y j) (j (j y)))))
         (λ (x k) (k x)))))

(define (add-labels e)
  (define c 0) (define (label!) (begin0 c (set! c (add1 c))))
  (let label ([e e])
    (match e
      [`(,(or 'lambda 'λ) (,x ...) ,e)
       `(λ ,x ,(label e))]
      [`(shift ,x ,e) `(shift ,x ,(label e))]
      [`(reset ,e) `(reset ,(label e))]
      [`(,e0 ,es ...)
       `(,(label!) ,(label e0) ,@(map label es))]
      [_ e])))

(apply-reduction-relation* R (term ((,(add-labels example1) #hash()) #hash() mt mt)))

(apply-reduction-relation* (R-table #hash() #hash() #f #f 0 0 #hash() #hash())
                           (term ((,(add-labels example1) #hash()) mt mt)))
(printf "Example 1~%")
(apply-reduction-relation* W (injectW example1))
(printf "Example 2~%")
(apply-reduction-relation* W (injectW example2))
(printf "Example 3~%")
(apply-reduction-relation* W (injectW example3))
