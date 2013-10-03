#lang racket

(provide L R)
(require redex racket/trace)
(define-language L
  [e x (label e e ...) (λ (x ...) e) (shift x e) (reset e) prims]
  [prims number + <= #t #f]
  [label natural]
  [(σ ρ Ξ M) any]
  [f (ev label (e ...) (v ...) ρ)]
  [a any]
  [(ks vs as) (side-condition (name vs any) (set? (term vs)))]  
  [v (clos (λ (x ...) e) ρ) prims]
  [x variable-not-otherwise-mentioned])

(define-syntax-rule (for/union guards body ...) (for/fold ([acc (set)]) guards (set-union acc (let () body ...))))

(define (hash-join σ a vs) (hash-set σ a (set-union (hash-ref σ a (set)) vs)))
(define (hashes-join σ σ*)
  (for*/fold ([σ σ]) ([(a vs*) (in-hash σ*)]
                      [vs (in-value (hash-ref σ a (set)))]
                      #:unless (eq? vs vs*))
    (hash-set σ a (set-union vs vs*))))
(define (hashes-join/change? σ σ*)
  (for*/fold ([σ σ] [change? #f])
      ([(a vs*) (in-hash σ*)]
       [vs (in-value (hash-ref σ a (set)))]
       #:unless (eq? vs vs*)) ;; speed up joins
    (define vs-next (set-union vs vs*))
    ;; Not eq, but union to same thing.
    (if (= (set-count vs-next) (set-count vs))
        (values σ change?)
        (values (hash-set σ a vs-next) #t))))
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
(define-syntax-rule (mk-bind name L)
  (...
   (define-metafunction L
     [(name σ ρ (x ...) (a ...) (v ...))
      (,(hash-set-many (term ρ) (term (x ...)) (term (a ...)))
       ,(hash-join-many (term σ) (term (a ...)) (term (v ...))))])))

(define-extended-language L-SR L
  [κ mt (f κ)]
  [C (∘ κ C) mt]
  [p (e ρ) v]
  [v .... (comp κ)]
  [ς (p σ κ C)
     (do-call label v (v ...) σ κ C)])
(mk-bind bind L-SR)

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
  [ctx ((e ρ) σ) (v v σ)
       ((e ρ) a)]
  [(Σ F) any]
  [ς ((p κ C) σ Ξ M)
     ((do-call label v (v ...) κ C) σ Ξ M)])
(define-metafunction L-SRT
  [(Ξextend Ξ ctx (κ C)) ,(hash-join (term Ξ) (term ctx) (set (term (κ C))))]
  [(Ξextend Ξ ctx κ) ,(hash-join (term Ξ) (term ctx) (set (term κ)))])
(define-metafunction L-SRT
  [(Mextend M ctx v σ) ,(hash-join (term M) (term ctx) (set (term v)))]) ;; for wide. (Narrow is (v σ))
(define-metafunction L-SRT
  [(Ξlookup Ξ ctx) ,(set->list
                     ((term-match/single L-SRT
                        [((e ρ) (side-condition (name a a) (not (hash? (term a)))))
                         (let ([mer
                                (for/union ([σ (in-set (hash-ref (term Ξ) (term a) (set)))])
                                  (hash-ref (term Ξ) (term ((e ρ) ,σ)) (set)))])
                           (printf "Here ~a ~a~%" (term ctx) mer)
                           mer)]
                        [_ (let ([res (hash-ref (term Ξ) (term ctx) (set))])
                             (printf "lookup ~a ~a~%" (term ctx) res)
                             res)])
                      (term ctx)))])
(define-metafunction L-SRT
  [(Mlookup M ctx σ) ,(for/list ([vσ (in-set (hash-ref (term M) (term ctx) (set)))])
                        (list vσ (term σ)))]) ;; for wide. (Narrow is just vσ)
(define-metafunction L-SRT
  [(approximate Ξ (rt ((e ρ) (side-condition (name σ σ) (hash? (term σ))))) a)
   (,(hash-join (term Ξ) (term a) (set (term σ)))
    (rt ((e ρ) a)))]
  [(approximate Ξ (f κ) a)
   (Ξ_1 (f κ_1))
   (where (Ξ_1 κ_1) (approximate Ξ κ a))]
  [(approximate Ξ mt a) (Ξ mt)])

(define W
  (reduction-relation L-SRT
    [--> (Σ F σ Ξ M)
         ,(step-system (term Σ) (term F) (term σ) (term Ξ) (term M))]))

(mk-bind bindt L-SRT)

(define R-table
  (reduction-relation L-SRT
    [--> (((prims ρ) κ C) σ Ξ M) ((prims κ C) σ Ξ M)]
    [--> ((((λ (x ...) e) ρ) κ C) σ Ξ M)
         (((clos (λ (x ...) e) ρ) κ C) σ Ξ M)]
    ;; Actually do prompt
    [--> ((((reset e) ρ) κ C) σ Ξ M)
         (((e ρ) mt (prompt ctx)) σ Ξ_1 M)
         (where ctx ((e ρ) σ))
         (where Ξ_1 (Ξextend Ξ ctx (κ C)))
         (side-condition (not (hash-has-key? (term M) (term ctx))))]
    ;; Use memo for prompt
    [--> ((((reset e) ρ) κ C) σ Ξ M)
         ((v κ C) σ_out Ξ_1 M)
         (where ctx ((e ρ) σ))
         (where Ξ_1 (Ξextend Ξ ctx (κ C)))
         (where (any_0 ... (v σ_out) any_1 ...) (Mlookup M ctx σ))]
    [--> ((name ς (((shift x e) ρ) κ C)) σ Ξ M)
         (((e ρ_1) mt C) σ_1 Ξ_1 M)
         (where (a) (alloc (x) ς))
         (where ctx ((e ρ) σ))
         (where (Ξ_1 κ_1) (approximate Ξ κ a))
         (where (ρ_1 σ_1) (bindt σ ρ (x) (a) ((comp κ_1))))]
    [--> (((x ρ) κ C) σ Ξ M)
         ((v κ C) σ Ξ M)
         (where (any_0 ... v any_1 ...) (σlookup σ (ρlookup ρ x)))]
    [--> ((((label e_0 e_rest ...) ρ) κ C) σ Ξ M)
         (((e_0 ρ) ((ev label (e_rest ...) () ρ) κ) C) σ Ξ M)]
    [--> ((v ((ev label (e e_rest ...) (v_done ...) ρ) κ) C) σ Ξ M)
         (((e ρ) ((ev label (e_rest ...) (v_done ... v) ρ) κ) C) σ Ξ M)]
    [--> ((v ((ev label () (v_fn v_args ...) ρ) κ) C) σ Ξ M)
         ((do-call label v_fn (v_args ... v) κ C) σ Ξ M)]
    [--> ((v ((ev label () () ρ) κ) C) σ Ξ M)
         ((do-call label v () κ C) σ Ξ M)]
    ;; actually do call
    [--> ((name ς (do-call label (clos (λ (x ..._i) e) ρ) (v ..._i) κ C)) σ Ξ M)
         (((e ρ_1) (rt ctx) C) σ_1 Ξ_1 M)
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σ_1) (bindt σ ρ (x ...) (a ...) (v ...)))
         (where ctx ((e ρ_1) σ_1))
         (where Ξ_1 (Ξextend Ξ ctx κ))
         (side-condition (not (hash-has-key? (term M) (term ctx))))]
    ;; Use memo table
    [--> ((name ς (do-call label (clos (λ (x ..._i) e) ρ) (v ..._i) κ C)) σ Ξ M)
         ((v_result κ C) σ_out Ξ_1 M)
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σ_1) (bindt σ ρ (x ...) (a ...) (v ...)))
         (where ctx ((e ρ_1) σ_1))
         (where Ξ_1 (Ξextend Ξ ctx κ))
         (where (any_0 ... (v_result σ_out) any_1 ...) (Mlookup M ctx σ))]
    ;; Actually do cont-invocation
    [--> ((do-call label (comp κ_call) (v) κ C) σ Ξ M)
         ((v κ_call (prompt ctx_1)) σ Ξ_1 M)
         (where ctx_1 ((comp κ_call) v σ))
         (where Ξ_1 (Ξextend Ξ ctx_1 (κ C)))
         (side-condition (not (hash-has-key? (term M) (term ctx_1))))]
    ;; Use memo table
    [--> ((do-call label (comp κ_call) (v) κ C) σ Ξ M)
         ((v_result κ C) σ_out Ξ_1 M)
         (where ctx_1 ((comp κ_call) v σ))
         (where Ξ_1 (Ξextend Ξ ctx_1 (κ C)))
         (where (any_0 ... (v_result σ_out) any_1 ...) (Mlookup M ctx_1 σ))]
    ;; needs further abstracting for a fully terminating analysis. Only here for testing.
    [--> ((do-call label + (number ...) κ C) σ Ξ M)
         ((,(apply + (term (number ...))) κ C) σ Ξ M)]
    [--> ((do-call label <= (number ...) κ C) σ Ξ M)
         ((,(apply <= (term (number ...))) κ C) σ Ξ M)]
    [--> ((v (rt ctx) C) σ Ξ M)
         ((v κ C) σ Ξ M_1)
         (where (any_0 ... κ any_1 ...) (Ξlookup Ξ ctx))
         (where M_1 (Mextend M ctx v σ))]
    [--> ((v mt (prompt ctx)) σ Ξ M)
         ((v κ C) σ Ξ M_1)
         (where (any_0 ... (κ C) any_1 ...) (Ξlookup Ξ ctx))
         (where M_1 (Mextend M ctx v σ))]))

(define (rewrite-ctx ctx σ)
  ((term-match/single L-SRT
     [((e ρ) any) (term ((e ρ) ,σ))]
     [(v_0 v_1 any) (term (v_0 v_1 ,σ))]
     [_ #f])
   ctx))

(define (step-system Σ F σ Ξ M)
  (define-values (ς-out σ* Ξ* M* change?)
    (for/fold ([ς-out (set)]
               [σ* σ]
               [Ξext #hash()]
               [Mext #hash()]
               [change? #f])
        ([ς (in-set F)])
      (define reds (apply-reduction-relation R-table (term (,ς ,σ ,Ξ ,M))))
      (when (empty? reds)
        (printf "Irreducible ~a~%~%" (term (,ς ,σ ,Ξ ,M))))
      (for/fold ([ς-out ς-out] [σ* σ*] [Ξext Ξext] [Mext Mext] [change? change?])
          ([ςσΞM (in-list reds)])
        (match ςσΞM
          [`(,ς ,σ** ,Ξ** ,M**)
           (define-values (next-σ change?) (hashes-join/change? σ* σ**))
           (define next-Ξ (hashes-join Ξext Ξ**))
           (define next-M (hashes-join Mext M**))
           (values (set-add ς-out ς) next-σ next-Ξ next-M change?)]
          [bad (error 'step-system "Bad ~a" bad)]))))
  (define next-ς
    (for/set ([ς (in-set ς-out)])
      ((term-match/single L-SRT
         [((e ρ) (rt ((e_1 ρ_1) (side-condition (name a a) (not (hash? (term a)))))) C) ς]
         [((e ρ) (rt ctx) C) (term ((e ρ) (rt ,(rewrite-ctx (term ctx) σ*)) C))]
         [((e ρ) mt (prompt ctx)) (term ((e ρ) mt (prompt ,(rewrite-ctx (term ctx) σ*))))]
         [_ ς])
       ς)))
  (define next-Ξ
    (for/fold ([Ξ Ξ]) ([(ctx κs) (in-hash Ξ*)])
      (match (rewrite-ctx ctx σ*)
        [#f (hash-join Ξ ctx (set σ*))]
        [ctx* (hash-join Ξ ctx* κs)])))
  (define next-M
    (for/fold ([M M]) ([(ctx vσs) (in-hash M*)])
      (hash-join M (rewrite-ctx ctx σ*) vσs)))
  (define-values (Σ* F*)
    (if change?
        (values (for/fold ([Σ* Σ]) ([ς (in-set next-ς)]) (hash-set Σ ς σ*)) ς-out)
        (for/fold ([Σ* Σ] [F* (set)])
            ([ς (in-set ς-out)]
             #:unless (equal? (hash-ref Σ ς #f) σ*))
          (values (hash-set Σ* ς σ*) (set-add F* ς)))))
  (if (set-empty? F*)
      (term (,(for/set ([(ς _) (in-hash Σ*)]
                        #:when (redex-match L (v mt mt) ς))
                (first ς))
             ,σ*))
      (term (,Σ* ,F* ,σ* ,next-Ξ ,next-M))))

(define (injectW e)
  (define ς (term ((,(add-labels e) #hash()) mt mt)))
  (term (,(hash ς #hash()) ,(set ς) #hash() #hash() #hash())))

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
(apply-reduction-relation* R-table (term (((,(add-labels example1) #hash()) mt mt) #hash() #hash())))
(printf "Example 1~%")
(apply-reduction-relation* W (injectW example1))
(printf "Example 2~%")
(apply-reduction-relation* W (injectW example2))
(printf "Example 3~%")
(apply-reduction-relation* W (injectW example3))