#lang racket

(provide L R)
(require redex)
(define-language L
  [e x (label e e ...) (λ (x ...) e) (shift x e) (reset e) prims]
  [prims number +]
  [label natural]
  [(σ ρ Ξ) any]
  [f (ev label (e ...) (v ...) ρ)]
  [a any]
  [(ks vs as) (side-condition (name vs any) (set? (term vs)))]  
  [v ((λ (x ...) e) ρ) prims]
  [x variable-not-otherwise-mentioned])

(define (hash-join σ a vs) (hash-set σ a (set-union (hash-ref σ a (set)) vs)))
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
(define-metafunction L [(ρlookup ρ x) ,(hash-ref (term ρ) (term x))])
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
    [--> (name ς (do-call label ((λ (x ..._i) e) ρ) (v ..._i) σ κ C))
         ((e ρ_1) σ_1 κ C)
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σ_1) (bind σ ρ (x ...) (a ...) (v ...)))]
    [--> (do-call label (comp κ_call) (v) σ κ C)
         (v σ κ_call (∘ κ C))]
    [--> (do-call label + (number ...) σ κ C)
         (,(apply + (term (number ...))) σ κ C)]
    [--> (v σ mt (∘ κ C))
         (v σ κ C)]))

(define-extended-language L-SRT L
  [κ mt (rt ctx) (f κ)]
  [C (prompt ctx) mt]
  [p (e ρ) v]
  [v .... (comp κ ctx)]
  [ctx ((e ρ) σ) (v v σ)]
  [(Σ F) any]
  [ς ((p κ C) σ Ξ) ((do-call label v (v ...) κ C) σ Ξ)])
(define-metafunction L-SRT
  [(Ξextend Ξ ctx (κ C)) ,(hash-join (term Ξ) (term ctx) (set (term (κ C))))])
(define-metafunction L-SRT
  [(Ξlookup Ξ ctx) ,(set->list (hash-ref (term Ξ) (term ctx) (set)))])

(define W
  (reduction-relation L-SRT
    [--> (Σ F σ Ξ)
         ,(step-system (term Σ) (term F) (term σ) (term Ξ))]))

(mk-bind bindt L-SRT)

(define R-table
  (reduction-relation L-SRT
    [--> (((prims ρ) κ C) σ Ξ) ((prims κ C) σ Ξ)]
    [--> ((((reset e) ρ) κ C) σ Ξ)
         (((e ρ) mt (prompt ctx)) σ Ξ_1)
         (where ctx ((e ρ) σ))
         (where Ξ_1 (Ξextend Ξ ctx (κ C)))]
    [--> ((name ς (((shift x e) ρ) κ C)) σ Ξ)
         (((e ρ_1) mt C) σ_1 Ξ)
         (where (a) (alloc (x) ς))
         (where ctx ((e ρ) σ))
         (where (ρ_1 σ_1) (bindt σ ρ (x) (a) ((comp κ ctx))))]
    [--> (((x ρ) κ C) σ Ξ)
         ((v κ C) σ Ξ)
         (where (any_0 ... v any_1 ...) (σlookup σ (ρlookup ρ x)))]
    [--> ((((label e_0 e_rest ...) ρ) κ C) σ Ξ)
         (((e_0 ρ) ((ev label (e_rest ...) () ρ) κ) C) σ Ξ)]
    [--> ((v ((ev label (e e_rest ...) (v_done ...) ρ) κ) C) σ Ξ)
         (((e ρ) ((ev label (e_rest ...) (v_done ... v) ρ) κ) C) σ Ξ)]
    [--> ((v ((ev label () (v_fn v_args ...) ρ) κ) C) σ Ξ)
         ((do-call label v_fn (v_args ... v) κ C) σ Ξ)]
    [--> ((v ((ev label () () ρ) κ) C) σ Ξ)
         ((do-call label v_fn () κ C) σ Ξ)]
    [--> ((name ς (do-call label ((λ (x ..._i) e) ρ) (v ..._i) κ C)) σ Ξ)
         (((e ρ_1) (rt ctx) C σ_1) Ξ_1)
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σ_1) (bindt σ ρ (x ...) (a ...) (v ...)))
         (where ctx (e ρ_1 σ_1))
         (where Ξ_1 (Ξextend Ξ ctx κ))]
    [--> ((do-call label (comp κ_call ctx) (v) κ C) σ Ξ)
         ((v κ_call (prompt ctx_1)) σ Ξ_1)
         (where ctx_1 ((comp κ_call ctx) v σ))
         (where Ξ_1 (Ξextend Ξ ctx_1 (κ C)))]
    ;; Needs further abstracting for a fully terminating analysis. Only here for testing.
    [--> ((do-call label + (number ...) κ C) σ Ξ)
         ((,(apply + (term (number ...))) κ C) σ Ξ)]
    [--> ((v (rt ctx) C) σ Ξ)
         ((v κ C) σ Ξ)
         (where (any_0 ... κ any_1 ...) (Ξlookup Ξ ctx))]
    [--> ((v mt (prompt ctx)) σ Ξ)
         ((v κ C) σ Ξ)
         (where (any_0 ... (κ C) any_1 ...) (Ξlookup Ξ ctx))]))

(define (step-system Σ F σ Ξ)
  (define-values (ς-out σ* Ξ* change?)
    (for/fold ([ς-out (set)]
               [σ* σ]
               [Ξ* Ξ]
               [change? #f])
        ([ς (in-set F)])
      (define reds (apply-reduction-relation R-table (term (,ς ,σ ,Ξ))))
      (when (empty? reds)
        (printf "Irreducible ~a~%~%" (term (,ς ,σ ,Ξ))))
      (for/fold ([ς-out ς-out] [σ* σ*] [Ξ* Ξ*] [change? change?])
          ([ςσΞ (in-list reds)])
        (match ςσΞ
          [`(,ς ,σ** ,Ξ**)
           (define-values (next-σ change?) (hashes-join/change? σ* σ**))
           (define-values (next-Ξ ignore) (hashes-join/change? Ξ* Ξ**))
           (values (set-add ς-out ς) next-σ next-Ξ change?)]))))
  (define-values (Σ* F*)
    (if change?
        (values (for/fold ([Σ* Σ]) ([ς (in-set ς-out)]) (hash-set Σ ς σ*)) ς-out)
        (for/fold ([Σ* Σ] [F* (set)])
            ([ς (in-set ς-out)]
             #:unless (equal? (hash-ref Σ ς #f) σ*))
          (values (hash-set Σ* ς σ*) (set-add F* ς)))))
  (if (set-empty? F*)
      (term (,(for/set ([(ς _) (in-hash Σ*)]
                        #:when (redex-match L (v mt mt) ς))
                (first ς))
             ,σ*))
      (term (,Σ* ,F* ,σ* ,Ξ*))))

(define (injectW e)
  (define ς (term ((,(add-labels example1) #hash()) mt mt)))
  (term (,(hash ς #hash()) ,(set ς) #hash() #hash())))

(define example1
  (term (reset (+ (shift k (+ 10 (k 100)))
                  (shift k* 1)))))

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
(apply-reduction-relation* W (injectW example1))