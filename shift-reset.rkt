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
      (term (,xi ,(gensym))))])
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
  [Ξ any]
  [ς (p σ κ C Ξ)])
(define-metafunction L-SRT
  [(Ξextend Ξ ctx (κ C)) ,(hash-join (term Ξ) (term ctx) (set (term (κ C))))])
(define-metafunction L-SRT
  [(Ξlookup Ξ ctx) ,(set->list (hash-ref (term Ξ) (term ctx) (set)))])

(mk-bind bindt L-SRT)

(define R-table
  (reduction-relation L-SRT
    [--> ((prims ρ) σ κ C Ξ) (prims σ κ C Ξ)]
    [--> (((reset e) ρ) σ κ C Ξ)
         ((e ρ) σ mt (prompt ctx) Ξ_1)
         (where ctx ((e ρ) σ))
         (where Ξ_1 (Ξextend Ξ ctx (κ C)))]
    [--> (name ς (((shift x e) ρ) σ κ C Ξ))
         ((e ρ_1) σ_1 mt C Ξ)
         (where (a) (alloc (x) ς))
         (where ctx ((e ρ) σ))
         (where (ρ_1 σ_1) (bindt σ ρ (x) (a) ((comp κ ctx))))]
    [--> ((x ρ) σ κ C Ξ)
         (v σ κ C Ξ)
         (where (any_0 ... v any_1 ...) (σlookup σ (ρlookup ρ x)))]
    [--> (((label e_0 e_rest ...) ρ) σ κ C Ξ)
         ((e_0 ρ) σ ((ev label (e_rest ...) () ρ) κ) C Ξ)]
    [--> (v σ ((ev label (e e_rest ...) (v_done ...) ρ) κ) C Ξ)
         ((e ρ) σ ((ev label (e_rest ...) (v_done ... v) ρ) κ) C Ξ)]
    [--> (v σ ((ev label () (v_fn v_args ...) ρ) κ) C Ξ)
         (do-call label v_fn (v_args ... v) σ κ C Ξ)]
    [--> (v σ ((ev label () () ρ) κ) C Ξ)
         (do-call label v_fn () σ κ C Ξ)]
    [--> (name ς (do-call label ((λ (x ..._i) e) ρ) (v ..._i) σ κ C Ξ))
         ((e ρ_1) σ_1 (rt ctx) C Ξ_1)
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σ_1) (bindt σ ρ (x ...) (a ...) (v ...)))
         (where ctx (e ρ_1 σ_1))
         (where Ξ_1 (Ξextend Ξ ctx κ))]
    [--> (do-call label (comp κ_call ctx) (v) σ κ C Ξ)
         (v σ κ_call (prompt ctx_1) Ξ_1)
         (where ctx_1 ((comp κ_call ctx) v σ))
         (where Ξ_1 (Ξextend Ξ ctx_1 (κ C)))]
    [--> (do-call label + (number ...) σ κ C Ξ)
         (,(apply + (term (number ...))) σ κ C Ξ)]
    [--> (v σ (rt ctx) C Ξ)
         (v σ κ C Ξ)
         (where (any_0 ... κ any_1 ...) (Ξlookup Ξ ctx))]
    [--> (v σ mt (prompt ctx) Ξ)
         (v σ κ C Ξ)
         (where (any_0 ... (κ C) any_1 ...) (Ξlookup Ξ ctx))]))

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
(apply-reduction-relation* R-table (term ((,(add-labels example1) #hash()) #hash() mt mt #hash())))