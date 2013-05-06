#lang racket
(require redex)

(define-language L
  [e x (e e) lam (let ([x e]) e)]
  [lam (λf (x) e)]
  [λf λ lambda]
  [x variable-not-otherwise-mentioned]
  ;; Machine
  [ρ (side-condition (name ρ any) (hash? (term ρ)))]
  [σ (side-condition (name σ any) (hash? (term σ)))]  
  [δ ((a vs) ...)]
  [a (x any)] ;; addresses
  [v (lam ρ) (many vs)]
  [vs (side-condition (name vs any) (set? (term vs)))]
  [· (e ρ)] ;; a point is a closed expression
  ;; continuations are lists of frames terminated by mt or a return
  [ϕ (ar ·) (lt x e ρ) (fn v)]
  [k (rt · σ) mt (ϕ k)]
  ;; returns are threaded through a table
  [Ξ (side-condition (name Ξ any) (hash? (term Ξ)))]
  [ς (· k) (v k)]
  [Σ (side-condition (name Σ any) (hash? (term Σ)))]
  [F (side-condition (name F any) (set? (term F)))]
  [σt natural]
  [S (Σ F σ σt Ξ)])

(define-metafunction L
  [(alloc x ς) (x ())]) ;; 0CFA for now.

(define-metafunction L
  [(lookup σ ρ x) ,(hash-ref (term σ) (hash-ref (term ρ) (term x)))])
(define-metafunction L
  [(extend ρ x a) ,(hash-set (term ρ) (term x) (term a))])
(define-metafunction L
  [(σextend σ a (many vs))
   ,(hash-set (term σ) (term a)
              (set-union (hash-ref (term σ) (term a) (set)) (term vs)))]
  [(σextend σ a v)
   ,(hash-set (term σ) (term a)
              (set-add (hash-ref (term σ) (term a) (set)) (term v)))])

(define-metafunction L
  [(unmany (many vs)) vs]
  [(unmany v) ,(set (term v))])
(define-metafunction L
  [(from-many v) ,(set->list (term (unmany v)))])

(define-metafunction L
  [(bind ς σ ρ x v)
   (ρ_1 ((a (unmany v))))
   (where a (alloc x ς))
   (where ρ_1 (extend ρ x a))])

(define-metafunction L
  [(push Ξ (· σ) k) (((· σ) ,(set (term k))))])
(define-metafunction L
  [(pop Ξ (· σ))
   ,(set->list (hash-ref (term Ξ) (term (· σ))))])

(define-metafunction L
  [(injectW e) (,(hash (term ((e #hash()) mt)) 0) ,(set (term ((e #hash()) mt))) #hash() 0 #hash())])

(define (join σ₀ σ₁)
  (for/fold ([σ σ₀]) ([(a vs) (in-hash σ₁)])
    (hash-set σ a (set-union (hash-ref σ a (set)) vs))))

(define R
  (reduction-relation L
    #:arrow -->
    ;; Variable reference
    [--> ({(x ρ) k} σ Ξ)
         ({(many (lookup σ ρ x)) k} () ())]
    ;; Evaluate application
    [--> ({((e_0 e_1) ρ) k} σ Ξ)
         ({(e_0 ρ) ((ar (e_1 ρ)) k)} () ())]
    ;; Evaluate let binding
    [--> ({((let ([x e_0]) e_1) ρ) k} σ Ξ)
         ({(e_0 ρ) ((lt x e_1 ρ) k)} () ())]
    ;; Function done. Evaluate argument
    [--> ({v ((ar ·) k)} σ Ξ)
         ({· ((fn v) k)} () ())]
    ;; Function call
    [--> ((name ς {v ((fn v_f) k)}) σ_0 Ξ)
         ({· (rt · σ_0)} δ (push Ξ (· σ_0) k))
         (where (v_p ... ((λf (x) e) ρ_0) v_s ...) (from-many v_f))
         (where (ρ_1 δ) (bind ς σ_0 ρ_0 x v))       
         (where · (e ρ_1))]
    ;; Let binding
    [--> ((name ς {v ((lt x e ρ_0) k)}) σ_0 Ξ)
         ({· k} δ ())
         (where (ρ_1 δ) (bind ς σ_0 ρ_0 x v))
         (where · (e ρ_1))]
    ;; "Return"
    [--> ({v (rt · σ_rt)} σ Ξ)
         ({v k} () ())
         (where (k_0 ... k k_1 ...) (pop Ξ (· σ_rt)))]
    ;; Answers self-reduce.
    [--> ({v mt} σ Ξ) ({v_0 mt} () ())
         (where (v_p ... v_0 v_s ...) (from-many v))]))

(define W
  (reduction-relation L
    [--> (Σ F σ σt Ξ)
         ,(step-system (term Σ) (term F) (term σ) (term σt) (term Ξ))]))

(define (will-change? σ δ)
  (for/or ([pair (in-list δ)])
    (match pair
      [`(,k ,v)
       (define old (hash-ref σ k (set)))
       (define new (set-union old v))
       (not (= (set-count old) (set-count new)))])))
(define (applyΔ h δ)
  (for/fold ([h h]) ([pair (in-list δ)])
    (match pair
      [`(,k ,v) (hash-set h k (set-union (hash-ref h k (set)) v))])))

(define (step-system Σ F σ σt Ξ)
  (define-values (Σ* F* δ δΞ changes?)
    (for/fold ([Σ* Σ]
               [F* (set)]
               [δ '()]
               [δΞ '()]
               [changes? #f])
        ([ς (in-set F)])
      (for/fold ([Σ* Σ*] [F* F*] [δ δ] [δΞ δΞ] [changes? changes?])
          ([ςσΞ (in-list (apply-reduction-relation R (term (,ς ,σ ,Ξ))))])
        (match ςσΞ
          [`(,ς ,δ* ,δΞ*)
           (define changes* (or changes? (will-change? σ δ*)))
           (values (hash-set Σ* ς σt)
                   (cond
                    [changes* (set-add F* ς)]
                    [(= (hash-ref Σ ς -1) σt) F*]
                    [else (set-add F* ς)])
                   (append δ* δ)
                   (append δΞ* δΞ)
                   changes*)]))))
  (define σ* (applyΔ σ δ))
  (define Ξ* (applyΔ Ξ δΞ))
  (if (set-empty? F*)
      (term (,(for/set ([(ς _) (in-hash Σ*)]
                        #:when (redex-match L (v mt) ς))
                (first ς))
             ,σ*))
      (term (,Σ* ,F* ,σ* ,(if changes? (add1 σt) σt) ,Ξ*))))

(define count-down
  (term (let ([Yf (lambda (f)
                    ((lambda (g0) (f (lambda (x0) ((g0 g0) x0))))
                     (lambda (g1) (f (lambda (x1) ((g1 g1) x1))))))])
          (let ([pred
                 (lambda (n)
                   (lambda (rf)
                     (lambda (rx)
                       (((n (lambda (g2) (lambda (h) (h (g2 rf)))))
                         (lambda (ignored) rx))
                        (lambda (id) id)))))])
            (let ([church3 (lambda (f3) (lambda (x3) (f3 (f3 (f3 x3)))))])
              (let ([true (lambda (xt) (lambda (yt) (xt (lambda (dummy0) dummy0))))])
                (let ([false (lambda (xf) (lambda (yf) (yf (lambda (dummy1) dummy1))))])
                 (let ([church0? (lambda (z) ((z (lambda (zx) false)) true))])
                    (let ([count-down
                           (Yf
                            (λ (count-down)
                              (λ (m)
                                (((church0? m) (λ (dummy2) true))
                                 (λ (dummy3)
                                   (count-down (pred m)))))))])
                      (count-down church3))))))))))

(apply-reduction-relation* W (term (injectW ,count-down)))
