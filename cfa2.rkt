#lang racket
(require redex)

(define-language L
  [e (x ℓ) (e e) lam (let ([x e]) e)]
  [lam (λf (x) e)]
  [ℓ natural]
  [λf λ lambda]
  [x variable-not-otherwise-mentioned]
  ;; Machine
  [(ξ ρ σ) (side-condition (name ρ any) (hash? (term ρ)))]
  [δ ((a vs) ...)]
  [a (x any)] ;; addresses
  [v (lam ρ) (many vs)]
  [vs (side-condition (name vs any) (set? (term vs)))]
  [· (e ρ)] ;; a point is a closed expression
  ;; continuations are lists of frames terminated by mt or a return
  [ϕ (ar · fake) (fn v fake) (lt x e ρ)]
  [k (rt ctx) mt (ϕ k)]
  [ctx (· ξ fake v σt)]
  [fake #f a]
  ;; returns are threaded through a table
  [Ξ (side-condition (name Ξ any) (hash? (term Ξ)))]
  [ς (· ξ k) (v ξ k)]
  [Σ (side-condition (name Σ any) (hash? (term Σ)))]
  [F (side-condition (name F any) (set? (term F)))]
  [σt natural]
  [S (Σ F σ σt Ξ)])

;; Simple escape pre-analysis (tree-walk)
(define stackable-references #f)
(define stack-binders #f)
(define (stackable? ℓ) (hash-ref stackable-references ℓ #f))
(define (stack-binder? x) (hash-ref stack-binders x #t))
(define (classify-program! e)
  (set! stackable-references (make-hash))
  (set! stack-binders (make-hash))
  (let recur ([e e] [currentλ #f] [bindingλ (hasheq)])
    ((term-match/single L
       [(x ℓ) (if (eq? (hash-ref bindingλ (term x)) currentλ)
                  (hash-set! stackable-references (term ℓ) #t)
                  (hash-set! stack-binders (term x) #f))]
       [(λf (x) e_body) (recur (term e_body) e (hash-set bindingλ (term x) e))]
       [(let ([x e_clause]) e_body) 
        (begin (recur (term e_clause) currentλ bindingλ)
               (recur (term e_body) currentλ (hash-set bindingλ (term x) currentλ)))]
       [(e_0 e_1)
        (begin (recur (term e_0) currentλ bindingλ)
               (recur (term e_1) currentλ bindingλ))])
     e)))

(define-metafunction L
  [(unfakeable? (x ℓ) ρ) ,(and (stackable? (term ℓ)) (hash-ref (term ρ) (term x)))]
  [(unfakeable? e ρ) #f])
;; We know v is not a "many" form. Just wrap with set.
(define-metafunction L
  [(unfake ξ #f v) ξ]
  [(unfake ξ a v) (ξextend ξ a ,(set (term v)))])

(define-metafunction L
  [(alloc x ς) (x ())]) ;; 0CFA for now.

(define-metafunction L
  [(lookup σ ρ ξ x ℓ) ,(let ([a (hash-ref (term ρ) (term x))])
                         (if (stackable? (term ℓ))
                             (hash-ref (term ξ) a (λ () (error 'lookup "Bad ξ ~a" a)))
                             (hash-ref (term σ) a)))])
(define-metafunction L
  [(extend ρ x a) ,(hash-set (term ρ) (term x) (term a))])
(define-metafunction L
  [(ξextend ξ a vs) ,(hash-set (term ξ) (term a) (term vs))])
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
   (ρ_1 ,(hash (term a) (term (unmany v))) ((a (unmany v))))
   (where a (alloc x ς))
   (where ρ_1 (extend ρ x a))])

(define-metafunction L
  [(bind-let ς σ ρ ξ x v)
   (ρ_1 ξ_1 ((a (unmany v))))
   (where a (alloc x ς))
   (where ξ_1 (ξextend ξ a (unmany v)))
   (where ρ_1 (extend ρ x a))])
(define-metafunction L
  [(push Ξ ctx ξ k) ((ctx ,(set (term (ξ k)))))])
(define-metafunction L
  [(pop Ξ ctx) ,(set->list (hash-ref (term Ξ) (term ctx)))])

(define-metafunction L
  [(injectW e)
   (,(begin (classify-program! (term e))
            (hash (term ((e #hash()) mt)) 0))
    ,(set (term ((e #hash()) #hash() mt)))
    #hash()
    0
    #hash())])

(define (join σ₀ σ₁)
  (for/fold ([σ σ₀]) ([(a vs) (in-hash σ₁)])
    (hash-set σ a (set-union (hash-ref σ a (set)) vs))))

(define R
  (reduction-relation L
    #:arrow -->
    ;; Variable reference
    [--> ({((x ℓ) ρ) ξ k} σ σt Ξ)
         ({(many (lookup σ ρ ξ x ℓ)) ξ k} () ())]
    ;; Evaluate application
    [--> ({((e_0 e_1) ρ) ξ k} σ σt Ξ)
         ({(e_0 ρ) ξ ((ar (e_1 ρ) (unfakeable? e_0 ρ)) k)} () ())]
    ;; Evaluate let binding
    [--> ({((let ([x e_0]) e_1) ρ) ξ k} σ σt Ξ)
         ({(e_0 ρ) ξ ((lt x e_1 ρ) k)} () ())]
    ;; Function done. Evaluate argument
    [--> ({v ξ ((ar · fake) k)} σ σt Ξ)
         ({· ξ ((fn v fake) k)} () ())]
    ;; Function call
    [--> ((name ς {v ξ ((fn v_f fake) k)}) σ_0 σt Ξ)
         ({· ξ_1 (rt ctx)} δ (push Ξ ctx ξ k))
         (where (v_p ... v_call v_s ...) (from-many v_f))
         (where ((λf (x) e) ρ_0) v_call)
         (where (ρ_1 ξ_1 δ) (bind ς σ_0 ρ_0 x v))       
         (where · (e ρ_1))
         (where ctx (· ξ_1 fake v_call σt))]
    ;; Let binding
    [--> ((name ς {v ξ ((lt x e ρ_0) k)}) σ_0 σt Ξ)
         ({· ξ_1 k} δ ())
         (where (ρ_1 ξ_1 δ) (bind-let ς σ_0 ρ_0 ξ x v))
         (where · (e ρ_1))]
    ;; "Return" and fix fake rebinding if it can be fixed.
    [--> ({v ξ (rt (name ctx (· ξ_ignore fake v_call σt_rt)))} σ σt Ξ)
         ({v (unfake ξ_rt fake v_call) k} () ())
         (where (any_0 ... (ξ_rt k) any_1 ...) (pop Ξ ctx))]
    ;; Answers self-reduce.
    [--> ({v ξ mt} σ σt Ξ) ({v_0 ξ mt} () ())
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
      (define reds (apply-reduction-relation R (term (,ς ,σ ,σt ,Ξ))))
      (when (empty? reds)
        (printf "Irreducible ~a~%~%" (term (,ς ,σ ,σt ,Ξ))))
      (for/fold ([Σ* Σ*] [F* F*] [δ δ] [δΞ δΞ] [changes? changes?])
          ([ςσΞ (in-list reds)])
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
                        #:when (redex-match L (v ξ mt) ς))
                (first ς))
             ,σ*))
      (term (,Σ* ,F* ,σ* ,(if changes? (add1 σt) σt) ,Ξ*))))

;; Helper to make example programs not have to uniquely label all references.
(define (label-references e)
  (define counter 0)
  (define (count!) (begin0 counter (set! counter (add1 counter))))
  (let loop ([e e])
    (match e
      [`(,(or 'lambda 'λ) (,x) ,e) `(λ (,x) ,(loop e))]
      [`(let ([,x ,e]) ,ebody) `(let ([,x ,(loop e)]) ,(loop ebody))]
      [(? symbol? x) `(,x ,(count!))]
      [`(,e0 ,e1) `(,(loop e0) ,(loop e1))])))

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

(apply-reduction-relation* W (term (injectW ,(label-references count-down))))

