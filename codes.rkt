#lang racket
(require pict pict/code
         file/convertible
         unstable/gui/pict)

(define pdf? #t)

(define (example stage)
  (parameterize ([current-code-font "LMMono10"]
                 [get-current-code-font-size (λ () 18)])
    (define-values (rt0x rt0y) (values -15 -15))
    (define-values (rt1x rt1y) (values -37 -64))
    (define-values (M0x M0y) (values 7 2))
    (define-values (M1x M1y) (values 35 10))
    (define r0theta (* 1/6 pi))
    (define r1theta (* 0.18 pi))
    (define base
      (parameterize ([get-current-code-font-size (λ () 24)])
        (code (let* ([id (λ (x) #,(tag-pict (code x) 'id-body))]
                     [y #,(tag-pict (code (id 0)) 'id0)]
                     [z #,(tag-pict (code (id 1)) 'id1)])
                #,(tag-pict (code (≤ y z)) 'body)))))
    (define call0
      (pin-arrow-label-line (rotate (code (rt ctx₀)) r0theta)
                            15
                            base
                            (find-tag base 'id0)
                            lc-find
                            (find-tag base 'id-body)
                            ct-find
                            #:start-angle (* 2/3 pi)
                            #:end-angle (* -1/3 pi)
                            #:start-pull 5/14 #:end-pull 1/3
                            #:line-width 2
                            #:x-adjust rt0x #:y-adjust rt0y))
    (define return0
      (pin-arrow-label-line (code M₀)
                            15
                            call0
                            (find-tag base 'id-body)
                            cb-find
                            (find-tag base 'id0)
                            rc-find
                            #:start-angle (* -2/3 pi)
                            #:end-angle pi
                            #:line-width 2
                            #:x-adjust M0x #:y-adjust M0y))
    (define cont0
      (pin-arrow-line 8 return0
                      (find-tag base 'id0)
                      rc-find
                      (find-tag base 'id1)
                      lc-find
                      #:start-angle (* -1/3 pi)
                      #:end-angle (* -7/12 pi)
                      #:start-pull 1/3
                      #:style 'dot))
    (define call1
      (pin-arrow-label-line (rotate (code (rt ctx₁)) r1theta)
                            15
                            cont0
                            (find-tag base 'id1)
                            lc-find
                            (find-tag base 'id-body)
                            ct-find
                            #:start-angle (* 2/3 pi)
                            #:end-angle (* -1/3 pi)
                            #:start-pull 1.2 #:end-pull 1/2
                            #:style 'short-dash
                            #:line-width 2
                            #:x-adjust rt1x #:y-adjust rt1y))
    (define return1
      (pin-arrow-label-line (code M₁)
                            15
                            call1
                            (find-tag base 'id-body)
                            cb-find
                            (find-tag base 'id1)
                            rc-find
                            #:start-angle (* -1/2 pi)
                            #:end-angle pi
                            #:style 'short-dash
                            #:line-width 2
                            #:x-adjust M1x #:y-adjust M1y))
    (define cont1
      (pin-arrow-line 8 return1
                      (find-tag base 'id1)
                      rc-find
                      (find-tag base 'body)
                      lc-find
                      #:start-angle (* -3/5 pi)
                      #:end-angle (* -1/3 pi)
                      #:start-pull 7/24
                      #:end-pull 1/4
                      #:style 'dot))
    (panorama (cond [(= stage 0) base]
                    [(= stage 1) return0]
                    [(= stage 2) return1]
                    [(= stage 3) cont1]))))

(define (impl)
  (code (struct state (point σ κ) #:transparent)
        (struct ar (e ρ) #:transparent)
        (struct fn (v) #:transparent)
        (struct mt () #:transparent)
        (struct rt (ctx) #:transparent)
        (struct ref (x) #:transparent)
        (struct app (e0 e1) #:transparent)
        (struct lam (x e) #:transparent)
        (define-values (F R Seen M Ξ)
             (values (mutable-set) (mutable-set) (mutable-set)
                     (make-hash) (make-hash)))
        (define (hash-add h k v)
          (hash-set h k (set-add (hash-ref h k (set)) v)))
        (define (hash-add! h k v)
          (hash-set! h k (set-add (hash-ref h k (set)) v)))
        (define (add-state! s)
          (unless (set-member? Seen s)
            (set-add! F s)
            (set-add! Seen s)))
        (define (add-reduction! s0 s1)
          (set-add! R (cons s0 s1))
          (add-state! s1))
        (define (step s)
          (match s
           [(state (cons (ref x) ρ) σ κ)
            (for ([v (in-set (hash-ref σ (hash-ref ρ x)))])
              (add-reduction! s (state v σ κ)))]
           [(state (cons (app e0 e1) ρ) σ κ)
            (add-reduction! s
             (state (cons e0 ρ) σ (cons (ar e1 ρ) κ)))]
           [(state v σ (cons (ar e ρ) κ))
            (add-reduction! s
             (state (cons e ρ) σ (cons (fn v) κ)))]
           [(state v σ (cons (fn (cons (lam x e) ρ)) κ))
            (define a (alloc s))
            (define ρ* (hash-set ρ x a))
            (define σ* (hash-add σ a v))
            (define ctx (list e ρ* σ*))
            (hash-add! Ξ ctx κ)
            (match (hash-ref M ctx #f)
              [#f
               (add-reduction! s
                (state (cons e ρ*) σ* (rt ctx)))]
              [results
               (for ([r (in-set results)])
                 (match-define (cons v* σ**) r)
                 (add-state! (state v* σ** κ)))])]
           [(state v σ (rt ctx))
            (hash-add! M ctx (cons v σ))
            (for ([κ (in-set (hash-ref Ξ ctx))])
              (add-reduction! s (state v σ κ)))]))
        (define (analyze e)
          (set-clear! F) (set-clear! R) (set-clear! Seen)
          (hash-clear! Ξ) (hash-clear! M)
          (set-add! F (state (cons e (hash)) (hash) (mt)))
          (let loop ()
            (unless (set-empty? F)
              (define ς (set-first F))
              (set-remove! F ς)
              (step ς)
              (loop)))
          '|the final system|
          (list R M Ξ))))
(define (concrete-alloc)
  (code (λ (s) (gensym))))
(define (monovariant-alloc)
  (code (match-lambda
         [(state _ _ (cons (fn (cons (lam x _) _)) _))
          x])))

(define alloc (match-lambda [(state _ _ (cons (fn (cons (lam x _) _)) _))
                       x]))
(struct state (point σ κ) #:transparent)
(struct ar (e ρ) #:transparent)
(struct fn (v) #:transparent)
(struct mt () #:transparent)
(struct rt (ctx) #:transparent)
(struct ref (x) #:transparent)
(struct app (e0 e1) #:transparent)
(struct lam (x e) #:transparent)

(define-values (F R Seen M Ξ)
  (values (mutable-set) (mutable-set) (mutable-set)
          (make-hash) (make-hash)))
(define (hash-add h k v)
  (hash-set h k (set-add (hash-ref h k (set)) v)))
(define (hash-add! h k v)
  (hash-set! h k (set-add (hash-ref h k (set)) v)))
(define (add-state! s)
  (unless (set-member? Seen s)
    (set-add! F s)
    (set-add! Seen s)))
(define (add-reduction! s0 s1)
  (set-add! R (cons s0 s1))
  (add-state! s1))
(define (step s)
  (match s
    [(state (cons (ref x) ρ) σ κ)
     (printf "WTF ~a~%~a~%" s x)
     (define a (hash-ref ρ x (λ () (error 'var-lookup "Var ~a" x))))
     (for ([v (in-set (hash-ref σ a (λ () (error 'addr-lookup "Addr ~a" a))))])
       (add-reduction! s (state v σ κ)))]
    [(state (cons (app e0 e1) ρ) σ κ)
     (add-reduction! s
                     (state (cons e0 ρ) σ (cons (ar e1 ρ) κ)))]
    [(state v σ (cons (ar e ρ) κ))
     (add-reduction! s
                     (state (cons e ρ) σ (cons (fn v) κ)))]
    [(state v σ (cons (fn (cons (lam x e) ρ)) κ))
     (define a (alloc s))
     (define ρ* (hash-set ρ x a))
     (define σ* (hash-add σ a v))
     (define ctx (list e ρ* σ*))
     (hash-add! Ξ ctx κ)
     (match (hash-ref M ctx #f)
       [#f
        (add-reduction! s
                        (state (cons e ρ*) σ* (rt ctx)))]
       [results
        (for ([r (in-set results)])
          (match-define (cons v* σ**) r)
          (add-state! (state v* σ** κ)))])]
    [(state v σ (rt ctx))
     (hash-add! M ctx (cons v σ))
     (for ([κ (in-set (hash-ref Ξ ctx (λ () (error 'bad-return "Context ~a" ctx))))])
       (add-reduction! s (state v σ κ)))]
    [_ (void)]))

(define (analyze e)
  (set-clear! F)
  (set-clear! R)
  (set-clear! Seen)
  (hash-clear! Ξ)
  (hash-clear! M)
  (set-add! F (state (cons e (hash)) (hash) (mt)))
  (let loop ()
    (unless (set-empty? F)
      (define ς (set-first F))
      (set-remove! F ς)
      (step ς)
      (loop)))
  R)
(analyze (app (lam 'x (ref 'x))
              (lam 'y (ref 'y))))

(define ((to-pdf prefix i) p)
  (with-output-to-file (if i
                           (format "~a~a.pdf" prefix i)
                           (format "~a.pdf" prefix))
    #:exists 'replace
    (λ () (write-bytes (convert p 'pdf-bytes)))))
(for/list ([i 4]) 
  ((if pdf? (to-pdf "example" i) values) (example i)))
((to-pdf "impl" #f) (impl))
((to-pdf "calloc" #f) (concrete-alloc))
((to-pdf "malloc" #f) (monovariant-alloc))
#|
(code (define (touch-kont κ Ξ)
        (define seen (mutable-seteq))
        (let loop ([κ κ])
          (match κ
            [(mt) ∅]
            [(cons φ κ) (∪ $\touchesf(φ)$ (loop κ))]
            [(rt ctx)
             (cond
              [(set-member? seen ctx) ∅]
              [else
               (set-add! seen ctx)
               (for/union ([κ (in-set ctx)]) (loop κ))])]))))

(code (let* ([id (λ (x) x)]
             [f (λ (y) (shift k (k (k y))))]
             [g (λ (z) (reset (id (f z))))])
        (≤ (g 0) (g 1))))

(code (let* ([id (λ (x k) (k x))]
             [f (λ (y j) (j (j y)))]
             [g (λ (z h) (h (f z (λ (fv) (id fv (λ (i) i))))))])
        (g 0 (λ (g0v) (g 1 (λ (g1v) (≤ g0v g1v)))))))

|#