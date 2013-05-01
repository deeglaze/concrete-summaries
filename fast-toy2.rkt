#lang racket
(require racket/trace)

;; Expressions
(struct exp (ℓ) #:transparent)
(struct lam exp (x body) #:transparent)
(struct app exp (ℓf e0 e1) #:transparent)
(struct letf exp (x e0 e1) #:transparent) ;; CFA2-specific
(struct var exp (r? x) #:transparent)

;; Values
(struct clos (x e ρ) #:transparent)
(struct many (vs) #:transparent)

;; Frames
(struct ar (ℓapp ℓf fr e ρ) #:transparent)
(struct lt (x e ρ) #:transparent)
(struct fn (ℓapp fr a) #:transparent)
;; Continuation tails
(struct mt () #:transparent)
(struct rt (ξp fr fnv) #:transparent)

;; A Kont is either
;; - (cons Frame Kont)
;; - Continuation tail

;; Points
;; ξ is CFA2-specific
(struct epoint (e ρ) #:transparent)
(struct vpoint (v) #:transparent)

(struct state (p #;σ #;ξ k
               ) #:transparent)
(struct answer (v #;σ #;ξ
                ) #:transparent)

(define r-only #f) ;; CFA2-specific
(define addr-var #f)
(define (r-only? a)
#f
#;#;#;
  (define var (hash-ref addr-var a))
  (when (>= var (vector-length r-only))
    (error 'r-only "Bad var ~a ~a~%" var a))
  ;; alloc for x s returns x, and x is an integer
  (vector-ref r-only var))

(define Ξ #f)
(define σ #f) (define σt 0)
(define seen #f)
(define todo #f)
(define answers #f)
(define (add-todo! s)
  (define st (hash-ref seen s -1))
  (cond [(= st σt) (void)]
        [else (hash-set! seen s σt)
              (set! todo (set-add todo s))]))
(define-match-expander state: (λ (stx) (syntax-case stx () [(_ p σ ξ k) #'(state p #;ξ k
                                                                                 )])))
(define-match-expander answer: (λ (stx) (syntax-case stx () [(_ v σ ξ) #'(answer v #;ξ
                                                                                 )])))
(define-syntax-rule (add-state! p σ ξ k) (add-todo! (state p #;ξ k
                                                           )))
(define-syntax-rule (add-answer! v σ ξ) (set! answers (set-add answers v #;(cons v ξ)
                                                               )))
(define-syntax-rule (define-σext (σ ξ) e) (define ξ e))

(define (note-return-point! pξ k #;ξ
                            )
  (match k
    [(rt ξp fr fnv)
     (hash-set! Ξ pξ (set-union (hash-ref Ξ pξ (set)) (hash-ref Ξ ξp)))]
    [_ (hash-set! Ξ pξ (set-add (hash-ref Ξ pξ (set)) k #;(cons ξ k)
                                ))]))

(define (grow-store!)
  (set! σ
   (for/vector #:length (* 2 (vector-length σ)) #:fill (set)
               ([v (in-vector σ)]) v)))

(define allocd (make-hash))
(define count 0)
(define (alloc x s) 
  (hash-set! allocd x #t)
  (define res count)
  (set! count (add1 count))
  (when (>= count (vector-length σ)) (grow-store!))
  (hash-set! addr-var res x)
  res)
(define ρextend hash-set)

(define (σextend σ a vs)
  (define old (vector-ref σ a))
  (define new (set-union old vs))
  (unless (= (set-count old) (set-count new))
    (vector-set! σ a new)
    (set! σt (add1 σt))))
;(trace σextend)

(define (bind-call σ a v)
  (define vs (match v [(many vs) vs] [_ (set v)]))
  (unless (r-only? a)
    (σextend σ a vs))
  #;(hash a vs)
  (hash))
;(trace bind-call)

(define (bind-let σ #;ξ a v
                  )
  (define vs (match v [(many vs) vs] [_ (set v)]))
  (unless (r-only? a)
    (σextend σ a vs))
;  (when (hash-has-key? ξ a) (error 'bind-let "Has key ~a ~a" ξ a))
  #;(hash-set ξ a vs)
  (hash)
  )
;(trace bind-let)

(define (bind-intermediate σ #;ξ a v
                           )
  (σextend σ a (match v [(many vs) vs] [_ (set v)]))
#;  (when (hash-has-key? ξ a) (error 'bind-intermediate "Has key ~a ~a" ξ a))
  #;(hash-set ξ a (match v [(many vs) vs] [_ (set v)]))
  (hash)
  )
;(trace bind-intermediate)

(define (lookup σ #;ξ ρ x r?
                )
  (define a (hash-ref ρ x (λ () (error 'lookup "Address not found ~a" a))))
  (define res
   (if #f ; r?
       (void)#; (hash-ref ξ a (λ () (error 'lookup "Register address not found ~a" a)))
       (vector-ref σ a)))
#;
  (when (set-empty? res)
    (error 'lookup "Empty variable ~a ~a ~a ~a" σ ξ r? a))
  res)
;(trace lookup)

(define (lookup-intermediate σ #;ξ a
                             )
  (define res
   (vector-ref σ a)
#;
   (hash-ref ξ a (λ () (error 'lookup-intermediate "Address not found ~a" a))))
#;
  (when (set-empty? res)
    (error 'lookup-intermediate "Empty intermediate ~a ~a" a ξ))
  res)
;(trace lookup-intermediate)

;; step : State -> ℘(State) U State U Answer
(define/match (step s)
  [((state: (epoint e ρ) σ ξ k))
   (match e
     [(lam ℓ x eb) (add-state! (vpoint (clos x eb ρ)) σ ξ k)]
     [(app ℓ ℓf e0 e1)
      ;; For fixing fake rebinding, pass along address to stackable function variable
      (define fr (match e0
                   [(var ℓ r? f) (and r? (hash-ref ρ f))]
                   [_ #f]))
      (add-state! (epoint e0 ρ) σ ξ (cons (ar ℓ ℓf fr e1 ρ) k))]
     [(var ℓ r? x)
      (define vs (lookup σ #;ξ ρ x r?
                         ))
      (printf "looked up ~a and got ~a~%" x vs)
      (add-state! (vpoint (many vs)) σ ξ k)]
     [(letf ℓ x e0 e1)
      (add-state! (epoint e0 ρ) σ ξ (cons (lt x e1 ρ) k))])]

  [((state: (and vp (vpoint v)) σ ξ k))
   (match k
     [(mt) (add-answer! v σ ξ)]

  #;
     [(rt ξp fr fnv)
      (define ret (hash-ref Ξ ξp))
      (unless (= 1 (set-count ret)) (error 'step "Not 1 ~a" ret))
      ;; Fix fake rebinding when we are returning from a call that had
      ;; a frame-able variable in function position.
      (if #f                            ;fr
          (for ([ξ′×k′ (in-set ret)])
            (match-define k′ #;(cons ξ′ k′) ξ′×k′)
            (add-state! vp σ (hash-set ξ′ fr (set fnv)) k′))
          (for ([ξ′×k′ (in-set ret)])
            (match-define k′ #;(cons ξ′ k′) ξ′×k′)
            (add-state! vp σ ξ′ k′)))]

     [(cons (ar ℓ ℓf fr e ρ) k*)
      (define a (alloc ℓf s))
      (define-σext (σ′ ξ′) (bind-intermediate σ #;ξ a v
                                              ))
      (printf "Binding ~a in ~a (~a) at ~a~%" v a ℓf ℓ)
      (add-state! (epoint e ρ) σ′ ξ′ (cons (fn ℓ fr a) k*))]

     [(cons (fn ℓ fr a) k*)
      (define vs (lookup-intermediate σ #;ξ a
                                      ))
      (for ([fnv (in-set vs)])
        (printf "Calling ~a from ~a~%" fnv ℓ)
        (match fnv
          [(clos x e ρ)
           (define b (alloc x s))
           (define ρ′ (ρextend ρ x b))
           (define-σext (σ′ ξ′) (bind-call σ b v))
           (define p (epoint e ρ′))
           (define ξp p #;(cons ξ′ p)
             )
           #;(note-return-point! ξp k* ξ)
           (add-state! p σ′ ξ′ k* #;(rt ξp fr fnv)
                       )]))]

     ;; Let is special in CFA2: we can extend the frame rather than create a new one.
     [(cons (lt x e ρ) k*)
      (define a (alloc x s))
      (define ρ′ (ρextend ρ x a))
      (define-σext (σ′ ξ′) (bind-let σ #;ξ a v
                                     ))
                                        ;      (printf "Let body ~a~%frame: ~a~%~%" e σ)
      (define p (epoint e ρ′))
      (add-state! p σ′ ξ′ k)])])
;(trace step)

(define (aval e heap-size)
  (set! Ξ (make-hash))
  (set! addr-var (make-hash))
  (set! σ (make-vector heap-size (set)))
  (set! σt 0)
  (set! answers (set))
  (set! todo (set))
  (set! seen (make-hash))
  (add-state! (epoint e (hash)) (hash) (hash) (mt))
  (let fix ()
    (cond
     [(set-empty? todo)
      (for ([r-only? (in-vector r-only)]
            [var-value (in-vector σ)]
            [i (in-naturals)]
            #:unless r-only?
            #:when (and (set-empty? var-value) (hash-ref allocd (hash-ref addr-var i -1) #f)))
        (printf "allocd, empty and not r-only: ~a~%" i))
      (list allocd r-only
            (for/list ([var-value (in-vector σ)]
                       [i (in-naturals)])
              (cons i var-value))
            answers)]
     [else
      (define todo-old todo)
      (set! todo (set))
      (for ([s (in-set todo-old)]) (step s))
      (fix)])))

(define-syntax-rule (inc! box) (begin0 (unbox box) (set-box! box (add1 (unbox box)))))
(define (parse sexp label-count var-count)  
  (define (label!) (inc! label-count))
  (define (var!) (inc! var-count))
  (define owners (make-hasheq))
  (define escape (make-hasheq))
  (define ast
    (let parse* ([sexp sexp] [ρ #hasheq()] [currentλ -2])
      (define-syntax-rule (define-fresh (ρ* n) (owner x))
        (define-values (ρ* n)
          (let* ([x-id (var!)])
            (hash-set! owners x-id owner)
            (values (hash-set ρ x x-id) x-id))))
      (match sexp
        [(? symbol? x)
         (define n (hash-ref ρ x))
         (define r? (= (hash-ref owners n -1) currentλ))
         (unless r? (hash-set! escape n #t))
         (var (label!) r? n)]
        [`(,(or 'lambda 'λ) (,x) ,e)
         (define ℓ (label!))
         (define-fresh (ρ* n) (ℓ x))
         (lam ℓ n (parse* e ρ* ℓ))]
        [`(let ([,x ,e]) ,body)
         (define-fresh (ρ* n) (currentλ x))
         (letf (label!) n (parse* e ρ currentλ) (parse* body ρ* currentλ))]
        [`(,e0 ,e1)
         (app (label!) (label!) (parse* e0 ρ currentλ) (parse* e1 ρ currentλ))]
        [_ (error 'parse "Bad sexp ~a" sexp)])))
  (define v (make-vector (unbox var-count) #t))
  (for ([i (in-range (unbox var-count))]
        #:when (hash-has-key? escape i))
    (vector-set! v i #f))
  (set! r-only v)
  ast)
(trace parse)

(define lcount (box 0))
(define vcount (box 0))
(define church
  (parse
   '(let ([plus
           (lambda (p1)
             (lambda (p2)
               (lambda (pf)
                 (lambda (x) ((p1 pf) ((p2 pf) x))))))])
      (let ([mult
             (lambda (m1)
               (lambda (m2)
                 (lambda (mf) (m2 (m1 mf)))))])
        (let ([pred
               (lambda (n)
                 (lambda (rf)
                   (lambda (rx)
                     (((n (lambda (g) (lambda (h) (h (g rf)))))
                       (lambda (ignored) rx))
                      (lambda (id) id)))))])
          (let ([sub
                 (lambda (s1)
                   (lambda (s2)
                     ((s2 pred) s1)))])
            (let ([church0 (lambda (f0) (lambda (x0) x0))])
              (let ([church1 (lambda (f1) (lambda (x1) (f1 x1)))])
                ;; multiplication distributes over addition
                (let ([church2 (lambda (f2) (lambda (x2) (f2 (f2 x2))))])
                  (let ([church3 (lambda (f3) (lambda (x3) (f3 (f3 (f3 x3)))))])
                    (let ([true (lambda (x) (lambda (y) (x (lambda (dummy) dummy))))])
                      (let ([false (lambda (x) (lambda (y) (y (lambda (dummy) dummy))))])
                        (let ([church0? (lambda (z) ((z (lambda (zx) false)) true))])
                          (let ([Y (lambda (f)
                                     ((lambda (g) (f (lambda (x) ((g g) x))))
                                      (lambda (g) (f (lambda (x) ((g g) x))))))])
                            (let ([church=?
                                   (Y
                                    (lambda (church=?)
                                      (lambda (e1)
                                        (lambda (e2)
                                          (((church0? e1)
                                            (lambda (dummy) (church0? e2)))
                                           (lambda (dummy)
                                             (((church0? e2)
                                               (lambda (dummy) false))
                                              (lambda (dummy)
                                                ((church=? ((sub e1) church1)) ((sub e2) church1))))))))))])
                              ((church=? ((mult church2) ((plus church1) church3)))
                               ((plus ((mult church2) church1)) ((mult church2) church3))))))))))))))))
   lcount
   vcount))
;;(aval church (unbox vcount))

(set-box! lcount 0)
(set-box! vcount 0)
(define fact3
  (parse
   '(let ([Yf (lambda (f)
                ((lambda (g) (f (lambda (x) ((g g) x))))
                 (lambda (g) (f (lambda (x) ((g g) x))))))])
      (let ([pred
             (lambda (n)
               (lambda (rf)
                 (lambda (rx)
                   (((n (lambda (g) (lambda (h) (h (g rf)))))
                     (lambda (ignored) rx))
                    (lambda (id) id)))))])
        (let ([add1
               (lambda (n) (lambda (f) (lambda (x) (f ((n f) x)))))])
          (let ([mult
                 (lambda (m1)
                   (lambda (m2)
                     (lambda (mf) (m2 (m1 mf)))))])
            (let ([church1 (lambda (f1) (lambda (x1) (f1 x1)))])
              (let ([church3 (lambda (f3) (lambda (x3) (f3 (f3 (f3 x3)))))])
                (let ([true (lambda (x) (lambda (y) (x (lambda (dummy) dummy))))])
                  (let ([false (lambda (x) (lambda (y) (y (lambda (dummy) dummy))))])
                    (let ([church0? (lambda (z) ((z (lambda (zx) false)) true))])
                      (let ([fact
                             (Yf
                              (λ (fact)
                                 (λ (m)
                                    (((church0? m) (λ (dummy) church1))
                                     (λ (dummy)
                                        ((mult (fact (pred m))) m))))))])
                        (fact church3)))))))))))
   lcount
   vcount))
;(aval fact3 (unbox vcount))

(set-box! lcount 0)
(set-box! vcount 0)
(define count-down
  (parse
   '(let ([Yf (lambda (f)
                ((lambda (g) (f (lambda (x) ((g g) x))))
                 (lambda (g) (f (lambda (x) ((g g) x))))))])
      (let ([pred
             (lambda (n)
               (lambda (rf)
                 (lambda (rx)
                   (((n (lambda (g) (lambda (h) (h (g rf)))))
                     (lambda (ignored) rx))
                    (lambda (id) id)))))])
        (let ([church3 (lambda (f3) (lambda (x3) (f3 (f3 (f3 x3)))))])
          (let ([true (lambda (x) (lambda (y) (x (lambda (dummy) dummy))))])
            (let ([false (lambda (x) (lambda (y) (y (lambda (dummy) dummy))))])
              (let ([church0? (lambda (z) ((z (lambda (zx) false)) true))])
                (let ([count-down
                       (Yf
                        (λ (count-down)
                           (λ (m)
                              (((church0? m) (λ (dummy) true))
                               (λ (dummy)
                                  (count-down (pred m)))))))])
                  (count-down church3))))))))
   lcount vcount))
(pretty-print (aval count-down (unbox vcount)))

;; Count-down with all functions named.
#;(let ([Yf (lambda (f)
            (define apper (lambda (g) (define double (lambda (x) ((g g) x))) (f double)))
            (apper apper))])
  (let ([pred
         (lambda (n)
           (define rf
             (lambda (rf)
               (define rx 
                 (lambda (rx)
                   (define gh (lambda (g) (define hf (lambda (h) (h (g rf)))) hf))
                   (define igrx (lambda (ignored) rx))
                   (define id (lambda (id) id))
                   (((n gh) igrx) id)))
               rx))
           rf)])
    (let ([church3 (lambda (f3) (printf "~a~%" f3) (define x3 (lambda (x3) (f3 (f3 (f3 x3))))) x3)])
      (let ([dummy (lambda (dummy) dummy)])
        (let ([true (lambda (x) (define yxdummy (lambda (y) (x dummy))) yxdummy)])
          (let ([yydummy (lambda (y) (y dummy))])
           (let ([false (lambda (x) yydummy)])
             (let ([dtrue (λ (dummy) true)])
               (let ([dfalse (lambda (zx) false)])
                 (let ([church0? (lambda (z) ((z dfalse) true))])
                       (let ([count-down
                              (Yf
                               (λ (count-down)
                                  (λ (m)
                                     (((church0? m) dtrue)
                                      (λ (dummy)
                                         (count-down (pred m)))))))])
                         (count-down church3))))))))))))