#lang racket

;; Expressions
(struct exp (ℓ) #:transparent)
(struct lam exp (x body) #:transparent)
(struct app exp (e0 e1) #:transparent)
(struct var exp (x) #:transparent)

;; Values
(struct clos (x e ρ) #:transparent)

;; Frames
(struct ar (e ρ) #:transparent)
(struct fn (v) #:transparent)
;; Continuation tails
(struct mt () #:transparent)
(struct rt (owner) #:transparent)
;; A Kont is either
;; - (cons Frame Kont)
;; - Continuation tail

;; Points
(struct epoint (e ρ) #:transparent)
(struct vpoint (v) #:transparent)

(struct state (p #;σ k) #:transparent)
(struct answer (v #;σ) #:transparent)

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
(define-match-expander state: (λ (stx) (syntax-case stx () [(_ p σ k) #'(state p k)])))
(define-match-expander answer: (λ (stx) (syntax-case stx () [(_ v σ) #'(answer v)])))
(define-syntax-rule (add-state! p σ k) (add-todo! (state p k)))
(define-syntax-rule (add-answer! v σ) (set! answers (set-add answers v)))

(define (note-return-point! p k)
  (hash-set! Ξ p (set-add (hash-ref Ξ p (set)) k)))

(define (alloc x s) x #;(cons x/ℓ (gensym)))
(define ρextend hash-set)
(define (σextend σ a v)
  ;;(hash-set σ a (set-add (hash-ref σ a (set)) v))
s  (define old (vector-ref σ a))
  (define new (set-add old v))
  (unless (= (set-count old) (set-count new))
    (vector-set! σ a new)
    (set! σt (add1 σt))))
(define (lookup σ ρ x) (vector-ref σ (hash-ref ρ x)))

;; step : State -> ℘(State) U State U (Pairof Point State) ∪ ℘((Pairof Point State)) U Answer
(define/match (step s)
  [((state: (epoint e ρ) σ k))
   (match e
     [(lam ℓ x eb) (add-state! (vpoint (clos x eb ρ)) σ k)]
     [(app ℓ e0 e1) (add-state! (epoint e0 ρ) σ (cons (ar e1 ρ) k))]
     [(var ℓ x) (for ([v (in-set (lookup σ ρ x))])
                  (add-state! (vpoint v) σ k))])]

  [((state: (and vp (vpoint v)) σ k))
   (match k
     [(mt) (add-answer! v σ)]
     [(rt ret-owner)
      (for ([k′ (in-set (hash-ref Ξ ret-owner))])
        (add-state! vp σ k′))]
     [(cons (ar e ρ) k*) (add-state! (epoint e ρ) σ (cons (fn v) k*))]
     [(cons (fn (clos x e ρ)) k*)
      (define a (alloc x s))
      (define ρ′ (ρextend ρ x a))
      (define σ′ (σextend σ a v))
      (define p (epoint e ρ′))
      (note-return-point! p k*)
      (add-state! p σ′ (rt p))])])

(define (aval e heap-size)
  (set! Ξ (make-hash))
  (set! σ (make-vector heap-size (set)))
  (set! σt 0)
  (set! answers (set))
  (set! todo (set))
  (set! seen (make-hash))
  (add-state! (epoint e (hash)) (hash) (mt))
  (let fix ()
    (cond
     [(set-empty? todo) answers]
     [else
      (define todo-old todo)
      (set! todo (set))
      (for ([s (in-set todo-old)]) (step s))
      (fix)])))

(define-syntax-rule (inc! box) (begin0 (unbox box) (set-box! box (add1 (unbox box)))))
(define (parse sexp label-count var-count)  
  (define (label!) (inc! label-count))
  (define (var!) (inc! var-count))
  (let parse* ([sexp sexp] [ρ #hasheq()])
    (define-syntax-rule (define-fresh (ρ* n) x)
      (define-values (ρ* n)
        (let* ([x-id (var!)])
          (values (hash-set ρ x x-id) x-id))))
    (match sexp
      [(? symbol? x) (var (label!) (hash-ref ρ x))]
      [`(,(or 'lambda 'λ) (,x) ,e)
       (define-fresh (ρ* n) x)
       (lam (label!) n (parse* e ρ*))]
      [`(let ([,x ,e]) ,body) (parse* `((lambda (,x) ,body) ,e) ρ)]
      [`(,e0 ,e1)
       (app (label!) (parse* e0 ρ) (parse* e1 ρ))]
      [_ (error 'parse "Bad sexp ~a" sexp)])))
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

(aval church (unbox vcount))