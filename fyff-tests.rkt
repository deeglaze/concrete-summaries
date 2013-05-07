#lang racket
(require redex "fyff.rkt" "fyff-grammar.rkt" "fyff-meta.rkt")

(define (sound? e expected [fail (λ (r) #f)])
  (define (valuefy e)
    (match e
      [`(,(or 'λ 'lambda) (,x ...) ,e)
       `((λ ,x ,e) #hash())]
      [_ e]))

  (define (consify lst σ final-addr)
    (let loop ([lst lst] [σ σ] [last-addr final-addr])
      (match lst
        ['() (hash-set σ last-addr (set '()))]
        [(cons v vrest)
         (define-values (a d) (values (gensym) (gensym)))
         (loop vrest 
               (hash-set* σ (list a last-addr) (list (set v) (set `(pair ,a ,d))))
               d)])))

  ;; might not terminate!
  (define (unconsify v σ)
    (match v
      [`(pair ,a ,d)
       (for*/set ([v₀ (in-set (hash-ref σ a (lookup-err 'unconsify-a a)))]
                  [p (in-set (hash-ref σ d (lookup-err 'unconsify-d d)))]
                  [v₁ (in-set (unconsify p σ))])
         (cons v₀ v₁))]
      [_ (set v)]))

  (define (⊑? v v* σ σ*)
    (let ⊑? ([v v] [v* v*])
      (match* (v v*)
        [(v v) #t]
        [(`(pair ,a0 ,d0) `(pair ,a1 ,d1))
         (and (⊑? (hash-ref σ a0 (lookup-err '⊑?-a0 a0))
                  (hash-ref σ* a1 (lookup-err '⊑?-a1 a1)))
              (⊑? (hash-ref σ d0 (lookup-err '⊑?-d0 d0))
                  (hash-ref σ* d1 (lookup-err '⊑?-d1 d1))))]
        [(`(prompt-tag (,ℓ ,more0)) `(prompt-tag (,ℓ ,more1))) #t]
        [(`(cont ,tag0 ,k0) `(cont ,tag1 ,k1)) (error '⊑? "Unsupported: cont")]
        [(`(comp ,k0) `(comp ,k1)) (error '⊑? "Unsupported: comp")]
        [(`(,(or 'lambda 'λ) (,xs0 ...) ,e0)
          `((,(or 'lambda 'λ) (,xs1 ...) ,e1) ,ρ))
         (⊑-term? v v* σ*)]
        [((? set?) _) (for/and ([vi (in-set v)]) (⊑? vi v*))]
        [(_ (? set?)) (for/or ([vi (in-set v*)]) (⊑? v vi))]
        [(_ _) #f])))

  (define (⊑-term? e e* σ*)
    (match* (e e*)
     [(v v) #t]
     [(`(if ,g0 ,t0 ,e0) `(if ,g1 ,t1 ,e1))
      (and (⊑-term? g0 g1 σ*)
           (⊑-term? t0 t1 σ*)
           (⊑-term? e0 e1 σ*))]
     [(`(set! ,x ,e) `(set! ,x ,e*)) (⊑-term? e e* σ*)]
     [(`(begin ,e0 ,e1) `(begin ,e0* ,e1*))
      (and (⊑-term? e0 e0* σ*)
           (⊑-term? e1 e1* σ*))]
     [(`(,(or 'lambda 'λ) (,xs ...) ,e0)
       `((,(or 'lambda 'λ) (,xs ...) ,e1) ,ρ))
      (for/or ([e* (in-list (substs e1 ρ σ*))])
        (⊑-term? e0 e* σ*))]
     [(`(,e00 ,es0 ...)
       `(,(? number? label) ,e01 ,es1 ...))
      (and (⊑-term? e00 e01 σ*)
           (= (length es0) (length es1))
           (for/and ([ei (in-list es0)]
                     [ei* (in-list es1)])
             (⊑-term? ei ei* σ*)))]
     [(_ _) #f]))

  (define (subst e ρ)
    (let subst ([e e] [ρ ρ])
      (match e
       [(? symbol? x) (hash-ref ρ x x)]
       [`(,(? number? label) ,e0 ,es ...)
        `(,label ,(subst e0 ρ) ,@(for/list ([ei (in-list es)]) (subst ei ρ)))]
       [`(if ,g ,t ,e)
        `(if ,(subst g ρ)
             ,(subst t ρ)
             ,(subst e ρ))]
       [`(set! ,x ,e) `(set! ,x ,(subst e ρ))]
       [`(begin ,e0 ,e1) `(begin ,(subst e0 ρ) ,(subst e1 ρ))]
       [`(,(or 'lambda 'λ) (,xs ...) ,e)
        (subst e (for/fold ([ρ ρ]) ([x (in-list xs)]
                                    #:when (hash-has-key? ρ x))
                   (hash-remove ρ x)))]
       [v v])))

  (define (substs e ρ σ*)
    ;; We need to collapse the cross product of all superpositions here.
    (define bigρ
      (for/hash ([(x a) (in-hash ρ)])
        (values x (hash-ref σ* a (lookup-err 'substs a)))))
    (let loop ([curρ* #hash()] [itr (hash-iterate-first bigρ)])
      (cond
       [itr (for/fold ([lst '()]) ([v (in-set (hash-iterate-value bigρ itr))])
              (append (loop (hash-set curρ* (hash-iterate-key bigρ itr) v)
                            (hash-iterate-next bigρ itr))
                      lst))]
       [else (list (subst e curρ*))])))

  (define (transform e)
    (define counter 0)
    (define (label!) (begin0 counter (set! counter (add1 counter))))
    (let add ([e e])
      (match e
       [`(if ,g ,t ,e)
        `(if ,(add g) ,(add t) ,(add e))]
       [`(set! ,x ,e) `(set! ,x ,(add e))]
       [`(begin ,e0 ,e1) `(begin ,(add e0) ,(add e1))]
       [`(,(or 'lambda 'λ) (,xs ...) ,e) `(λ ,xs ,(add e))]
       [`(% ,tag ,body ,handler)
        `(,(label!) call-with-continuation-prompt
          (λ () ,(add body))
          ,(add tag)
          ,(add handler))]
       [`(list) ''()]
       [`(list ,e0 ,es ...)
        `(,(label!) cons ,(add e0) ,(add `(list ,@es)))]
       [`(,e0 ,es ...)
        `(,(label!) ,(add e0) ,@(map add es))]
       [v v])))

  (define injected
    (match e
      [`(<> ([,a ,v] ...) () ,expr)
       (define ρ (hash-set* #hash() a a))
       (define σ (hash-set* (hash output (set '())) a (map (compose set valuefy) v)))
       (define e* (transform expr))
       (unless (redex-match? L e e*)
         (error 'sound? "Bad expr ~a" e*))
       (printf "Starting store (env ~a) (addrs ~a) ~a~%program: ~a~%" ρ a σ e*)
       (list (list e* ρ) σ 'mt)]))

;  (traces R injected #:edge-labels? #t)
  (define results (apply-reduction-relation* R injected))
  (match expected
     [`(<> ([,a ,v] ...) (,out ...) ,expr)
      (define σ (hash-set* #hash() a (map set v)))
      (define σ* (consify (reverse out) σ output))
      (printf "Expected store ~a~%" σ*)
      (or
       (for/or ([result (in-list results)])
         ((term-match/single L
            [(v σ mt)
             (if (⊑? expr (term v) σ* (term σ))
                 (or (for/and ([addr (in-list (cons output a))])
                       (⊑? (hash-ref σ* addr (lookup-err 'sound?σ* addr))
                           (hash-ref (term σ) addr (lookup-err 'sound?σ addr))
                           σ* (term σ)))
                     (not (printf "Output mismatch ~a~%" (unconsify (for/first ([v (in-set (hash-ref (term σ) output))]) v) (term σ)))))
                 (not (printf "Result mismatch~%")))
             ]
            [any #f])
          result))
       (fail results))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abbreviations:

;; The classic (let ([v (call/cc call/cc)]) 
;;              ((call/cc call/cc) v))
(define call/cc-loop
  `(<>
    () []
    (% 0
       ((λ (v) ((call/cc (λ (x) (call/cc x 0)) 0) v))
        (call/cc (λ (x) (call/cc x 0)) 0))
       (λ (x) x))))

(define (show prog)
  (stepper R prog))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests
(define (test desc expr result)
  (sound? expr result (λ (actuals)
                         (printf "~s:\n~s\n" desc expr)
                         (printf "=> ~s\n\n" actuals)
                         (error 'test "expected ~s" result)))
  (printf "Pass!~%")
  (set! tests-passed (add1 tests-passed)))
(define tests-passed 0)

;; Basic ----------------------------------------

(define (basic-tests)
  (test "(λx.e)[y←v] ≠ λy.(e[x←y][y←v])"
        '(<>
          ([k 4]) []
          (((λ (k1) (λ (k) k))
            (λ () k))
           0))
        '(<> ([k 4]) [] 0))
  (test "(λx.e)[y←v] ≠ λz.(e[x←z][y←v]) if z ∈ FV(e)"
        '(<>
          ([k2 5])
          ()
          (((λ (k1) (λ (k) k2))
            (λ () k))
           0))
        '(<> ([k2 5]) [] 5))
  (test "basic dw"
        '(<>
          () []
          (dynamic-wind (λ () (print 1))
                        (λ () (print 2))
                        (λ () (print 3))))
        '(<> () (1 2 3) #f))
  (test "call/cc dw"
        '(<>
          () []
          (%
           0
           (call/cc
            (λ (k)
              (dynamic-wind (λ () (print 1))
                            (λ () (k 0))
                            (λ () (print 3))))
            0)
           (λ (x) x)))
        '(<> () (1 3) 0))
  (test "abort"
        '(<>
          () []
          (%
           0             
           (+ 10 (abort 0 7))
           (λ (x) (+ x 1))))
        '(<>
          () []
          8))
  (test "abort inner"
        '(<>
          () []
          (%
           0             
           (+ 10 
              (%
               1         
               (abort 1 7)
               (λ (x) (+ x 1))))
           (λ (x) (+ x 2))))
        '(<>
          () []
          18))
  (test "abort outer"
        '(<>
          () []
          (%
           0             
           (+ 10 
              (%
               1
               (abort 0 7)
               (λ (x) (+ x 1))))
           (λ (x) (+ x 2))))
        '(<>
          () []
          9))
  (test "abort inner with same tag"
        '(<>
          () []
          (%
           0             
           (+ 10 
              (%
               0
               (abort 0 7)
               (λ (x) (+ x 1))))
           (λ (x) (+ x 2))))
        '(<>
          () []
          18))
  #;
  (test "abort handler in tail position"
        '(<>
          () []
          (%
           0
           (call/cm
            100 1
            (λ ()
               (%
                1
                (abort 1 (λ ()
                            (call/cm
                             100 2
                             (λ ()
                                (current-marks 100 0)))))
                (λ (f)
                   (f)))))
           (λ (x) x)))
        '(<>
          () []
          (list 2)))
  (test "abort dw"
        '(<>
          () []
          (%
           0
           (call/cc
            (λ (k)
               (dynamic-wind (λ () (print 1))
                   (λ () (abort 0 7))
                   (λ () (print 3))))
            0)
           (λ (x) (+ x 1))))
        '(<> () (1 3) 8))
  (test "abort tag eval"
        '(<>
          () []
          (% (print 1) 2 3))
        '(<> () [1] 2))
  (test "abort handler eval"
        '(<>
          () []
          (% 1 2 (print 3)))
        '(<> () [3] 2))
  (test "call/cc 2 levels dw"
        '(<>
          ()
          []
          (%
           0
           (call/cc
            (λ (k)
               (dynamic-wind
                   (λ () (print 1))
                   (λ ()
                      (dynamic-wind
                          (λ () (print 2))
                          (λ ()
                             (k 10))
                          (λ () (print 3))))
                   (λ () (print 4))))
            0)
           (λ (x) x)))
        '(<> () [1 2 3 4] 10))
  (test "abort 2 levels dw"
        '(<>
          ()
          []
          (%
           0
           (dynamic-wind
               (λ () (print 1))
               (λ ()
                  (dynamic-wind
                      (λ () (print 2))
                      (λ ()
                         (abort 0 10))
                      (λ () (print 3))))
               (λ () (print 4)))
           (λ (x) (+ x 1))))
        '(<> () [1 2 3 4] 11))
  (test "in thunk isn't really in"
        '(<>
          () []
          (%
           0
           (call/cc
            (λ (k)
               (dynamic-wind
                   (λ () (begin
                           (print 1)
                           (k 11)))
                   (λ () (print 2))
                   (λ () (print 3))))
            0)
           (λ (x) x)))
        '(<> () [1] 11))
  (test "in thunk isn't really in, but it's in surrounding"
        '(<>
          () []
          (%
           0
           (call/cc
            (λ (k)
               (dynamic-wind
                   (λ () (print -1))
                   (λ ()
                      (dynamic-wind
                          (λ () (begin
                                  (print 1)
                                  (k 11)))
                          (λ () (print 2))
                          (λ () (print 3))))
                   (λ () (print -2))))
            0)
           (λ (x) x)))
        '(<> () [-1 1 -2] 11))
  (test "dw shared during jump"
        '(<>
          () []
          (% 0 
             (dynamic-wind 
                 (λ () (print 0))
                 (λ () ((call/cc (λ (f) f) 0) (λ (x) 10)))
                 (λ () (print 1)))
             (λ (x) x)))
        '(<> () [0 1] 10))
  (test "dw not shared during jump"
        '(<>
          () []
          (% 0 
             ((dynamic-wind 
                  (λ () (print 0))
                  (λ () (call/cc (λ (f) f) 0))
                  (λ () (print 1)))
              (λ (x) 10))
             (λ (x) x)))
        '(<> () [0 1 0 1] 10))
  #;
  (test "composable captures continuation marks"
        '(<>
          () []
          (%
           100
           ((λ (k) (k (λ (v) (current-marks 0 100)))) 
            (% 0 
               (call/cm 0 100 
                        (λ ()
                           ((call/comp (λ (k) (λ (v) k)) 0)
                            99)) )
               (λ (x) x)))
           (λ (x) x)))
        '(<> () [] (list 100)))
  #;
  (test "continuation marks wrapping % not captured"
        '(<>
          () []
          (%
           101
           ((λ (k) (k (λ (v) (current-marks 0 101)))) 
            (call/cm 0 100 
                     (λ ()
                        (% 0 
                           ((call/comp (λ (k) (λ (v) k)) 0)
                            99)
                           (λ (x) x)))))
           (λ (x) x)))
        '(<> () [] (list)))
  #;
  (test "visible marks restricted by prompt tag"
        '(<>
          () []
          (% 101
             (call/cm 0 100
                      (λ ()
                         (% 102
                            (call/cm 0 99
                                     (λ () 
                                        (current-marks 0 102)))
                            (λ (x) x))))
             (λ (x) x)))
        '(<> () [] (list 99)))
  #;
  (test "visible marks not restricted by other prompt tags"
        '(<>
          () []
          (% 101
             (call/cm 0 100
                      (λ ()
                         (% 102
                            (call/cm 0 99
                                     (λ () 
                                        (current-marks 0 101)))
                            (λ (x) x))))
             (λ (x) x)))
        '(<> () [] (list 99 100)))
  #;
  (test "getting marks fails if there's no prompt with the given tag"
  '(<>
  () []
  (% 101
  (call/cm 0 100
  (λ ()
  (current-marks 0 102)))
  (λ (x) x)))
  '(<> () [] (% 101 (wcm ((0 100)) (current-marks 0 102)) (λ (x) x))))
  (test "pre and post thunks in a composable continuation"
        '(<> 
          () []
          ((λ (f)
              (f (λ (v) 10)))
           (%
            0
            (dynamic-wind
                (λ () (print 1))
                (λ ()
                   (call/comp (λ (k) k) 0))
                (λ () (print 2)))
            (λ (x) x))))
        '(<>
          ()
          [1 2 1 2]
          (λ (v) 10)))
  (test "prompt enclosing prompt-tag expression"
        '(<> () [] 
             (% 0
                (% (abort 0 1) 2 3)
                (λ (x) x)))
        '(<> () [] 1))
  (test "prompt enclosing prompt-handler expression"
        '(<> () []
             (% 0 
                (begin 
                  (% 0 1 (abort 0 2))
                  (print 3))
                (λ (x) x)))
        '(<> () [] 2))
  #;
  (test "prompt-tag position in continuation-marks context"
  '(<> () []
  (% 0 
  (call/cm 
  1 2
  (λ ()
  (% (abort 0 (current-marks 1 0))
  3
  4)))
  (λ (x) x)))
  '(<> () [] (list 2)))
  #;
  (test "prompt-handler position in continuation-marks context"
  '(<> () []
  (% 0 
  (call/cm 
  1 2
  (λ ()
  (call/cm
  1 3
  (% 0
  4
  (abort 0 (current-marks 1 0))))))
  (λ (x) x)))
  '(<> () [] (list 2)))
  #;
  (test "if-test position in continuation-marks context"
  '(<> ()
  []
  (% 0
  (call/cm 
  1 2 
  (λ () (if (abort 0 (current-marks 1 0)) 3 4)))
  (λ (x) x)))
  '(<> () [] (list 2)))
  #;
  (test "dw in continuation-marks context"
  '(<> ()
  []
  (% 0
  (call/cm 1 2 
  (λ () 
  (dynamic-wind
  (λ () #f)
  (λ () (current-marks 1 0))
  (λ () #t))))
  (λ (x) x)))
  '(<> () [] (list 2)))
  #;
  (test "wcm without key in continuation-marks context"
  '(<> ()
  []
  (% 0
  (wcm ([1 2])
  ((λ (x) x)
  (wcm ([3 4])
  (current-marks 3 0))))
  (λ (x) x)))
  '(<> () [] (list 4))))

;; R6RS dynamic-wind ----------------------------------------

(define (r6rs-dw-tests)
  (test "out thunk is really out"
        '(<>
          ([n 0]
           [do-jump? #t]
           [k-out #f])
          []
          (%
           0
           (begin
             (begin
               (call/cc
                (λ (k)
                  (dynamic-wind
                   (λ () (set! n (+ n 1)))
                   (λ () (k 99))
                   (λ ()
                     (begin
                       (set! n (+ n 1))
                       (call/cc (λ (k) (set! k-out k)) 0)))))
                0)
               (if do-jump?
                   (begin
                     (set! do-jump? #f)
                     (k-out 0))
                   11))
             (begin
               (set! k-out #f)
               n))
           (λ (x) x)))
        '(<> ([n 2] [do-jump? #f] [k-out #f]) [] 2))
  (test "out thunk is really out during trimming"
        '(<>
          ([n 0]
           [do-jump? #t]
           [k-out #f])
          []
          (%
           0
           (begin
             (call/cc
              (λ (k)
                (dynamic-wind
                 (λ () (set! n (+ n 1)))
                 (λ () (k 100))
                 (λ ()
                   (begin
                     (set! n (+ n 1))
                     (call/cc (λ (k) (set! k-out k)) 0)))))
              0)
             (begin
               (if do-jump?
                   (begin
                     (set! do-jump? #f)
                     (k-out 0))
                   11)
               (begin
                 (set! k-out #f)
                 n)))
           (λ (x) x)))
        '(<> ([n 2] [do-jump? #f] [k-out #f]) () 2))
  (test "jumping during the results of trimming, pre-thunk"
        '(<> 
          ([pre-count 0]
           [pre-jump? #f]
           [after-jump? #t]
           [grab? #t]
           [the-k #f])
          []
          (%
           0
           (begin
             (dynamic-wind
              (λ ()
                (begin
                  (set! pre-count (+ pre-count 1))
                  (if pre-jump?
                      (begin
                        (set! pre-jump? #f)
                        (begin
                          (set! after-jump? #f)
                          (the-k 999)))
                      999)))
              (λ () 
                (if grab?
                    (call/cc
                     (λ (k)
                       (begin
                         (set! grab? #f)
                         (set! the-k k)))
                     0)
                    999))
              (λ () (+ 0 10)))
             (begin
               (if after-jump?
                   (begin
                     (set! pre-jump? #t)
                     (the-k 999))
                   999)
               (begin
                 (set! the-k #f) ;; just to make testing simpler
                 pre-count)))
           (λ (x) x)))
        '(<>
          ([pre-count 3]
           [pre-jump? #f]
           [after-jump? #f]
           [grab? #f]
           [the-k #f])
          ()
          3))
  (test "jumping during the results of trimming, post-thunk"
        '(<>
          ([post-count 0] 
           [post-jump? #t]
           [jump-main? #t]
           [grab? #t]
           [the-k #f])
          []
          (%
           0
           (begin
             (begin
               (if grab?
                   (call/cc
                    (λ (k)
                      (begin
                        (set! grab? #f)
                        (set! the-k k)))
                    0)
                   999)
               (dynamic-wind
                (λ () (+ 0 1))
                (λ () 
                  (if jump-main?
                      (begin
                        (set! jump-main? #f)
                        (the-k 999))
                      999))
                (λ () 
                  (begin
                    (set! post-count (+ post-count 1))
                    (if post-jump?
                        (begin
                          (set! post-jump? #f)
                          (the-k 999))
                        999)))))
             (begin
               (set! the-k #f) ;; just to make testing simpler
               post-count))
           (λ (x) x)))
        '(<>
          ([post-count 2]
           [post-jump? #f]
           [jump-main? #f]
           [grab? #f]
           [the-k #f]) 
          []
          2))
  (test "hop out one level"
        '(<>
          ()
          []
          
          (%
           0
           ((dynamic-wind (λ () (print 0))
                          (λ () (call/cc (λ (k) k) 0))
                          (λ () (print 1)))
            (λ (y) (print 7)))
           (λ (x) x)))
        '(<>
          ()
          [0 1 0 1 7]
          #f))
  (test "hop out two levels"
        '(<> ()
             []
             (%
              0
              ((dynamic-wind 
                (λ () (print 1))
                (λ () 
                  (dynamic-wind
                   (λ () (print 2))
                   (λ () (call/cc (λ (k) k) 0))
                   (λ () (print 3))))
                (λ () (print 4)))
               (λ (y) (print 8)))
              (λ (x) x)))
        '(<>
          ()
          [1 2 3 4 1 2 3 4 8]
          #f))
  (test "don't duplicate tail"
        '(<>
          ()
          []
          (%
           0
           (dynamic-wind 
            (λ () (print 1))
            (λ () 
              ((dynamic-wind (λ () (print 2))
                             (λ () (call/cc (λ (k) k) 0))
                             (λ () (print 3)))
               (λ (y) (print 9))))
            (λ () (print 4)))
           (λ (x) x)))
        '(<>
          ()
          [1 2 3 2 3 9 4]
          #f))
  (test "don't duplicate tail, 2 deep"
        '(<>
          ()
          []
          
          (%
           0
           (dynamic-wind 
            (λ () (print 1))
            (λ () 
              (dynamic-wind 
               (λ () (print 2))
               (λ () 
                 ((dynamic-wind (λ () (print 3))
                                (λ () (call/cc (λ (k) k) 0))
                                (λ () (print 4)))
                  (λ (y) (print 9))))
               (λ () (print 5))))
            (λ () (print 6)))
           (λ (x) x)))
        '(<>
          ()
          [1 2 3 4 3 4 9 5 6]
          #f))
  (test "hop out and back into another one"
        '(<>
          ()
          []
          (%
           0
           ((λ (ok)
              (dynamic-wind (λ () (print 1))
                            (λ () (ok (λ (y) (print 9))))
                            (λ () (print 2))))
            (dynamic-wind (λ () (print 3))
                          (λ () (call/cc (λ (k) k) 0))
                          (λ () (print 4))))
           (λ (x) x)))
        '(<>
          ()
          [3 4 1 2 3 4 1 9 2]
          #f))
  (test "hop out one level and back in two levels"
        '(<>
          ()
          []
          (%
           0
           ((λ (ok)
              (dynamic-wind
               (λ () (print 1))
               (λ ()
                 (dynamic-wind
                  (λ () (print 2))
                  (λ () (ok (λ (y) (print 9))))
                  (λ () (print 3))))
               (λ () (print 4))))
            (call/cc (λ (k) k) 0))
           (λ (x) x)))
        '(<>
          ()
          [1 2 3 4 1 2 9 3 4]
          #f))
  (test "hop out two levels and back in two levels"
        '(<>
          ()
          []
          (%
           0
           ((λ (ok)
              (dynamic-wind
               (λ () (print 1))
               (λ () 
                 (dynamic-wind
                  (λ () (print 2))
                  (λ () (ok (λ (y) (print 9))))
                  (λ () (print 3))))
               (λ () (print 4))))
            (dynamic-wind
             (λ () (print 5))
             (λ () 
               (dynamic-wind
                (λ () (print 6))
                (λ () (call/cc (λ (k) k) 0))
                (λ () (print 7))))
             (λ () (print 8))))
           (λ (x) x)))
        '(<>
          ()
          [5 6 7 8 1 2 3 4 5 6 7 8 1 2 9 3 4]
          #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; composability

(define (cont-tests)
  (test "captured under new %"
        '(<>
          ([retry #f])
          []
          (begin
            (%
             0
             (+ 18
                (call/cc
                 (λ (k)
                   (begin
                     (set! retry k)
                     17))
                 0))
             (λ (x) x))
            ((λ (y)
               (begin
                 (set! retry #f)
                 y))
             (+ 1 (%
                   0
                   (retry 10)
                   (λ (x) x))))))
        '(<>
          ([retry #f])
          []
          29))               
  (test "catch in composed"
        '(<>
          () []
          (%
           0
           ((λ (k)
              ((λ (k2)
                 (%
                  0
                  (k2 (list 89))
                  (λ (x) x)))
               (%
                0
                (k (λ ()
                     (first (call/cc (λ (k2)
                                       (cons k2 (list)))
                                     0))))
                (λ (x) x))))
            (%
             0
             ((call/cc (λ (k) (λ () k))
                       0))
             (λ (x) x)))
           (λ (x) x)))
        '(<>
          () []
          89))
  (test "simple composable"
        '(<>
          [] ()
          ((λ (k)
             (k (λ () 8)))
           (%
            0
            ((call/comp
              (λ (k) (λ () k))
              0))
            (λ (x) x))))
        '(<> [] () 8))
  (test "composable doesn't introduce %"
        '(<>
          [] ()
          (%
           0
           ((λ (k)
              ((λ (k2)
                 (if (first (rest k2))
                     ((first k2) (list 10 #f))
                     (first k2)))
               (k (λ ()
                    (call/cc (λ (k2) 
                               (cons k2 (list #t)))
                             0)))))
            (%
             0
             ((call/comp
               (λ (k) (λ () k))
               0))
             (λ (x) x)))
           (λ (x) x)))
        '(<>
          [] ()
          10))
  (test "post thunk runs current continuation as composable"
        '(<>
          ([a #f]
           [do-a? #t])
          []
          (%
           0
           (dynamic-wind
            (λ () (print 1))
            (λ ()
              (begin
                (dynamic-wind
                 (λ () (print 2))
                 (λ () 
                   ((call/cc (λ (k)
                               (begin
                                 (set! a k)
                                 (λ () 12)))
                             0)))
                 (λ () (print 3)))
                (dynamic-wind
                 (λ () (print 4))
                 (λ ()
                   (if do-a?
                       (begin
                         (set! do-a? #f)
                         (a (λ () 11)))
                       (begin
                         (set! a #f)
                         12)))
                 (λ ()
                   (begin
                     (print 5)
                     (call/comp
                      (λ (k)
                        (k 10))
                      0))))))
            (λ () (print 6)))
           (λ (x) x)))
        '(<>
          ([a #f][do-a? #f])
          [1 2 3 4 5 1 6 2 3 4 5 1 6 6]
          12))
  (test "post thunk runs current continuation as composable under %"
        '(<>
          ([a #f]
           [do-a? #t])
          []
          (%
           0
           (dynamic-wind
            (λ () (print 1))
            (λ ()
              (begin
                (dynamic-wind
                 (λ () (print 2))
                 (λ () 
                   ((call/cc (λ (k)
                               (begin
                                 (set! a k)
                                 (λ () 12)))
                             0)))
                 (λ () (print 3)))
                (dynamic-wind
                 (λ () (print 4))
                 (λ ()
                   (if do-a?
                       (begin
                         (set! do-a? #f)
                         (a (λ () 11)))
                       (begin
                         (set! a #f)
                         12)))
                 (λ ()
                   (begin
                     (print 5)
                     (call/comp
                      (λ (k)
                        (%
                         0
                         (k 10)
                         (λ (x) x)))
                      0))))))
            (λ () (print 6)))
           (λ (x) x)))
        '(<>
          ([a #f] [do-a? #f])
          [1 2 3 4 5 1 2 3 4 5 1 6 6 2 3 4 5 1 6 6]
          12))
  (test "post think trims dws to run on exit"
        '(<>
          ([output (list)]
           [exit-k #f]
           [done? #f])
          []
          (%
           0
           (begin
             ;; Capture a continuation w.r.t. the default prompt tag:
             (call/cc
              (λ (esc)
                (dynamic-wind
                 (λ () 0)
                 (λ () 
                   ;; Set a prompt for tag p1:
                   (%
                    1
                    
                    (dynamic-wind
                     (λ () 0)
                     ;; inside d-w, jump out:
                     (λ () (esc 100))
                     (λ ()
                       (begin
                         ;; As we jump out, capture a continuation 
                         ;; w.r.t. p1:
                         ((call/cc
                           (λ (k) 
                             (begin
                               (set! exit-k k)
                               (λ () 10)))
                           1))
                         (set! output (cons 99 output)))))
                    (λ (x) x)))
                 (λ ()
                   ;; This post thunk is not in the
                   ;;  delimited continuation captured
                   ;; via tag p1:
                   (set! output (cons 101 output)))))
              0)
             (if done?
                 (begin
                   (set! exit-k #f)
                   output)
                 (begin
                   (set! done? #t)
                   ;; Now invoke the delimited continuation, which must
                   ;; somehow continue the jump to `esc':
                   (%
                    1
                    (exit-k (λ () 10))
                    (λ (x) x)))))
           (λ (x) (x))))
        '(<> 
          ([output (list 99 101 99)]
           [exit-k #f]
           [done? #t])
          ()
          (list 99 101 99)))
  (test "post thunk captures continuation that is invoked without target % (gets stuck)"
        '(<>
          ([output (list)]
           [exit-k #f])
          ()
          (%
           0
           ((λ (k)
              (abort 0
                     (λ ()
                       (%
                        1
                        (exit-k (λ () (set! exit-k #f)))
                        (λ (x) x)))))
            (call/cc 
             (λ (esc)
               (%
                1
                (dynamic-wind
                 (λ () 0)
                 (λ () (esc 100))
                 (λ ()
                   (begin
                     ((call/cc
                       (λ (k) 
                         (begin
                           (set! exit-k k)
                           (λ () 10)))
                       1))
                     (set! output (cons 101 output)))))
                (λ (x) x)))
             0))
           (λ (f) (f))))
        (term (<>
               ((output (list 101 101))
                (exit-k #f))
               ()
               (%
                1
                ((cont 0
                       ((λ (k)
                          (abort
                           0
                           (λ ()
                             (%
                              1
                              (exit-k (λ () (set! exit-k #f)))
                              (λ (x) x)))))
                        hole))
                 100)
                (λ (x1) x1)))))
  (test "similar way to get stuck, but using the pre thunk"
        '(<>
          ([output (list)]
           [exit-k #f])
          ()
          (%
           0
           ((λ (k)
              (abort 0
                     (λ ()
                       (%
                        1
                        (exit-k (λ () (set! exit-k #f)))
                        (λ (x) x)))))
            (call/cc 
             (λ (esc)
               (%
                1
                (dynamic-wind
                 (λ ()
                   (begin
                     ((call/cc
                       (λ (k) 
                         (begin
                           (set! exit-k k)
                           (λ () 10)))
                       1))
                     (set! output (cons 101 output))))
                 (λ () (esc 100))
                 (λ () 0))
                (λ (x) x)))
             0))
           (λ (f) (f))))
        (term (<>
               ((output (list 101 101))
                (exit-k #f))
               ()
               (%
                1
                (dw
                 x_1 ; <--- beware: this is a fresh variable. Will it always be x_1?
                 (begin
                   ((call/cc
                     (λ (k1)
                       (begin
                         (set! exit-k k1)
                         (λ () 10)))
                     1))
                   (set! output (cons 101 output)))
                 ((cont
                   0
                   ((λ (k)
                      (abort
                       0
                       (λ ()
                         (%
                          1
                          (exit-k (λ () (set! exit-k #f)))
                          (λ (x)
                            x)))))
                    hole))
                  100)
                 0)
                (λ (x1) x1)))))
  (test "loop"
        '(<>
          ([counter (list 4 3 2 1 0)])
          []
          (%
           0
           ((λ (k)
              ((λ (k2)
                 (if (first (rest k2))
                     ((first k2) (λ () 
                                   (if (zero? (first counter))
                                       (list 10 #f)
                                       (begin
                                         (set! counter (rest counter))
                                         ((call/cc (λ (k) (λ () 
                                                            (cons k (list #t))))
                                                   0))))))
                     (first k2)))
               (%
                1
                (k (λ ()
                     ((call/cc (λ (k) (λ () 
                                        (cons k (list #t))))
                               0))))
                (λ (x) x))))
            (%
             1
             ((call/cc (λ (k) (λ () k))
                       1))
             (λ (x) x)))
           (λ (x) x)))
        '(<>
          ([counter (list 0)])
          []
          10))
  (void))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Chain

(define chain-defns
  `([make
     (λ (pre post)
       (%
        0
        (dynamic-wind
         (λ () (print pre))
         (λ ()
           ((call/comp
             (λ (k) (λ () k))
             0)))
         (λ () (print post)))
        (λ (x) x)))]
    [chain
     (λ (E_1 E_2)
       (%
        0
        (E_1 (λ ()
               (E_2 (λ ()
                      ((call/comp
                        (λ (k) (λ () k))
                        0))))))
        (λ (x) x)))]
    [composable->replacing
     (λ (E)
       (%
        0
        (E (λ ()
             ((call/cc
               (λ (k) (λ () k))
               0))))
        (λ (x) x)))]))

(define (with-chain-bindings e)
  `((λ (one-two three-four)
      ((λ (one-three-four-two one-NINE-three-four-two )
         ((λ (one-two* three-four* one-three-four-two* one-NINE-three-four-two*)
            (%
             0
             ,e
             (λ (x) x)))
          (composable->replacing one-two)
          (composable->replacing three-four)
          (composable->replacing one-three-four-two)
          (composable->replacing one-NINE-three-four-two)))
       (chain one-two three-four)
       (chain one-two (λ (x) ((λ (z)
                                (begin (print 9) z))
                              (three-four x))))))
    (make 1 2)
    (make 3 4)))

(define chain-output '(1 2 3 4 1 3 4 2 1 3 4 9 2 1 2 3 4 1 3 4 2 1 3 4 9 2))

(define (chain-tests)
  (test "check chain setup"
        `(<>
          (,@chain-defns)
          []
          ,(with-chain-bindings 10))
        `(<>
          (,@chain-defns)
          [,@chain-output]
          10))
  (test "chain sharing"
        `(<>
          (,@chain-defns)
          []
          ,(with-chain-bindings 
            `(one-three-four-two* (λ ()
                                    (one-two* (λ () 0))))))
        `(<>
          (,@chain-defns)
          [,@chain-output 1 3 4 2]
          0))
  (test "chain non-sharing"
        `(<>
          (,@chain-defns)
          []
          ,(with-chain-bindings 
            `(one-three-four-two* (λ ()
                                    (three-four* (λ () 0))))))
        `(<>
          (,@chain-defns)
          [,@chain-output 1 3 4 2 3 4]
          0))
  (test "chain sharing with spliced frame"
        `(<>
          (,@chain-defns)
          []
          ,(with-chain-bindings 
            `(one-three-four-two* (λ ()
                                    (one-NINE-three-four-two* (λ () 0))))))
        `(<>
          (,@chain-defns)
          [,@chain-output 1 3 4 9 2]
          0))
  (test "chain sharing with spliced frame (skipped)"
        `(<>
          (,@chain-defns)
          []
          ,(with-chain-bindings 
            `(one-NINE-three-four-two* (λ ()
                                         (one-three-four-two* (λ () 0))))))
        `(<>
          (,@chain-defns)
          [,@chain-output 1 3 4 2]
          0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Run

(begin
  (basic-tests)
  (r6rs-dw-tests)
  (cont-tests)
  (chain-tests)
  (printf "All ~s tests passed.\n" tests-passed))
