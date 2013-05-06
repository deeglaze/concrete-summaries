#lang racket
(provide L)
(require redex)

(define-language L
  [e x (label e e ...) (λ (x ...) e)
     (if e e e)
     control-prim prim
     (set! x e)
     (begin e e)]
  [control-prim dynamic-wind ;; pre body post (thunks) -> ...
                abort-current-continuation ;; tag value -> ...
                default-continuation-prompt-tag ;; -> tag
                make-continuation-prompt-tag ;; -> tag
                call-with-continuation-prompt ;; thunk tag handler -> ...
                call-with-composable-continuation ;; unary-fn tag -> ...
                call-with-current-continuation ;; unary-fn tag -> ...
                continuation-marks ;; continuation tag -> list
                ]
  [prim zero? integer #f #t '() print - first rest empty? cons]
  [nullary default-continuation-prompt-tag make-continuation-prompt-tag ((λ () e) ρ)]
  [prims control-prim prim]
  [label natural]
  [(σ ρ) any]
  [w (side-condition (name w any) (hash? (term w)))]
  [f (ev label (e ...) (v ...) ρ)
     (ifk e e ρ)
     (dw a v v) ;; pre/post thunks and gensym
     (dw/i a v v e ρ) ;; inserted dynamic-wind to run. Run (e ρ) in (dw a v v).
     (abort/i v v) ;; inserted abort
     (call/i v v) ;; inserted call
     (bgn p)
     (prompt v v)
     (setk a)]
  [p (e ρ) v]
  [a any]
  [(ks vs) (side-condition (name vs any) (set? (term vs)))]  
  [k (f k) mt]
  [v ((λ (x ...) e) ρ) tag (cont v k) (comp k) (pair a a) prims void]
  [tag default-tag (prompt-tag a)]
  [x variable-not-otherwise-mentioned])