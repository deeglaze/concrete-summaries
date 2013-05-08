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
                abrt
                default-continuation-prompt-tag ;; -> tag
                make-continuation-prompt-tag ;; -> tag
                call-with-continuation-prompt ;; thunk tag handler -> ...
                cmp
                cc
                ;;call/cm ;; removed due to lack of time
                continuation-marks ;; continuation tag -> list
                ]
  [cc call-with-current-continuation call/cc]
  [cmp call/comp call-with-composable-continuation]
  [abrt abort abort-current-continuation]
  [prim zero? number boolean () print + first rest empty? cons]
  [nullary default-continuation-prompt-tag make-continuation-prompt-tag ((λ () e) ρ)]
  [prims control-prim prim]
  [label natural]
  [(σ ρ) any]
  [w (side-condition (name w any) (hash? (term w)))]
  [f (ev label (e ...) (v ...) ρ)
     (ifk e e ρ)
     (dw a v v) ;; pre/post thunks and gensym
     (dw/i a v v e ρ) ;; inserted dynamic-wind to run. Run (e ρ) in (dw a v v).
     (dw/call label a v v v v)
     (abort/i label v v) ;; inserted abort
     (call/i label v v) ;; inserted call
     (bgn p)
     (prompt v v)
     (setk a)]
  [κ (f κ) mt]
  [p (e ρ) v]
  [boolean #t #f]
  [a any]
  [part (π₀ label) (π₁ label)]
  [alloc-point x part]
  [(ks vs as) (side-condition (name vs any) (set? (term vs)))]  
  [v ((λ (x ...) e) ρ) tag (cont v κ) (comp κ) (pair a a) prims]
  [tag default-tag (prompt-tag a) number boolean '()] ;; natural added to cope with fyff paper's tests.
  [ς (p σ κ) (do-call label v (v ...) σ κ)]
  [x variable-not-otherwise-mentioned])

