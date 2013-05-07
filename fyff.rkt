#lang racket

(provide R output)
(require redex "fyff-grammar.rkt" "fyff-meta.rkt")

(struct -output ()) (define output (-output))

(define R
  (reduction-relation L
    ;; eval
    [--> ((x ρ) σ κ) (v σ κ)
         (where (any_0 ... v any_1 ...) (lookup σ ρ x))
         "variable"]
    [--> (((label e_0 e_rest ...) ρ) σ κ)
         ((e_0 ρ) σ ((ev label (e_rest ...) () ρ) κ))
         "application"]
    [--> (((begin e_0 e_1) ρ) σ κ)
         ((e_0 ρ) σ ((bgn (e_1 ρ)) κ))
         "begin"]
    [--> ((prims ρ) σ κ) (prims σ κ) "prim-v"]
    [--> (((if e e_then e_else) ρ) σ κ)
         ((e ρ) σ ((ifk e_then e_else ρ) κ)) "if"]
    [--> (((set! x e) ρ) σ κ)
         ((e ρ) σ ((setk (ρlookup ρ x)) κ))
         "set!"]
    ;; ;;;;;;;;;;;;;;;
    ;; Continue rules
    ;; ;;;;;;;;;;;;;;;
    [--> (nullary σ ((ev label () () ρ_ignore) κ))
         (do-call label nullary () σ κ)
         "nullary fn"]
    [--> (v σ ((ev label (e e_rest ...) (v_done ...) ρ) κ))
         ((e ρ) σ ((ev label (e_rest ...) (v_done ... v) ρ) κ))
         "argument"]
    [--> (v σ ((prompt tag v_1) κ))
         (v σ κ)
         "prompt-v"]
    [--> (v σ ((bgn p) κ))
         (p σ κ)
         "begin-v"]
    [--> (name ς (v_last σ ((ev label () (v_fn v_args ...) ρ_ignore) κ)))
         (do-call label v_fn (v_args ... v_last) σ κ)
         "multiary fn call"]
    [--> (#t σ ((ifk e_then e_else ρ) κ))
         ((e_then ρ) σ κ)
         "if true"]
    [--> (#f σ ((ifk e_then e_else ρ) κ))
         ((e_else ρ) σ κ)
         "if false"]
    [--> (v σ ((setk a) κ))
         (#f σ_1 κ)
         (where σ_1 (σupdate σ a v))
         "mutate"]
    ;; ;;;;;;;;;;;;
    ;; apply rules
    ;; ;;;;;;;;;;;;
    [--> (name ς (do-call label ((λ (x ..._i) e) ρ) (v ..._i) σ κ))
         ((e ρ_1) σ_1 κ)
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σ_1) (bind σ ρ (x ...) (a ...) (v ...)))
         "call lambda"]
    ;; non-control primitives (zero? empty? first rest cons - print)
    [--> (do-call label zero? (0) σ κ)
         (#t σ κ)
         "zero? true"]
    [--> (do-call label zero? (v) σ κ)
         (#f σ κ)
         (side-condition/hidden (not (zero? (term v))))
         "zero? false"]
    [--> (do-call label + (integer ...) σ κ)
         (,(apply + (term (integer ...))) σ κ)
         "plus"]
    [--> (do-call label empty? ('()) σ κ)
         (#t σ κ)
         "empty? true"]
    [--> (do-call label empty? (v) σ κ)
         (#t σ κ)
         (side-condition/hidden (not (null? (term v))))
         "empty? false"]
    [--> (do-call label first ((pair a_fst a_rst)) σ κ)
         (v σ κ)
         (where (any_0 ... v any_1 ...) (σlookup σ a_fst))
         "first"]
    [--> (do-call label rest ((pair a_fst a_rst)) σ κ)
         (v σ κ)
         (where (any_0 ... v any_1 ...) (σlookup σ a_rst))
         "rest"]
    [--> (name ς (do-call label cons (v_0 v_1) σ κ))
         ((pair a_fst a_rst) σ_1 κ)
         (where (a_fst a_rst) (alloc ((π₀ label) (π₁ label)) ς))
         (where σ_1 (σextend* σ (a_fst a_rst) (v_0 v_1)))
         "cons"]
    ;; Printing is a little tricky in the abstract.
    ;; We're model output as continually adding output to a special list in the store.
    [--> (name ς (do-call label print (v) σ κ))
         (#f σ_2 κ)
         (where (a_fst a_rst) (alloc ((π₀ label) (π₁ label)) ς))
         (where σ_0 (σextend σ a_rst (σlookups σ ,output)))
         (where σ_1 (σextend* σ_0 (a_fst) (v)))
         (where σ_2 (σupdate σ_1 ,output (pair a_fst a_rst)))
         "print"]
    ;; control primitives
    [--> (name ς (do-call label default-continuation-prompt-tag () σ κ))
         (default-tag σ κ)
         "default tag"]
    [--> (name ς (do-call label make-continuation-prompt-tag () σ κ))
         ((prompt-tag a) tag σ κ)
         (where a (alloc label ς))
         "make tag"]
    [--> (do-call label call-with-continuation-prompt (((λ () e) ρ) tag v_handler) σ κ)
         ((e ρ) σ ((prompt tag v_handler) κ))
         "prompt"]
    [--> (name ς (do-call label cmp (((λ (x) e) ρ) tag) σ κ))
         ((e ρ_1) σ_1 κ)
         (where (a) (alloc (x) ς))
         (where ρ_1 (extend ρ x a))
         (where σ_1 (σextend σ a (capture-upto κ tag)))
         "call/comp"]
    [--> (name ς (do-call label cc (((λ (x) e) ρ) tag) σ κ))
         ((e ρ_1) σ_1 κ)
         (where (a) (alloc (x) ς))
         (where ρ_1 (extend ρ x a))
         (where σ_1 (σextend σ a (capture-upto/cc κ tag)))
         "call/cc"]
    [--> (do-call label abrt (tag v) σ κ)
         ((e_post ρ) σ ((abort/i label tag v) κ_1))
         (where (any_0 ... (((λ () e_post) ρ) κ_1) any_1 ...) (abort-targets κ tag σ))
         "abort-post"]
    [--> (name ς (do-call label abrt (tag v) σ κ))
         ((e_handle ρ_1) σ_1 κ_1)
         (where (any_0 ... (((λ (x) e_handle) ρ) κ_1) any_1 ...) (abort-targets κ tag σ))
         (where (a) (alloc (x) ς))
         (where (ρ_1 σ_1) (bind σ ρ (x) (a) (v)))
         "abort"]
    [--> (v σ ((dw a v_pre ((λ () e_post) ρ)) κ))
         ((e_post ρ) σ ((bgn v) κ))
         "dw-v"]
    [--> (name ς (do-call label dynamic-wind ((name v_pre ((λ () e_pre) ρ_pre)) ((λ () e_body) ρ_body) v_post) σ κ))
         ((e_pre ρ_pre) σ ((dw/i a v_pre v_post e_body ρ_body) κ))
         (where a (alloc label ς))
         "dw"]
    [--> (do-call label (comp κ_call) (v) σ κ)
         ((e_pre ρ) σ ((dw/call label a v_pre v_post (comp κ_next) v) κ))
         (where ((name v_pre ((λ () e_pre) ρ)) v_post κ_next) (first-preprocess κ_call))
         "comp-pre"]
    [--> (do-call label (comp κ_call) (v) σ κ)
         (v σ (kont-append κ_call κ))
         (where #f (first-preprocess κ_call))
         "comp"]
    [--> (do-call label (cont tag κ_call) (v) σ κ)
         ((e_pre ρ) σ ((dw/call label a v_pre v_post (cont tag κ_call) v) κ_next))
         (where (any_0 ...
                       (pre
                        a
                        (name v_pre ((λ () e_pre) ρ))
                        v_post
                        κ_next)
                       any_1 ...)
                (unwrap-call/cc κ_call tag κ))
         "cont-pre"]
    [--> (name ς (do-call label (cont tag κ_call) (v) σ κ))
         ((e_post ρ) σ ((call/i label (cont tag κ_call) v) κ_next))
         (where (any_0 ... (post ((λ () e_post) ρ) κ_next) any_1 ...)
                (unwrap-call/cc κ_call tag κ))
         "cont-post"]
    [--> (do-call label (cont tag κ_call) (v) σ κ)
         (v σ κ_next)
         (where (any_0 ... κ_next any_1 ...) (unwrap-call/cc κ_call tag κ))
         "cont"]
    ;; continuation marks not covered
    ;; adiministrative reductions for control
    [--> (v_ignore σ ((abort/i label tag v) κ))
         (do-call label abort-current-continuation (tag v) σ κ)]
    [--> (v_ignore σ ((dw/i a v_pre v_post e_body ρ_body) κ))
         ((e_body ρ_body) σ ((dw a v_pre v_post) κ))]
    [--> (v_ignore σ ((call/i label v_fn v) κ))
         (do-call label v_fn (v) σ κ)]
    [--> (v_ignore σ ((dw/call label a v_pre v_post v_fn v) κ))
         (do-call label v_fn (v) σ ((dw a v_pre v_post) κ))]))
