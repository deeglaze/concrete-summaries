#lang racket
(require redex "fyff-grammar.rkt" "fyff-meta.rkt")

(struct -output ()) (define output (-output))

(define R
  (reduction-relation L
    ;; eval
    [--> ((x ρ) σ k) (v σ k)
         (where (any_0 ... v any_1 ...) (lookup σ ρ x))
         "variable"]
    [--> (((label e_0 e_rest ...) ρ) σ k)
         ((e_0 ρ) σ ((ev label (e_rest ...) () ρ) k))
         "application"]
    [--> (((begin e_0 e_1) ρ) σ k)
         ((e_0 ρ) σ ((bgn (e_1 ρ)) k))
         "begin"]
    [--> ((prims ρ) σ k) (prims σ k) "prim-v"]
    [--> (((if e e_then e_else) ρ) σ k)
         ((e ρ) σ ((ifk e_then e_else ρ) k)) "if"]
    [--> (((set! x e) ρ) σ k)
         ((e ρ) σ ((setk (ρlookup ρ x)) k))
         "set!"]
    ;; ;;;;;;;;;;;;;;;
    ;; Continue rules
    ;; ;;;;;;;;;;;;;;;
    [--> (nullary σ ((ev label () () ρ_ignore) k))
         (do-call label nullary () σ k)
         "nullary fn"]
    [--> (v σ ((ev label (e e_rest ...) (v_done ...) ρ) k))
         ((e ρ) σ ((ev label (e_rest ...) (v_done ... v)) k))
         "argument"]
    [--> (v σ ((prompt tag v_1) k))
         (v σ k)
         "prompt-v"]
    [--> (v σ ((bgn p) k))
         (p σ k)
         "begin-v"]
    [--> (name ς (v_last σ ((ev label () (((λ (x ...) e) ρ) v_args ...) ρ_ignore) k)))
         (do-call label ((λ (x ...) e) ρ) (v_args ... v_last) σ k)
         "multiary fn call"]
    [--> (#t σ ((ifk e_then e_else ρ) k))
         ((e_then ρ) σ k)
         "if true"]
    [--> (#f σ ((ifk e_then e_else ρ) k))
         ((e_else ρ) σ k)
         "if false"]
    [--> (v σ ((setk a) k))
         (void σ_1 k)
         (where σ_1 (σupdate σ a v))
         "mutate"]
    ;; ;;;;;;;;;;;;
    ;; apply rules
    ;; ;;;;;;;;;;;;
    [--> (name ς (do-call label ((λ (x ..._i) e) ρ) (v ..._i) σ k))
         ((e ρ_1) σ_1 k)
         (where (a ...) (alloc (x ...) ς))
         (where (ρ_1 σ_1) (bind ρ σ (x ...) (a ...) (v ...)))
         "call lambda"]
    ;; non-control primitives (zero? empty? first rest cons - print)
    [--> (do-call label zero? (0) σ k)
         (#t σ k)
         "zero? true"]
    [--> (do-call label zero? (v) σ k)
         (#f σ k)
         (side-condition/hidden (not (zero? (term v))))
         "zero? false"]
    [--> (do-call label - (integer ...) σ k)
         (,(apply - (term (integer ...))) σ k)
         "minus"]
    [--> (do-call label empty? ('()) σ k)
         (#t σ k)
         "empty? true"]
    [--> (do-call label empty? (v) σ k)
         (#t σ k)
         (side-condition/hidden (not (null? (term v))))
         "empty? false"]
    [--> (do-call label first ((pair a_fst a_rst)) σ k)
         (v σ k)
         (where (any_0 ... v any_1 ...) (σlookup σ a_fst))
         "first"]
    [--> (do-call label rest ((pair a_fst a_rst)) σ k)
         (v σ k)
         (where (any_0 ... v any_1 ...) (σlookup σ a_rst))
         "rest"]
    [--> (name ς (do-call label cons (v_0 v_1) σ k))
         ((pair a_fst a_rst) σ_1 k)
         (where (a_fst a_rst) (alloc ((π₀ label) (π₁ label)) ς))
         (where σ_1 (σextend* (a_fst a_rst) (v_0 v_1)))
         "cons"]
    ;; Printing is a little tricky in the abstract.
    ;; We're model output as continually adding output to a special list in the store.
    [--> (name ς (do-call label print (v) σ k))
         (void σ_2 k)
         (where (a_fst a_rst) (alloc ((π₀ label) (π₁ label)) ς))
         (where σ_0 (σextend σ a_rst (σlookups σ ,output)))
         (where σ_1 (σextend* σ_0 (a_fst) (v)))
         (where σ_2 (σupdate σ_1 ,output (pair a_fst a_rst)))]
    ;; control primitives
    [--> (name ς (do-call label default-continuation-prompt-tag () σ k))
         (default-tag σ k)
         "default tag"]
    [--> (name ς (do-call label make-continuation-prompt-tag () σ k))
         ((prompt-tag a) tag σ k)
         (where a (alloc label ς))
         "make tag"]
    [--> (do-call label call-with-continuation-prompt (((λ () e) ρ) tag v_handler) σ k)
         ((e ρ) σ ((prompt tag v_handler) k))
         "prompt"]
    [--> (do-call label call-with-composable-continuation (((λ (x) e) ρ) tag) σ k)
         ((e ρ_1) σ_1 k)
         (where (a) (alloc (x) ς))
         (where ρ_1 (extend ρ x a))
         (where σ_1 (σextend σ a (capture-upto k tag)))
         "call/comp"]
    [--> (do-call label call-with-current-continuation (((λ (x) e) ρ) tag) σ k)
         ((e ρ_1) σ_1 k)
         (where (a) (alloc (x) ς))
         (where ρ_1 (extend ρ x a))
         (where σ_1 (σextend σ a (capture-upto/cc k tag)))
         "call/cc"]
    [--> (do-call label abort-current-continuation (tag v) σ k)
         ((e_post ρ) σ ((abort/i tag v) k_1))
         (where (any_0 ... (((λ () e_post) ρ) k_1) any_1 ...) (abort-targets v_tag k σ))
         "abort-post"]
    [--> (do-call abort-current-continuation (tag v) σ k)
         ((e_handle ρ_1) σ_1 k_1)
         (where (any_0 ... (((λ (x) e_handle) ρ) k_1) any_1 ...) (abort-targets v_tag k σ))
         (where (a) (alloc (x) ς))
         (where (ρ_1 σ_1) (bind σ ρ (x) (a) (v)))
         "abort"]
    [--> (v σ ((dw a v_pre ((λ () e_post) ρ)) k))
         ((e_post ρ) σ ((bgn v) k))
         "dw-v"]
    [--> (name ς (do-call label dynamic-wind ((name v_pre ((λ () e_pre) ρ_pre)) ((λ () e_body) ρ_body) v_post) σ k))
         ((e_pre ρ_pre) σ ((dw/i a v_pre v_post e_body ρ_body) k))
         (where a (alloc label ς))
         "dw"]
    [--> (do-call label (comp k_call) (v) σ k)
         ((e_pre ρ) σ ((dw/call a v_pre v_post (comp k_next) v) k))
         (where (((λ () e_pre) ρ) k_next) (first-preprocess k_call))
         "comp-pre"]
    [--> (do-call label (comp k_call) (v) σ k)
         (v σ (kont-append k_call k))
         (where #f (first-preprocess k_call))
         "comp"]
    [--> (do-call label (cont tag k_call) (v) σ k)
         ((e_pre ρ) σ ((dw/call a v_pre v_post (cont tag k_call) v) k_next))
         (where (any_0 ...
                       (pre
                        a
                        (name v_pre ((λ () e_pre) ρ))
                        v_post
                        k_next)
                       any_1 ...)
                (unwrap-call/cc k_call tag k))
         "cont-pre"]
    [--> (do-call label (cont tag k_call) (v) σ k)
         ((e_post ρ) σ ((call/i (cont tag k_call) v) k_next))
         (where (any_0 ... (post e_post ρ k_next) any_1 ...)
                (unwrap-call/cc k_call tag k))
         "cont-post"]
    [--> (do-call label (cont tag k_call) (v) σ k)
         (v σ k_next)
         (where (any_0 ... k_next any_1 ...) (unwrap-call/cc k_call tag k))
         "cont"]
    ;; adiministrative reductions for control
    [--> (v_ignore ((abort/i tag v) k)) (do-call abort-current-continuation (tag v) σ k)]
    [--> (v_ignore σ ((dw/i a v_pre v_post e_body ρ_body) k))
         ((e_body ρ_body) σ ((dw a v_pre v_post) k))]
    [--> (v_ignore σ ((call/i v_fn v) k)) (do-call v_fn (v) σ k)]
    [--> (v_ignore σ ((dw/call a v_pre v_post v_fn v) k))
         (do-call v_fn (v) σ ((dw a v_pre v_post) k))]))