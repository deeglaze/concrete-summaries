Require Import ZArith NArith List.
Definition Name := nat.
Notation "'dec_type' T" := (forall x y : T, {x=y}+{x<>y}) (at level 70, no associativity).

Definition name_eq_dec : dec_type Name.
  decide equality.
Defined.

Generalizable All Variables.
Set Implicit Arguments.

Inductive Expr : Type :=
| var : Name -> Expr
| app : Expr -> Expr -> Expr
| lam : Name -> Expr -> Expr.

Definition expr_eq_dec : dec_type Expr.
  decide equality; apply name_eq_dec.
Defined.

Section Data.
Variables Addr Time : Type.
Variable addr_eq_dec : dec_type Addr.
Variable time_eq_dec : dec_type Time.

Definition Env := list (Name * Addr).
Definition env_eq_dec : dec_type Env.
  apply list_eq_dec; decide equality; try solve [apply name_eq_dec | apply addr_eq_dec].
Defined.
(*
Inductive sexp :=
  | atom : Addr -> sexp
  | lst : sexps -> sexp
with sexps :=
       | snil : sexps
       | scons : sexp -> sexps -> sexps.
Scheme sexp_ind_2 := Induction for sexp Sort Prop
                     with sexps_ind_2 := Induction for sexps Sort Prop.
Combined Scheme sexp_mutind from sexp_ind_2, sexps_ind_2.
Lemma sexp_eq_dec : forall (s s': sexp) (ss ss' : sexps), (s = s' \/ s <> s') /\ (ss = ss' \/ ss <> ss').
Proof.
  Check sexp_mutind.
  intro s; apply (sexp_mutind (fun s' => s = s' \/ s <> s'));
  induction s;
  try solve
    [intro a0; destruct (addr_eq_dec a a0); [left|right;injection]; congruence
    | right; discriminate].
  intros s0 Hdec;
    pose (Hdec0 := (Hdec (lst s0) s s0));
    inversion Hdec0 as ([Heq|Hneq] & [Heqs|Hneqs]); firstorder.
  induction s'.
  destruct (addr_eq_dec a a0).
*)

Inductive val :=
  | closure : Name -> Expr -> Env -> val
  | adelay : Addr -> val
  | amany : list val -> val.
Definition AbsVal := list val.
Axiom val_eq_dec : dec_type val.
Definition absval_eq_dec : dec_type AbsVal.
  apply list_eq_dec,val_eq_dec.
Defined.

Definition Store := list (Addr * AbsVal).
Definition store_eq_dec : dec_type Store.
  apply list_eq_dec; decide equality; try solve [apply addr_eq_dec | apply absval_eq_dec].
Defined.

Inductive Frame :=
  | ar : Expr -> Env -> Frame
  | fn : val -> Frame.

Definition frame_eq_dec : dec_type Frame.
  decide equality; try solve [apply val_eq_dec | apply expr_eq_dec | apply env_eq_dec].
Defined.

Definition Kont : Type := list Frame.

Definition kont_eq_dec : dec_type Kont.
  apply list_eq_dec,frame_eq_dec.
Defined.

Inductive CESK :=
  | ev : Expr -> Env -> Store -> Kont -> Time -> CESK
  | co : val -> Store -> Kont -> Time -> CESK
  | ap : Name -> Expr -> Env -> (* Closure *)
         val -> (* Argument *)
         Store -> Kont -> Time -> CESK.

Definition cesk_eq_dec : dec_type CESK.
  decide equality; try solve [apply expr_eq_dec | apply env_eq_dec | apply kont_eq_dec
                             | apply time_eq_dec | apply val_eq_dec | apply store_eq_dec | apply name_eq_dec].
Defined.

Inductive MapsTo {A B} : list (A * B) -> A -> B -> Prop :=
  | map_fst : `{MapsTo ((a,b)::rst) a b}
  | map_rst : `{a <> a' -> MapsTo l a b -> MapsTo ((a',b')::l) a b}.

Inductive Unmapped {A B} : list (A * B) -> A -> Prop :=
  | unil : forall a, Unmapped nil a
  | ucons : forall a a' b l, Unmapped l a' -> a <> a' -> Unmapped ((a,b)::l) a'.

Theorem unmapped_not_mapped : forall A B
                                     (eq_dec : dec_type A)
                                     (l : list (A*B)) a,
                              Unmapped l a <-> forall b, ~ MapsTo l a b.
Proof.
  intros A B eq_dec l a; induction l as [|(a',b') l'];
  split;
  [intros H b bad; inversion bad
  |constructor
  |intros H b0 bad;
    inversion H as [| ? ? ? ? Hunmapped Hbad];
    inversion bad as [| ? ? ? ? ? ? Hbadmap]; subst;
    [contradict Hbad; reflexivity
    | rewrite IHl' in Hunmapped; apply Hunmapped in Hbadmap; auto]
  |intros H; constructor;
  [rewrite IHl'; intros bb bad; destruct (eq_dec a a'); subst;
      [pose (HC := (H b')); contradict HC; constructor
      |pose (HC := (H bb)); contradict HC; constructor; auto]
     |intro Heq; subst; apply H with (b := b'); constructor]].
Qed.

Definition in_aval := In.

Definition in_list_list {A B} (l : list (A * (list B))) (a : A) (b : B) : Prop :=
  exists bs, In (a,bs) l /\ In b bs.

Inductive in_force (σ : Store) : forall (v v' : val), Prop :=
| forced : `{in_force σ v v}
| do_force : `{MapsTo σ a vs -> in_aval v' vs -> in_force σ v' (adelay a)}.

Fixpoint extend_map {A B} (eq_dec : (dec_type A)) (a : A) (b : B) (ρ : list (A * B)) :=
  match ρ with
    | nil => (a, b)::nil
    | (a',b')::ρ' => if eq_dec a a' then
                       (a,b)::ρ'
                     else (a',b')::(extend_map eq_dec a b ρ')
  end.
Definition extend_ρ := extend_map name_eq_dec (B := Addr).

Fixpoint lookup_map {A B} (eq_dec : (dec_type A)) (a : A) (ρ : list (A * B)) : option B :=
  match ρ with
    | nil => None
    | (a',b)::ρ' => if eq_dec a a' then
                       Some b
                     else (lookup_map eq_dec a ρ')
  end.

Theorem lookup_mapsto : forall A B (eq_dec : dec_type A) (l : list (A * B)) a b,
                          MapsTo l a b <-> (lookup_map eq_dec a l) = Some b.
Proof.
  induction l as [|(a,b) l' IH]; [intros a b; split; intro Hvac; inversion Hvac|].
  intros a' b'; split; intro H; simpl in *;
  destruct (eq_dec a' a) as [Hleft|Hright];
  solve
   [inversion H;
   try solve [contradict Hleft; auto
             |contradict Hright; auto
             |apply IH; auto
             |auto]
   |injection H; intros; subst; constructor
   |constructor; [|apply IH];auto].
Qed. 
Definition lookup_ρ := lookup_map name_eq_dec (B := Addr).
Definition lookup_σ := lookup_map addr_eq_dec (B := AbsVal).

Fixpoint list_add_nodup {A} (eq_dec : dec_type A) (l : list A) (a : A) : list A :=
  match l with
      nil => a::nil
    | a'::l' => if eq_dec a a' then l else a'::(list_add_nodup eq_dec l' a)
  end.
Fixpoint list_append_nodup {A} (eq_dec : dec_type A) (l l' : list A) :=
  match l with
      nil => l'
    | a::l => list_add_nodup eq_dec (list_append_nodup eq_dec l l') a
  end.

Fixpoint list_join {A B C}
         (eq_dec : dec_type A)
         (combine : list (A * B) -> B -> C -> B)
         (base : list (A * B) -> C -> B)
         (l : list (A * B))
         (l_orig : list (A * B))
         (a : A) (c : C) : list (A * B) :=
  (fix inner l :=
  match l with
      | nil => (a,base l_orig c)::nil
      | (a',b)::l' => if (eq_dec a a') then
                        (a,(combine l_orig b c))::l'
                       else (a',b)::(inner l')
  end) l.

Definition force (σ : Store) (v:val) : AbsVal :=
  match v with
      | adelay a => match lookup_σ a σ with
                        None => nil
                      | Some vs => vs
                    end
      | amany vs => vs
      | v => v::nil
  end.
Definition absval_join (vs vs' : AbsVal) :=
  list_append_nodup val_eq_dec vs vs'.

Definition σ_join (σ : Store) (a : Addr) (v : val) : Store :=
  list_join addr_eq_dec
            (fun σ_orig vs v => (absval_join vs (force σ_orig v)))
            force σ σ a v.
Section StandardSemantics.
Variable alloc : CESK -> Addr.
Variable tick : CESK -> Time.

Inductive red_cesk : CESK -> CESK -> Prop :=
  ev_var : `{let s := (ev (var x) ρ σ κ t) in
             MapsTo ρ x a ->
             red_cesk s (co (adelay a) σ κ (tick s))}
| ev_app : `{let s := (ev (app e0 e1) ρ σ κ t) in
             red_cesk s (ev e0 ρ σ ((ar e1 ρ)::κ) (tick s))}
| ev_lam : `{let s := (ev (lam x e) ρ σ κ t) in
             red_cesk s (co (closure x e ρ) σ κ (tick s))}
| co_ar : `{let s := (co v σ ((ar e ρ)::κ) t) in
            red_cesk s (ev e ρ σ ((fn v)::κ) (tick s))}
| co_fn : `{let s := (co v σ ((fn fnv)::κ) t) in
            in_force σ (closure x e ρ) fnv ->
            red_cesk s (ap x e ρ v σ κ (tick s))}
| do_ap : `{let s := (ap x e ρ v σ κ t) in
            let a := alloc s in
            let ρ' := extend_ρ x a ρ in
            let σ' := σ_join σ a v in
            red_cesk s (ev e ρ' σ' κ (tick s))}.
End StandardSemantics.

Section NonStandardData.
Inductive Context :=
  context : Expr -> Env -> Store -> Context.

Definition context_eq_dec : dec_type Context.
  decide equality; try solve [apply expr_eq_dec | apply env_eq_dec | apply store_eq_dec].
Defined.

Inductive Result :=
  res: val -> Store -> Result.
Definition Results := list Result.

Definition result_eq_dec : dec_type Result.
  decide equality; try solve [apply val_eq_dec | apply store_eq_dec].
Defined.

Inductive TrunKont :=
| mt : TrunKont
| kpush : Frame -> TrunKont -> TrunKont
| rt : Context -> TrunKont.

Definition trunkont_eq_dec : dec_type TrunKont.
  decide equality; try solve [apply frame_eq_dec | apply context_eq_dec].
Defined.

Definition TrunKonts := list TrunKont.
Definition Memo := list (Context * Results).
Definition KTable := list (Context * TrunKonts).

Definition trunckonts_join (κs κs' : TrunKonts) := list_append_nodup trunkont_eq_dec κs κs'.
Definition lookup_M := lookup_map context_eq_dec (B := Results).
Definition lookup_Ξ := lookup_map context_eq_dec (B := TrunKonts).

Definition Ξ_join (Ξ : KTable) (ctx : Context) (κ : TrunKont) : KTable :=
  list_join context_eq_dec
            (fun _ κs κ => (list_add_nodup trunkont_eq_dec κs κ))
            (fun _ κ => κ :: nil) Ξ Ξ ctx κ.
Definition M_join (M : Memo) (ctx : Context) (r : Result) : Memo :=
  list_join context_eq_dec
            (fun _ rs r => (list_add_nodup result_eq_dec rs r))
            (fun _ r => r :: nil) M M ctx r.

Definition in_ctxs (Ξ : KTable) (ctx : Context) (κ : TrunKont) : Prop :=
  in_list_list Ξ ctx κ.

Definition in_memos (M : Memo) (ctx : Context) (r : Result) : Prop :=
  in_list_list M ctx r.


Inductive WCESKMΞ :=
  | evmk : Expr -> Env -> Store -> TrunKont -> Time -> WCESKMΞ
  | comk : val -> Store -> TrunKont -> Time -> WCESKMΞ
  | apmk : Name -> Expr -> Env -> (* Closure *)
           val -> (* Argument *)
           Store -> TrunKont -> Time -> WCESKMΞ.

Definition wceskmξ_eq_dec : dec_type WCESKMΞ.
  decide equality; try solve [apply expr_eq_dec | apply store_eq_dec | apply trunkont_eq_dec | apply time_eq_dec | apply val_eq_dec | apply env_eq_dec | apply name_eq_dec].
Defined. 
Inductive CESKMΞ :=
  | widemk : WCESKMΞ -> Memo -> KTable -> CESKMΞ.

Section NonStandardSemantics.
Variable allocmk : CESKMΞ -> Addr.
Variable tickmk : CESKMΞ -> Time.

Inductive red_ceskmk : CESKMΞ -> CESKMΞ -> Prop :=
  evmk_var : `{let s := widemk (evmk (var x) ρ σ κ t) M Ξ in
             MapsTo ρ x a ->
             red_ceskmk s (widemk (comk (adelay a) σ κ (tickmk s))  M Ξ)}
| evmk_app : `{let s := widemk (evmk (app e0 e1) ρ σ κ t) M Ξ in
             red_ceskmk s (widemk (evmk e0 ρ σ (kpush (ar e1 ρ) κ) (tickmk s)) M Ξ)}
| evmk_lam : `{let s := widemk (evmk (lam x e) ρ σ κ t) M Ξ in
             red_ceskmk s (widemk (comk (closure x e ρ) σ κ (tickmk s)) M Ξ)}
| comk_ar : `{let s := widemk (comk v σ (kpush (ar e ρ) κ) t) M Ξ in
            red_ceskmk s (widemk (evmk e ρ σ (kpush (fn v) κ) (tickmk s)) M Ξ)}
| comk_fn : `{let s := widemk (comk v σ (kpush (fn fnv) κ) t) M Ξ in
              in_force σ (closure x e ρ) fnv ->
              red_ceskmk s (widemk (apmk x e ρ v σ κ (tickmk s)) M Ξ)}
| do_apmk : `{let s := widemk (apmk x e ρ v σ κ t) M Ξ in
              let a := allocmk s in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let ctx := (context e ρ' σ') in
              let Ξ' := Ξ_join Ξ ctx κ in
              Unmapped M ctx ->
              red_ceskmk s (widemk (evmk e ρ' σ' (rt ctx) (tickmk s)) M Ξ')}
| do_memo : `{let s := widemk (apmk x e ρ v σ κ t) M Ξ in
              let a := allocmk s in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let ctx := (context e ρ' σ') in
              let Ξ' := Ξ_join Ξ ctx κ in
              in_memos M ctx (res vm σm) ->
              red_ceskmk s (widemk (comk vm σm κ (tickmk s)) M Ξ')} (* XXX: tick? *)
| do_rt : `{let s := widemk (comk v σ (rt ctx) t) M Ξ in
            let M' := M_join M ctx (res v σ) in
            in_ctxs Ξ ctx κ ->
            red_ceskmk s (widemk (comk v σ κ (tickmk s)) M' Ξ)}.

Definition step_all (s : CESKMΞ) : list CESKMΞ :=
  match s with
    | widemk (evmk (var x) ρ σ κ t) M Ξ  =>
      match (lookup_ρ x ρ) with
       | None => nil
       | Some a => (widemk (comk (adelay a) σ κ (tickmk s)) M Ξ)::nil
      end
    | widemk (evmk (app e0 e1) ρ σ κ t) M Ξ =>
      (widemk (evmk e0 ρ σ (kpush (ar e1 ρ) κ) (tickmk s)) M Ξ)::nil
    | widemk (evmk (lam x e) ρ σ κ t) M Ξ =>
      (widemk (comk (closure x e ρ) σ κ (tickmk s)) M Ξ)::nil
    | widemk (comk v σ (kpush (ar e ρ) κ) t) M Ξ =>
              (widemk (evmk e ρ σ (kpush (fn v) κ) (tickmk s)) M Ξ)::nil
    | widemk (comk v σ (kpush (fn fnv) κ) t) M Ξ =>
      (* Append forces *)
      fold_right (fun v acc =>
                    match v with
                        closure x e ρ => (widemk (apmk x e ρ v σ κ (tickmk s)) M Ξ)::acc
                      | _ => acc
                 end)
                 nil
                 (force σ fnv)
    | widemk (apmk x e ρ v σ κ t) M Ξ =>
      let a := allocmk s in
      let ρ' := extend_ρ x a ρ in
      let σ' := σ_join σ a v in
      let ctx := (context e ρ' σ') in
      let Ξ' := Ξ_join Ξ ctx κ in
      (* both call and use memo table *)
      match (lookup_M ctx M) with
            | None => (widemk (evmk e ρ' σ' (rt ctx) (tickmk s)) M Ξ')::nil
            | Some rs =>
              fold_right (fun r acc =>
                            match r with
                                res vm σm => (widemk (comk vm σm κ (tickmk s)) M Ξ')::acc
                            end)
                         nil
                         rs
      end
    | widemk (comk v σ (rt ctx) t) M Ξ =>
      let M' := M_join M ctx (res v σ) in
      match (lookup_Ξ ctx Ξ) with
          | None => nil
          | Some κs =>
            fold_right (fun κ acc =>
                          (widemk (comk v σ κ (tickmk s)) M' Ξ)::acc)
                       nil κs
      end                 
    | widemk (comk v σ mt t) M Ξ => nil
  end.

Theorem finite_steps : forall s, exists ss : list CESKMΞ, forall s',
                         red_ceskmk s s' <-> In s' ss.
Proof.
  intro s; exists (step_all s); intro s'; split; [intro Hred|intro Hin].
  inversion_clear Hred; simpl; try solve [left; auto|
rewrite lookup_mapsto with (eq_dec := name_eq_dec) in H;
unfold lookup_ρ; rewrite H; constructor; auto].
inversion H.
Admitted. 

Inductive Wide_CESKMΞ : list WCESKMΞ -> list WCESKMΞ -> Memo -> KTable ->
                        list WCESKMΞ -> list WCESKMΞ -> Memo -> KTable -> Prop :=
  | big_step : `{Wide_CESKMΞ (**) Seen (s::F) M Ξ (**)
                                  (list_append_nodup wceskmξ_eq_dec F' (list_add_nodup WCESKMΞ_eq_dec Seen s))
                                  (list_append_nodup wceskmξ_eq_dec F' F)
                                  M' Ξ'}.
End NonStandardSemantics.
End NonStandardData.
