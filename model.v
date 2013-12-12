Require Import ZArith NArith List ListSet Paco.paco.
Import ListNotations.
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
  | amany : set val -> val.
Definition AbsVal := set val.
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

Inductive Shell (P : Type) :=
  shell : P -> Kont -> Time -> Shell P.

Inductive CES_point :=
  | ev : Expr -> Env -> Store -> CES_point
  | co : val -> Store -> CES_point
  | ap : Name -> Expr -> Env -> (* Closure *)
         val -> (* Argument *)
         Store -> CES_point.
Definition CESK := Shell CES_point.

Definition ces_point_eq_dec : dec_type CES_point.
  decide equality; try solve [apply expr_eq_dec | apply env_eq_dec | apply kont_eq_dec
                             | apply time_eq_dec | apply val_eq_dec | apply store_eq_dec | apply name_eq_dec].
Defined.

Definition cesk_eq_dec : dec_type CESK.
  decide equality; try solve [apply kont_eq_dec | apply time_eq_dec | apply ces_point_eq_dec].
Defined.

Inductive InDom {A B} : list (A * B) -> A -> Prop :=
  | dom_fst : `{InDom ((a,b)::rst) a}
  | dom_rst : `{InDom l a -> InDom ((a',b')::l) a}.

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

Definition in_list_list {A B} (l : list (A * (set B))) (a : A) (b : B) : Prop :=
  exists bs, In (a,bs) l /\ set_In b bs.

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

Fixpoint list_join {A B C}
         (eq_dec : dec_type A)
         (combine : list (A * B) -> B -> C -> B)
         (base : list (A * B) -> C -> B)
         (l_orig : list (A * B))
         (a : A) (c : C)
         (l : list (A * B)) : list (A * B) :=
  match l with
      | nil => (a,base l_orig c)::nil
      | (a',b)::l' => if (eq_dec a a') then
                        (a,(combine l_orig b c))::l'
                      else (a',b)::(list_join eq_dec combine base l_orig a c l')
  end.

Lemma in_list_join :
  forall A B (combine : list (A * set B) -> set B -> B -> set B) base l l' a c
    (eq_dec : dec_type A),
    (forall l b c, set_In c (combine l b c)) ->
    (forall l c, set_In c (base l c)) ->
    (forall ab, In ab l -> In ab l') ->
  in_list_list (list_join eq_dec combine base l' a c l) a c.
Proof.
  intros A B combine base l l' a c eq_dec Hextensive Hsingleton Hcontain.
  induction l; simpl.
  exists (base l' c); split; [left| apply Hsingleton]; auto.
  destruct a0 as [a' b]; destruct (eq_dec a a') as [Heq | Hneq];
  [subst; exists (combine l' b c); split; [left|apply Hextensive]; auto
  |].
  destruct IHl as [bs [Hainbs Hbinbs]].
   (* backchain IHl *)
    intros (a_,bs') Hin; apply Hcontain; right; auto.
  exists bs; split; [right|]; auto.
Qed.

Lemma in_list_join2 :
  forall A B (combine : list (A * set B) -> set B -> B -> set B) base l l' a a' c c'
    (eq_dec : dec_type A),
    (forall l b c c', set_In c' b -> set_In c' (combine l b c)) ->
    (forall l b c, set_In c (combine l b c)) ->
    (forall l c, set_In c (base l c)) ->
    (forall ab, In ab l -> In ab l') ->
  in_list_list l a' c' ->
  in_list_list (list_join eq_dec combine base l' a c l) a' c'.
Proof.
  intros A B combine base l l' a a' c c' eq_dec Hextensive1 Hextensive2 Hsingleton Hcontain Hold.
  induction l; simpl;
  inversion Hold as [bs [Hpairin Hsetin]];
  [(* base case *) inversion Hpairin
  |destruct a0; destruct (eq_dec a a0) as [Heq | Hneq]; subst;
   [(* Heq *)
     destruct (eq_dec a0 a') as [Heq' | Hneq']; subst;
    [(* Heq' *)
      inversion Hpairin as [Hpeq|Hrest];[
        injection Hpeq; intros; subst;
        exists (combine l' bs c); split; [left; auto|apply Hextensive1]
       |exists bs; split; [right|]]; auto
    |(* Hneq' *)
      inversion Hpairin as [Hbad|Hrest]; [
        injection Hbad; intros; subst; contradict Hneq'|
        exists bs; split; [right|]]; auto]
    |(* Hneq *)]].
  destruct (eq_dec a0 a') as [Heq' | Hneq']; subst;
  inversion Hpairin as [Hpeq|Hrest]; try solve
  [ (* Heq', Hpeq *)
    injection Hpeq; intros; subst;
      exists bs; split; [left|]; auto
   |(* Heq', Hrest *)
   assert (Hneed : in_list_list l a' c') by (exists bs; split; auto);
     assert (Hcontain' : forall ab, In ab l -> In ab l') by (intros ab Hin; apply Hcontain; right; auto);
     destruct (IHl Hcontain' Hneed) as [bs' [H0 H1]]; exists bs'; split; [right|]; auto].
Qed.

Definition singleton {A} (eq_dec : dec_type A) (x : A) : set A := set_add eq_dec x (@empty_set A).

Definition force (σ : Store) (v:val) : AbsVal :=
  match v with
      | adelay a => match lookup_σ a σ with
                        None => nil
                      | Some vs => vs
                    end
      | amany vs => vs
      | v => singleton val_eq_dec v
  end.
Definition absval_join (vs vs' : AbsVal) :=
  set_union val_eq_dec vs vs'.

Definition σ_join (σ : Store) (a : Addr) (v : val) : Store :=
  list_join addr_eq_dec
            (fun σ_orig vs v => (absval_join vs (force σ_orig v)))
            force σ a v σ.
Section StandardSemantics.
Variable alloc : CESK -> Addr.
Variable tick : CESK -> Time.
Variable time0 : Time.

Inductive red_cesk : CESK -> CESK -> Prop :=
  ev_var : `{let s := (shell (ev (var x) ρ σ) κ t) in
             MapsTo ρ x a ->
             red_cesk s (shell (co (adelay a) σ) κ (tick s))}
| ev_app : `{let s := (shell (ev (app e0 e1) ρ σ) κ t) in
             red_cesk s (shell (ev e0 ρ σ) ((ar e1 ρ)::κ) (tick s))}
| ev_lam : `{let s := (shell (ev (lam x e) ρ σ) κ t) in
             red_cesk s (shell (co (closure x e ρ) σ) κ (tick s))}
| co_ar : `{let s := (shell (co v σ) ((ar e ρ)::κ) t) in
            red_cesk s (shell (ev e ρ σ) ((fn v)::κ) (tick s))}
| co_fn : `{let s := (shell (co v σ) ((fn fnv)::κ) t) in
            in_force σ (closure x e ρ) fnv ->
            red_cesk s (shell (ap x e ρ v σ) κ (tick s))}
| do_ap : `{let s := (shell (ap x e ρ v σ) κ t) in
            let a := alloc s in
            let ρ' := extend_ρ x a ρ in
            let σ' := σ_join σ a v in
            red_cesk s (shell (ev e ρ' σ') κ (tick s))}.

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream
  | Nil : stream.
End stream.

CoInductive Trace {State} (s0 : State) (R : State -> State -> Prop) : stream State -> Prop :=
  | initial : Trace s0 R (Cons s0 (Nil _))
  | CESK_step : `{Trace s0 R (Cons ς π) ->
                  R ς ς' ->
                  Trace s0 R (Cons ς' (Cons ς π))}.

Definition CESK_trace (e : Expr) := Trace (shell (ev e nil nil) nil time0) red_cesk.
Section NonStandardData.
Inductive Context :=
  context : Expr -> Env -> Store -> Context.

Definition context_eq_dec : dec_type Context.
  decide equality; try solve [apply expr_eq_dec | apply env_eq_dec | apply store_eq_dec].
Defined.

Inductive Result :=
  res: val -> Store -> Result.
Definition Results := set Result.

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

Definition TrunKonts := set TrunKont.
Definition Memo := list (Context * Results).
Definition KTable := list (Context * TrunKonts).

Definition memo_eq_dec : dec_type Memo.
  decide equality;
  decide equality; try solve [apply context_eq_dec | apply list_eq_dec, result_eq_dec].
Defined.

Definition ktable_eq_dec : dec_type KTable.
  decide equality;
  decide equality; try solve [apply context_eq_dec | apply list_eq_dec, trunkont_eq_dec].
Defined.

Definition trunckonts_join (κs κs' : TrunKonts) := set_union trunkont_eq_dec κs κs'.
Definition lookup_M := lookup_map context_eq_dec (B := Results).
Definition lookup_Ξ := lookup_map context_eq_dec (B := TrunKonts).

Definition Ξ_join (Ξ : KTable) (ctx : Context) (κ : TrunKont) : KTable :=
  list_join context_eq_dec
            (fun _ κs κ => (set_add trunkont_eq_dec κ κs))
            (fun _ κ => singleton trunkont_eq_dec κ) Ξ ctx κ Ξ.
Definition M_join (M : Memo) (ctx : Context) (r : Result) : Memo :=
  list_join context_eq_dec
            (fun _ rs r => (set_add result_eq_dec r rs))
            (fun _ r => singleton result_eq_dec r) M ctx r M.

Fixpoint map_join {A B} (join1 : list (A * B) -> A -> B -> list (A * B)) (l l' : list (A * B)) :=
  match l with
      nil => l'
    | (a,b)::l'' => join1 (map_join join1 l'' l') a b
  end.
Definition Ξs_join := map_join (fun Ξ ctx κs => list_join context_eq_dec
                                                          (fun _ κs' κs => set_union trunkont_eq_dec κs' κs)
                                                          (fun _ κs => κs)
                                                          Ξ ctx κs Ξ).
Definition Ms_join := map_join (fun M ctx rs => list_join context_eq_dec
                                                          (fun _ rs' rs => set_union result_eq_dec rs' rs)
                                                          (fun _ rs => rs)
                                                          M ctx rs M).

Definition in_ctxs (Ξ : KTable) (ctx : Context) (κ : TrunKont) : Prop :=
  in_list_list Ξ ctx κ.

Definition in_memos (M : Memo) (ctx : Context) (r : Result) : Prop :=
  in_list_list M ctx r.

Inductive WShell (P : Type) :=
  wshell : P -> TrunKont -> Time -> WShell P.

Definition WCESKMΞ := WShell CES_point.

Definition wceskmξ_eq_dec : dec_type WCESKMΞ.
  decide equality; try solve [apply ces_point_eq_dec | apply trunkont_eq_dec | apply time_eq_dec].
Defined.
Inductive CESKMΞ :=
  | widemk : WCESKMΞ -> Memo -> KTable -> CESKMΞ.

Definition ceskmξ_eq_dec : dec_type CESKMΞ.
  decide equality; try solve [apply wceskmξ_eq_dec | apply memo_eq_dec | apply ktable_eq_dec].
Defined.

Section NonStandardSemantics.
Variable allocmk : CESKMΞ -> Addr.
Variable tickmk : CESKMΞ -> Time.
Variable time0mk : Time.

Inductive red_ceskmk : CESKMΞ -> CESKMΞ -> Prop :=
  evmk_var : `{let s := widemk (wshell (ev (var x) ρ σ) κ t) M Ξ in
             MapsTo ρ x a ->
             red_ceskmk s (widemk (wshell (co (adelay a) σ) κ (tickmk s))  M Ξ)}
| evmk_app : `{let s := widemk (wshell (ev (app e0 e1) ρ σ) κ t) M Ξ in
             red_ceskmk s (widemk (wshell (ev e0 ρ σ) (kpush (ar e1 ρ) κ) (tickmk s)) M Ξ)}
| evmk_lam : `{let s := widemk (wshell (ev (lam x e) ρ σ) κ t) M Ξ in
             red_ceskmk s (widemk (wshell (co (closure x e ρ) σ) κ (tickmk s)) M Ξ)}
| comk_ar : `{let s := widemk (wshell (co v σ) (kpush (ar e ρ) κ) t) M Ξ in
            red_ceskmk s (widemk (wshell (ev e ρ σ) (kpush (fn v) κ) (tickmk s)) M Ξ)}
| comk_fn : `{let s := widemk (wshell (co v σ) (kpush (fn fnv) κ) t) M Ξ in
              in_force σ (closure x e ρ) fnv ->
              red_ceskmk s (widemk (wshell (ap x e ρ v σ) κ (tickmk s)) M Ξ)}
| do_apmk : `{let s := widemk (wshell (ap x e ρ v σ) κ t) M Ξ in
              let a := allocmk s in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let ctx := (context e ρ' σ') in
              let Ξ' := Ξ_join Ξ ctx κ in
              Unmapped M ctx ->
              red_ceskmk s (widemk (wshell (ev e ρ' σ') (rt ctx) (tickmk s)) M Ξ')}
| do_memo : `{let s := widemk (wshell (ap x e ρ v σ) κ t) M Ξ in
              let a := allocmk s in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let ctx := (context e ρ' σ') in
              let Ξ' := Ξ_join Ξ ctx κ in
              in_memos M ctx (res vm σm) ->
              red_ceskmk s (widemk (wshell (co vm σm) κ (tickmk s)) M Ξ')} (* XXX: tick? *)
| do_rt : `{let s := widemk (wshell (co v σ) (rt ctx) t) M Ξ in
            let M' := M_join M ctx (res v σ) in
            in_ctxs Ξ ctx κ ->
            red_ceskmk s (widemk (wshell (co v σ) κ (tickmk s)) M' Ξ)}.

Inductive Dom_in_Dom {A B C} : list (A * B) -> list (A * C) -> Prop :=
  | no_dom : `{Dom_in_Dom nil l}
  | cons_dom : `{(exists b, In (a,b) l')-> Dom_in_Dom l l' -> Dom_in_Dom ((a,b)::l) l'}.

Lemma In_join : forall A B C (eq_dec: dec_type A) (l l' : list (A * B))
                        (f : list (A * B) -> B -> C -> B)  g a a' b b',
                  (forall a b, In (a,b) l -> In (a,b) l') ->
                  In (a,b) l ->
                  exists b'', In (a,b'') (list_join eq_dec f g l' a' b' l).
Proof.
  intros A B C eq_dec l l' f g a a' b b' Hcontain Hin; induction l as [|(a0,b0) l_ IH];
  inversion Hin;
  assert (IHneed : forall a b, In (a,b) l_ -> In (a,b) l') by
      (intros; apply Hcontain; right; auto);
  pose (rec := IH IHneed);
  [injection H; intros; subst;
   unfold list_join;
   destruct (eq_dec a' a) as [Heq | Hneq];[
     subst; exists (f l' b b')
    |exists b]; constructor; auto
  |unfold list_join;
    destruct (eq_dec a' a0) as [Heq | Hneq];[
      exists b; right; auto
           | destruct rec as [b'' Hb'']; auto; exists b''; right; auto]].
Qed.

Lemma Dom_join : forall A B C D (eq_dec: dec_type A) (l : list (A * B)) (l' : list (A * D))
                        (f : list (A * D) -> D -> C -> D)  g a b,
                   Dom_in_Dom l l' -> Dom_in_Dom l (list_join eq_dec f g l' a b l').
Proof.
  intros A B C D eq_dec l l' f g a b Hdom; induction Hdom;
  constructor;
  (induction l';[destruct H as [? bad]; inversion bad |]);
  [destruct H as [b' Hb'];
    apply In_join with (b := b')|]; auto.
Qed.

Definition TraceTo {State} (R : State -> State -> Prop) (s0 s1 : State) : Prop :=
  exists pi, Trace s0 R (Cons s1 pi).

Definition step_all (s : CESKMΞ) : set CESKMΞ :=
  match s with
    | widemk (wshell (ev (var x) ρ σ) κ t) M Ξ  =>
      match (lookup_ρ x ρ) with
       | None => empty_set _
       | Some a => singleton ceskmξ_eq_dec (widemk (wshell (co (adelay a) σ) κ (tickmk s)) M Ξ)
      end
    | widemk (wshell (ev (app e0 e1) ρ σ) κ t) M Ξ =>
      singleton ceskmξ_eq_dec (widemk (wshell (ev e0 ρ σ) (kpush (ar e1 ρ) κ) (tickmk s)) M Ξ)
    | widemk (wshell (ev (lam x e) ρ σ) κ t) M Ξ =>
      singleton ceskmξ_eq_dec (widemk (wshell (co (closure x e ρ) σ) κ (tickmk s)) M Ξ)
    | widemk (wshell (co v σ) (kpush (ar e ρ) κ) t) M Ξ =>
              singleton ceskmξ_eq_dec (widemk (wshell (ev e ρ σ) (kpush (fn v) κ) (tickmk s)) M Ξ)
    | widemk (wshell (co v σ) (kpush (fn fnv) κ) t) M Ξ =>
      (* Append forces *)
      fold_right (fun v acc =>
                    match v with
                        closure x e ρ => set_add ceskmξ_eq_dec
                                                 (widemk (wshell (ap x e ρ v σ) κ (tickmk s)) M Ξ)
                                                 acc
                      | _ => acc
                 end)
                 (empty_set _)
                 (force σ fnv)
    | widemk (wshell (ap x e ρ v σ) κ t) M Ξ =>
      let a := allocmk s in
      let ρ' := extend_ρ x a ρ in
      let σ' := σ_join σ a v in
      let ctx := (context e ρ' σ') in
      let Ξ' := Ξ_join Ξ ctx κ in
      (* both call and use memo table *)
      match (lookup_M ctx M) with
            | None => singleton ceskmξ_eq_dec (widemk (wshell (ev e ρ' σ') (rt ctx) (tickmk s)) M Ξ')
            | Some rs =>
              fold_right (fun r acc =>
                            match r with
                                res vm σm => set_add ceskmξ_eq_dec
                                                     (widemk (wshell (co vm σm) κ (tickmk s)) M Ξ')
                                                     acc
                            end)
                         (empty_set _)
                         rs
      end
    | widemk (wshell (co v σ) (rt ctx) t) M Ξ =>
      let M' := M_join M ctx (res v σ) in
      match (lookup_Ξ ctx Ξ) with
          | None => (empty_set _)
          | Some κs =>
            fold_right (fun κ acc =>
                          set_add ceskmξ_eq_dec
                                  (widemk (wshell (co v σ) κ (tickmk s)) M' Ξ)
                                  acc)
                       (empty_set _) κs
      end
    | widemk (wshell (co v σ) mt t) M Ξ => empty_set _
  end.

Inductive Wide_step :=
  wide_step : set WCESKMΞ -> Memo -> KTable -> Wide_step.

Inductive System :=
  system : set WCESKMΞ -> set WCESKMΞ -> Memo -> KTable -> System.


Definition smush_steps (s : WCESKMΞ) (M: Memo) (Ξ: KTable) (S : set WCESKMΞ) : Wide_step :=
  (fix smush (ss : set CESKMΞ) (nexts : set WCESKMΞ) (M : Memo) (Ξ : KTable) :=
     match ss with
         nil => wide_step (filter (fun s => if In_dec wceskmξ_eq_dec s S then false else true) nexts) M Ξ
       | (widemk s M' Ξ')::ss' => smush ss' (set_add wceskmξ_eq_dec s nexts)
                                        (Ms_join M' M)
                                        (Ξs_join Ξ' Ξ)
     end)
    (step_all (widemk s M Ξ)) nil nil nil.

Theorem finite_steps : forall s, exists ss : set CESKMΞ, forall s',
                         red_ceskmk s s' <-> set_In s' ss.
Proof.
  intro s; exists (step_all s); intro s'; split; [intro Hred|intro Hin].
  inversion_clear Hred; simpl; try solve [left; auto|
rewrite lookup_mapsto with (eq_dec := name_eq_dec) in H;
unfold lookup_ρ; rewrite H; constructor; auto].
inversion H.
Admitted.

Check smush_steps.

Inductive Wide_CESKMΞ : System -> System -> Prop :=
  | big_step : forall s M Ξ Seen F ss M' Ξ',
                 (wide_step ss M' Ξ') = (smush_steps s M Ξ Seen) ->
                 Wide_CESKMΞ (**) (system Seen (s::F) M Ξ) (**)
                                  (system
                                  (set_union wceskmξ_eq_dec ss (set_add wceskmξ_eq_dec s Seen))
                                  (set_union wceskmξ_eq_dec F ss)
                                  M' Ξ').

Definition WCESKMΞ_trace (e : Expr) := Trace (system ((wshell (ev e nil nil) mt time0)::nil) ((wshell (ev e nil nil) mt time0)::nil) nil nil) Wide_CESKMΞ.

(*
Inductive StackUnroll_gen gen (Ξ : KTable) : Kont -> TrunKont -> set Context -> Prop :=
  unroll_mt : forall G, StackUnroll_gen gen Ξ nil mt G
| unroll_push : forall κ tκ (R : gen Ξ κ tκ (empty_set Context) : Prop) φ G, StackUnroll_gen gen Ξ (φ :: κ) (kpush φ tκ) G
| unroll_rt : forall ctx G tκ κ (R : gen Ξ κ tκ (set_add context_eq_dec ctx G) : Prop),
                ~ set_In ctx G -> in_ctxs Ξ ctx tκ ->
                StackUnroll_gen gen Ξ κ (rt ctx) G.

Check monotone3.
Check (rel3 Kont (fun _ => TrunKont) (fun _ _ => (set Context))).


CoInductive StackUnroll (Ξ : KTable) κ tκ G : Prop :=
| stackunroll_fold (IN : StackUnroll_gen Ξ StackUnroll κ tκ G).

*)

CoInductive StackUnroll (Ξ : KTable) : Kont -> TrunKont -> list Context -> Prop :=
  unroll_mt : forall G, StackUnroll Ξ nil mt G
| unroll_push : forall κ tκ φ G, StackUnroll Ξ κ tκ G -> StackUnroll Ξ (φ :: κ) (kpush φ tκ) G
| unroll_rt : forall ctx G tκ κ,
                In ctx G ->
                StackUnroll Ξ κ tκ (remove_one context_eq_dec ctx G) ->
                in_ctxs Ξ ctx tκ ->
                StackUnroll Ξ κ (rt ctx) G.

Theorem unroll_with_extension : forall
        (Ξ : KTable) (ctx : Context) (κ : Kont) (tκ tκ' : TrunKont) (G G' : list Context)
        (hyp : StackUnroll Ξ κ tκ G) (Hsub : Sublist context_eq_dec G G'), StackUnroll (Ξ_join Ξ ctx tκ') κ tκ G'.
Proof.
  cofix; intros Ξ ctx κ tκ tκ' G G' hyp Hsub.
  inversion hyp; subst;
  [constructor
  |apply unroll_push,unroll_with_extension with (G := G)
  | ]; auto.
  apply unroll_rt with (tκ := tκ0); [
  (* In ctx0 G' *)
  apply sublist_subset in Hsub;
    unfold Subset in Hsub;
    rewrite Forall_forall in Hsub;
    apply Hsub; assumption
  |apply unroll_with_extension with (G := (remove_one context_eq_dec ctx0 G));
    [|apply sublist_remove];assumption
  |(* in_ctxs*)
    apply in_list_join2; solve [
                             intros; apply set_add_intro1; auto
                            | intros; apply set_add_intro2; auto 
                            | auto]].
Qed.

Inductive KontTail : Kont -> Kont -> Prop :=
| same_tail : `{KontTail κ κ}
| push_tail : `{KontTail κ κ' -> KontTail κ (φ :: κ')}.

Fixpoint kont_tailp (κ κ' : Kont) : bool :=
  match (kont_eq_dec κ κ') with
      | left eqprf => true
      | right neqprf => match κ' with
                            nil => false
                          | φ :: κ' => kont_tailp κ κ'
                        end
  end.

Lemma kont_tailp_correct : forall κ κ', kont_tailp κ κ' = true <-> KontTail κ κ'.
Proof.
  induction κ'; simpl;
  [destruct (kont_eq_dec κ nil); split; intro H; subst; try solve [constructor
                                                                  |inversion H; contradiction]
  |destruct (kont_eq_dec κ (a :: κ')) as [Heq|Hneq]; split; intro H; subst; try solve [constructor];
   [rewrite IHκ' in H; constructor
   |rewrite IHκ'; inversion H; subst; [contradict Hneq|]]; auto].
Qed.

CoInductive hastail (κ : Kont) : stream CESK -> Prop :=
  Nil_tail : hastail κ (Nil _)
| Cons_tail : forall π p κ' t, hastail κ π -> KontTail κ κ' ->
                           hastail κ (Cons (shell p κ' t) π).

Inductive Inv : CESKMΞ -> Prop :=
  inv : forall p κ tκ t M Ξ G,
Dom_in_Dom M Ξ ->
StackUnroll Ξ κ tκ G ->
(forall e ρ σ tκ' κ' G',
in_ctxs Ξ (context e ρ σ) tκ' ->
StackUnroll Ξ κ' tκ' G' ->
(exists t', TraceTo red_cesk
                    (shell (ev e ρ σ) κ' t')
                    (shell p κ t))
/\
(forall v σ'',
   in_memos M (context e ρ σ) (res v σ'') ->
   exists pi t' t'', (Trace (shell (ev e ρ σ) κ' t')
                        red_cesk
                        (Cons (shell (co v σ'') κ' t'') pi) /\
                  hastail κ' pi))) ->
Inv (widemk (wshell p tκ t) M Ξ).

Axiom comparable_ticks : forall p κ tκ t M Ξ G,
                           StackUnroll Ξ κ tκ G ->
                           tick (shell p κ t) = tickmk (widemk (wshell p tκ t) M Ξ).

Lemma inv_invariant : forall s s', Inv s -> red_ceskmk s s' -> Inv s'.
Proof.
  intros s s' Hinv Hstep.
  inversion Hinv as [? ? ? ? ? ? G Hdom Htail Φ]; subst.
  Ltac common Φ kont point κ t invG tightenG pushG :=
      apply (inv (κ := kont) (G := invG)); try solve [apply unroll_push; auto
                                                  |constructor; auto
                                                  |auto];
      intros e' ρ' σ' tκ' κ' G' Htκ' Hunroll;
      pose (Φrinst := (Φ e' ρ' σ' tκ' κ' G' Htκ' Hunroll));
      destruct Φrinst as [Φreach Φmemo];
      destruct Φreach as [t'_ [π Φreach_path]];
      split;[
        (* reach *)
        exists t'_;
          exists (Cons (shell point κ t) π);
          constructor; [assumption|
                        compute;
                          rewrite <- (comparable_ticks _ _ _ (κ := κ) (G := tightenG));
                          solve [constructor; auto
                                    |auto]]
              |(* memo *) auto].
  inversion Hstep as [? ? ? ? ? (* <- time *) ? ? ? s0 Hmap Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? ? Hpeq |
                      ? ? ? ? ? ? ? ? s0 Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? s0 Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? ? ? s0 Hin_force Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? ? s0 a ρ' σ' ctx Ξ' Hunmapped Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? ? ? ? s0 a ρ' σ' ctx Ξ' Hin_memos Hpeq Hs'eq |
                      ? ? ? ? ? ? s0 M' Hin_ctxs Hpeq Hs'eq].
  (* Var lookup *)
  subst; common Φ κ (ev (var x) ρ σ) κ t G G G.
  (* function eval *)
  subst; common Φ ((ar e1 ρ)::κ) (ev (app e0 e1) ρ σ) κ t G G G.
  (* lam *)
  subst; common Φ κ (ev (lam x e) ρ σ) κ t G G G.
  (* arg eval *)
  inversion Htail as [|? ? ? ? G'' Hκtail|]; subst;
  try discriminate;
  injection H4; intros; subst;
  common Φ (fn v :: κ1) (co v σ) ((ar e ρ)::κ1) t G G G''.
  (* fn -> ap *)
  inversion Htail as [|? ? ? ? Hκtail|]; subst;
  try discriminate;
  injection H4; intros; subst;
  common Φ κ1 (co v σ) ((fn fnv)::κ1) t G G G.
  (* do unmemoized ap *)
  apply inv with (κ := κ) (G:= G); auto.
  apply Dom_join; auto.
  assert (Htail' : StackUnroll Ξ' κ tκ (ctx :: G)).
  apply unroll_with_extension with (G := G);[assumption|].
  apply sublist_extension with (l'' := [ ctx ]).
 with (G' := (set_add context_eq_dec ctx G)); try solve [auto | apply subset_refl].
  apply unroll_rt with (tκ := tκ); try solve [intro bad; inversion bad].
  unfold in_ctxs.
  apply in_list_join; auto;
  intros; apply set_add_intro2; auto.
  pose (Φrinst := (Φ e ρ' σ' (rt ctx) κ' Htκ' Htail));
    destruct Φrinst as [Φreach Φmemo];
    destruct Φreach as [t'_ [π Φreach_path]].

Inductive state_rel : CESK -> System -> Prop :=
  point_rel : `{StackUnroll Ξ κ κ' nil ->
                (set_In (wshell p κ' t) Seen \/ set_In (wshell p κ' t) F) ->
                state_rel (shell p κ t) (system Seen F M Ξ)}.

Theorem simulation : forall e s, CESK_trace e π -> exists s', state_rel s s' /\ WCESKMΞ_trace e π'.
Proof.
  intros e s π.


End NonStandardSemantics.
End NonStandardData.
End StandardSemantics.
End Data.