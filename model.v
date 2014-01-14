Require Import ZArith NArith List ListSet CpdtTactics stutter basic fmaplist joins.
Import ListNotations.
Definition Name := nat.

Definition name_eq_dec : dec_type Name. decide equality. Defined.
Hint Immediate name_eq_dec.

Generalizable All Variables.
Set Implicit Arguments.

Inductive Expr : Type :=
| var : Name -> Expr
| app : Expr -> Expr -> Expr
| lam : Name -> Expr -> Expr.

Definition expr_eq_dec : dec_type Expr. decide equality. Defined.
Hint Immediate expr_eq_dec.

Section Data.
Variables Addr Time : Type.
Variable addr_eq_dec : dec_type Addr.
Variable time_eq_dec : dec_type Time.

Definition Env := list (Name * Addr).
Inductive storeable := s_closure : Name -> Expr -> Env -> storeable.
Definition AbsVal := set storeable.
Inductive val :=
  | closure : Name -> Expr -> Env -> val
  | adelay : Addr -> val
  | amany : AbsVal -> val.

Definition Store := list (Addr * AbsVal).
Inductive Frame :=
  | ar : Expr -> Env -> Frame
  | fn : val -> Frame.

Definition Kont : Type := list Frame.
Inductive Shell (P : Type) :=
  shell : P -> Kont -> Time -> Shell P.
Inductive CES_point :=
  | ev : Expr -> Env -> Store -> CES_point
  | co : val -> Store -> CES_point
  | ap : Name -> Expr -> Env -> (* Closure *)
         val -> (* Argument *)
         Store -> CES_point.
Definition CESK := Shell CES_point.

Hint Immediate addr_eq_dec time_eq_dec.
Definition env_eq_dec : dec_type Env. apply list_eq_dec; decide equality. Defined.
Hint Immediate env_eq_dec.
Definition storeable_eq_dec : dec_type storeable. decide equality. Defined.
Hint Immediate storeable_eq_dec.
Definition absval_eq_dec : dec_type AbsVal. apply list_eq_dec; auto. Defined.
Hint Immediate absval_eq_dec.
Definition val_eq_dec : dec_type val. decide equality. Defined.
Hint Immediate val_eq_dec.
Definition store_eq_dec : dec_type Store. apply list_eq_dec; decide equality. Defined.
Hint Immediate store_eq_dec.
Definition frame_eq_dec : dec_type Frame. decide equality. Defined.
Hint Immediate frame_eq_dec.
Definition kont_eq_dec : dec_type Kont. apply list_eq_dec,frame_eq_dec. Defined.
Hint Immediate kont_eq_dec.
Hint Constructors Shell.

Definition store_of (p : CES_point) : Store :=
  match p with
      ev _ _ σ => σ
    | co _ σ => σ
    | ap _ _ _ _ σ => σ
  end.
Hint Unfold Kont CESK store_of.

Definition ces_point_eq_dec : dec_type CES_point. decide equality. Defined.
Hint Immediate ces_point_eq_dec.
Definition cesk_eq_dec : dec_type CESK. decide equality. Defined.
Hint Immediate cesk_eq_dec.

Definition in_aval := @In storeable.

Inductive in_force (σ : Store) : forall (s : storeable) (v : val), Prop :=
| forced : `{in_force σ (s_closure x e ρ) (closure x e ρ)}
| do_force : `{MapsTo σ a vs -> in_aval s vs -> in_force σ s (adelay a)}
| many_force : `{set_In s vs -> in_force σ s (amany vs)}.

Definition extend_ρ := extend_map name_eq_dec (B := Addr).

Definition lookup_ρ := lookup_map name_eq_dec (B := Addr).
Definition lookup_σ := lookup_map addr_eq_dec (B := AbsVal).

Definition force (σ : Store) (v:val) : AbsVal :=
  match v with
      | adelay a => match lookup_σ a σ with
                        None => nil
                      | Some vs => vs
                    end
      | amany vs => vs
      | closure x e ρ => singleton storeable_eq_dec (s_closure x e ρ)
  end.

Lemma in_force_In_force : forall σ v s, in_force σ s v <-> set_In s (force σ v).
Proof.
intros; split; intro H.
inversion H as [|? ? ? Hmap|s_ Hmany]; simpl;
[intuition
|rewrite lookup_mapsto in Hmap; unfold lookup_σ; rewrite Hmap; auto
|subst; auto].
destruct v as [x e ρ | a |vs];
simpl in H;[inversion H; [subst|contradiction]; constructor
           |case_eq (lookup_σ a σ);[intros ss Hsseq; rewrite Hsseq in H; unfold lookup_σ in Hsseq; rewrite <- lookup_mapsto in Hsseq; apply do_force with (vs := ss); auto|intro bad; rewrite bad in H; inversion H]
           |constructor; auto].
Qed.

Definition absval_join (vs vs' : AbsVal) :=
  set_union storeable_eq_dec vs vs'.

Definition σ_combine := (fun σ_orig vs v => (absval_join vs (force σ_orig v))).
Definition σ_join (σ : Store) (a : Addr) (v : val) : Store :=
  list_join addr_eq_dec σ_combine force σ a v σ.

Lemma σ_combine_extensive : forall (σ : Store) (vs : AbsVal)
                                   (v : val)
                                   (s : storeable)
                                   (Hin : set_In s vs),
                              set_In s (σ_combine σ vs v).
Proof.
  intros; unfold σ_combine;
  destruct v; simpl; solve [apply set_add_intro1; auto
                           |apply set_union_intro1; auto].
Qed.

Lemma σ_join_ordering : forall σ a v, MappingLE σ (σ_join σ a v).
Proof.
intros; apply (list_join_ordering addr_eq_dec σ_combine force σ_combine_extensive).
Qed.

(* needs to be proof-relevant for an always-correct replacetail *)
Inductive KontTail : Kont -> Kont -> Prop :=
| same_tail : `{KontTail κ κ}
| push_tail : `{KontTail κ κ' -> KontTail κ (φ :: κ')}.
Hint Constructors KontTail.

Fixpoint kont_tailp (κ κ' : Kont) : bool :=
  match (kont_eq_dec κ κ') with
      | left eqprf => true
      | right neqprf => match κ' with
                            nil => false
                          | φ :: κ' => kont_tailp κ κ'
                        end
  end.

Lemma kont_tailp_correct1 : forall κ κ',
                             kont_tailp κ κ' = true -> KontTail κ κ'.
Proof.
  induction κ'; simpl;
  [destruct (kont_eq_dec κ nil); intro H; subst; try solve [auto
                                                           |inversion H; contradiction]
  |destruct (kont_eq_dec κ (a :: κ')) as [Heq|Hneq]; intro H; subst; auto;
   apply IHκ' in H]; auto.
Qed.

Lemma kont_tailp_correct2 : forall κ κ',
                              KontTail κ κ' -> kont_tailp κ κ' = true.
Proof.
  induction κ'; simpl;
  [destruct (kont_eq_dec κ nil); intro H; subst; try solve [auto
                                                           |inversion H; contradiction]
  |destruct (kont_eq_dec κ (a :: κ')) as [Heq|Hneq]; intro H; subst; try solve [constructor];
   apply IHκ'; inverts H; [contradict Hneq|]; auto].
Qed.

Lemma kont_tail_nil : `{KontTail nil κ}.
Proof. induction κ as [|φ κ_ IH]; constructor; auto. Qed.

Lemma kont_tail_cons : forall φ κ κ' (H : KontTail (φ::κ) κ'), KontTail κ κ'.
Proof.
  induction κ' as [|φ_ κ_ IH]; intros; inverts H.
  apply push_tail; constructor.
  apply push_tail,IH; auto.
Qed.

Lemma kont_tail_app : forall κ κ' κ'' (H : KontTail (κ ++ κ') κ''), KontTail κ' κ''.
Proof.
  induction κ as [|φ κ_ IH]; intros;
  simpl in H; auto.
  apply kont_tail_cons in H; apply IH; auto.
Qed.

Section StandardSemantics.
Variable alloc : CES_point -> Addr.
Variable tick : CES_point -> Time.
Variable time0 : Time.
Definition inject_cesk (e : Expr) := shell (ev e nil nil) nil time0.

(* Proof relevant or not? *)
Inductive red_cesk : CESK -> CESK -> Prop :=
  ev_var : `{let p := (ev (var x) ρ σ) in
             MapsTo ρ x a ->
             red_cesk (shell p κ t) (shell (co (adelay a) σ) κ (tick p))}
| ev_app : `{let p := (ev (app e0 e1) ρ σ) in
             red_cesk (shell p κ t) (shell (ev e0 ρ σ) ((ar e1 ρ)::κ) (tick p))}
| ev_lam : `{let p := (ev (lam x e) ρ σ) in
             red_cesk (shell p κ t) (shell (co (closure x e ρ) σ) κ (tick p))}
| co_ar : `{let p := (co v σ) in
            red_cesk (shell p ((ar e ρ)::κ) t) (shell (ev e ρ σ) ((fn v)::κ) (tick p))}
| co_fn : `{let p := (co v σ) in
            in_force σ (s_closure x e ρ) fnv ->
            red_cesk (shell p ((fn fnv)::κ) t) (shell (ap x e ρ v σ) κ (tick p))}
| do_ap : `{let p := (ap x e ρ v σ) in
            let a := alloc p in
            let ρ' := extend_ρ x a ρ in
            let σ' := σ_join σ a v in
            red_cesk (shell p κ t) (shell (ev e ρ' σ') κ (tick p))}.
Inductive PR_red_cesk : CESK -> CESK -> Type :=
  pr_ev_var : `{let p := (ev (var x) ρ σ) in
             MapsTo ρ x a ->
             PR_red_cesk (shell p κ t) (shell (co (adelay a) σ) κ (tick p))}
| pr_ev_app : `{let p := (ev (app e0 e1) ρ σ) in
             PR_red_cesk (shell p κ t) (shell (ev e0 ρ σ) ((ar e1 ρ)::κ) (tick p))}
| pr_ev_lam : `{let p := (ev (lam x e) ρ σ) in
             PR_red_cesk (shell p κ t) (shell (co (closure x e ρ) σ) κ (tick p))}
| pr_co_ar : `{let p := (co v σ) in
            PR_red_cesk (shell p ((ar e ρ)::κ) t) (shell (ev e ρ σ) ((fn v)::κ) (tick p))}
| pr_co_fn : `{let p := (co v σ) in
            in_force σ (s_closure x e ρ) fnv ->
            PR_red_cesk (shell p ((fn fnv)::κ) t) (shell (ap x e ρ v σ) κ (tick p))}
| pr_do_ap : `{let p := (ap x e ρ v σ) in
            let a := alloc p in
            let ρ' := extend_ρ x a ρ in
            let σ' := σ_join σ a v in
            PR_red_cesk (shell p κ t) (shell (ev e ρ' σ') κ (tick p))}.

Definition fresh_ρ_inv (σ : Store) (ρ : Env) : Prop :=
  forall x a, MapsTo ρ x a -> InDom σ a.

Lemma fresh_ρ_inv_join : forall σ ρ a v, fresh_ρ_inv σ ρ -> fresh_ρ_inv (σ_join σ a v) ρ.
Proof.
  intros σ ρ a v freshρ x a' Hmap; apply InDom_join2'; apply freshρ with (x := x); auto.
Qed.

Definition fresh_storeable_inv (σ : Store) (s : storeable) :=
  match s with
      s_closure x e ρ => fresh_ρ_inv σ ρ
  end.

Lemma fresh_storeable_inv_join : forall σ a s v, fresh_storeable_inv σ s -> fresh_storeable_inv (σ_join σ a v) s.
Proof.
  intros; destruct s; apply fresh_ρ_inv_join; auto.
Qed.

Definition fresh_σ_inv (σ : Store) : Prop :=
  forall a vs, MapsTo σ a vs -> exists s, vs = (singleton storeable_eq_dec s) /\ fresh_storeable_inv σ s.

Definition fresh_val_inv (σ : Store) (v : val) : Prop :=
  match v with
      closure x e ρ => fresh_ρ_inv σ ρ
    | (adelay a) => InDom σ a
    | (amany vs) => exists s, vs = (singleton storeable_eq_dec s) /\ fresh_storeable_inv σ s
  end.

Lemma fresh_val_inv_join : forall σ a v v', fresh_val_inv σ v -> fresh_val_inv (σ_join σ a v') v.
Proof.
  intros; destruct v; simpl;
  [apply fresh_ρ_inv_join
  |apply InDom_join2'
  |destruct H as [s [Heq freshs]];
   exists s; split; [|apply fresh_storeable_inv_join]];auto.
Qed.

Definition fresh_φ_inv (σ : Store) (φ : Frame) : Prop :=
  match φ with
      | ar e ρ => fresh_ρ_inv σ ρ
      | fn v => fresh_val_inv σ v
  end.

Inductive fresh_point_inv : CES_point -> Prop :=
  fresh_ev : `{fresh_σ_inv σ -> fresh_ρ_inv σ ρ -> fresh_point_inv (ev e ρ σ)}
| fresh_co : `{fresh_val_inv σ v -> fresh_σ_inv σ -> fresh_point_inv (co v σ)}
| fresh_ap : `{fresh_val_inv σ v -> fresh_ρ_inv σ ρ -> fresh_σ_inv σ -> fresh_point_inv (ap x e ρ v σ)}.
Hint Constructors fresh_point_inv.
Hint Unfold fresh_φ_inv fresh_val_inv fresh_ρ_inv fresh_σ_inv. 
(* what do we know of states when the allocation function gives fresh allocations? *)
Definition fresh_inv (s : CESK) : Prop :=
  match s with
      shell p κ t => Forall (fresh_φ_inv (store_of p)) κ /\ fresh_point_inv p
  end.

Definition alloc_fresh (alloc : CES_point -> Addr) :=
  forall p, Unmapped (store_of p) (alloc p).

(* if not stuck, then all steps are the same *)
Definition deterministic {S} (R : S -> S -> Prop) : Prop :=
  forall s s', R s s' -> forall s'', R s s'' -> s' = s''.

Theorem CESK_fresh_inv : forall s s' (fresh : (alloc_fresh alloc))
                                (Hinv : fresh_inv s)
                                (Hstep : red_cesk s s'), fresh_inv s'.
Proof.
  Ltac subgoal Hall :=
    repeat split; 
    try (rewrite Forall_forall);
    try solve [auto
              |intros φ Hin; ((inversion Hin; [subst; simpl; auto|]) || idtac); apply Hall; (right || idtac); auto].
  intros; inversion Hstep as [x ρ σ a κ t p Hmap
                        |e0 e1 ρ σ κ t p Hpeq
                        |x elam ρ σ κ t p Hpeq Hs'eq
                        |v σ e ρ κ t p Hpeq Hs'eq
                        |v σ x e ρ fnv κ t p Hin_force Hpeq Hs'eq
                        |x e ρ v σ κ t p a ρ' σ' Hpeq Hs'eq]; 
  subst; subst p; destruct Hinv as [Hall Hfpoint];
  inversion_clear Hfpoint as [? ? ? freshσ freshρ|? ? freshv freshσ|? ? ? ? ? freshv freshρ freshσ];
  rewrite Forall_forall in Hall; subst;
  try solve [subgoal Hall].

  split; [subgoal Hall
         |constructor; [apply freshρ with (x := x)|]; auto].

  split; [subgoal Hall
         |constructor; [|specialize (Hall (ar e ρ) (or_introl (eq_refl _))); simpl in Hall]; assumption].

  split; [subgoal Hall
         |constructor;
    [|specialize (Hall (fn fnv) (or_introl (eq_refl _)));
       inversion Hin_force as [|a vs ? Hmap Hin|]; subst; simpl in Hall;
       [|apply freshσ in Hmap; destruct Hmap as [s [Heq freshs]]; subst;
         inversion Hin as [|bad]; [subst|inversion bad]; auto
        |destruct Hall as [s [Heq freshs]];
          inversion Hin_force as [| |? ? Hin]; subst; inversion Hin as [|bad]; [subst|inversion bad]]|]; auto].
  
  assert (subgoal' : fresh_σ_inv σ') by
      (intros a' vs Hmap;
  destruct (addr_eq_dec a a') as [Heq|Hneq];
    [(* eq case tricky *)
      assert (Hmap' : MapsTo σ' a' (force σ v))
      by (subst a'; apply join_an_unmapped'; apply (fresh (ap x e ρ v σ)));
     assert (feq : vs = (force σ v)) by exact (MapsTo_same Hmap Hmap');
     destruct v as [x_ e_ ρ_ | a_ | vs_];
       [exists (s_closure x_ e_ ρ_); split; [|simpl; apply fresh_ρ_inv_join]; auto
              |apply (InDom_lookup addr_eq_dec) in freshv;
                destruct freshv as [vs' vs'eq];
                remember vs'eq as vs'eq_;
                clear Heqvs'eq_; rewrite <- lookup_mapsto in vs'eq;
                simpl in feq; unfold lookup_σ in feq; rewrite vs'eq_ in feq; subst;
                apply freshσ in vs'eq;
                destruct vs'eq as [s [seq freshs]];
                exists s; split; [|apply fresh_storeable_inv_join]; auto
              |destruct freshv as [s [seq freshs]];
                exists s; split; [subst σ' ρ'; subst; exact (MapsTo_same Hmap Hmap')|apply fresh_storeable_inv_join]; auto]
     |assert (Hmap' : MapsTo σ a' vs) by
         (apply (@non_join_untouched' _ _ _ addr_eq_dec σ_combine force σ σ a a' v vs); auto);
       apply freshσ in Hmap';
       destruct Hmap' as [s [seq freshs]]; exists s; split; [|apply fresh_storeable_inv_join]; auto]).

  split;
    [rewrite Forall_forall; intros φ Hin;
     destruct φ as [κe κρ | κv]; simpl;
     [apply fresh_ρ_inv_join
     |apply fresh_val_inv_join]; apply (Hall _ Hin); auto
    |constructor;
      [auto
      |intros x_ a_ Hmap;
        destruct (name_eq_dec x x_) as [Heq|Hneq];
        [subst x_; subst ρ'; unfold extend_ρ in Hmap; rewrite <- (@extend_map_MapsTo_eq _ _ name_eq_dec x a a_ ρ Hmap);
         apply InDom_join'
        |assert (Hmap' : MapsTo ρ x_ a_) by
            (apply (@extend_map_old _ _ name_eq_dec ρ x x_ a a_ Hneq); auto);
          apply InDom_join2'; apply freshρ in Hmap'; auto]]].
Qed.

Definition CESK_trace (e : Expr) := Trace (inject_cesk e) red_cesk.
Section NonStandardData.
Inductive Context := context : Expr -> Env -> Store -> Time -> Context.
Inductive Result := res: val -> Store -> Time -> Result.
Definition Results := set Result.

Inductive TrunKont :=
| mt : TrunKont
| kpush : Frame -> TrunKont -> TrunKont
| rt : Context -> TrunKont.

Definition TrunKonts := set TrunKont.
Definition Memo := list (Context * Results).
Definition KTable := list (Context * TrunKonts).

Definition context_eq_dec : dec_type Context. decide equality. Defined.
Hint Immediate context_eq_dec.
Definition result_eq_dec : dec_type Result. decide equality. Defined.
Hint Immediate result_eq_dec.
Definition trunkont_eq_dec : dec_type TrunKont. decide equality. Defined.
Hint Immediate trunkont_eq_dec.

Inductive TrunKontTail : TrunKont -> TrunKont -> Prop :=
| same_ttail : `{TrunKontTail κ κ}
| push_ttail : `{TrunKontTail κ κ' -> TrunKontTail κ (kpush φ κ')}.
Hint Constructors TrunKontTail.
Lemma trunkont_tail_kpush : forall tκ φ tκ', TrunKontTail (kpush φ tκ) tκ' -> TrunKontTail tκ tκ'.
Proof.
  induction tκ'; intro H; inverts H; constructor; [|apply IHtκ']; auto.
Qed.

Definition memo_eq_dec : dec_type Memo. do 3 (decide equality). Defined.
Definition ktable_eq_dec : dec_type KTable. do 3 (decide equality). Defined.
Hint Immediate memo_eq_dec ktable_eq_dec.

Definition trunckonts_join (κs κs' : TrunKonts) := set_union trunkont_eq_dec κs κs'.
Definition lookup_M := lookup_map context_eq_dec (B := Results).
Definition lookup_Ξ := lookup_map context_eq_dec (B := TrunKonts).

Definition κs_join := (fun (_ : KTable) κs κ => (set_add trunkont_eq_dec κ κs)).
Definition κ_singleton := (fun (_ : KTable) κ => singleton trunkont_eq_dec κ).
Definition res_join := (fun (_ : Memo) rs r => (set_add result_eq_dec r rs)).

Lemma κs_join_extensive (_ : KTable) (b : TrunKonts) (tκ : TrunKont) : In tκ (set_add trunkont_eq_dec tκ b).
Proof. apply set_add_intro2; auto. Qed.
Hint Resolve κs_join_extensive.
(*
Lemma κs_join_extensive' (_ : KTable) (b : TrunKonts) (tκ : TrunKont) := (set_add_intro1 trunkont_eq_dec).
*)
Definition κ_singleton_extensive : forall (Ξ : KTable) (tκ : TrunKont), In tκ (κ_singleton Ξ tκ).
intros; apply κs_join_extensive; auto.
Defined.

Definition Ξ_join (Ξ : KTable) (ctx : Context) (κ : TrunKont) : KTable :=
  list_join context_eq_dec
            κs_join
            κ_singleton Ξ ctx κ Ξ.
Definition M_join (M : Memo) (ctx : Context) (r : Result) : Memo :=
  list_join context_eq_dec
            res_join
            (fun _ r => singleton result_eq_dec r) M ctx r M.

Fixpoint map_join {A B} (join1 : list (A * B) -> A -> B -> list (A * B)) (l l' : list (A * B)) :=
  match l with
      nil => l'
    | (a,b)::l'' => join1 (map_join join1 l'' l') a b
  end.
Definition mjoiner {A B} (Aeq_dec : dec_type A) (Beq_dec : dec_type B) (l : list (A * set B)) a bs :=
  list_join Aeq_dec
            (fun _ bs' bs => set_union Beq_dec bs' bs)
            (fun _ bs => bs)
            l a bs l.
Definition Ξs_join := map_join (mjoiner context_eq_dec trunkont_eq_dec).
Definition Ms_join := map_join (mjoiner context_eq_dec result_eq_dec).
Lemma map_join_ordering1 : forall A B (Aeq_dec : dec_type A) (Beq_dec : dec_type B)
                                 (l l' : list (A * set B)),
                            MappingLE l (map_join (mjoiner Aeq_dec Beq_dec) l l').
Proof.
Admitted.

Lemma map_join_ordering2 : forall A B (Aeq_dec : dec_type A) (Beq_dec : dec_type B)
                                 (l l' : list (A * set B)),
                            MappingLE l (map_join (mjoiner Aeq_dec Beq_dec) l' l).
Proof.
Admitted.

Definition in_ctxs (Ξ : KTable) (ctx : Context) (κ : TrunKont) : Prop :=
  in_list_list Ξ ctx κ.
Definition in_ctxs_tail (Ξ : KTable) (ctx : Context) (tκ : TrunKont) : Prop :=
  exists tκ', in_list_list Ξ ctx tκ' /\ TrunKontTail tκ tκ'.

Definition in_memos (M : Memo) (ctx : Context) (r : Result) : Prop :=
  in_list_list M ctx r.

Inductive WShell (P : Type) :=
  wshell : P -> TrunKont -> Time -> WShell P.

Definition WCESKMΞ := WShell CES_point.
Inductive CESKMΞ :=
  | widemk : WCESKMΞ -> Memo -> KTable -> CESKMΞ.

Definition wceskmξ_eq_dec : dec_type WCESKMΞ. decide equality. Defined.
Hint Immediate wceskmξ_eq_dec.
Definition ceskmξ_eq_dec : dec_type CESKMΞ. decide equality. Defined.
Hint Immediate ceskmξ_eq_dec.
Section NonStandardSemantics.

Definition inject_wceskmk (e : Expr) : WCESKMΞ := (wshell (ev e nil nil) mt time0).
Definition inject_ceskmk (e : Expr) : CESKMΞ := widemk (inject_wceskmk e) nil nil.

(* Proof relevant or not? *)
Inductive red_ceskmk : CESKMΞ -> CESKMΞ -> Prop :=
  evmk_var : forall x ρ σ a tκ t M Ξ,
               let p := (ev (var x) ρ σ) in
               MapsTo ρ x a ->
               red_ceskmk (widemk (wshell p tκ t) M Ξ)
                          (widemk (wshell (co (adelay a) σ) tκ (tick p)) M Ξ)
| evmk_app : forall e0 e1 ρ σ tκ t M Ξ,
               let p := (ev (app e0 e1) ρ σ) in
               red_ceskmk (widemk (wshell p tκ t) M Ξ)
                          (widemk (wshell (ev e0 ρ σ) (kpush (ar e1 ρ) tκ) (tick p)) M Ξ)
| evmk_lam : forall x e ρ σ tκ t M Ξ,
               let p := (ev (lam x e) ρ σ) in
               red_ceskmk (widemk (wshell p tκ t) M Ξ)
                          (widemk (wshell (co (closure x e ρ) σ) tκ (tick p)) M Ξ)
| comk_ar : forall v σ e ρ tκ t M Ξ,
              let p := (co v σ) in
              red_ceskmk (widemk (wshell p (kpush (ar e ρ) tκ) t) M Ξ)
                         (widemk (wshell (ev e ρ σ) (kpush (fn v) tκ) (tick p)) M Ξ)
| comk_fn : forall v σ x e ρ fnv tκ t M Ξ,
              let p := (co v σ) in
              in_force σ (s_closure x e ρ) fnv ->
              red_ceskmk (widemk (wshell p (kpush (fn fnv) tκ) t) M Ξ)
                         (widemk (wshell (ap x e ρ v σ) tκ (tick p)) M Ξ)
| do_apmk : forall x e ρ v σ tκ t M Ξ,
              let p := (ap x e ρ v σ) in
              let a := alloc p in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let t' := (tick p) in
              let ctx := (context e ρ' σ' t') in
              Unmapped M ctx ->
              red_ceskmk (widemk (wshell p tκ t) M Ξ)
                         (widemk (wshell (ev e ρ' σ') (rt ctx) t') M (Ξ_join Ξ ctx tκ))
| do_memo : forall x e ρ v σ tκ t M Ξ vm σm tm,
              let p := (ap x e ρ v σ) in
              let a := alloc p in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let ctx := (context e ρ' σ' (tick p)) in
              in_memos M ctx (res vm σm tm) ->
              red_ceskmk (widemk (wshell p tκ t) M Ξ)
                         (widemk (wshell (co vm σm) tκ tm) M (Ξ_join Ξ ctx tκ)) (* XXX: tick? *)
| do_rt : forall v σ ctx tκ M Ξ,
            let t' := (tick (co v σ)) in
            let M' := M_join M ctx (res v σ t') in
            in_ctxs Ξ ctx tκ ->
            red_ceskmk (widemk (wshell (co v σ) (rt ctx) t') M Ξ)
                       (widemk (wshell (co v σ) tκ t') M' Ξ). (* XXX: tick? *)
Inductive PR_red_ceskmk : CESKMΞ -> CESKMΞ -> Type :=
  pr_evmk_var : forall x ρ σ a tκ t M Ξ,
               let p := (ev (var x) ρ σ) in
               MapsTo ρ x a ->
               PR_red_ceskmk (widemk (wshell p tκ t) M Ξ)
                          (widemk (wshell (co (adelay a) σ) tκ (tick p)) M Ξ)
| pr_evmk_app : forall e0 e1 ρ σ tκ t M Ξ,
               let p := (ev (app e0 e1) ρ σ) in
               PR_red_ceskmk (widemk (wshell p tκ t) M Ξ)
                          (widemk (wshell (ev e0 ρ σ) (kpush (ar e1 ρ) tκ) (tick p)) M Ξ)
| pr_evmk_lam : forall x e ρ σ tκ t M Ξ,
               let p := (ev (lam x e) ρ σ) in
               PR_red_ceskmk (widemk (wshell p tκ t) M Ξ)
                          (widemk (wshell (co (closure x e ρ) σ) tκ (tick p)) M Ξ)
| pr_comk_ar : forall v σ e ρ tκ t M Ξ,
              let p := (co v σ) in
              PR_red_ceskmk (widemk (wshell p (kpush (ar e ρ) tκ) t) M Ξ)
                         (widemk (wshell (ev e ρ σ) (kpush (fn v) tκ) (tick p)) M Ξ)
| pr_comk_fn : forall v σ x e ρ fnv tκ t M Ξ,
              let p := (co v σ) in
              in_force σ (s_closure x e ρ) fnv ->
              PR_red_ceskmk (widemk (wshell p (kpush (fn fnv) tκ) t) M Ξ)
                         (widemk (wshell (ap x e ρ v σ) tκ (tick p)) M Ξ)
| pr_do_apmk : forall x e ρ v σ tκ t M Ξ,
              let p := (ap x e ρ v σ) in
              let a := alloc p in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let t' := (tick p) in
              let ctx := (context e ρ' σ' t') in
              Unmapped M ctx ->
              PR_red_ceskmk (widemk (wshell p tκ t) M Ξ)
                         (widemk (wshell (ev e ρ' σ') (rt ctx) t') M (Ξ_join Ξ ctx tκ))
| pr_do_memo : forall x e ρ v σ tκ t M Ξ vm σm tm,
              let p := (ap x e ρ v σ) in
              let a := alloc p in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let ctx := (context e ρ' σ' (tick p)) in
              in_memos M ctx (res vm σm tm) ->
              PR_red_ceskmk (widemk (wshell p tκ t) M Ξ)
                         (widemk (wshell (co vm σm) tκ tm) M (Ξ_join Ξ ctx tκ)) (* XXX: tick? *)
| pr_do_rt : forall v σ ctx tκ M Ξ,
            let t' := (tick (co v σ)) in
            let M' := M_join M ctx (res v σ t') in
            in_ctxs Ξ ctx tκ ->
            PR_red_ceskmk (widemk (wshell (co v σ) (rt ctx) t') M Ξ)
                       (widemk (wshell (co v σ) tκ t') M' Ξ). (* XXX: tick? *)

Definition step_all (s : CESKMΞ) : set CESKMΞ :=
  match s with
    | widemk (wshell (ev (var x) ρ σ) tκ t) M Ξ  =>
      match (lookup_ρ x ρ) with
       | None => empty_set _
       | Some a => singleton ceskmξ_eq_dec (widemk (wshell (co (adelay a) σ) tκ (tick (ev (var x) ρ σ))) M Ξ)
      end
    | widemk (wshell (ev (app e0 e1) ρ σ) tκ t) M Ξ =>
      singleton ceskmξ_eq_dec (widemk (wshell (ev e0 ρ σ) (kpush (ar e1 ρ) tκ) (tick (ev (app e0 e1) ρ σ))) M Ξ)
    | widemk (wshell (ev (lam x e) ρ σ) tκ t) M Ξ =>
      singleton ceskmξ_eq_dec (widemk (wshell (co (closure x e ρ) σ) tκ (tick (ev (lam x e) ρ σ))) M Ξ)
    | widemk (wshell (co v σ) (kpush (ar e ρ) tκ) t) M Ξ =>
              singleton ceskmξ_eq_dec (widemk (wshell (ev e ρ σ) (kpush (fn v) tκ) (tick (co v σ))) M Ξ)
    | widemk (wshell (co v σ) (kpush (fn fnv) tκ) t) M Ξ =>
      (* Append forces *)
      fold_right (fun fv acc =>
                    match fv with
                        s_closure x e ρ => set_add ceskmξ_eq_dec
                                                 (widemk (wshell (ap x e ρ v σ) tκ (tick (co v σ))) M Ξ)
                                                 acc
                 end)
                 (empty_set _)
                 (force σ fnv)
    | widemk (wshell (ap x e ρ v σ) tκ t) M Ξ =>
      let a := alloc (ap x e ρ v σ) in
      let ρ' := extend_ρ x a ρ in
      let σ' := σ_join σ a v in
      let t' := (tick (ap x e ρ v σ)) in
      let ctx := (context e ρ' σ' t') in
      let Ξ' := Ξ_join Ξ ctx tκ in
      (* both call and use memo table *)
      match (lookup_M ctx M) with
            | None => singleton ceskmξ_eq_dec (widemk (wshell (ev e ρ' σ') (rt ctx) t') M Ξ')
            | Some rs =>
              fold_right (fun r acc =>
                            match r with
                                res vm σm tm => set_add ceskmξ_eq_dec
                                                     (widemk (wshell (co vm σm) tκ tm) M Ξ')
                                                     acc
                            end)
                         (empty_set _)
                         rs
      end
    | widemk (wshell (co v σ) (rt ctx) t) M Ξ =>
      let t' := (tick (co v σ)) in
      let M' := M_join M ctx (res v σ t') in
      match (lookup_Ξ ctx Ξ) with
          | None => (empty_set _)
          | Some tκs =>
            fold_right (fun tκ acc =>
                          set_add ceskmξ_eq_dec
                                  (widemk (wshell (co v σ) tκ t') M' Ξ)
                                  acc)
                       (empty_set _) tκs
      end
    | widemk (wshell (co v σ) mt t) M Ξ => empty_set _
  end.

Inductive Wide_step :=
  wide_step : set WCESKMΞ -> Memo -> KTable -> Wide_step.

Inductive System :=
  system : set WCESKMΞ -> set WCESKMΞ -> Memo -> KTable -> System.


Fixpoint smusher (S : set WCESKMΞ) (ss : set CESKMΞ) (nexts : set WCESKMΞ) (M : Memo) (Ξ : KTable) :=
  match ss with
      nil => wide_step (filter (fun s => if In_dec wceskmξ_eq_dec s S then false else true) nexts) M Ξ
    | (widemk s M' Ξ')::ss' => smusher S ss' (set_add wceskmξ_eq_dec s nexts)
                                     (Ms_join M' M)
                                     (Ξs_join Ξ' Ξ)
  end.

Definition smush_steps (s : WCESKMΞ) (M: Memo) (Ξ: KTable) (S : set WCESKMΞ) : Wide_step :=
  smusher S (step_all (widemk s M Ξ)) nil nil nil.

Inductive ForallT {A} (P:A->Type) : list A -> Type :=
 | ForallT_nil : ForallT P nil
 | ForallT_cons : forall x l, P x -> ForallT P l -> ForallT P (x::l).
Hint Constructors ForallT.

Theorem PR_finite_steps1 : forall s, forall s', red_ceskmk s s' -> InT s' (step_all s).
Proof.
Admitted.

Theorem PR_finite_steps2 : forall s, forall s', InT s' (step_all s) -> red_ceskmk s s'.
Proof.
Admitted.

Theorem finite_steps : forall s, forall s', red_ceskmk s s' <-> In s' (step_all s).
Proof.
Admitted.

(* Proof relevant or not? *)
Inductive Wide_CESKMΞ : System -> System -> Prop :=
  | big_step : forall s M Ξ Seen F ss M' Ξ',
                 (wide_step ss M' Ξ') = (smush_steps s M Ξ Seen) ->
                 Wide_CESKMΞ (**) (system Seen (s::F) M Ξ) (**)
                                  (system
                                  (set_union wceskmξ_eq_dec ss (set_add wceskmξ_eq_dec s Seen))
                                  (set_union wceskmξ_eq_dec F ss)
                                  M' Ξ').

Definition inject_wide_ceskmk (e : Expr) := (system [(inject_wceskmk e)] [(inject_wceskmk e)] nil nil).
Definition CESKMΞ_trace (e : Expr) :=
  Trace (inject_ceskmk e) red_ceskmk.
Definition WCESKMΞ_trace (e : Expr) :=
  Trace (system [(inject_wceskmk e)] [(inject_wceskmk e)] nil nil) Wide_CESKMΞ.

Inductive StackUnroll (Ξ : KTable) : Kont -> TrunKont -> Prop :=
  unroll_mt : `{StackUnroll Ξ nil mt}
| unroll_push : forall κ tκ φ, StackUnroll Ξ κ tκ -> StackUnroll Ξ (φ :: κ) (kpush φ tκ)
| unroll_rt : forall ctx tκ κ,
                StackUnroll Ξ κ tκ ->
                in_ctxs Ξ ctx tκ ->
                StackUnroll Ξ κ (rt ctx).

Ltac textend_map := apply in_list_join2;solve [
                             intros; apply set_add_intro1; auto
                            | intros; apply set_add_intro2; auto
                            | auto].

Theorem unroll_with_extension : forall
        (Ξ : KTable) (ctx : Context) (κ : Kont) (tκ tκ' : TrunKont)
        (hyp : StackUnroll Ξ κ tκ), StackUnroll (Ξ_join Ξ ctx tκ') κ tκ.
Proof.
  intros Ξ ctx κ tκ tκ' hyp; induction hyp;[
    constructor
   |constructor; assumption
   |apply unroll_rt with (tκ := tκ); [|textend_map]; auto].
Qed.

Ltac inject_push :=
  match goal with [H: kpush ?φ0 ?tκ0 = kpush ?φ1 ?tκ1 |- _] => injection H; intros;
                                                               try (subst φ1 tκ1); try subst end.

Inductive Unroll_inv : KTable -> TrunKont -> Prop :=
  unroll_inv : forall Ξ κ tκ,
                 StackUnroll Ξ κ tκ ->
                 (forall ctx tκ', in_ctxs Ξ ctx tκ' -> exists κ', StackUnroll Ξ κ' tκ') ->
                 Unroll_inv Ξ tκ.

Lemma unrolling_inv : forall p p' tκ tκ' t t' M M' Ξ Ξ'
                             (Hstep : red_ceskmk (widemk (wshell p tκ t) M Ξ)
                                                 (widemk (wshell p' tκ' t') M' Ξ'))
                             (Hinv : Unroll_inv Ξ tκ),
                             Unroll_inv Ξ' tκ'.
Proof with auto.
  intros; inversion Hstep as [x ρ σ a tκs ts Ms Ξs ps Hmap Hpeq Hs'eq |
                              e0 e1 ρ σ tκs ts Ms Ξs ps Hpeq |
                              x e ρ σ tκs ts Ms Ξs ps Hpeq Hs'eq |
                              v σ e ρ tκs ts Ms Ξs ps Hpeq Hs'eq |
                              v σ x e ρ fnv tκs ts Ms Ξs ps Hin_force Hpeq Hs'eq |
                              x e ρ v σ tκs ts Ms Ξs ps a ρ' σ' ts' ctx Hunmapped Hpeq Hs'eq |
                              x e ρ v σ tκs ts Ms Ξs vm σm tm ps a ρ' σ' ctx Hinmemos Hpeq Hs'eq |
                              v σ ctx tκs Ms Ξs t's M's Hin_ctxs Hpeq Hs'eq];
  inversion Hinv as [? κ ? Hunroll HΞ]; subst;
  try solve [apply unroll_inv with (κ := κ); auto
            |apply unroll_inv with (κ := ((ar e1 ρ)::κ)); [constructor|];auto
            |inversion Hunroll as [|κκ|]; subst;
             solve [discriminate | apply unroll_inv with (κ := ((fn v)::κκ)); [constructor|];auto]
            |inversion Hunroll as [|κκ|]; subst;
             solve [discriminate | apply unroll_inv with (κ := ((fn fnv)::κκ)); [constructor|];auto]].
  (* fn -> ap *)
  inversion Hunroll as [|κκ|]; apply unroll_inv with (κ := κκ); auto.
  (* unmemoized ap *)
  apply unroll_inv with (κ := κ);[
  apply unroll_rt with (tκ := tκ);
      [apply unroll_with_extension
      |apply in_list_join; solve [intros; apply set_add_intro2; auto | auto]]; auto
  |].
  intros ctx_ tκ_ Hin_;
  destruct (in_list_join_set_split context_eq_dec trunkont_eq_dec)
       with (l := Ξ) (l' := Ξ) (a := ctx) (a' := ctx_) (c := tκ) (c' := tκ_)
    as [[? ?]|S1]; auto;
  [exists κ; apply unroll_with_extension; subst; intuition (subst; auto)
  |destruct (HΞ ctx_ tκ_) as [κ' ?]; auto;
    unfold in_ctxs; subst; exists κ'; apply unroll_with_extension; auto].
  (* memoized ap *)
  subst;
  apply unroll_inv with (κ := κ);
    [apply unroll_with_extension
    |intros ctx_ tκ_ Hin_;
      destruct (in_list_join_set_split context_eq_dec trunkont_eq_dec)
       with (l := Ξ) (l' := Ξ) (a := ctx) (a' := ctx_) (c := tκ') (c' := tκ_)
       as [[? ?]|S1]; auto;[intuition; subst tκ_; exists κ; apply unroll_with_extension
       |destruct (HΞ ctx_ tκ_) as [κ' ?]; solve [exists κ'; apply unroll_with_extension; auto
                                                       |auto]]]; auto.
  (* return and memoize *)
  subst;
  destruct (HΞ ctx tκ') as [κ' ?]; auto.
  apply unroll_inv with (κ := κ'); auto.
Qed.

Section StackIrrelevance.
Inductive hastail (κ : Kont) : list CESK -> Prop :=
  Nil_tail : hastail κ nil
| Cons_tail : forall π p κ' t, hastail κ π -> KontTail κ κ' ->
                           hastail κ ((shell p κ' t) :: π).
Hint Constructors hastail.

(* Tail_replacement κorig κtail κreplacement κresult *)
Inductive Tail_replacement : Kont -> Kont -> Kont -> Kont -> Prop :=
| tail_replacement : `{Tail_replacement κ κ κ'' κ''}
| push_replacement : `{Tail_replacement κ κ' κ'' κ''' ->
                       Tail_replacement (φ::κ) κ' κ'' (φ::κ''')}.

Lemma good_tailrep : forall κorig κtail κrep,
                       Tail_replacement (κorig++κtail) κtail κrep (κorig ++ κrep).
Proof.
  induction κorig as [|φ κ_ IH]; intros;simpl; constructor; apply IH.
Qed.

Fixpoint replacetail_kont (κ κ' κ'' : Kont) : option Kont :=
  match (kont_eq_dec κ κ') with
  | left _ => Some κ''
  | right _ => match κ with
               | nil => None
               | φ::κ_ => match replacetail_kont κ_ κ' κ'' with
                            | None => None
                            | Some κ''_ => Some (φ::κ''_)
                          end
               end
  end.

Definition replacetail_kont_good : forall κ κ' κ'' (Htail : KontTail κ' κ),
                                     exists κ''', replacetail_kont κ κ' κ'' = Some κ'''.
induction κ as [|φ κ_ IH]; intros;
[exists κ''; inverts Htail; simpl; reflexivity
|inversion Htail as [|? ? ? Htail']; subst;
  [(* tail base case: κ = κ' *) exists κ''; unfold replacetail_kont; split_refl kont_eq_dec (φ :: κ_)
  |destruct (kont_eq_dec (φ :: κ_) κ') as [Heq | Hneq];
    [subst; exists κ''; unfold replacetail_kont; split_refl kont_eq_dec (φ :: κ_)
    |set (mumble := IH κ' κ'' Htail');
      inversion mumble as [κ''' Heq]; subst;
      exists (φ :: κ'''); unfold replacetail_kont; split_refl2 kont_eq_dec (φ :: κ_) κ'; fold replacetail_kont; rewrite Heq]; auto]].
Qed.

Definition replacetail_state (s : CESK) (κ' κ'' : Kont) :=
  match s with
      shell p κ t => match replacetail_kont κ κ' κ'' with
                         None => None
                       | Some κ_ => Some (shell p κ_ t)
                     end
  end.

Lemma replacetail_state_good : forall s κ' κ'' (Htail : match s with shell p κ t => KontTail κ' κ end),
                                 exists s', replacetail_state s κ' κ'' = Some s'.
Proof.
  intros; destruct s as [p κ t]; set (good := replacetail_kont_good κ'' Htail);
  inversion good as [κ''' Hgood]; subst;
  exists (shell p κ''' t);
  unfold replacetail_state; rewrite Hgood; auto.
Qed.

Fixpoint replacetail (π : list CESK) (κ' κ'' : Kont) : list (option CESK) :=
  match π with
      nil => nil
    | ς :: π' => (replacetail_state ς κ' κ'') :: (replacetail π' κ' κ'')
  end.

Theorem replacetail_good : forall (π : list CESK) (κ' κ'' : Kont) (Htail : hastail κ' π),
  exists (π' : list CESK), (replacetail π κ' κ'') = (map (@Some CESK) π').
Proof.
  induction π; intros.
  exists nil; simpl; auto.
  inversion Htail as [|? p κ_ t Htail' κtail]; subst.
  destruct (replacetail_state_good (shell p κ_ t) κ' κ'' κtail) as [s' Heq].
  destruct (IHπ κ' κ'' Htail') as [π' Heq'].
  exists (s' :: π'); simpl.
  unfold replacetail_state in Heq; rewrite Heq, Heq'; auto.
Qed.

Lemma no_circular_cons : forall A a (l : list A), l <> a :: l.
Proof.
  intros; intro bad;
  assert (H : length l = S (length l)) by (rewrite bad at 1; simpl; auto);
  contradict H; omega.
Qed.

Lemma no_circular_app : forall A (l l' : list A), length l > 0 -> l' <> l ++ l'.
Proof.
  intros; intro bad.
  assert (H' : length l' = (length l) + (length l')) by (rewrite bad at 1; rewrite app_length; reflexivity).
  contradict H; omega.
Qed.

Lemma no_longer_kont_tail : forall κ κmore, length κmore > 0 -> ~ KontTail (κmore ++ κ) κ.
Proof.
  induction κ.
  induction κmore; intros; [inversion H|intro bad; inversion bad].
  intros κmore H bad.
  apply IHκ with (κmore := κmore ++ [a]).
  rewrite app_length; omega.
  rewrite app_assoc_reverse; simpl.
  inversion bad as [bad0 bad1 bad2|bad0 bad1 bad2 bad3 bad4 bad5];
                             [symmetry in bad2; apply no_circular_app in bad2; [contradiction|]
                             |subst]; auto.
Qed.

Lemma no_conflicting_kont_tail : forall κ φ φ' (H : φ <> φ'), ~ KontTail (φ :: κ) (φ' :: κ).
Proof.
  induction κ; intros φ φ' H bad;
  inversion bad as [|? ? ? bad3];
  solve [contradiction|inversion bad3
         |subst;
           assert (goal : ~ KontTail ([φ] ++ (a :: κ)) (a :: κ)) by (apply no_longer_kont_tail; simpl; omega);
           simpl in goal; auto].
Qed.

Lemma no_longer_tail_replacement : forall κ κ' κmore,
                                      length κmore > 0 ->
                                      replacetail_kont κ (κmore ++ κ) κ' = None.
Proof.
  induction κ as [|φ κ_ IH].
  intros; simpl; rewrite app_nil_r; destruct κmore; [contradict H;simpl; omega|reflexivity].
  intros.
  unfold replacetail_kont.
  destruct (kont_eq_dec (φ :: κ_) (κmore ++ φ :: κ_)) as [bad|Hneq].
  apply no_circular_app in bad; [contradiction|auto].
  fold replacetail_kont.
  intros.
  assert (R : κmore ++ φ :: κ_ = κmore ++ [φ] ++ κ_) by (simpl; reflexivity).
  rewrite R.
  rewrite app_assoc with (m := [φ]).
  rewrite IH; [auto| rewrite app_length; omega].
Qed.

Lemma no_longer_tail_replacement2 : forall κ κ' φ, replacetail_kont κ (φ :: κ) κ' = None.
Proof.
  intros; assert (goalapp : replacetail_kont κ ([φ] ++ κ) κ' = None);
  [apply no_longer_tail_replacement; simpl;omega|simpl].
  simpl in goalapp; auto.
Qed.

Lemma no_conflicting_tail_replacement : forall κ κ' φ φ' (H : φ <> φ'), replacetail_kont (φ :: κ) (φ' :: κ) κ' = None.
Proof.
  induction κ as [|φ κ_ IH]; intros.
  unfold replacetail_kont; destruct (kont_eq_dec [φ] [φ']) as [bad|]; [injection bad; intros; contradiction|auto].
  unfold replacetail_kont; destruct (kont_eq_dec (φ0 :: φ :: κ_) (φ' :: φ :: κ_)) as [bad|];
  [injection bad; intros; contradiction
  |fold replacetail_kont].
  destruct (kont_eq_dec (φ :: κ_) (φ' :: φ :: κ_)) as [bad|];
    [injection bad; intros toolong;apply no_circular_cons in toolong; contradiction
    |rewrite no_longer_tail_replacement with (κmore := [φ' ; φ]); [reflexivity | simpl; omega]].
Qed.

Inductive ctx_of : TrunKont -> Context -> Prop :=
  | push_ctx : `{ctx_of tκ ctx -> ctx_of (kpush φ tκ) ctx}
  | rt_ctx : `{ctx_of (rt ctx) ctx}.
Hint Constructors ctx_of.

Fixpoint get_ctx (tκ : TrunKont) : option Context :=
  match tκ with
      mt => None
    | kpush _ tκ => get_ctx tκ
    | rt ctx => Some ctx
  end.
Theorem reflect_ctx : forall tκ ctx, ctx_of tκ ctx <-> get_ctx tκ = Some ctx.
Proof. induction tκ; intuition solve [inversion H; auto
                                     |constructor; rewrite IHtκ; auto
                                     |inverts H; simpl; rewrite <- IHtκ; auto].
Qed.

Definition ctx_in_dom (Ξ : KTable) (tκ : TrunKont) :=
  forall ctx : Context, `{ctx_of tκ ctx -> (exists κs, In (ctx,κs) Ξ)}.

(* Proof relevant or not? *)
Inductive Tailed_Trace : forall (κ : Kont) (p : CES_point) (t : Time) (p' : CES_point) (t' : Time), Prop :=
  tailt : `{Trace (shell p κ t)
                  red_cesk
                  ((shell p' κ t') :: π)
            -> (hastail κ π) -> Tailed_Trace κ p t p' t'}.

(* prove option versions save with hastail so this goes through *)

Inductive Stack_Irrelevant : CESK -> Kont -> Kont -> list CESK -> Prop :=
  irrelevant_intro : forall s s' π π' κ' κ'',
                       (replacetail_state s κ' κ'') = Some s' ->
                       (replacetail π κ' κ'') = (map (@Some CESK) π') ->
                       Trace s' red_cesk π' ->
                       Stack_Irrelevant s κ' κ'' π.

Ltac grumble H_ := try solve [simpl; rewrite H_; reflexivity | constructor].
Lemma stack_irrelevance : forall p κ t π κ' κ''
                                 (orig : Trace (shell p κ t) red_cesk π)
                                 (tail0 : KontTail κ' κ)
                                 (Htail : hastail κ' π),
                            Stack_Irrelevant (shell p κ t) κ' κ'' π.
Proof.
  intros; destruct (replacetail_kont_good κ'' tail0) as [κ_ H_]; subst.
  induction orig as [|s0 π0 s1 HT ? Hstep].
  apply irrelevant_intro with (s' := (shell p κ_ t)) (π' := [shell p κ_ t]); grumble H_.
  (* Step *)
  inversion Htail as [|? pt κt tt Htail' κtail];
  destruct (replacetail_kont_good κ'' κtail) as [κt_ Ht_]; subst.
  set (use := IHorig Htail'); inversion use as [? s' ? [|[p0' κ0' t0'] π'] ? ? Hreps Hrep HT'];
    subst; clear use; try solve [inversion HT'].
  assert (s'eq : s' = shell p κ_ t) by (simpl in Hreps; rewrite H_ in Hreps; injection Hreps; auto); subst.
  simpl in Hrep; injection Hrep; intros πeq seq; clear Hrep.
  Ltac ε out p0' κ0' t0' pp κt_ ts s0'eq Ht_ H_ πeq initial pfrom pto π' σ := assert (out : shell p0' κ0' t0' = shell pp κt_ ts); (subst; simpl in s0'eq; rewrite Ht_ in s0'eq; try injection s0'eq; intros; subst; subst p0'; auto);
       apply (irrelevant_intro _ _ (s' := initial)
              (π' := (shell pto κ0' (tick pfrom)) :: (shell pfrom κ0' t0') :: π'));
  [grumble H_
  |unfold replacetail,replacetail_state,map; fold replacetail; fold map; f_equal;
   rewrite Ht_;[auto|f_equal; apply πeq]
  |repeat constructor; auto].

  Ltac push out p0' κ0' t0' κs κ' κ'' pp φ κt_ ts seq Ht_ :=
    assert (out : (shell p0' (φ :: κ0') t0') = shell pp κt_ ts) by
      (subst; simpl in seq; unfold replacetail_kont in Ht_;
       destruct (kont_eq_dec (φ :: κs) κ') as [Heq | Hneq];
       [injection Ht_; intros; subst; rewrite (no_longer_tail_replacement2 κs κt_ φ) in seq; discriminate
       |fold replacetail_kont in Ht_;
         destruct (replacetail_kont κs κ' κ'') as [preκt|]; [|discriminate];
         injection Ht_; injection seq; intros; subst; subst p0'; auto]).

  inversion Hstep as [x ρ σ a κs ts (* <- time *) pp Hmap Hpeq Hs'eq | (* var *)
                      e0 e1 ρ σ κs ts pp Hpeq | (* app *)
                      x e ρ σ κs ts pp Hpeq Hs'eq | (* lam *)
                      v σ e ρ κs ts pp Hpeq Hs'eq | (* arg *)
                      v σ x e ρ fnv κs ts pp Hin_force Hpeq Hs'eq | (* fn -> ap *)
                      x e ρ v σ κs ts pp a ρ' σ' Hpeq Hs'eq];
    [(* var : ε*)
      ε s0'eq p0' κ0' t0' pp κt_ ts seq Ht_ H_ πeq (shell p κ_ t) (ev (var x) ρ σ) (co (adelay a) σ) π' σ
    |(* app : push*)
    push s0'eq' p0' κ0' t0' κs κ' κ'' pp (ar e1 ρ) κt_ ts seq Ht_;
  apply irrelevant_intro with (s' := (shell p κ_ t)) (π' := (shell (ev e0 ρ σ) ((ar e1 ρ)::κ0') tt) :: (shell (ev (app e0 e1) ρ σ) κ0' t0') :: π'); injection s0'eq'; intros; subst;
   [grumble H_
   |unfold replacetail,replacetail_state,map; fold replacetail; fold map; f_equal;
    [rewrite Ht_|repeat f_equal]; auto
   |repeat constructor; auto]
    |(* lam : ε*)
    ε s0'eq p0' κ0' t0' pp κt_ ts seq Ht_ H_ πeq (shell p κ_ t) (ev (lam x e) ρ σ) (co (closure x e ρ) σ) π' σ
    |(* arg : exchange *)
    subst;
      assert (unf0 : exists κt_t, κt_ = fn v :: κt_t /\ replacetail_kont κs κ' κ'' = Some κt_t) by
        (unfold replacetail_kont in Ht_; fold replacetail_kont in Ht_;
         destruct (kont_eq_dec (fn v :: κs) κ') as [Heq | Hneq];
         [injection Ht_; intros; subst;
          unfold replacetail_state in seq;
          assert (badframe : (ar e ρ) <> (fn v)) by discriminate;
          rewrite (no_conflicting_tail_replacement κs κt_ badframe) in seq; discriminate
         |destruct (replacetail_kont κs κ' κ'') as [κt_t|];
           [exists κt_t; injection Ht_; intros; subst; split; auto
                  |discriminate]]);
      destruct unf0 as [κt_t [Hκt Hκs]];

      assert (Ht_' : replacetail_kont (ar e ρ :: κs) κ' κ'' = Some (ar e ρ :: κt_t)) by
          (unfold replacetail_kont; fold replacetail_kont;
           rewrite Hκs;
           destruct (kont_eq_dec (ar e ρ :: κs) κ') as [Heq | Hneq];
           [(* can't be equal, since then ar e ρ :: κs is a tail of fn v :: κs *)
             inversion Htail as [bad0|bad0 bad1 bad2 bad3 bad4 bad5]; subst;
            assert (badframe : (ar e ρ) <> (fn v)) by discriminate;
            apply (no_conflicting_kont_tail badframe) in bad5; contradiction
            |auto]);

      assert (unf1 : κ0' = ar e ρ :: κt_t /\ p0' = pp) by
          (unfold replacetail_state,replacetail_kont in seq; fold replacetail_kont in seq;
           rewrite Hκs in seq;
           destruct (kont_eq_dec (ar e ρ :: κs) κ') as [Heq | Hneq];
           [(* can't be equal, since then ar e ρ :: κs is a tail of fn v :: κs *)
             inversion Htail as [bad0|bad0 bad1 bad2 bad3 bad4 bad5]; subst;
            assert (badframe : (ar e ρ) <> (fn v)) by discriminate;
            apply (no_conflicting_kont_tail badframe) in bad5; contradiction
            |injection seq; intros; subst; split; auto]);
      destruct unf1 as [Hκ0' Hpeq];

      assert (s0'eq' : (shell p0' (fn v :: κt_t) t0') = shell pp κt_ ts) by
          (unfold replacetail_state in seq;
           destruct (replacetail_kont (ar e ρ :: κs) κ' κ''); [|discriminate];
           injection seq; intros; subst; auto);

      apply irrelevant_intro with (s' := (shell p κ_ t))
                                    (π' := (shell (ev e ρ σ) (fn v :: κt_t) (tick pp)) ::
                                           (shell pp ((ar e ρ)::κt_t) t0') :: π');
      [grumble H_
      |unfold replacetail, replacetail_state,map; fold replacetail; fold map; f_equal;
       [rewrite Ht_; subst; auto
       |f_equal; [rewrite Ht_';injection s0'eq'; intros; subst; auto
                 |apply πeq]]
    |subst; repeat constructor; auto]
    |(* fn -> ap : pop*)
    subst;
      assert (Ht_' : replacetail_kont (fn fnv :: κt) κ' κ'' = Some (fn fnv :: κt_)) by
        (unfold replacetail_kont; fold replacetail_kont;
         destruct (kont_eq_dec (fn fnv :: κt) κ') as [Heq | Hneq];
         [(* can't be equal, since then ar e ρ :: κs is a tail of fn v :: κs *)
           inversion Htail as [bad0|bad0 bad1 bad2 bad3 bad4 bad5]; subst;
          assert (badframe : (ar e ρ) <> (fn v)) by discriminate;
          assert (contr : ~ KontTail ([fn fnv] ++ κt) κt) by (apply no_longer_kont_tail; simpl; omega);
          simpl in contr; contradiction
          |rewrite Ht_; auto]);

      unfold replacetail_state in seq; rewrite Ht_' in seq; injection seq; intros; subst;
      apply irrelevant_intro with (s' := (shell p κ_ t))
                                    (π' := (shell (ap x e ρ v σ) κt_ (tick p0')) ::
                                           (shell p0' ((fn fnv)::κt_) t0') :: π');
    [grumble H_
    |unfold replacetail, replacetail_state,map; fold replacetail; fold map; f_equal;
     [rewrite Ht_; subst
     |f_equal; [rewrite Ht_'|]]; auto
    |subst p0'; repeat constructor; auto]
    |(* do ap : ε *)
     ε s0'eq p0' κ0' t0' pp κt_ ts seq Ht_ H_ πeq (shell p κ_ t) (ap x e ρ v σ) (ev e ρ' σ') π' σ].
Qed.
End StackIrrelevance.

(* Proof relevant or not? *)
Inductive KontUpto p tκ Ξ e ρ σ κ' : Prop:=
  kontupto_intro : forall κ,
                     StackUnroll Ξ κ tκ ->
                     forall t' t'',
                       TraceTo red_cesk (shell (ev e ρ σ) κ' t')
                               (shell p κ t'')
                               -> KontUpto p tκ Ξ e ρ σ κ'.
(* Proof relevant or not? *)
Inductive MemoTrace e ρ σ t v σ'' t' : Prop :=
  memotrace_intro : forall κ_irrelevant,
                      Tailed_Trace κ_irrelevant (ev e ρ σ) t (co v σ'') t' ->
                      MemoTrace e ρ σ t v σ'' t'.
Inductive Context_inv p tκ M Ξ ctx : Prop :=
  context_inv_intro :
    forall e ρ σ t tκ'
           (ctxform : ctx = (context e ρ σ t))
           (Hctx : in_ctxs Ξ (context e ρ σ t) tκ')
           (Hupto :
              (forall κ',
               StackUnroll Ξ κ' tκ' ->
               KontUpto p tκ Ξ e ρ σ κ'))
           (Hmemo :
              (forall v σ'' t',
                 in_memos M (context e ρ σ t) (res v σ'' t') ->
                 MemoTrace e ρ σ t v σ'' t')),
              Context_inv p tκ M Ξ ctx.

Definition ContextLE (ctx ctx' : Context) : Prop :=
  match ctx, ctx' with
      context e ρ σ t, context e' ρ' σ' t' => MappingLE σ σ'
  end.
Definition KTableOrd (Ξ : KTable) := forall ctx tκ (Hin : in_ctxs Ξ ctx tκ) ctx' (Hctx : ctx_of tκ ctx'), ContextLE ctx' ctx /\ InDom Ξ ctx'.
Definition MTableOrd (M : Memo) := forall e ρ σ t vm σm tm (Hin : in_memos M (context e ρ σ t) (res vm σm tm)), MappingLE σ σm.
Inductive StateOrd : WCESKMΞ -> Memo -> KTable -> Prop :=
  stateord_intro : forall p tκ t M Ξ
                          (Mord : MTableOrd M)
                          (Kord : KTableOrd Ξ)
                          (ctxord : match (get_ctx tκ) with
                                        None => True
                                      | Some ctx =>
                                        InDom Ξ ctx /\
                                        match ctx with
                                            (context _ _ σ _) => MappingLE σ (store_of p)
                                        end
                                    end),
                     StateOrd (wshell p tκ t) M Ξ.

Lemma InDom_join : forall Ξ ctx tκ, InDom (Ξ_join Ξ ctx tκ) ctx.
Proof.
  intros; rewrite (InDom_is_mapped context_eq_dec);
  destruct (in_list_join context_eq_dec
                         κs_join
                         κ_singleton
                         κs_join_extensive
                         κ_singleton_extensive
                         Ξ Ξ
                         ctx
                         tκ
                         (fun (ab : Context * TrunKonts) (H : In ab Ξ) => H)) as [damn [? ?]];
  exists damn; auto.
Qed.

Lemma InDom_join2 : forall Ξ ctx ctx' tκ',
                      InDom Ξ ctx -> InDom (Ξ_join Ξ ctx' tκ') ctx.
Proof.
intros;
rewrite (InDom_In context_eq_dec);
rewrite (InDom_In context_eq_dec) in H;
inversion H as [b ?]; apply In_join with (b := b); solve [auto | exact context_eq_dec].
Qed.

(* This ordering invariant I believe is important to make sure that unrolled continuations
   cannot refer to a table extension "deep" in the unrolling. The contexts a continuation is
   unrolled through are partially ordered, so once the contexts differ, no "later" unrolling can
   use the trunkonts mapped at that context.
XXX: This still leaves the tricky case of [ctx ↦ ...rt ctx...].*)
Lemma ord_invariant : forall s M Ξ s' M' Ξ'
                             (Hstep : red_ceskmk (widemk s M Ξ) (widemk s' M' Ξ'))
                             (Hinv : StateOrd s M Ξ), StateOrd s' M' Ξ'.
Proof.
intros;
  inversion Hinv;
  inversion Hstep as [x ρ σ a tκs ts Ms Ξs ps Hmap Hpeq Hs'eq |
                      e0 e1 ρ σ tκs ts Ms Ξs ps Hpeq |
                      x e ρ σ tκs ts Ms Ξs ps Hpeq Hs'eq |
                      v σ e ρ tκs ts Ms Ξs ps Hpeq Hs'eq |
                      v σ x e ρ fnv tκs ts Ms Ξs ps Hin_force Hpeq Hs'eq |
                      x e ρ v σ tκs ts Ms Ξs ps a ρ' σ' ts' ctx Hunmapped Hpeq Hs'eq |
                      x e ρ v σ tκs ts Ms Ξs vm σm tm ps a ρ' σ' ctx Hinmemos Hpeq Hs'eq |
                      v σ ctx tκs Ms Ξs t's M's Hin_ctxs Hpeq Hs'eq]; subst;
  try (injection Hpeq; intros; subst; clear Hpeq); apply stateord_intro;
  try solve [auto
            |subst p; simpl;
             match goal with
               |[ctx : context[get_ctx (kpush ?φ ?tκ)] |- _] =>
                simpl in ctx; destruct (get_ctx tκ) as [[e'' ρ'' σ'' t'']|]; destruct ctx; split; auto
               |[ctx : context[get_ctx ?tκ] |- _] => destruct (get_ctx tκ) as [[e'' ρ'' σ'' t'']|];
                                                    destruct ctx; split; auto end
           (* Kord for unmapped ap *)
            |intros ctx' tκ' Hin ctx'' Hctx;
              subst p; destruct (in_list_join_set_split context_eq_dec trunkont_eq_dec)
                       with (l := Ξ) (l' := Ξ) (a := ctx) (a' := ctx') (c := tκ) (c' := tκ')
                       as [[mum ble]|S1]; auto;
              [subst; rewrite reflect_ctx in Hctx; rewrite Hctx in ctxord; destruct ctx',ctx''; simpl in *; auto;
               injection mum; intros; subst t0 s e1 e0;
               apply maple_trans with (l' := σ); [|apply σ_join_ordering]; auto
              |apply Kord with (tκ := tκ'); auto]
            (* unmapped ap memo *)
            |simpl; split;[
               apply InDom_join|apply maple_refl]
            (* memoizing memo *)
            |destruct (get_ctx tκ) as [[_ _ σ_ _]|]; [|auto];
             simpl;
             apply maple_trans with (l' := σ');
             [subst p; simpl in ctxord; apply maple_trans with (l' := σ);
              [auto|apply σ_join_ordering]
             |apply (Mord _ _ _ _ _ _ _ Hinmemos)]
               (* stupid goal dependencies... *)
            |injection Hpeq; intros; subst M t tκ p Ξ; auto
            |(* Kord for unmapped ap *)
            intros ctx' tκ' Hin ctx'' Hctx;
              subst p; destruct (in_list_join_set_split context_eq_dec trunkont_eq_dec)
                       with (l := Ξ) (l' := Ξ) (a := ctx) (a' := ctx') (c := tκ) (c' := tκ')
                       as [[mum [? ble]]|S1]; auto;
              [subst; rewrite reflect_ctx in Hctx; rewrite Hctx in ctxord; destruct ctxord; destruct ctx',ctx''; simpl in *; auto;
               injection mum; intros; subst t0 s e1 e0;
               split;
               [apply maple_trans with (l' := σ); [|apply σ_join_ordering]; auto
               |apply InDom_join2]
              |destruct (Kord _ _ S1 ctx'' Hctx); split; [|apply InDom_join2]]; auto].

(* memoized ap context ordering *)
subst p; simpl;
destruct (get_ctx tκ) as [[e'' ρ'' σ'' t'']|]; destruct ctxord; split; [apply InDom_join2|];auto;
apply maple_trans with (l' := σ'); [apply maple_trans with (l' := σ);[|apply σ_join_ordering]|apply (Mord _ _ _ _ _ _ _ Hinmemos)];auto.

(* memoizing memo table ordering *)
unfold MTableOrd; (* injection Hpeq; *) intros; subst; simpl in ctxord; destruct ctxord.
(* intros ce cρ cσ ct cvm cσm ctm Hinmemos. *)
destruct (in_list_join_set_split context_eq_dec result_eq_dec)
                       with (l := M) (l' := M) (a := ctx) (a' := (context e ρ σ0 t0)) (c := (res v σ (tick (co v σ)))) (c' := (res vm σm tm))
                       as [[mum [ble ?]]|S1]; auto.
destruct ctx as [? ρblah σblah ?];
  injection mum; intros; subst e ρ σ0 t0;
  injection ble; intros; subst vm σm tm; auto.
pose (grumble := Mord _ _ _ _ _ _ _ S1); auto.

subst; simpl in ctxord; destruct ctxord; destruct ctx as [? ρblah σblah ?];
case_eq (get_ctx tκs); [intros [e_ ρ_ σ_ t_] Hctxeq; rewrite <- reflect_ctx in Hctxeq; simpl;
                        pose (mumble := Kord _ _ Hin_ctxs _ Hctxeq);
                        simpl in mumble; destruct mumble; split; [|apply maple_trans with (l' := σblah)]|];auto.
Qed.

Remark ord_invariant0 : forall e, StateOrd (inject_wceskmk e) nil nil.
intro e; apply stateord_intro;
[intros ? ? ? ? ? ? ? H|intros ? ? H|simpl; trivial]; inversion H as [? [bad ?]]; inversion bad.
Qed.

(* Proof relevant or not? *)
Inductive WInv : WCESKMΞ -> Memo -> KTable -> Prop :=
  winv : forall p tκ t M Ξ,
          Dom_in_Dom M Ξ ->
          ctx_in_dom Ξ tκ ->
          (forall ctx', (InDom Ξ ctx') -> Context_inv p tκ M Ξ ctx')
           ->
          WInv (wshell p tκ t) M Ξ.

Inductive Inv : CESKMΞ -> Prop :=
  inv : forall s M Ξ, WInv s M Ξ -> Inv (widemk s M Ξ).

Remark inject_ceskmk_inv : forall e, Inv (inject_ceskmk e) /\ StateOrd (inject_wceskmk e) nil nil.
Proof.
  constructor.
  constructor.
  constructor.
  constructor.
  intros ctx bad; inversion bad.
  intros ? bad; inversion bad.
  constructor.
  intros ? ? ? ? ? ? ? [? [bad ?]]; inversion bad.
  intros ? ? [? [bad ?]]; inversion bad.
  simpl; exact I.
Qed.

Inductive WideInv : System -> Prop :=
  wideinv : forall Seen F M Ξ
                (SeenInv : forall s, set_In s Seen -> WInv s M Ξ * StateOrd s M Ξ)
                (FrontierInv : forall s, set_In s F -> WInv s M Ξ * StateOrd s M Ξ),
           WideInv (system Seen F M Ξ).

Lemma inv_invariant : forall s M Ξ s' M' Ξ', WInv s M Ξ -> StateOrd s M Ξ -> red_ceskmk (widemk s M Ξ) (widemk s' M' Ξ') -> WInv s' M' Ξ'.
Proof.
Admitted.

Lemma ForallT_forall1 : forall A (P : A -> Type) x l, ForallT P l -> InT x l -> P x.
Proof.
induction l; intros HF H; [inversion H|inverts HF; inversion H as [? ? HH|];[inversion HH|]; auto].
Defined.
Lemma ForallT_forall2 : forall A (P : A -> Type) l, (forall x, InT x l -> P x) -> ForallT P l.
Proof.
induction l; intros H; [|constructor; [apply H; left; constructor|apply IHl; intros; apply H; right]];auto.
Defined.

Lemma PR_step_all_invariant : forall s M Ξ, WInv s M Ξ -> StateOrd s M Ξ -> ForallT Inv (step_all (widemk s M Ξ)).
Proof.
intros ? ? ? Hwinv Hoinv; apply ForallT_forall2; intros [? ? ?]. intro H; apply PR_finite_steps2 in H;
exact (inv (inv_invariant Hwinv Hoinv H)).
Qed.

Lemma step_all_invariant : forall s M Ξ, WInv s M Ξ -> StateOrd s M Ξ -> Forall Inv (step_all (widemk s M Ξ)).
Proof.
intros ? ? ? Hwinv Hoinv; rewrite Forall_forall; intros [? ? ?]. intro H; rewrite <- finite_steps in H;
exact (inv (inv_invariant Hwinv Hoinv H)).
Qed.

Lemma PR_step_all_ord_invariant : forall s M Ξ, StateOrd s M Ξ -> ForallT (fun ws => match ws with widemk s' M' Ξ' => StateOrd s' M' Ξ' end) (step_all (widemk s M Ξ)).
Proof.
intros ? ? ? Hoinv; apply ForallT_forall2; intros [? ? ?]; intro H; apply PR_finite_steps2 in H;
exact (ord_invariant H Hoinv).
Qed.

Lemma step_all_ord_invariant : forall s M Ξ, StateOrd s M Ξ -> Forall (fun ws => match ws with widemk s' M' Ξ' => StateOrd s' M' Ξ' end) (step_all (widemk s M Ξ)).
Proof.
intros ? ? ? Hoinv; rewrite Forall_forall; intros [? ? ?]; intro H; rewrite <- finite_steps in H;
exact (ord_invariant H Hoinv).
Qed.

Definition TableContains (M : Memo) (Ξ: KTable) (ss : set CESKMΞ) :=
  Forall (fun s => match s with widemk ws M' Ξ' => MappingLE M' M /\ MappingLE Ξ' Ξ end) ss.

Check filter_In.
Lemma filter_InT1: forall (A : Type) (f : A -> bool) x l, InT x (filter f l) -> (InT x l) * (f x = true).
Proof.
induction l; auto; intro H; [inversion H|].
simpl in H.
case_eq (f a); [intro Hfatrue|intro Hfafalse];
[rewrite Hfatrue in H; inversion H as [? ? Heq|]; [inversion Heq|destruct IHl; auto]; subst; split; auto|rewrite Hfafalse in H; destruct IHl; auto].
Defined.

Lemma smush_invariant : forall Seen ss M Ξ nexts
                               (SeenInv : ForallT (fun s => WInv s M Ξ) Seen)
                               (MΞinv : TableContains M Ξ ss)
                               (ssInv : ForallT Inv ss)
                               (nextsInv : ForallT (fun s => WInv s M Ξ) nexts),
                          match smusher Seen ss nexts M Ξ with
                              wide_step ss M' Ξ' => ForallT (fun s => WInv s M' Ξ') ss
                          end.
Proof.
  induction ss as [|[s' M' Ξ'] ss' IH]; intros.
  (* base *)
  simpl; apply ForallT_forall2; intros s H; apply filter_InT1 in H; destruct H as [Hin feq].
  apply ForallT_forall1 with (x := s) in nextsInv; auto.
  (* induction step *)
  simpl.
apply IH.
Focus 2.
unfold TableContains; rewrite Forall_forall;
unfold TableContains in MΞinv; rewrite Forall_forall in MΞinv;
intros mum ble; assert (blahneed : In mum (widemk s' M' Ξ' :: ss')) by (right; exact ble); pose (blah := (MΞinv mum blahneed));
destruct mum; intuition ((apply maple_trans with (l' := M) || apply maple_trans with (l' := Ξ)); solve [apply map_join_ordering2; auto | auto]).
Focus 2.
apply ForallT_forall2;
pose (useIH := IH (Ms_join M' M) (Ξs_join Ξ' Ξ) (set_add wceskmξ_eq_dec s' nexts)).
Abort.

Lemma wideinv_invariant : forall Seen F M Ξ Seen' F' M' Ξ'
                                 (Hinv: WideInv (system Seen F M Ξ))
                                 (Hstep : Wide_CESKMΞ (system Seen F M Ξ) (system Seen' F' M' Ξ')),
                            WideInv (system Seen' F' M' Ξ').
Proof.
intros; inversion Hstep as [ws ? ? ? F_ Seen_ ? ? Hstepeq]; subst; constructor; intros ws' Hin.
destruct ws as [[e ρ σ | v σ | x e ρ v σ] tκ t]; [|destruct tκ|].
(* ev case *)
destruct e as [x | e0 e1 | x e ]; simpl in Hstepeq.
Abort.

Inductive state_rel : CESK -> System -> Prop :=
  point_rel : forall Ξ κ tκ p t Seen F M,
                StackUnroll Ξ κ tκ ->
                (In (wshell p tκ t) Seen \/ In (wshell p tκ t) F) ->
                state_rel (shell p κ t) (system Seen F M Ξ).

Print sigT.
(*
Definition red_cesk_dec (s s' : CESK) : option (red_cesk s s').
destruct s as [[e ρ σ | v σ | x e ρ v σ] κ t];
destruct s' as [[e' ρ' σ' | v' σ' | x' e' ρ' v' σ'] κ' t'].
(* ev -> ev *)
destruct e as [x | e0 e1 | x e];
[exact None (* var -/-> ev *)
|destruct (expr_eq_dec e0 e'); [destruct (env_eq_dec ρ ρ'); [destruct (store_eq_dec σ σ'); [destruct (kont_eq_dec κ' ((ar e1 ρ) :: κ)); [destruct (time_eq_dec t' (tick (ev (app e0 e1) ρ σ))); [subst; apply Some; apply ev_app |]|]|]|]|]; exact None
|(* lam -/-> ev *)
exact None].

(* ev -> co *)
destruct e as [x | e0 e1 | x e];
[set (oa := lookup_ρ x ρ);
  case_eq oa; [intros a Haeq;subst oa;unfold lookup_ρ in Haeq; rewrite <- lookup_mapsto in Haeq|intros; exact None];
  destruct (val_eq_dec v' (adelay a)); [destruct (store_eq_dec σ σ'); [destruct (kont_eq_dec κ κ'); [destruct (time_eq_dec t' (tick (ev (var x) ρ σ))); [subst;apply Some,ev_var; assumption|]|]|]|]; exact None
|exact None (* app -/-> co *)
|destruct (val_eq_dec v' (closure x e ρ)); [destruct (store_eq_dec σ σ'); [destruct (kont_eq_dec κ κ'); [destruct (time_eq_dec t' (tick (ev (lam x e) ρ σ))); [subst; apply Some,ev_lam|]|]|]|]; exact None].

(* ev -> ap *)
exact None.

(* co -> ev *)
destruct κ as [|[e ρ|fnv] κ_];
  [exact None (* mt -/> *)
  |destruct (expr_eq_dec e e');[destruct (env_eq_dec ρ ρ'); [destruct (store_eq_dec σ σ'); [destruct (kont_eq_dec κ' (fn v :: κ_)); [destruct (time_eq_dec t' (tick (co v σ))); [subst; apply Some,co_ar|]|]|]|]|]; exact None
  |exact None (* fn v -/-> ev *)].

(* co -> co *)
exact None.

(* co -> ap *)
destruct κ as [|[e ρ|fnv] κ_];
  [exact None
  |exact None
  |destruct (set_In_dec storeable_eq_dec (s_closure x' e' ρ') (force σ fnv)) as [doable|];
    [rewrite <- in_force_In_force in doable;
      destruct (val_eq_dec v' v); [destruct (store_eq_dec σ σ'); [destruct (kont_eq_dec κ_ κ'); [destruct (time_eq_dec t' (tick (co v σ))); [subst; apply Some,co_fn; auto|]|]|]|]|]; exact None].

(* ap -> ev *)
set (a := alloc (ap x e ρ v σ));
destruct (expr_eq_dec e' e); [destruct (env_eq_dec ρ' (extend_ρ x a ρ));[destruct (store_eq_dec σ' (σ_join σ a v));[destruct (kont_eq_dec κ' κ);[destruct (time_eq_dec t' (tick (ap x e ρ v σ))); [subst; apply Some, do_ap;auto|]|]|]|]|]; exact None.

(* ap -> co *)
exact None.
(* ap -> ap *)
exact None.
Defined.
*)

Inductive Shallow_TrunKont_Kont_rel : TrunKont -> Kont -> Prop :=
| mt_rel : `{Shallow_TrunKont_Kont_rel mt nil}
| push_rel : `{Shallow_TrunKont_Kont_rel tκ κ ->
               Shallow_TrunKont_Kont_rel (kpush φ tκ) (φ :: κ)}
|  rt_rel : `{Shallow_TrunKont_Kont_rel (rt ctx) κ}.

Inductive Relate_nonmemo : CES_point -> Memo -> Prop :=
  rel_ev : `{Relate_nonmemo (ev e ρ σ) M}
| rel_co : `{Relate_nonmemo (co v σ) M}
| rel_nonmemo_ap : forall x e ρ v σ M,
                     let p := (ap x e ρ v σ) in
                     let a := alloc p in
                     let ρ' := extend_ρ x a ρ in
                     let σ' := σ_join σ a v in
                     let t' := tick p in
                     let ctx := (context e ρ' σ' t') in
                     Unmapped M ctx ->
                     Relate_nonmemo (ap x e ρ v σ) M.

Inductive relate_CESK_CESKMΞ : CESK -> CESKMΞ -> Prop :=
  relate_nonmemo_full : `{Shallow_TrunKont_Kont_rel tκ κ ->
                          Relate_nonmemo p M ->
                          relate_CESK_CESKMΞ (shell p κ t) (widemk (wshell p tκ t) M Ξ)}.

Inductive relate_CESK_CESKMΞ_traces : list CESK -> list (nat * CESKMΞ) -> Prop :=
| relate_inject : forall e n, relate_CESK_CESKMΞ_traces [inject_cesk e] [(n, (inject_ceskmk e))]
| relate_nonmemo : `{relate_CESK_CESKMΞ_traces (ς :: π) ((n,ςw) :: wπ) ->
                     red_cesk ς ς' ->
                     relate_CESK_CESKMΞ ς' ςw' ->
                     relate_CESK_CESKMΞ_traces (ς' :: ς :: π) ((nw,ςw') :: (n,ςw) :: wπ)}
| relate_stutter : `{nw' < nw ->
                     red_cesk ς ς' ->
                     relate_CESK_CESKMΞ_traces (ς :: π) ((nw,ςw) :: wπ) ->
                     relate_CESK_CESKMΞ_traces (ς' :: ς :: π) ((nw',ςw) :: (nw,ςw) :: wπ)}
| relate_memo : `{relate_CESK_CESKMΞ_traces (ς :: π)
                                            ((n', (widemk (wshell p_ tκ t_) M Ξ)) :: wπ)
                  ->
                  red_cesk ς (shell (ap x e ρ v σ) κ t) ->
                  let p := (ap x e ρ v σ) in
                  let a := alloc p in
                  let ρ' := extend_ρ x a ρ in
                  let σ' := σ_join σ a v in
                  let t' := tick p in
                  let ctx := (context e ρ' σ' t') in
                  in_memos M ctx (res vm σm tm) ->
                  Trace (shell (ev e ρ σ) κ t) red_cesk
                        ((shell (co vm σm) κ tm) :: mπ) ->
                  relate_CESK_CESKMΞ_traces ((shell (ap x e ρ v σ) κ t) :: π)
                                            ((length mπ,(widemk (wshell (ap x e ρ v σ) tκ t) M Ξ))
                                               :: (n',(widemk (wshell p_ tκ t_) M Ξ)) :: wπ)}.

Theorem initial_trace_inv : forall e wπ,
                              Trace (inject_ceskmk e) red_ceskmk wπ ->
                              Forall (fun x =>
                                        Inv x /\
                                        match x with
                                            widemk s M Ξ => StateOrd s M Ξ
                                        end) wπ.
Proof.
  induction wπ; intros HT; [constructor|].
  inversion HT as [| ς wπ' ? HT' Hstep Hin];
    [constructor;[exact (inject_ceskmk_inv e)
                 |constructor]
    |subst;rewrite Forall_forall; intros ς' Hin; inversion Hin;
     rewrite Forall_forall in IHwπ;
     [subst;
       destruct ς as [s M Ξ];
       assert (invlast : Inv (widemk s M Ξ) /\ StateOrd s M Ξ) by
           (apply IHwπ; [|left];auto);
      destruct invlast as [invlast ordlast];
        destruct ς' as [s' M' Ξ'];
        split;
        [inversion invlast as [? ? ? Hwinv]; subst;constructor; apply (inv_invariant Hwinv); auto
        |apply (ord_invariant Hstep ordlast)]
      |apply IHwπ; auto]].
Qed.

Theorem TraceRed_preserves_relation : forall e π wπ
                                             (Hrel : relate_CESK_CESKMΞ_traces π wπ)
                                             π' wπ'
                                             (HMK : TraceRed_Stutter (inject_ceskmk e) red_ceskmk wπ wπ')
                                             (Horig : TraceRed (inject_cesk e) red_cesk π π'),
                                        relate_CESK_CESKMΞ_traces π' wπ'.
Proof.
  intros e_ ? ? Hrel; induction Hrel as [|ς π_ wn wς wπ_ ς' wς' wn' Hrel' IH Hstep Hsrel
                                         |
                                         |x e* ρ v σ κ t π_ tκ M Ξ wπ_ v_ σ_ t_ π'_ πsuff ? IH
                                          p a ρ' σ' t' ctx Hinmemo HT Htail];
  [intros π' wπ' HMK Horig
  |intros π' wπ' HMK Horig
  |intros π' wπ' HMK Horig
  |intros Hsuff π_'].

  (* injection case always not memo'd *)
  inversion Horig as [|? ? ς' Horig' Hstep];
  inversion HMK as [nw foo bar |nw_ nw'_ ? ? Hlew |? nw ? ? wς' HMK' Hstep']; subst;
  [apply relate_stutter; [| |apply relate_inject]; auto
  |apply relate_nonmemo;
    [apply relate_inject| |
     inversion Hstep' as [x ρ σ a tκs ts Ms Ξs ps Hmap Hpeq Hs'eq |
                          e0 e1 ρ σ tκs ts Ms Ξs ps Hpeq |
                          x elam ρ σ tκs ts Ms Ξs ps Hpeq Hs'eq |
                          v σ earg ρ tκs ts Ms Ξs ps Hpeq Hs'eq |
                          v σ x ebody ρ fnv tκs ts Ms Ξs ps Hin_force Hpeq Hs'eq |
                          x ebody ρ v σ tκs ts Ms Ξs ps a ρ' σ' ts' ctx Hunmapped Hpeq Hs'eq |
                          x ebody ρ v σ tκs ts Ms Ξs vm σm tm ps a ρ' σ' ctx Hinmemos Hpeq Hs'eq |
                          v σ ctx tκs Ms Ξs t's M's Hin_ctxs Hpeq Hs'eq]; subst;
     try solve [inversion Hmap];
     inversion Hstep as [x_ ρ_ σ_ a_ κ_ t_ p_ Hmap_
                        |e0_ e1_ ρ_ σ_ κ_ t_ p_ Hpeq_
                        |x_ elam_ ρ_ σ_ κ_ t_ p_ Hpeq Hs'eq_
                        | | | ];
     try solve [inversion Hmap_]; subst; repeat constructor]]; auto.

  inversion Horig as [|? ? ς'_ Horig' Hstep_];
  inversion HMK as [nw foo bar |nw_ nw'_ ? ? Hlew |? nw ? ? wς'_ HMK' Hstep']; subst.
Abort.

Definition refine_CESK (e : Expr) π (T : CESK_trace e π) : sigT (fun π => CESKMΞ_trace e π).
induction T.
exists [(inject_ceskmk e)]; constructor.
destruct IHT as [π' HT].
inverts HT.

Fixpoint
  match π with
      nil => nil
    | [shell p κ t] => [widemk (wshell p mt t) nil nil]
    | ς' :: ς :: π => nil
  end.

Theorem simulation : WEB_refinement state_rel forall e π (HT: CESK_trace e π), exists π', WCESKMΞ_trace e π' /\ Forall (fun xy => match xy with (x,y) => state_rel x y end) (combine π π').
Proof.
  intros e π HT; induction HT.
  exists [(inject_wide_ceskmk e)];
    split; [constructor
           |rewrite Forall_forall; simpl; intros [cesk sys Hin]; inversion_clear Hin as [Heq|bad]; [injection Heq; intros; subst;apply point_rel with (tκ := mt); constructor; left; auto|destruct bad]].
  destruct IHHT as [π' [HT' Hrel]].
  inversion H as [x ρ σ a κ t p Hmap
                 | | | | |]; subst.
  simpl in Hrel.
End NonStandardSemantics.
End NonStandardData.
End StandardSemantics.
End Data.