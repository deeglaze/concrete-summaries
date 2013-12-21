Require Import ZArith NArith List ListSet.
Import ListNotations.
Definition Name := nat.
Notation "'dec_type' T" := (forall x y : T, {x=y}+{x<>y}) (at level 70, no associativity).

Ltac split_refl eq_dec a := let H:= fresh in destruct (eq_dec a a) as [H|bad]; [clear H|contradict bad]; auto.
Ltac split_refl2 eq_dec a a' := let H:= fresh in
                                destruct (eq_dec a a') as [bad|H]; [contradict bad|clear H]; auto.

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

Inductive InDom {A B} : list (A * B) -> A -> Type :=
  | dom_fst : `{InDom ((a,b)::rst) a}
  | dom_rst : `{InDom l a -> InDom ((a',b')::l) a}.

Inductive MapsTo {A B} : list (A * B) -> A -> B -> Type :=
  | map_fst : `{MapsTo ((a,b)::rst) a b}
  | map_rst : `{a <> a' -> MapsTo l a b -> MapsTo ((a',b')::l) a b}.

Inductive Unmapped {A B} : list (A * B) -> A -> Type :=
  | unil : forall a, Unmapped nil a
  | ucons : forall a a' b l, Unmapped l a' -> a <> a' -> Unmapped ((a,b)::l) a'.

Inductive Functional {A B} : list (A * B) -> Type :=
  | empty_fn : Functional nil
  | extend_fn : `{Functional l -> Unmapped l a -> Functional ((a,b)::l)}.

Inductive InT {A} : A -> list A -> Type :=
  in_fst : forall a l, InT a (a :: l)
| in_rst : forall a l b, InT a l -> InT a (b :: l).

Lemma MapsTo_In : forall A B (l : list (A * B)) a b (H: MapsTo l a b), InT (a,b) l.
Proof.
  induction l as [|(a,b) l' IH];
  intros a' b' H; inversion H; (* finishes base case *)
  subst; [constructor|right; apply IH]; auto.
Qed.

Theorem unmapped_not_mapped : forall A B
                                     (eq_dec : dec_type A)
                                     (l : list (A*B)) a,
                                (Unmapped l a -> forall b, MapsTo l a b -> False) *
                                ((forall b, (MapsTo l a b -> False)) -> Unmapped l a).
Proof.
  intros A B eq_dec l a; induction l as [|(a',b') l' [IHl'0 IHl'1]];
  split;
  [intros H b bad; inversion bad
  |constructor
  |intros H b0 bad;
    inversion H as [| ? ? ? ? Hunmapped Hbad];
    inversion bad as [| ? ? ? ? ? ? Hbadmap]; subst;
    [contradict Hbad; reflexivity
    |specialize IHl'0 with Hunmapped; apply IHl'0 in Hbadmap]  
  |intros H; constructor;
  [apply IHl'1; intros bb bad; destruct (eq_dec a a'); subst;
      [pose (HC := (H b')); contradict HC; constructor
      |pose (HC := (H bb)); contradict HC; constructor; auto]
     |intro Heq; subst; apply H with (b := b'); constructor]]; auto.
Qed.

Lemma in_not_unmapped : forall A B (l : list (A * B)) a b (H:InT (a,b) l), Unmapped l a -> False.
Proof.
  induction l as [|(a,b) l' IH]; intros a0 b0 H bad; inversion H; subst;[
  inversion bad; intuition
  |inversion bad as [|? ? ? ? bad']; apply IH with (b:= b0) in bad'; auto].
Qed.

Lemma in_functional_mapsto : forall A B (eq_dec : dec_type A) (l : list (A * B)) (F : Functional l)
                                    a b (H : InT (a,b) l), MapsTo l a b.
Proof.
  induction l as [|(a,b) l' IH];
  intros F a' b' H; inversion H;[ (* finishes base case *)
    subst; constructor; auto
  |inversion F as [|? ? ? Hfun Hunmapped]; subst;
   destruct (eq_dec a a'); [subst; contradict Hunmapped; apply in_not_unmapped with (b:=b')
                           |constructor]]; auto.
Qed.

Remark functional_exchange : forall A B (l : list (A * B)) a b (F: Functional ((a,b)::l)) b', Functional ((a,b')::l).
Proof. intros; inversion F; constructor; auto. Qed.

Definition in_aval := In.

Inductive exT {A} : (A -> Type) -> Type :=
  exT_intro : forall a P, (P a) -> exT P.
Notation "'existsT' x .. y , p" := (exT (fun x => .. (exT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'").


Definition in_list_list {A B} (l : list (A * (list B))) (a : A) (b : B) : Type :=
  existsT bs, prod (MapsTo l a bs) (InT b bs).

Inductive in_force (σ : Store) : forall (v v' : val), Type :=
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
                          prod ((MapsTo l a b) -> (lookup_map eq_dec a l) = Some b)
                               ((lookup_map eq_dec a l) = Some b -> (MapsTo l a b)).
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

Section ListJoin.
Variables (A B C : Type) (eq_dec : dec_type A)
          (combine : list (A * B) -> B -> C -> B)
          (base : list (A * B) -> C -> B).
Fixpoint list_join  (l_orig : list (A * B))
         (a : A) (c : C)
         (l : list (A * B)) : list (A * B) :=
  match l with
      | nil => (a,base l_orig c)::nil
      | (a',b)::l' => if (eq_dec a a') then
                        (a,(combine l_orig b c))::l'
                      else (a',b)::(list_join l_orig a c l')
  end.
Definition singleton {A} (eq_dec : dec_type A) (x : A) : list A := set_add eq_dec x (empty_set _).
End ListJoin.

Section ListJoin_facts.
Variables (A C : Type) (eq_dec : dec_type A)
          (combine : list (A * list C) -> list C -> C -> list C)
          (base : list (A * list C) -> C -> list C)
          (Hextensive : (forall l b c, InT c (combine l b c)))
          (Hsingleton : (forall l c, InT c (base l c))).
Lemma in_list_join :
  forall l l' a c,
    (forall ab, InT ab l -> InT ab l') ->
  in_list_list (list_join eq_dec combine base l' a c l) a c.
Proof.
  intros l l' a c Hcontain.
  induction l; simpl.
  exists (base l' c); split; [left| apply Hsingleton]; auto.
  destruct a0 as [a' b]; destruct (eq_dec a a') as [Heq | Hneq];
  [subst; exists (combine l' b c); split; [left|apply Hextensive]
  |assert (IHneed : (forall ab, InT ab l -> InT ab l')) by (intros (a_,bs') Hin; apply Hcontain; right; auto);
    set (mumble := (IHl IHneed));
    inversion mumble as [wit P Hwit Heq]; subst; destruct Hwit as [Hmap Hin];
    exists wit; split; [apply map_rst|]]; auto.
Qed.

Lemma unmapped_join : `{Unmapped l a -> a <> a' -> Unmapped (list_join eq_dec combine base l' a' c l) a}.
Proof.
  induction l as [|(a,b) l_ IH]; intros a0 a' l' c H ?;
  simpl; repeat constructor; auto.
  simpl; destruct (eq_dec a' a) as [Heq|Hneq];
  [subst; inversion H; constructor
  |constructor;inversion H;[apply IH|]];auto.
Qed.

Lemma functional_join : `{Functional l -> Functional (list_join eq_dec combine base l' a c l)}.
Proof.
  induction l as [|(a,b) l_ IH]; simpl;
  [intros; repeat constructor
  |intros l' a' c F].
  destruct (eq_dec a' a) as [Heq|Hneq];
  [subst; apply functional_exchange with (b := b)
  |constructor; inversion F; [apply IH|apply unmapped_join]]; auto.
Qed.

Variable Hextensive' : (forall l b c c', InT c' b -> InT c' (combine l b c)).
Lemma in_list_join2 :
  forall l l' a a' c c',
  in_list_list l a' c' ->
  in_list_list (list_join eq_dec combine base l' a c l) a' c'.
Proof.
  intros l l' a a' c c' Hold;
  induction l; simpl;
  inversion Hold as [bs ? Hwit]; destruct Hwit as [Hpairin Hsetin]; subst;
  [(* base case *) inversion Hpairin
  |destruct a0; destruct (eq_dec a a0) as [Heq | Hneq]; subst;
   [(* Heq *)
     subst; inversion Hpairin; subst;
    [exists (combine l' bs c); split; [left|apply Hextensive']; auto
           |exists bs; split; [right|]; auto]
   |(* Hneq *)
    destruct (eq_dec a0 a') as [Heq' | Hneq'];
     inversion Hpairin as [|? ? ? ? ? ? Hmap']; subst;
    [exists bs; split; [constructor|]; auto
    |match goal with [Hbad : ?a <> ?a |- _] => contradict Hbad; auto end
    |exists bs; constructor; [constructor|]; auto
    |assert (IHneed : in_list_list l a' c') by (exists bs; repeat constructor; auto);
     set (IHl_ := IHl IHneed);
     inversion IHl_ as [x ? Hwit]; destruct Hwit as [Hmap Hin];
     exists x; repeat constructor; auto]]].
Qed.

Lemma non_join_untouched : forall l l' a a' c b
                             (Hneq : a <> a')
                             (H: MapsTo (list_join eq_dec combine base l' a c l) a' b),
                             MapsTo l a' b.
Proof.
  induction l as [|(a_,b_) l_ IH]; intros;
  [inversion H; subst; [contradict Hneq|]; auto
  |
  simpl in H; inversion H as [? ? rst H'|? a'' ? ? ? Hneq'' map' Hinj]; subst;
  destruct (eq_dec a a_) as [Heq_|Hneq_];
  try (injection H'; intros; subst);
  try (injection Hinj; intros; subst);
  [
  (* Eq *)
  constructor; [auto
               |apply IH with (l' := l') (a := a_) (c := c);
                 [auto
                 |contradict Hneq; auto]]
  |constructor
  |subst; constructor; auto
  |constructor; [auto | apply IH with (l' := l') (a := a) (c := c); auto]]].
Qed.

(*
  
Lemma unmapped_join2 : forall l a a' b c l'
                             (Hcontain : (forall a c, in_list_list l a c -> in_list_list l' a c)
                                          \/ (b = (base l' c))),
                        Unmapped l a' ->
                        MapsTo (list_join eq_dec combine base l' a c l) a' b ->
                        (b = (base l' c)) /\ a = a'.
Proof.
  induction l as [|(a_,b_) l_ IH];
  simpl; intros a a' b c l' Hcontain Hunmap Hmap;
  [inversion Hmap as [|? ? ? ? ? ? Hbad]; subst; split; solve [auto|reflexivity|inversion Hbad]
  |].
  destruct (eq_dec a a_) as [Heq | Hneq];
    [inversion Hunmap as [|? ? ? ? Hunmap' Hneq]; subst;
     inversion Hmap as [|? ? ? ? ? ? Hbad]; split; try solve [reflexivity|
                                             rewrite unmapped_not_mapped in Hunmap';
                                             [apply Hunmap' in Hbad; contradiction
                                             |auto]]
    |].
  inversion Hmap as [|? ? ? ? ? ? Hbad]; subst; contradict Hneq; auto.
  apply IH with (b := b) (c := c) (l' := l').
  inversion Hcontain as [L|R].
  specialize L with a_ b_
  intros a_' c_' Hin; inversion Hin as [bs_ [Hmap_ Hsetin_]];
  apply Hcontain; destruct (eq_dec a_' a_) as [Heq_|Hneq_];
  [subst
    |exists bs_; repeat constructor]; auto.
  unfold in_list_list.
  Focus 2.
  
    [intros a_' c_' Hin
    |inversion Hunmap
    |]; auto.

; 
  inversion Hmap; [(* a_' = a_ *)
                   rewrite unmapped_not_mapped in Hunmap; [
                    (* rewritten *)
                    subst; match goal with [bad : ?a <> ?a |- _] => contradict bad; auto end
                    |(* satisfy hyp *)assumption]
                   |subst]. 
  Check unmapped_not_mapped.
                       
   [specialize Hunmap with b; contradict Hunmap; constructor
   |assumption
   |
   |assumption].
  .
  ; constructor; auto | auto].
    

 subst; repeat constructor|]
  constructor.
Qed.
Admitted.*)
Theorem set_add_intro1T : forall (a b : A) (l : list A), InT a l -> InT a (set_add eq_dec b l).
Proof.
  clear; induction l as [|x l' IH]; intros H; inversion H; subst; simpl;
  destruct (eq_dec b x); subst; constructor; auto.
Qed.

Theorem set_add_intro2T : forall (a : A) (l : list A), InT a (set_add eq_dec a l).
Proof.
  clear; induction l as [|x l' IH]; subst; simpl;[
    constructor
    |destruct (eq_dec a x); subst; constructor; auto].
Qed.

Theorem set_add_elimT : forall (a b : A) (l : list A) (H: InT a (set_add eq_dec b l)),
          (a = b) + (InT a l).
Proof.
  clear.
  induction l; intros; simpl in H; inversion H as [? l_|? l' b' Hin]; subst; try solve [intuition];
  destruct (eq_dec b a0) as [Heq | Hneq];
  try match goal with [H : ?a :: ?l = ?b :: ?k |- _] => injection H; intros; subst end;
  try solve
  [right; constructor | right; auto].
  set (IHl_ := IHl Hin).
  inversion IHl_; [left|right;constructor]; auto.
Qed.

End ListJoin_facts.
Section ListJoin_morefacts.
Variables (A C : Type) (eq_dec : dec_type A) (ceq_dec : dec_type C).
Definition joiner := (fun (_ : list (A * list C)) κs κ => (set_add ceq_dec κ κs)).
Definition singler := (fun (_ : list (A * list C)) c => (singleton ceq_dec c)).
Hint Unfold singleton singler.

Lemma in_list_join_set_split : forall (l l' : list (A * list C))
                                      (a a' : A)
                                      (c c' : C)
                                 (Hin : in_list_list (list_join eq_dec joiner singler l' a c l) a' c'),
                                 sum (prod (a = a') (c = c')) (in_list_list l a' c').
Proof.
  induction l as [|(a,cs) l_ IH]; [intros|intros ll' aa aa' cc cc' Hin];
  simpl in *; 
  inversion Hin as [cs_ ? Hwit]; destruct Hwit as [map_ in_]; subst;
  [(* base case *)
  inversion map_ as [|? ? ? ? ? ? bad]; subst;
    [inversion in_ as [|? ? ? bad]; subst; [left; split; auto|inversion bad]
    |inversion bad]
  |].
  destruct (eq_dec aa a) as [Heq|Hneq];
    inversion map_ as [|foo bar baz qux moo boo too];subst.

  (* Eq case with inversion *)
  destruct (set_add_elimT ceq_dec _ _ in_) as [Hceq|Hinrest];
       [intuition
       |subst; right; exists cs; repeat constructor; auto].

  right; exists cs_; repeat constructor; auto.

  (* Neq case with inversion *)
  right; exists cs_; repeat constructor; auto.

  destruct (eq_dec aa aa') as [Heq_|Hneq_].
  (* eq *)
  destruct IH with (l' := ll') (a := aa) (a' := aa') (c := cc) (c' := cc') as [S|S];
    [exists cs_; constructor; auto
    |left; exact S
    |inversion S as [ccs ? Hwit]; destruct Hwit as [mmap min]; right; exists ccs; split;[constructor|];auto].
  (* neq *)
  right.
  apply non_join_untouched with (eq_dec := eq_dec) (combine := joiner) (base := singler) in too;
    [exists cs_; repeat constructor|]; auto.
Qed.
    
End ListJoin_morefacts.

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
Variable alloc : CES_point -> Store -> Addr.
Variable tick : CES_point -> Store -> Time.
Variable time0 : Time.

Inductive red_cesk : CESK -> CESK -> Type :=
  ev_var : `{let p := (ev (var x) ρ σ) in
             MapsTo ρ x a ->
             red_cesk (shell p κ t) (shell (co (adelay a) σ) κ (tick p σ))}
| ev_app : `{let p := (ev (app e0 e1) ρ σ) in
             red_cesk (shell p κ t) (shell (ev e0 ρ σ) ((ar e1 ρ)::κ) (tick p σ))}
| ev_lam : `{let p := (ev (lam x e) ρ σ) in
             red_cesk (shell p κ t) (shell (co (closure x e ρ) σ) κ (tick p σ))}
| co_ar : `{let p := (co v σ) in
            red_cesk (shell p ((ar e ρ)::κ) t) (shell (ev e ρ σ) ((fn v)::κ) (tick p σ))}
| co_fn : `{let p := (co v σ) in
            in_force σ (closure x e ρ) fnv ->
            red_cesk (shell p ((fn fnv)::κ) t) (shell (ap x e ρ v σ) κ (tick p σ))}
| do_ap : `{let p := (ap x e ρ v σ) in
            let a := alloc p σ in
            let ρ' := extend_ρ x a ρ in
            let σ' := σ_join σ a v in
            red_cesk (shell p κ t) (shell (ev e ρ' σ') κ (tick p σ))}.

Inductive Trace {State} (s0 : State) (R : State -> State -> Type) : list State -> Type :=
  | initial : Trace s0 R (s0 :: nil)
  | CESK_step : `{Trace s0 R (ς :: π) ->
                  R ς ς' ->
                  Trace s0 R (ς' :: (ς :: π))}.

Definition CESK_trace (e : Expr) := Trace (shell (ev e nil nil) nil time0) red_cesk.
Section NonStandardData.
Inductive Context :=
  context : Expr -> Env -> Store -> Time -> Context.

Definition context_eq_dec : dec_type Context.
  decide equality; try solve [apply expr_eq_dec | apply env_eq_dec | apply store_eq_dec].
Defined.

Inductive Result :=
  res: val -> Store -> Time -> Result.
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

Definition κs_join := (fun (_ : KTable) κs κ => (set_add trunkont_eq_dec κ κs)).
Definition κ_singleton := (fun (_ : KTable) κ => singleton trunkont_eq_dec κ).
Definition res_join := (fun (_ : Memo) rs r => (set_add result_eq_dec r rs)).

Lemma κs_join_extensive (_ : KTable) (b : TrunKonts) (tκ : TrunKont) : InT tκ (set_add trunkont_eq_dec tκ b).
Proof. apply set_add_intro2T; auto. Qed.
(*
Lemma κs_join_extensive' (_ : KTable) (b : TrunKonts) (tκ : TrunKont) := (set_add_intro1 trunkont_eq_dec).
*)
Definition κ_singleton_extensive := κs_join_extensive.

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
Definition Ξs_join := map_join (fun Ξ ctx κs => list_join context_eq_dec
                                                          (fun _ κs' κs => set_union trunkont_eq_dec κs' κs)
                                                          (fun _ κs => κs)
                                                          Ξ ctx κs Ξ).
Definition Ms_join := map_join (fun M ctx rs => list_join context_eq_dec
                                                          (fun _ rs' rs => set_union result_eq_dec rs' rs)
                                                          (fun _ rs => rs)
                                                          M ctx rs M).

Definition in_ctxs (Ξ : KTable) (ctx : Context) (κ : TrunKont) : Type :=
  in_list_list Ξ ctx κ.

Definition in_memos (M : Memo) (ctx : Context) (r : Result) : Type :=
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

Inductive red_ceskmk : CESKMΞ -> CESKMΞ -> Type :=
  evmk_var : `{let s := widemk (wshell (ev (var x) ρ σ) tκ t) M Ξ in
             MapsTo ρ x a ->
             red_ceskmk s (widemk (wshell (co (adelay a) σ) tκ (tickmk s))  M Ξ)}
| evmk_app : `{let s := widemk (wshell (ev (app e0 e1) ρ σ) tκ t) M Ξ in
             red_ceskmk s (widemk (wshell (ev e0 ρ σ) (kpush (ar e1 ρ) tκ) (tickmk s)) M Ξ)}
| evmk_lam : `{let s := widemk (wshell (ev (lam x e) ρ σ) tκ t) M Ξ in
             red_ceskmk s (widemk (wshell (co (closure x e ρ) σ) tκ (tickmk s)) M Ξ)}
| comk_ar : `{let s := widemk (wshell (co v σ) (kpush (ar e ρ) tκ) t) M Ξ in
            red_ceskmk s (widemk (wshell (ev e ρ σ) (kpush (fn v) tκ) (tickmk s)) M Ξ)}
| comk_fn : `{let s := widemk (wshell (co v σ) (kpush (fn fnv) tκ) t) M Ξ in
              in_force σ (closure x e ρ) fnv ->
              red_ceskmk s (widemk (wshell (ap x e ρ v σ) tκ (tickmk s)) M Ξ)}
| do_apmk : `{let s := widemk (wshell (ap x e ρ v σ) tκ t) M Ξ in
              let a := allocmk s in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let t' := (tickmk s) in
              let ctx := (context e ρ' σ' t') in
              let Ξ' := Ξ_join Ξ ctx tκ in
              Unmapped M ctx ->
              red_ceskmk s (widemk (wshell (ev e ρ' σ') (rt ctx) t') M Ξ')}
| do_memo : `{let s := widemk (wshell (ap x e ρ v σ) tκ t) M Ξ in
              let a := allocmk s in
              let ρ' := extend_ρ x a ρ in
              let σ' := σ_join σ a v in
              let ctx := (context e ρ' σ' t') in
              let Ξ' := Ξ_join Ξ ctx tκ in
              in_memos M ctx (res vm σm tm) ->
              red_ceskmk s (widemk (wshell (co vm σm) tκ tm) M Ξ')} (* XXX: tick? *)
| do_rt : `{let s := widemk (wshell (co v σ) (rt ctx) t) M Ξ in
            let t' := (tickmk s) in
            let M' := M_join M ctx (res v σ t') in
            in_ctxs Ξ ctx tκ ->
            red_ceskmk s (widemk (wshell (co v σ) tκ t') M' Ξ)}.

Inductive Dom_in_Dom {A B C} : list (A * B) -> list (A * C) -> Type :=
  | no_dom : forall l, Dom_in_Dom nil l
  | cons_dom : forall a l l' b',
                 (existsT b, InT (a,b) l') ->
                 Dom_in_Dom l l' ->
                 Dom_in_Dom ((a,b')::l) l'.

Lemma In_join : forall A B C (eq_dec: dec_type A) (l l' : list (A * B))
                        (f : list (A * B) -> B -> C -> B)  g a a' b b'
                        (Hcontain : (forall a b, InT (a,b) l -> InT (a,b) l'))
                        (H : InT (a,b) l),
                  (existsT b'', InT (a,b'') (list_join eq_dec f g l' a' b' l)).
Proof.
  intros A B C eq_dec l l' f g a a' b b' Hcontain Hin; induction l as [|(a0,b0) l_ IH];
  inversion Hin as [(a1,b1) l1|(a1, b1) l1 ? Hin']; subst;
  assert (IHneed : forall a b, InT (a,b) l_ -> InT (a,b) l') by
      (intros; apply Hcontain; right; auto);
  pose (rec := IH IHneed);

  unfold list_join;
  destruct (eq_dec a' a0) as [Heq | Hneq];
  try solve [subst; exists (f l' b0 b'); constructor; auto
            |exists b; constructor; auto
            |exists b0; constructor; auto
            |set (rec2 := rec Hin'); inversion rec2 as [b'' ? Hin_];
             exists b''; right; auto].
Qed.

Lemma Dom_join_right : forall A B C D (eq_dec: dec_type A) (l : list (A * B)) (l' : list (A * D))
                        (f : list (A * D) -> D -> C -> D)  g a c
                        (Hdom : Dom_in_Dom l l'), Dom_in_Dom l (list_join eq_dec f g l' a c l').
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Hdom; induction Hdom as [|aa l' ll bb Hex]; [|inversion Hex as [dd ? Hwit]];
  [constructor
  |].  
  induction ll as [|(a_,b_) l'_ IHl'_].
  inversion Hwit.
  simpl in *; auto.
  inversion IHHdom; subst.
  Admitted.
(*
  destruct (eq_dec a a_) as [Heq | Hneq]; [subst|].
  constructor.
  apply In_join with (b := dd); auto.
  simpl in *.
;[destruct H as [? bad]; inversion bad |]);
  [destruct H as [b' Hb'];
    apply In_join with (b := b')|]; auto.
Qed.
*)

Lemma Dom_join_left : forall A B C D (eq_dec: dec_type A) (l l_ : list (A * B)) (l' : list (A * D))
                        (f : list (A * B) -> B -> C -> B)  g a b
                        (Hcontain: (forall ab, InT ab l -> InT ab l_)),
                   Dom_in_Dom l l' ->
                   (existsT d, MapsTo l' a d) ->
                   Dom_in_Dom (list_join eq_dec f g l_ a b l) l'.
Proof.
  intros A B C D eq_dec l l_ l' f g a b Hcontain Hdom Hex; inversion Hex as [d ? Hin]; induction Hdom as [|? ? ? ? Hex'].
  constructor; [exists d; apply MapsTo_In |constructor];auto.
  simpl; destruct (eq_dec a a0) as [Heq|Hneq]; subst; simpl;
  [constructor; [exists d; apply MapsTo_In|]; auto
  |inversion Hex' as [d' ? Hin']; constructor; [exists d'|]; auto].
  apply IHHdom; try solve [intros; apply Hcontain; right; auto|auto].
Qed.


Definition TraceTo {State} (R : State -> State -> Type) (s0 s1 : State) : Type :=
  existsT π, Trace s0 R (s1 :: π).

Definition step_all (s : CESKMΞ) : set CESKMΞ :=
  match s with
    | widemk (wshell (ev (var x) ρ σ) tκ t) M Ξ  =>
      match (lookup_ρ x ρ) with
       | None => empty_set _
       | Some a => singleton ceskmξ_eq_dec (widemk (wshell (co (adelay a) σ) tκ (tickmk s)) M Ξ)
      end
    | widemk (wshell (ev (app e0 e1) ρ σ) tκ t) M Ξ =>
      singleton ceskmξ_eq_dec (widemk (wshell (ev e0 ρ σ) (kpush (ar e1 ρ) tκ) (tickmk s)) M Ξ)
    | widemk (wshell (ev (lam x e) ρ σ) tκ t) M Ξ =>
      singleton ceskmξ_eq_dec (widemk (wshell (co (closure x e ρ) σ) tκ (tickmk s)) M Ξ)
    | widemk (wshell (co v σ) (kpush (ar e ρ) tκ) t) M Ξ =>
              singleton ceskmξ_eq_dec (widemk (wshell (ev e ρ σ) (kpush (fn v) tκ) (tickmk s)) M Ξ)
    | widemk (wshell (co v σ) (kpush (fn fnv) tκ) t) M Ξ =>
      (* Append forces *)
      fold_right (fun v acc =>
                    match v with
                        closure x e ρ => set_add ceskmξ_eq_dec
                                                 (widemk (wshell (ap x e ρ v σ) tκ (tickmk s)) M Ξ)
                                                 acc
                      | _ => acc
                 end)
                 (empty_set _)
                 (force σ fnv)
    | widemk (wshell (ap x e ρ v σ) tκ t) M Ξ =>
      let a := allocmk s in
      let ρ' := extend_ρ x a ρ in
      let σ' := σ_join σ a v in
      let t' := (tickmk s) in
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
      let t' := (tickmk s) in
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


Definition smush_steps (s : WCESKMΞ) (M: Memo) (Ξ: KTable) (S : set WCESKMΞ) : Wide_step :=
  (fix smush (ss : set CESKMΞ) (nexts : set WCESKMΞ) (M : Memo) (Ξ : KTable) :=
     match ss with
         nil => wide_step (filter (fun s => if In_dec wceskmξ_eq_dec s S then false else true) nexts) M Ξ
       | (widemk s M' Ξ')::ss' => smush ss' (set_add wceskmξ_eq_dec s nexts)
                                        (Ms_join M' M)
                                        (Ξs_join Ξ' Ξ)
     end)
    (step_all (widemk s M Ξ)) nil nil nil.

Theorem finite_steps : forall s, existsT ss : set CESKMΞ, forall s',
                          (red_ceskmk s s' -> InT s' ss) *
                          (InT s' ss -> red_ceskmk s s').
Proof.
  intro s; exists (step_all s); intro s'; split; [intro Hred|intro Hin].
  inversion_clear Hred; simpl; try solve [left; auto|
rewrite lookup_mapsto with (eq_dec := name_eq_dec) in H;
unfold lookup_ρ; rewrite H; constructor; auto].
Admitted.

Check smush_steps.

Inductive Wide_CESKMΞ : System -> System -> Type :=
  | big_step : forall s M Ξ Seen F ss M' Ξ',
                 (wide_step ss M' Ξ') = (smush_steps s M Ξ Seen) ->
                 Wide_CESKMΞ (**) (system Seen (s::F) M Ξ) (**)
                                  (system
                                  (set_union wceskmξ_eq_dec ss (set_add wceskmξ_eq_dec s Seen))
                                  (set_union wceskmξ_eq_dec F ss)
                                  M' Ξ').

Definition WCESKMΞ_trace (e : Expr) := Trace (system ((wshell (ev e nil nil) mt time0)::nil) ((wshell (ev e nil nil) mt time0)::nil) nil nil) Wide_CESKMΞ.

Inductive StackUnroll (Ξ : KTable) : Kont -> TrunKont -> Type :=
  unroll_mt : `{StackUnroll Ξ nil mt}
| unroll_push : forall κ tκ φ, StackUnroll Ξ κ tκ -> StackUnroll Ξ (φ :: κ) (kpush φ tκ)
| unroll_rt : forall ctx tκ κ,
                StackUnroll Ξ κ tκ ->
                in_ctxs Ξ ctx tκ ->
                StackUnroll Ξ κ (rt ctx).

Ltac textend_map := apply in_list_join2;solve [
                             intros; apply set_add_intro1T; auto
                            | intros; apply set_add_intro2T; auto 
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

Inductive Unroll_inv : KTable -> TrunKont -> Type :=
  unroll_inv : forall Ξ κ tκ,
                 StackUnroll Ξ κ tκ ->
                 (forall ctx tκ', in_ctxs Ξ ctx tκ' -> existsT κ', StackUnroll Ξ κ' tκ') ->
                 Unroll_inv Ξ tκ.

Lemma unrolling_inv : forall p p' tκ tκ' t t' M M' Ξ Ξ'
                             (Hstep : red_ceskmk (widemk (wshell p tκ t) M Ξ)
                                                 (widemk (wshell p' tκ' t') M' Ξ'))
                             (Hinv : Unroll_inv Ξ tκ),
                             Unroll_inv Ξ' tκ'.
Proof with auto.
  intros; inversion Hstep as [? ? ? ? ? (* <- time *) ? ? ? s0 Hmap Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? s0 Hpeq |
                      ? ? ? ? ? ? ? ? s0 Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? s0 Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? ? ? s0 Hin_force Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? ? s0 a ρ' σ' t0 ctx Ξ0 Hunmapped Hpeq Hs'eq |
                      ? ? ? ? ? ? ? ? ? ? ? ? ? s0 a ρ' σ' ctx Ξ0 Hin_memos Hpeq Hs'eq |
                      ? ? ? ? ? ? tκ0 s0 t0 M0 Hin_ctxs Hpeq Hs'eq];
  inversion Hinv as [? κ ? Hunroll HΞ];
  try solve [destruct s0; subst; apply unroll_inv with (κ := κ); auto
            |destruct s0; subst; apply unroll_inv with (κ := ((ar e1 ρ)::κ)); [constructor|];auto
            |destruct s0; subst; inversion Hunroll as [|κκ|]; subst; 
             solve [discriminate | apply unroll_inv with (κ := ((fn v)::κκ)); [constructor|];auto]
            |destruct s0; subst; inversion Hunroll as [|κκ|]; subst; 
             solve [discriminate | apply unroll_inv with (κ := ((fn fnv)::κκ)); [constructor|];auto]].
  (* fn -> ap *)
  destruct s0; inversion Hunroll as [|κκ|]; subst;
  solve [discriminate
        |inject_push; exists κκ; auto].
  (* unmemoized ap *)
  apply unroll_inv with (κ := κ);[
  apply unroll_rt with (tκ := tκ);
  [apply unroll_with_extension
  |apply in_list_join]; try solve [auto | intros; apply set_add_intro2T; auto]
    |].
  intros ctx_ tκ_ Hin_.
  destruct (in_list_join_set_split context_eq_dec trunkont_eq_dec) 
       with (l := Ξ) (l' := Ξ) (a := ctx) (a' := ctx_) (c := tκ) (c' := tκ_)
    as [[? ?]|S1]; auto;
  [exists κ; apply unroll_with_extension; subst tκ1 Ξ2 ctx_ tκ_; auto
  |assert (HΞneed : in_ctxs Ξ ctx_ tκ_) by (unfold in_ctxs; subst tκ1 Ξ2; auto);
    set (mer := (HΞ ctx_ tκ_ HΞneed)); inversion mer as [κ' ? Hκ'];
    exists κ'; apply unroll_with_extension; auto].
  (* memoized ap *)
  subst Ξ0 Ξ' Ξ2 tκ1 p p' t' tκ'.
  apply unroll_inv with (κ := κ);
    [apply unroll_with_extension
    |intros ctx_ tκ_ Hin_;
      destruct (in_list_join_set_split context_eq_dec trunkont_eq_dec) 
       with (l := Ξ) (l' := Ξ) (a := ctx) (a' := ctx_) (c := tκ) (c' := tκ_)
       as [[? ?]|S1]; auto;
    [subst tκ_; exists κ; apply unroll_with_extension
    |assert (HΞneed : in_ctxs Ξ ctx_ tκ_) by auto;
     set (mer := HΞ ctx_ tκ_ HΞneed); inversion mer as [κ' ? HH];
     solve [exists κ'; apply unroll_with_extension; auto
           |auto]]]; auto.
  (* return and memoize *)
  subst p p' tκ tκ' Ξ'.
  assert (HΞneed : in_ctxs Ξ ctx tκ0) by auto;
    set (mer := (HΞ ctx tκ0 HΞneed)); inversion mer as [κ' ? HH]; auto.
  apply unroll_inv with (κ := κ'); auto.
Qed.  

(* needs to be proof-relevant for an always-correct replacetail *)
Inductive KontTail : Kont -> Kont -> Type :=
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

Lemma kont_tailp_correct1 : forall κ κ',
                             kont_tailp κ κ' = true -> KontTail κ κ'.
Proof.
  induction κ'; simpl;
  [destruct (kont_eq_dec κ nil); intro H; subst; try solve [constructor
                                                           |inversion H; contradiction]
  |destruct (kont_eq_dec κ (a :: κ')) as [Heq|Hneq]; intro H; subst; try solve [constructor];
   apply IHκ' in H; constructor]; auto.
Qed.

Lemma kont_tailp_correct2 : forall κ κ',
                              KontTail κ κ' -> kont_tailp κ κ' = true.
Proof.
  induction κ'; simpl;
  [destruct (kont_eq_dec κ nil); intro H; subst; try solve [constructor
                                                                  |inversion H; contradiction]
  |destruct (kont_eq_dec κ (a :: κ')) as [Heq|Hneq]; intro H; subst; try solve [constructor];
   apply IHκ'; inversion H; subst; [contradict Hneq|]; auto].
Qed.

Lemma kont_tail_nil : `{KontTail nil κ}.
Proof. induction κ as [|φ κ_ IH]; constructor; auto. Qed.

Lemma kont_tail_cons : forall φ κ κ' (H : KontTail (φ::κ) κ'), KontTail κ κ'.
Proof.
  induction κ' as [|φ_ κ_ IH]; intros; inversion H; subst.
  apply push_tail; constructor.
  apply push_tail,IH; auto.
Qed.  

Lemma kont_tail_app : forall κ κ' κ'' (H : KontTail (κ ++ κ') κ''), KontTail κ' κ''.
Proof.
  induction κ as [|φ κ_ IH]; intros;
  simpl in H; auto.
  apply kont_tail_cons in H; apply IH; auto.
Qed.

Inductive hastail (κ : Kont) : list CESK -> Type :=
  Nil_tail : hastail κ nil
| Cons_tail : forall π p κ' t, hastail κ π -> KontTail κ κ' ->
                           hastail κ ((shell p κ' t) :: π).

(* Tail_replacement κorig κtail κreplacement κresult *)
Inductive Tail_replacement : Kont -> Kont -> Kont -> Kont -> Type :=
| tail_replacement : `{Tail_replacement κ κ κ'' κ''}
| push_replacement : `{Tail_replacement κ κ' κ'' κ''' ->
                       Tail_replacement (φ::κ) κ' κ'' (φ::κ''')}.

Lemma good_tailrep : forall κorig κtail κrep,
                       Tail_replacement (κorig++κtail) κtail κrep (κorig ++ κrep).
Proof.
  induction κorig as [|φ κ_ IH];
  intros;[simpl; constructor
         |].
  simpl; constructor; apply IH.
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

Inductive Good_Kont : Kont -> Kont -> Kont -> Type :=
  gkont : forall κ κ' κ'' κ''', replacetail_kont κ κ' κ'' =  Some κ''' -> Good_Kont κ κ' κ''.

Definition replacetail_kont_good : forall κ κ' κ'' (Htail : KontTail κ' κ), Good_Kont κ κ' κ''.
induction κ as [|φ κ_ IH]; intros;
[exists κ''; inversion Htail; subst; simpl; reflexivity
|inversion Htail as [|? ? ? Htail']; subst;
  [(* tail base case: κ = κ' *) exists κ''; unfold replacetail_kont; split_refl kont_eq_dec (φ :: κ_)
  |destruct (kont_eq_dec (φ :: κ_) κ') as [Heq | Hneq];
    [subst; exists κ''; unfold replacetail_kont; split_refl kont_eq_dec (φ :: κ_)
    |set (mumble := IH κ' κ'' Htail');
      inversion mumble as [? ? ? κ''' Heq]; subst;
      exists (φ :: κ'''); unfold replacetail_kont; split_refl2 kont_eq_dec (φ :: κ_) κ'; fold replacetail_kont; rewrite Heq]; auto]].
Defined.

Definition replacetail_state (s : CESK) (κ' κ'' : Kont) :=
  match s with
      shell p κ t => match replacetail_kont κ κ' κ'' with
                         None => None
                       | Some κ_ => Some (shell p κ_ t)
                     end
  end.

Lemma replacetail_state_good : forall s κ' κ'' (Htail : match s with shell p κ t => KontTail κ' κ end),
                                 existsT s', replacetail_state s κ' κ'' = Some s'.
Proof.
  intros; destruct s as [p κ t]; set (good := replacetail_kont_good κ'' Htail);
  inversion good as [? ? ? κ''' Hgood]; subst;
  exists (shell p κ''' t);
  unfold replacetail_state; rewrite Hgood; auto.
Qed.

Fixpoint replacetail (π : list CESK) (κ' κ'' : Kont) : list (option CESK) :=
  match π with
      nil => nil
    | ς :: π' => (replacetail_state ς κ' κ'') :: (replacetail π' κ' κ'')
  end.

Theorem replacetail_good : forall (π : list CESK) (κ' κ'' : Kont) (Htail : hastail κ' π),
  existsT (π' : list CESK), (replacetail π κ' κ'') = (map (@Some CESK) π').
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

(*
Require Import Setoid.


Lemma no_longer_tail_replacement : forall κ κ' κ'' κmore,
                                     length κmore > 0 ->
                                     ~ Tail_replacement κ (κmore ++ κ) κ' κ''.
Proof.
  induction κ as [|φ κ_].
  intros; intro bad; inversion bad; rewrite app_nil_r in H2; contradict H; subst; simpl; omega.
  intros; intro bad; inversion bad; subst.
  apply no_circular_app in H2; [contradiction|assumption].
  assert (~ Tail_replacement κ_ ((κmore ++ [φ]) ++ κ_) κ' κ''').
  apply IHκ_ with (κmore := κmore ++ [φ]).
  rewrite app_length; omega.
  rewrite app_assoc_reverse in H0; simpl in H0; contradiction.
Qed.

Lemma no_longer_tail_replacement2 : forall κ κ' κmore,
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

Lemma replace_is_replacement : forall κ κ' κ'' κ''',
                       (Tail_replacement κ κ' κ'' κ''' <-> replacetail_kont κ κ' κ'' = Some κ''').
Proof.
  induction κ as [|φ κ_ IH];
  [(* base case *)
  intros; inversion H; subst; split; intro H'; inversion H'; subst; simpl; constructor; auto
  |
  intros; inversion H; subst; split; intro H';
  [(* inversion case 1, first split *)
  inversion H' as [| foo bar baz qux boo baa]; subst; unfold replacetail_kont; split_refl kont_eq_dec (φ :: κ_);
    inversion baa; [match goal with [B : ?k = ?f :: ?k |- _] => apply no_circular_cons in B; contradiction end
                 |subst;apply no_longer_tail_replacement with (κmore := [φ]) in baa; [contradiction|simpl;omega]]
  (* second split *)
  |unfold replacetail_kont in H'; split_refl kont_eq_dec (φ :: κ_);
  injection H'; intros; subst; constructor; auto
  (* inversion case 2, first split *)
  |inversion H'; subst;
   [unfold replacetail_kont; split_refl kont_eq_dec (φ0 :: κ'0)
   |rewrite IH in H6;
   apply kont_tail_cons in H; auto]
  |]].

  unfold replacetail_kont; fold replacetail_kont; rewrite H6;
  destruct (kont_eq_dec (φ :: κ_) (φ0 :: κ'0)) as [Heq | Hneq];
    [inversion H0; subst;
     [apply no_circular_app with (l := [φ0]) in Heq; [contradiction|simpl;omega]
     |injection Heq; intros; subst;
      assert (bad : replacetail_kont (φ1 :: κ') (φ0 :: φ1 :: κ') κ'' = None) by
          (apply no_longer_tail_replacement2 with (κmore := [φ0]); simpl; auto);
      rewrite bad in H6; discriminate]
    |auto].

  unfold replacetail_kont in H'; fold replacetail_kont in H'.
  destruct (kont_eq_dec (φ :: κ_) (φ0 :: κ'0)) as [Heq | Hneq];
    [injection H'; injection Heq; intros; subst; constructor
    |].
  
  assert (R : exists κ''_, (replacetail_kont κ_ (φ0 :: κ'0) κ'') = Some κ''_).
  destruct (replacetail_kont κ_ (φ0 :: κ'0) κ'') as [κ''_|];
    [injection H';intros;subst; exists κ''_; auto
    |discriminate].
  destruct R as [κ''_ repeq].
  assert (R' : φ :: κ''_ = κ''').
  destruct (replacetail_kont κ_ (φ0 :: κ'0) κ'') as [κ''__|];
    [injection H'; injection repeq; intros; subst; auto
    |discriminate].
  rewrite <- R'.
  apply push_replacement.
  rewrite <- IH in repeq; [| apply kont_tail_cons in H]; auto.
Qed.
*)  

Inductive ctx_of : TrunKont -> Context -> Type :=
  | push_ctx : `{ctx_of tκ ctx -> ctx_of (kpush φ tκ) ctx}
  | rt_ctx : `{ctx_of (rt ctx) ctx}.

Definition ctx_in_dom (Ξ : KTable) (tκ : TrunKont) :=
  forall ctx : Context, `{ctx_of tκ ctx -> (existsT κs, InT (ctx,κs) Ξ)}.

Inductive Tailed_Trace : forall (κ : Kont) (p : CES_point) (t : Time) (p' : CES_point) (t' : Time), Type :=
  tailt : `{Trace (shell p κ t)
                  red_cesk
                  ((shell p' κ t') :: π)
            -> (hastail κ' π) -> Tailed_Trace κ p t p' t'}.

Definition Context_inv :=
  (fun p tκ M Ξ ctx =>
     match ctx with
         context e ρ σ t =>
         forall tκ',
             exists κ',
               StackUnroll Ξ κ' tκ'
               /\
               (* seems false now... *)
               (forall κ,
                  StackUnroll Ξ κ tκ ->
                  (exists t', TraceTo red_cesk
                                      (shell (ev e ρ σ) κ' t')
                                      (shell p κ t)))
               /\
             (forall v σ'' t',
                in_memos M (context e ρ σ t) (res v σ'' t') ->
                forall κ_irrelevant, Tailed_Trace κ_irrelevant (ev e ρ σ) t (co v σ'') t')
  end).

(* prove option versions save with hastail so this goes through *)

Lemma step_push_replace : forall p κ t p' φ t' κ' κ'' κ'''
                                 (Hstep : red_cesk (shell p κ t) (shell p' (φ :: κ) t'))
                                 (Hrep : replacetail_kont κ κ' κ'' = Some κ'''),
                          red_cesk (shell p κ''' t) (shell p' (φ :: κ''') t').
Proof.
  intros; inversion Hstep;
  try solve [match goal with [bad : ?κ = ?φ :: ?κ |- _] => apply no_circular_cons in bad; auto; contradiction end
            |match goal with [bad : ?κ = ?φ :: ?φ0 :: ?κ |- _] =>
                             apply no_circular_app with (l := [φ; fn fnv]) in bad; [contradiction|simpl;omega] end].
  (* app push *)
  subst; apply ev_app.
Qed.  

Lemma step_ε_replace : forall p κ t p' t' κ' κ'' κ'''
                              (Hstep : red_cesk (shell p κ t) (shell p' κ t'))
                              (Hrep : replacetail_kont κ κ' κ'' = Some κ'''),
                          red_cesk (shell p κ''' t) (shell p' κ''' t').
Proof.
  intros; inversion Hstep;
  try solve [match goal with [bad : ?κ = ?φ :: ?κ |- _] => apply no_circular_cons in bad; auto; contradiction end
            |match goal with [bad : ?φ :: ?κ = ?κ |- _] => symmetry in bad; apply no_circular_cons in bad; auto; contradiction end
            |subst p κ t p' t'; constructor; auto].
Qed.
  
Lemma step_pop_replace : forall p κ t p' φ t' κ' κ'' κ'''
                                 (Hstep : red_cesk (shell p (φ :: κ) t) (shell p' κ t'))
                                 (Hrep : replacetail_kont κ κ' κ'' = Some κ'''),
                          red_cesk (shell p (φ :: κ''') t) (shell p' κ''' t').
Proof.
  intros; inversion Hstep;
  try solve [match goal with [bad : ?φ :: ?κ = ?κ |- _] => symmetry in bad; apply no_circular_cons in bad; auto; contradiction end
            |match goal with [bad : ?φ :: ?φ0 :: ?κ = ?κ |- _] =>
                             symmetry in bad; apply no_circular_app with (l := [ar e1 ρ; φ0]) in bad; [contradiction|simpl;omega] end
            |constructor; auto].
Qed.

Inductive Stack_Action : Kont -> Kont -> Type :=
  push_action : forall κ φ, Stack_Action κ (φ :: κ)
| ε_action : forall κ, Stack_Action κ κ
| pop_action : forall φ κ, Stack_Action (φ :: κ) κ
| exchange_action : forall φ φ' κ, Stack_Action (φ :: κ) (φ' :: κ).

Lemma step_push_ε_pop : forall p p' κ κ' t t'
                               (Hstep : red_cesk (shell p κ t) (shell p' κ' t')),
                          Stack_Action κ κ'.
Proof.
  intros; inversion Hstep;
  [(* var: ε *)apply ε_action
  |(* app: push (ar e1 ρ) *)apply push_action
  |(* lam: ε *)apply ε_action
  |(* co_ar: exchange *)apply exchange_action
  |(* fn -> ap: pop (fn v) *)apply pop_action
  |(* ap : ε *)apply ε_action].
Qed.

Lemma step_replace : forall p p' κ κ' t t' κtail κrep κres
                            (Hstep : red_cesk (shell p κ t) (shell p' κ' t'))
                            (Hrep : replacetail_kont κ κtail κrep = Some κres),
                       match (step_push_ε_pop Hstep) with
                           push_action κ φ => red_cesk (shell p κ t) (shell p' (φ :: κ) t')
                         | ε_action κ => red_cesk (shell p κ t) (shell p' κ t')
                         | pop_action φ κ => red_cesk (shell p (φ :: κ) t) (shell p' κ t')
                         | exchange_action φ φ' κ => red_cesk (shell p (φ :: κ) t) (shell p' (φ' :: κ) t)
                       end.
                     

Lemma stack_irrelevance : forall p κ t π κ' κ''
                                 (orig : Trace (shell p κ t) red_cesk π)
                                 (tail0 : KontTail κ' κ)
                                 (Htail : hastail κ' π),
                            exists (s : CESK) (π' : list CESK),
                              (replacetail_state (shell p κ t) κ' κ'') = Some s /\
                              (replacetail π κ' κ'') = (map (@Some CESK) π') /\
                              Trace s red_cesk π'.
Proof.
  intros; set (use:=replacetail_kont_good κ'' tail0); inversion use as [? ? ? κ_ H_]; subst.
  exists (shell p κ_ t);
  induction orig as [|s0 π0 s1 HT ? Hstep].
  (* Initial *)
  exists [(shell p κ_ t)]; repeat split;
  [unfold replacetail_state; rewrite H_
  |simpl; rewrite H_
  |constructor]; auto.
  (* Step *)
  inversion Htail as [|? pt κt tt Htail' κtail];
  set (useκ := replacetail_kont_good κ'' κtail); inversion useκ as [? ? ? κt_ Ht_]; subst;
  destruct (IHorig Htail') as [π' [Hreps [Hrep HT']]];
  rewrite Hreps;
  destruct π' as [|[pr κr tr] π''];
   [inversion HT'
   |simpl in Hrep; injection Hrep; intros Hrep0 Hrep1; subst;
    exists ((shell pt κt_ tt) :: (shell pr κr tr) :: π'');
    repeat split;
    [simpl; rewrite Ht_; f_equal|constructor];auto].
  destruct s0 as [pr' κb tr'].
  assert (Hκrep : replacetail_kont κb κ' κ'' = Some κr) by
    (simpl in Hrep1; destruct (replacetail_kont κb κ' κ'');[injection Hrep1; intros; subst; auto|discriminate]).
  simpl in Hrep1; destruct (replacetail_kont κb κ' κ''); [injection Hrep1; intros; subst; clear Hrep1|discriminate].
  inversion Hstep;
    try solve [apply step_push_replace | apply step_pop_replace | constructor; auto].

as [x ρ σ κs tx (* <- time *) a s Hmap Hpeq Hs'eq | (* var *)
                      e0 e1 ρ σ κs ta s Hpeq | (* app *)
                      x e ρ σ κs tl s Hpeq Hs'eq | (* lam *)
                      v σ e ρ κs s Hpeq Hs'eq | (* arg *)
                      v σ fnv κs tf s Hin_force Hpeq Hs'eq | (* fn -> ap *)
                      x e ρ v σ κs ts s a ρ' σ' Hpeq Hs'eq].
  exists ((shell (co (adelay a) σ) κt_ (tick s1)) :: π'); repeat split.
  Focus 2.
  
  try solve [simpl in *; rewrite Ht_, Hrep; auto | auto].
  simpl in *; rewrite Ht_, <- Hrep; unfold replacetail_state. rewrite Ht_; auto.
  simpl in Hrep; rewrite <- Hrep.
  unfold replacetail_state.
  simpl in *. rewrite Ht_; auto.
  exists ((shell pt κt_ tt) :: π'); repeat split; auto.

  inversion HT' as [|foo bar baz qux moo boo]; subst.
  
  exists (
  set (last:=replacetail_kont_good κ'' κtail); inversion last as [? ? ? κs_ Hs_];
  exists ((shell pt κs_ tt) :: π'); repeat split;
   [simpl in *; rewrite Hs_, Hrep; auto
   |subst].
  apply initial.
  inversion Hstep as [x ρ σ κs tx (* <- time *) a s Hmap Hpeq Hs'eq | (* var *)
                      e0 e1 ρ σ κs ta s Hpeq | (* app *)
                      x e ρ σ κs tl s Hpeq Hs'eq | (* lam *)
                      v σ e ρ κs s Hpeq Hs'eq | (* arg *)
                      v σ fnv κs tf s Hin_force Hpeq Hs'eq | (* fn -> ap *)
                      x e ρ v σ κs ts s a ρ' σ' Hpeq Hs'eq];

  (* var *)
  exists (s1 
  cofix; intros; inversion orig as [Heq|ς H].
  subst π.
  inversion Htail as [|? ? ? ? Htail' κtail']; subst.
(*  set (repd := replacetail_kont κ κ' κ''). *)
  set (repd_eq := replacetail_kont_good κ'' κtail').
  inversion repd_eq as [? ? ? κ''' Heq].
  assert (seq : replacetail_state (shell p κ t) κ' κ'' tail0 = (shell p κ''' t)).
  simpl; f_equal; auto.
  subst.
  destruct (replacetail_kont_good κ'' tail0).
  rewrite Heq.
  apply initial with (s0 := (replacetail_state (shell p κ t) κ' κ'' tail0)).

Inductive Inv : CESKMΞ -> Type :=
  inv : forall p tκ t M Ξ ctx,
          Dom_in_Dom M Ξ ->
          ctx_in_dom Ξ tκ ->
          ctx_of tκ ctx ->
          (Context_inv p tκ t M Ξ ctx) ->
          (forall ctx', (exists κs, InT (ctx',κs) Ξ) -> Context_inv p tκ t M Ξ ctx')
           ->
          Inv (widemk (wshell p tκ t) M Ξ).

Axiom comparable_ticks : forall p κ tκ t M Ξ,
                           StackUnroll Ξ κ tκ ->
                           tick (shell p κ t) = tickmk (widemk (wshell p tκ t) M Ξ).

Lemma inv_invariant : forall s s', Inv s -> red_ceskmk s s' -> Inv s'.
Proof.
  intros s s' Hinv Hstep.
  inversion Hinv as [? ? ? ? ? [ce cρ cσ] Hdom tκctx ctxdom Hctx Φ]; subst.
  Ltac doinvert Un κ tκ φ H ctx Hin :=
    inversion Un as [|κ tκ φ H|ctx tκ κ H Hin];
    try (set (ctx := (context (var 0) (@nil (Name * Addr)) (@nil (Addr * AbsVal))));
         set (Hin := 0)).
  Ltac noinvert Un κ tκ φ H ctx Hin := set (κ := (@nil Frame));
                                       set (tκ := mt);
                                       set (φ := (ar (var 0) (@nil (Name * Addr))));
                                       set (H := 0);
                                       set (ctx := (context (var 0) (@nil (Name * Addr)) (@nil (Addr * AbsVal))));
                                       set (Hin := 0).
  Ltac part1 ctx tκctx := apply (inv _ _ (ctx := ctx)); try solve [apply unroll_push; auto
                           |repeat constructor; auto
                           |auto
                           |apply Dom_join_left; firstorder
                           |apply Dom_join_right; firstorder
                           |intros blah blorg; apply tκctx; inversion blorg; subst; auto
                           |inversion Hctx; subst; try solve [discriminate
                                                              |constructor; auto
                                                             |auto]].
  inversion Hstep as [? ρ σ ? ? (* <- time *) ? ? ? s0 Hmap Hpeq Hs'eq | (* var *)
                      ? ? ρ σ ? ? ? ? ? Hpeq | (* app *)
                      ? ? ρ σ ? ? ? ? s0 Hpeq Hs'eq | (* lam *)
                      ? ? σ ? ? ? ? ? s0 Hpeq Hs'eq | (* arg *)
                      ? ? σ ? ? ? ? ? ? ? s0 Hin_force Hpeq Hs'eq | (* fn -> ap *)
                      ? ?  ? ? ? ? ? ? s0 a ρ' σ' ctx' Ξ' Hunmapped Hpeq Hs'eq | (* call unmemo'd *)
                      ? ? ? ? ? ? ? ? ? ? ? s0 a ρ' σ' ctx' Ξ' Hin_memos Hpeq Hs'eq | (* call memo' *)
                      ? ? ? ? ? ? tκ' s0 M' Hin_ctxs Hpeq Hs'eq]. (* return *)
  Ltac solve_inner point t reach :=
    let tκ' := fresh "tκ'" in
    let cκ := fresh "cκ" in
    let cunroll := fresh "cunroll" in
    let creach := fresh "creach" in
    let cmemo := fresh "cmemo" in
    let t'_ := fresh "t'_" in
    let π := fresh "π" in
    let chκ := fresh "chκ" in
    let cH := fresh "cH" in
    split; [assumption
           |split;[intros chκ cH; destruct (reach chκ) as [t'_ [π ?]];
                   try solve [auto | constructor; auto];
                   exists t'_;
                   exists (Cons (shell point chκ t) π);
                   constructor; [assumption
                                |compute; rewrite <- comparable_ticks with (κ := chκ);
                                 solve [repeat constructor; auto | auto]]
                  |]];
    repeat constructor; auto.
  (* Var lookup *)
  subst; part1 (context ce cρ cσ) tκctx. 
  intro tκ'; destruct (Hctx tκ') as [cκ [cunroll [creach cmemo]]];
  exists cκ; solve_inner (ev (var x) ρ σ) t creach.
  intros [cce ccρ ccσ] ccH; pose (Φinst := Φ (context cce ccρ ccσ) ccH); simpl in Φinst.
  intro tκ'; destruct (Φinst tκ') as [κ' [un' [reach' memo']]];
  exists κ'; solve_inner (ev (var x) ρ σ) t reach'.
  (* function eval *)
  subst; part1 (context ce cρ cσ) tκctx.
  intro tκ'; destruct (Hctx (kpush (ar e1 ρ) tκ')) as [cκ [cunroll [creach cmemo]]].
  exists cκ_;
    split; [assumption
           |split;[intros chκ cH
                                                            |]].
  destruct (creach ((ar e1 ρ)::cκ_)) as [t'_ [π ?]]
    inversion cH; subst; auto.
                   try solve [auto | constructor; auto];


 solve_inner (ev (app e0 e1) ρ σ) t creach.
  
  destruct ctx
  inversion Hctx; subst; try solve [discriminate
                                                              |constructor; auto
                                                             |auto].
 part2 Φ mumble t idκ; repeat split; auto.
    let κ_ := fresh "κ_" in
    let Hunroll_ := fresh "Hunroll_" in    
    repeat split; auto;
    intros κ_ Hunroll_;
    inversion Hunroll_ as [|κ__ ? ? Hu__|]; subst;
    destruct (mumble κ__) as [t'_ [π Φreach_path]]; auto;
    exists t'_;
        exists (Cons (shell (ev (app e0 e1) ρ σ) κ__ t) π);
        constructor; [assumption|
                      compute;
                        rewrite <- (comparable_ticks _ _ _ (κ := κ__));
                        solve [constructor; auto
                              |auto]].
  (* lam *)
  subst; part1; part2 Φ mumble t idκ; repeat split; auto.
    let κ_ := fresh "κ_" in
    let Hunroll_ := fresh "Hunroll_" in    
    repeat split; auto;
    intros κ_ Hunroll_;
    destruct (mumble κ_) as [t'_ [π Φreach_path]]; auto;
    exists t'_;
        exists (Cons (shell (ev (lam x e) ρ σ) κ_ t) π);
        constructor; [assumption|
                      compute;
                        rewrite <- (comparable_ticks _ _ _ (κ := κ_));
                        solve [constructor; auto
                              |auto]].  
  (* evaluated fn, now arg eval *)
    subst; part1; part2 Φ mumble t idκ; repeat split; auto;
    let κ_ := fresh "κ_" in
    let Hunroll_ := fresh "Hunroll_" in    
    repeat split; auto;
    intros κ_ Hunroll_;
    inversion Hunroll_ as [|κ__|]; subst;
    destruct (mumble ((ar e ρ)::κ__)) as [t'_ [π Φreach_path]];
      [constructor|];auto;
    exists t'_;
        exists (Cons (shell (co v σ) ((ar e ρ)::κ__) t) π);
        constructor; [assumption
                     |compute; rewrite <- (comparable_ticks _ _ _ (κ := ((ar e ρ)::κ__)));
                      solve [constructor; auto | auto]].
  (* fn -> ap *)
    subst; part1; part2 Φ mumble t idκ; repeat split; auto.
    let κ_ := fresh "κ_" in
    let Hunroll_ := fresh "Hunroll_" in    
    repeat split; auto;
    intros κ_ Hunroll_;
    destruct (mumble ((fn fnv)::κ_)) as [t'_ [π Φreach_path]];
    [constructor|]; auto;
    exists t'_;
        exists (Cons (shell (co v σ) ((fn fnv)::κ_) t) π);
        constructor; [assumption|
                      compute;
                        rewrite <- (comparable_ticks _ _ _ (κ := ((fn fnv)::κ_)));
                        solve [constructor; auto
                              |auto]].
  (* do unmemoized ap *)
    part1.
    constructor.
    destruct in_list_join with (eq_dec := context_eq_dec) (combine := κs_join) (base := κ_singleton)
                                                          (l := Ξ) (l' := Ξ) (a := ctx) (c := tκ)
                                                          as [κs [? ?]];
      [intros; apply set_add_intro2T
       |intros; simpl
       |
      |exists κs;apply MapsTo_In]; auto.    
    let e' := fresh "e'" in
    let ρ'' := fresh "ρ''" in
    let σ'' := fresh "σ''" in
    let tκ' := fresh "tκ'" in
    let κ' := fresh "κ'" in
    let Htκ' := fresh "Htκ'" in
    let Hunroll:= fresh "Hunroll" in
    intros e' ρ'' σ'' tκ' Htκ'.
    destruct (in_list_join_set_split context_eq_dec trunkont_eq_dec)
    with (l := Ξ) (l' := Ξ) (a := ctx) (a' := (context e' ρ'' σ'')) (c := tκ) (c' := tκ')
                  as [[? ?]|ble];
      [unfold in_ctxs in Htκ'; auto
      |(* considered context is the one we extended Ξ with *)
      subst ctx;
        match goal with [H : (context ?uu ?vv ?hh) = (context ?ww ?xx ?yy) |- _] =>
                        injection H; intros aaa bbb ccc; subst ww xx yy end
      |].
    inversion Hctx as [HH|? ? HH|? HH].
    (* mt case *)
    assert (R : tκ' = mt) by congruence; rewrite R.
    exists nil; repeat constructor; auto.
    subst p.
    pose (mar := Φ e ρ' σ' tκ').
    
    
match goal with [H' : mt = t
    destruct (Φ e ρ' σ' tκ0) as [stuff boo].
    injection H3; intros aaa bbb ccc; subst e' ρ'' σ''.
    
    [apply in_list_join2
      |
      |].

    

    Check in_list_join_split.
    destruct (in_list_join_split context_eq_dec κs_join κ_singleton) with
      (l := Ξ)
      (l' := Ξ)
      (a := ctx)
      (a' := (context e' ρ'' σ''))
      (c := tκ)
      (c' := tκ') as [S0|[S1|S2]]; auto.
    destruct (Φ e' ρ'' σ'' tκ' S0) as [κseen [seenunroll [seenreach seenmemo]]].
    exists κseen; repeat split;
    [apply unroll_with_extension
    |intros κreach reachunroll
    |]; auto.


; specialize seenreach with κreach
 [intros;  | ]; auto.
.: forall l l' a a' c c'
                             (Hcontain : (forall ab, InT ab l -> InT ab l')),
    
    destruct Φrinst as [κ' [Hunroll [Φreach Φmemo]]].
    exists (κfn1 κ').


 part2 Φ mumble t idκ; repeat split; auto.
  Focus 3.
  (* return and memoize *)
  inversion Htail as [| | ? ? ? Hunroll Hctxin]; subst;
  [discriminate
  |discriminate
  |match goal with [H : rt ?ctx0 = rt ctx |- _] => injection H; intros; subst end].
  destruct ctx as [e_ ρ_ σ_];
    destruct (Φ e_ ρ_ σ_ tκ' Hin_ctxs) as [κ' [? [? ?]]].

  apply (inv (κ := κ')); try solve [apply unroll_push; auto
                                  |constructor; auto
                                  |auto
                                  |apply Dom_join_left; firstorder].
  intros e'' ρ'' σ'' tκ'' Htκ'';
    pose (Φrinst := (Φ e'' ρ'' σ'' tκ'' Htκ''));
    destruct Φrinst as [κ'' [Hunroll' [Φreach Φmemo]]];
    exists κ'';
    destruct Φreach as [t'_ [π Φreach_path]];
    repeat split; [auto
                  |exists t'_|].

 solve [auto |
      (* reach *)
      exists t'_;
        exists (Cons (shell (co v σ) (rt (context e_ ρ_ σ_)) t) π);
        constructor; [assumption|
                      compute;
                        rewrite <- (comparable_ticks _ _ _ (κ := κ));
                        solve [constructor; auto
                              |auto]]
            |(* memo *) auto].
      part2 Φ point κ t.

  subst; common Φ κ' (co v σ) κ t.
  
  constructor.
  subst; common Φ κ (co v σ) (rt ctx) t.

  apply inv with (κ := κ); auto; subst.
  (* satisfy hyps of inv first *)
  apply Dom_join_right; auto.
  apply unroll_rt with (tκ := tκ); [apply unroll_with_extension; auto
                                   |apply in_list_join; solve [
                                                            intros; apply set_add_intro1T; auto
                                                          | intros; apply set_add_intro2T; auto 
                                                          | auto]];
  subst.
  intros e'' ρ'' σ'' tκ'' κ'' Htκ'' Hunroll'.
  destruct (in_list_join_split context_eq_dec
                               κs_join
                               κ_singleton
                               κs_join_extensive
                               Ξ
                               Ξ
                               ctx
                               tκ
                               (fun a b => b)
                               (a' := (context e'' ρ'' σ''))
                               (c' := tκ'')) as [Hctx|[Hctx|Hctx]];
    auto.
  (* first case: already there *)
  pose (Φrinst := (Φ e'' ρ'' σ'' tκ'' κ'' Hctx)).
    destruct Φrinst as [Φreach Φmemo];
    destruct Φreach as [t'_ [π Φreach_path]].
    
                               Ξ' (* l *)
                               Ξ' (* l' *)
                               ctx (* a *)
                               (context e'' ρ'' σ'') (* a' *)
                               tκ (* c *)
                               tκ'' (* c' *).
  (* unmemoized ap inv needs to split on ctx mapped before or is new *)
  part2 Φ (ap x e ρ v σ) κ t.
  inversion Htκ'' as [tκs [Hinp Hinr]].
  

  pose (Φparinst := (Φ e'' ρ'' σ'' tκ'' κ'' n'')).
  red in Hinp.
  pose (Φrinst := ).
    destruct Φrinst as [Φreach Φmemo];
    destruct Φreach as [t'_ [π Φreach_path]].


  part2 Φ (ap x e ρ v σ) κ t n.
  (* do memoized ap *)
  
  assert (Htail' : StackUnroll Ξ' κ tκ (ctx :: G)).
  apply unroll_with_extension with (G := G);[assumption|].
  apply sublist_extension with (l'' := [ ctx ]).
 with (G' := (set_add context_eq_dec ctx G)); try solve [auto | apply subset_refl].
  apply unroll_rt with (tκ := tκ); try solve [intro bad; inversion bad].
  unfold in_ctxs.
  apply in_list_join; auto;
  intros; apply set_add_intro2T; auto.
  pose (Φrinst := (Φ e ρ' σ' (rt ctx) κ' Htκ' Htail));
    destruct Φrinst as [Φreach Φmemo];
    destruct Φreach as [t'_ [π Φreach_path]].

Inductive state_rel : CESK -> System -> Type :=
  point_rel : `{StackUnroll Ξ κ κ' nil ->
                (InT (wshell p κ' t) Seen \/ InT (wshell p κ' t) F) ->
                state_rel (shell p κ t) (system Seen F M Ξ)}.

Theorem simulation : forall e s, CESK_trace e π -> exists s', state_rel s s' /\ WCESKMΞ_trace e π'.
Proof.
  intros e s π.


End NonStandardSemantics.
End NonStandardData.
End StandardSemantics.
End Data.