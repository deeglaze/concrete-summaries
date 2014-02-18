Require Import List ListSet basic Morphisms RelationClasses Equivalence.
Import ListNotations.

Section Definitions.

Definition union_fold {A B} (eq_dec : dec_type B) (f : A -> set B) (s : set A) (base : set B) : set B :=
  set_fold_left (fun acc a => set_union eq_dec acc (f a)) s base.
Definition union_map {A B} (eq_dec : dec_type B) (f : A -> set B) (s : set A) : set B :=
  union_fold eq_dec f s (empty_set _).

Definition triple_union_fold {A B C D}
           (Beq_dec : dec_type B) (Ceq_dec : dec_type C) (Deq_dec : dec_type D)
           (f : A -> (set B * set C * set D)) (l : set A) (base : set B * set C * set D) :
  (set B * set C * set D) :=
  set_fold_left
    (fun (acc : (set B * set C * set D)) (a : A) =>
               match acc with
                   (bs,cs,ds) =>
                   match f a with
                       (bs',cs',ds') =>
                       (set_union Beq_dec bs bs', set_union Ceq_dec cs cs', set_union Deq_dec ds ds')
                   end
               end)
    l base.

Definition triple_union_map {A B C D}
           (Beq_dec : dec_type B) (Ceq_dec : dec_type C) (Deq_dec : dec_type D)
           (f : A -> (set B * set C * set D)) (l : set A) : (set B * set C * set D) :=
  triple_union_fold Beq_dec Ceq_dec Deq_dec f l ((empty_set _),(empty_set _),(empty_set _)).
Definition Subset {A} (s s' : set A) := forall x, In x s -> In x s'.
Definition Set_equiv {A} (s s' : set A) := Subset s s' /\ Subset s' s.

Fixpoint dedup {A} (eq_dec : dec_type A) (s : set A) :=
  match s with
      nil => nil
    | a::s' => if set_mem eq_dec a s' then
                 dedup eq_dec s'
               else
                 a::(dedup eq_dec s')
  end.
Fixpoint set_remove_all {A} (eq_dec : dec_type A) (a : A) (s : set A) :=
  match s with
      nil => nil
    | a'::s' => if eq_dec a a' then
                  set_remove_all eq_dec a s'
                else
                  a'::(set_remove_all eq_dec a s')
  end.

End Definitions.

Global Program Instance subset_refl {A} : Reflexive (@Subset A).
Next Obligation.
intros y Hin; auto.
Qed.
Hint Immediate subset_refl.

Global Program Instance subset_trans {A} : Transitive (@Subset A).
Next Obligation. intros w Hin; apply H,H0 in Hin; assumption.
Qed.

Global Program Instance set_equiv_equiv {A} : Equivalence (@Set_equiv A).
Next Obligation.
intro; split; reflexivity.
Qed.
Next Obligation.
intros ? ? [? ?]; split; auto.
Qed.
Next Obligation.
intros ? ? ? [H ?] [H1 ?]; split; intros ? ?;[apply H1,H|]; auto.
Qed.

Section Facts.
Variables (A : Type) (Aeq_dec : dec_type A).

Lemma set_add_elim_LEM : forall (s : set A) a b, set_In a (set_add Aeq_dec b s) ->
                                                 (a = b /\ ~ set_In a s) \/ set_In a s.
Proof.
  intros s a ? H; destruct (set_add_elim _ _ _ _ H);
  [destruct (set_In_dec Aeq_dec a s)|]; auto.
Qed.

Theorem set_union_elim_LEM : forall (s s' : set A) a, set_In a (set_union Aeq_dec s s') ->
                                                      set_In a s \/
                                                      (set_In a s' /\ ~ set_In a s).
Proof.
  intros s ? a H; destruct (set_union_elim _ _ _ _ H);[|destruct (set_In_dec Aeq_dec a s)]; auto.
Qed.  

Lemma set_add_nodup : forall (s : set A) a, NoDup s -> NoDup (set_add Aeq_dec a s).
Proof.
  induction s as [|a' s IH]; intros; simpl;
  [constructor; [intro bad; inversion bad|constructor]
  |destruct (Aeq_dec a a');
    [|inversion H as [|? ? Hnin Hdup]; subst;
      specialize (IH a Hdup);
      constructor;
      [intro Hin; apply set_add_elim2 in Hin;[apply Hnin in Hin|]
      |]]]; auto.
Qed.

Lemma set_union_nodup : forall (s s' : set A), NoDup s -> NoDup (set_union Aeq_dec s s').
Proof.
  induction s'; intro nds; [|apply set_add_nodup];auto.
Qed.

Theorem set_remove_in : forall (s : set A) (a a' : A), set_In a (set_remove Aeq_dec a' s) -> set_In a s.
Proof.
  induction s as [|a_ s IH]; intros a a' H;
  [inversion H
  |simpl in H;
    destruct (Aeq_dec a' a_);
    [right; auto
    |inversion H; [subst; left|right; apply (IH a a')]; auto]].
Qed.

Theorem set_remove_all_in : forall (s : set A) (a a' : A), set_In a (set_remove_all Aeq_dec a' s) -> set_In a s.
Proof.
  induction s as [|a_ s IH]; intros a a' H;
  [inversion H
  |simpl in H;
    destruct (Aeq_dec a' a_);
    [subst; right; apply (IH a a_); auto
    |inversion H; [subst; left|right; apply (IH a a')]]]; auto.
Qed.

Theorem set_remove_all_neq : forall (s : set A) (a a' : A), set_In a (set_remove_all Aeq_dec a' s) -> a <> a'.
Proof.
  induction s as [|a_ s IH]; intros a a' H;
  [inversion H
  |simpl in H;
    destruct (Aeq_dec a' a_); [|inversion H];subst]; auto.
Qed.

Theorem set_remove_all_neq_in : forall (s : set A) (a a' : A), set_In a s -> a <> a' -> set_In a (set_remove_all Aeq_dec a' s).
Proof.
  induction s as [|a_ s IH]; intros a a' Hin Hneq;
  [inversion Hin
  |simpl;
    destruct (Aeq_dec a' a_);
    inversion Hin;
    subst; [bad_eq|apply IH |left |right; apply IH]]; auto.
Qed.

Theorem set_remove_all_notin : forall a (s : set A), ~ set_In a (set_remove_all Aeq_dec a s).
Proof.
  induction s; [intros bad; inversion bad
               |simpl; destruct (Aeq_dec a a0);
                [subst|intro bad; inversion bad; [subst;bad_eq|]]; auto].
Qed.

Global Program Instance set_union_respects : Proper (Set_equiv ==> Set_equiv ==> Set_equiv) (set_union Aeq_dec).
Next Obligation.
intros x y H0 z w H1; split; intros u Hin;
(destruct (set_union_elim Aeq_dec _ _ _ Hin);
[apply set_union_intro1, H0
|apply set_union_intro2, H1]; auto).
Qed.

Global Program Instance set_remove_all_respects : Proper ((@eq A) ==> Set_equiv ==> Set_equiv) (set_remove_all Aeq_dec).
Next Obligation.
intros ? ? Heq s s' [Sub Sub']; split; intros u Hin;
(subst;
cut (In u s');
  [cut (u <> y);
    [intros Hin' Hneq; apply set_remove_all_neq_in; try apply Sub'
    |apply (set_remove_all_neq _ _ _ Hin)]
  |apply set_remove_all_in in Hin; (apply Sub in Hin || apply Sub' in Hin)]; auto).
Qed.

Global Program Instance set_add_respects : Proper ((@eq A) ==> Set_equiv ==> Set_equiv) (set_add Aeq_dec).
Next Obligation.
  intros ? ? Heq s s' [Sub Sub']; subst; split; intros u Hin;
  (destruct (set_add_elim Aeq_dec _ _ _ Hin) as [|Hin'];
    [subst; apply set_add_intro2; reflexivity
    |(apply Sub in Hin' || apply Sub' in Hin'); apply set_add_intro1]; auto).
Qed.

Global Program Instance set_diff_respects : Proper (Set_equiv ==> Set_equiv ==> Set_equiv) (set_diff Aeq_dec).
Next Obligation.
intros u v [Subv Subu] s s' [Subs Subs']; split; intros x Hin;
(pose (need0 := set_diff_elim1 _ _ _ _ Hin);
pose (need1 := set_diff_elim2 _ _ _ _ Hin);
(apply Subv in need0 || apply Subu in need0);
((cut (~ In x s');[intro; apply set_diff_intro; auto|intro xs'; apply Subs' in xs'; contradiction])
||(cut (~ In x s);[intro; apply set_diff_intro; auto|intro xs'; apply Subs in xs'; contradiction]))).
Qed.

Theorem dedup_notin : forall (s : set A) a, ~ set_In a s -> ~ set_In a (dedup Aeq_dec s).
Proof.
  induction s; intros a' Hnin bad; [inversion bad|simpl in bad;case_eq (set_mem Aeq_dec a s); intro res; rewrite res in bad;[apply IHs in bad; [|intro bad'; apply Hnin; right]; auto|]].
inversion bad; [subst; apply Hnin; left; reflexivity|apply IHs in H; [|intro bad'; apply Hnin; right]]; auto.
Qed.

Theorem dedup_in : forall (s : set A) a, set_In a (dedup Aeq_dec s) -> set_In a s.
Proof.
  induction s; intros a' Hin; [inversion Hin|simpl in Hin].
  case_eq (set_mem Aeq_dec a s); intro res; rewrite res in Hin.
  apply IHs in Hin; right; auto.
  inversion Hin; [subst; left|apply IHs in H; right]; auto.
Qed.

Theorem in_dedup : forall (s : set A) a, set_In a s -> set_In a (dedup Aeq_dec s).
Proof.
  induction s; intros a' Hin; [inversion Hin|simpl].
  case_eq (set_mem Aeq_dec a s); intro res;
  [apply set_mem_correct1 in res; apply IHs;
   inversion Hin; subst; auto
  |inversion Hin; subst; [left|right; apply IHs]; auto].
Qed.

Theorem dedup_nodup : forall (s : set A), NoDup (dedup Aeq_dec s).
Proof.
  induction s;[constructor|simpl; case_eq (set_mem Aeq_dec a s);intro res;[auto|apply set_mem_complete1 in res]].
  apply dedup_notin in res; constructor; auto.
Qed.

Global Program Instance dedup_respects : Proper (Set_equiv ==> Set_equiv) (dedup Aeq_dec).
Next Obligation.
intros s s' [Subs Subs']; split; intros ? ?; apply in_dedup; [apply Subs|apply Subs']; apply dedup_in; auto.
Qed.

Theorem fold_left_nodup : forall B (f: set A -> B -> set A) (fprop : forall X b, NoDup X -> NoDup (f X b))
                                 (s : set B) (b : set A),
                            NoDup b -> NoDup (set_fold_left f s b).
Proof.
  induction s; intros b ndb;[|apply IHs, fprop]; auto.
Qed.

Theorem union_map_nodup : forall B (f : B -> set A) s, NoDup (union_map Aeq_dec f s).
Proof.
  intros; apply fold_left_nodup;
  [intros; apply set_union_nodup; auto
  |constructor].
Qed.

Theorem union_fold_base_subset : forall B (f: B -> set A) (s : set B) (base : set A),
                                   Subset base (union_fold Aeq_dec f s base).
Proof.
  induction s; intros b a' Hin.
  auto.
  simpl in *.
  apply IHs.
  apply set_union_intro1; auto.
Qed.

Theorem union_subset1 : forall {B} (Beq_dec : dec_type B) (s s' s'' : set B), Subset (set_union Beq_dec s s') s'' ->
                                                                              Subset s s''.
Proof.
  intros; intros x Hin; apply (set_union_intro1 Beq_dec _ _ s'),H in Hin; auto.
Qed.

Theorem union_subset2 : forall {B} (Beq_dec : dec_type B) (s s' s'' : set B), Subset (set_union Beq_dec s s') s'' ->
                                                                              Subset s' s''.
Proof.
  intros; intros x Hin; apply (set_union_intro2 Beq_dec _ _ s'),H in Hin; auto.
Qed.

Definition Triple_subset {A B C} (s s' : set A * set B * set C) : Prop :=
  match s,s' with
      (As,Bs,Cs),(As',Bs',Cs') => Subset As As' /\ Subset Bs Bs' /\ Subset Cs Cs'
  end.
Theorem triple_union_fold_base_subset : forall B C D (Beq_dec : dec_type B) (Ceq_dec : dec_type C)
                                               (f: D -> set A * set B * set C) (s : set D)
                                               (base : set A * set B * set C),
                                          Triple_subset base (triple_union_fold Aeq_dec Beq_dec Ceq_dec f s base).
Proof.
  induction s; intros [[Bas Bbs] Bcs].
  hnf; repeat split; reflexivity.
  simpl.
  specialize (IHs (let (p, ds') := f a in
          let (bs', cs') := p in
          (set_union Aeq_dec Bas bs', set_union Beq_dec Bbs cs',
          set_union Ceq_dec Bcs ds'))).
  destruct (f a) as [[bs' cs'] ds'].
  destruct (triple_union_fold Aeq_dec Beq_dec Ceq_dec f s
         (set_union Aeq_dec Bas bs', set_union Beq_dec Bbs cs',
         set_union Ceq_dec Bcs ds')) as [[As' Bs'] Cs'].
  destruct IHs as [X [Y Z]]; repeat split; solve [eapply union_subset1; eauto| eapply union_subset2; eauto].
Qed.

Theorem union_fold_subset_in : forall B (f: B -> set A) (s : set B) (base : set A) b,
                                 In b s -> Subset (f b) (union_fold Aeq_dec f s base).
Proof.
  induction s; intros base b Hin a' Hin'.
  inversion Hin.
  simpl in *.
  inversion Hin as [Heq|Hrest].
  subst; apply union_fold_base_subset,set_union_intro2; auto.
  apply (IHs (set_union Aeq_dec base (f a)) b Hrest); auto.
Qed.

Theorem triple_union_fold_subset_in : forall B C D
                                            (Beq_dec : dec_type B) (Ceq_dec : dec_type C)
                                            (f: D -> set A * set B * set C) (s : set D)
                                            (base : set A * set B * set C) d,
                                       In d s ->
                                       Triple_subset (f d) (triple_union_fold Aeq_dec Beq_dec Ceq_dec f s base).
Proof.
  induction s; intros base d Hin; inversion Hin; [subst|apply IHs; auto].

  case_eq (triple_union_fold Aeq_dec Beq_dec Ceq_dec f s
         (let (p, ds) := base in
          let (bs, cs) := p in
          let (p0, ds') := f d in
          let (bs', cs') := p0 in
          (set_union Aeq_dec bs bs', set_union Beq_dec cs cs',
          set_union Ceq_dec ds ds'))).
    intros [As' Bs'] Cs' peq.
    pose (L := triple_union_fold_base_subset).
    specialize (L _ _ _ Beq_dec Ceq_dec f s (let (p, ds) := base in
           let (bs, cs) := p in
           let (p0, ds') := f d in
           let (bs', cs') := p0 in
           (set_union Aeq_dec bs bs', set_union Beq_dec cs cs',
           set_union Ceq_dec ds ds'))).
    rewrite peq in L.
    simpl; rewrite peq.
    destruct base as [[bs cs] ds].
    destruct (f d) as [[a b] c].
    destruct L as [Asub [Bsub Csub]]; repeat split; solve [eapply union_subset1; eauto | eapply union_subset2; eauto].
Qed.

Theorem union_map_subset : forall B (f : B -> set A) s b, In b s -> Subset (f b) (union_map Aeq_dec f s).
Proof.
  intros; apply union_fold_subset_in; auto.
Qed.

Theorem triple_union_map_subset : forall B C D (Beq_dec : dec_type B) (Ceq_dec : dec_type C)
                                          (f : D -> (set A * set B * set C)) (s : set D) d,
                                    set_In d s ->
                                    Triple_subset (f d) (triple_union_map Aeq_dec Beq_dec Ceq_dec f s).
Proof.
  intros; apply triple_union_fold_subset_in; auto.
Qed.

Lemma in_set_ind : forall A (P : set A -> Prop),
                     P nil ->
                     forall s',
                       (forall s a, P s /\ In a s' /\ Subset s s' -> P (a :: s)) ->
                       P s'.
induction s'; intros; auto.
apply H0; split. apply IHs'; intros ? ? [? [? ?]]. apply H0; repeat split; [|right|intros x X; apply H3 in X;right]; auto.
(* Todo *)
split;[left|right];auto.
Qed.

Theorem union_folded_property : forall B (f : B -> set A) (P : A -> Prop) s base
                                       (fprop : forall b, set_In b s -> Forall P (f b)),
                                  Forall P base ->
                                  Forall P (union_fold Aeq_dec f s base).
Proof.
  intros ? ? ? s;
  apply (@in_set_ind _ (fun s =>
                     forall base (fprop : forall b, set_In b s -> Forall P (f b)),
                       Forall P base ->
                       Forall P (union_fold Aeq_dec f s base))).
  intros base fprop allbase; auto.
  intros s' a [IH [ains Hsub]] base fprop allbase.
  simpl; apply IH.
  intros b Hin; apply fprop; right; auto.
  rewrite Forall_forall; intros x Hin; apply set_union_elim in Hin.
  destruct Hin as [inbase|inf].
  rewrite Forall_forall in allbase; apply allbase; auto.
  specialize (fprop a (or_introl (eq_refl _))); rewrite Forall_forall in fprop; apply fprop; auto.
Qed.

(*
Inductive Forall3 {D B C} (P : D -> B -> C -> Prop) : list D -> list B -> list C -> Prop :=
  nil_forall3 : Forall3 P nil nil nil
| cons_forall3 : forall d b c Ds Bs Cs, Forall3 P Ds Bs Cs -> P d b c -> Forall3 P (d::Ds) (b::Bs) (c::Cs).

Fixpoint In3 {D B C} (d : D) (b : B) (c : C) (Ds : list D) (Bs : list B) (Cs : list C) : Prop :=
  length Ds = length Bs /\ length Bs = length Cs /\
  match Ds,Bs,Cs with
      d'::Ds,b'::Bs,c'::Cs => (d = d' /\ b' = b /\ c' = c) \/ (In3 d b c Ds Bs Cs)
    | nil,nil,nil => False
    | _,_,_ => True (* bad lists just make this meaningless *)
  end.
Fixpoint list3 {D B C} (Ds : list D) (Bs : list B) (Cs : list C) : Prop :=
  match Ds,Bs,Cs with
      d'::Ds,b'::Bs,c'::Cs => (list3 Ds Bs Cs)
    | _,_,_ => True
  end.
Functional Scheme in3_ind := Induction for list3 Sort Prop.

Theorem Forall3_forall : forall D B C (P : D -> B -> C -> Prop) (Ds : list D) (Bs : list B) (Cs : list C),
                           (Forall3 P Ds Bs Cs) <-> (length Ds = length Bs /\ length Bs = length Cs /\ forall d b c, In3 d b c Ds Bs Cs -> P d b c).
Proof.
  intros; split.
  intro H; induction H; repeat split.
  intros d b c Hin; inversion Hin.
  intuition.
  destruct IHForall3 as [len0 [len1 IH]]; simpl; auto.
  destruct IHForall3 as [len0 [len1 IH]]; simpl; auto.
  intros d' b' c' Hin.
  inversion Hin as [len0 [len1 [[dd [bb cc]]|Hrest]]].
  subst; auto.
  apply IHForall3; auto.
  apply (@in3_ind _ _ _ (fun Ds Bs Cs prp => prp -> length Ds = length Bs /\ length Bs = length Cs /\ (forall d b c, In3 d b c Ds Bs Cs -> P d b c) -> Forall3 P Ds Bs Cs)); intros; try solve [auto |contradiction|intuition; simpl in *; discriminate].
  subst; intuition; simpl in *;
  cut (Bs0 = []); [|destruct Bs0; [auto|discriminate]];
  intro;
  cut (Cs0 = []); [|destruct Cs0; [auto|subst; simpl in *; discriminate]];
  intros; subst; constructor.

  subst.
  destruct H1 as [? [? ?]].
  simpl in *.
  injects H2; injects H1.
  remember H3 as IH; clear HeqIH.
  specialize (H3 _x _x0 _x1 (conj H1 (conj H2 (or_introl (conj (eq_refl _x) (conj (eq_refl _x0) (eq_refl _x1))))))).
  constructor; auto.
  apply H; auto.
  repeat split; auto.
  revert Bs Cs.
  induction Ds; simpl; [auto|];
  induction Bs; simpl; [auto|];
  induction Cs; simpl; [auto|];
  apply IHDs.
Qed.
*)
Theorem triple_union_folded_property : forall B C D (Beq_dec : dec_type B) (Ceq_dec : dec_type C)
                                              (f : D -> set A * set B * set C)
                                              (PA : A -> Prop) (PB : B -> Prop) (PC : C -> Prop) s
                                              (base : set A * set B * set C)
                                              (fprop : forall d, set_In d s -> match (f d) with (As,Bs,Cs) => Forall PA As /\ Forall PB Bs /\ Forall PC Cs end),
                                         match base with (As,Bs,Cs) => Forall PA As /\ Forall PB Bs /\ Forall PC Cs end  ->
                                         (match (triple_union_fold Aeq_dec Beq_dec Ceq_dec f s base) with
                                              (As,Bs,Cs) => Forall PA As /\ Forall PB Bs /\ Forall PC Cs end).
  intros ? ? ? ? ? ? ? ? ? s;
  apply (@in_set_ind _ (fun s => forall (base : set A * set B * set C)
                                              (fprop : forall d, set_In d s -> match (f d) with (As,Bs,Cs) => Forall PA As /\ Forall PB Bs /\ Forall PC Cs end),
                                         match base with (As,Bs,Cs) => Forall PA As /\ Forall PB Bs /\ Forall PC Cs end  ->
                                         (match (triple_union_fold Aeq_dec Beq_dec Ceq_dec f s base) with
                                              (As,Bs,Cs) => Forall PA As /\ Forall PB Bs /\ Forall PC Cs end))).
  auto.
  intros s' a IH base fprop allbase.
  simpl; apply IH.
  intros d Hin; apply fprop; right; auto.
  destruct base as [[ds bs] cs].
  case_eq (f a); intros [bs' cs'] ds' Heq.
  repeat rewrite Forall_forall; repeat split; intros x Hin;
  specialize (fprop a (or_introl (eq_refl _)));
  rewrite Heq in fprop;
  repeat rewrite Forall_forall in *;
  apply set_union_elim in Hin; destruct Hin as [inbase|inf];
  try solve [apply allbase; auto|apply fprop;auto].
Qed.

Theorem length_add : forall s a, ~ set_In a s -> length (set_add Aeq_dec a s) = S (length s).
Proof.
  induction s as [|a s IH]; intros a' H;
  [|simpl;
     destruct (Aeq_dec a' a);
     [subst; elimtype False; apply H; left
     |simpl; f_equal; apply IH; intro bad; apply H; right]]; auto.
Qed.

End Facts.