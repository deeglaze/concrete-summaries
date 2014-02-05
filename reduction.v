Require Import List Relation_Definitions Relation_Operators basic.
Import ListNotations.
Set Implicit Arguments.
Definition action_relation (S A : Type) := S -> A -> S -> Prop.

Section TraceClosures.

Inductive clos_refl_trans_action (S A : Type) (R : action_relation S A) : S -> S -> Prop :=
  rta_step : forall (x y z : S) (a : A),
               clos_refl_trans_action R x y ->
               R y a z -> clos_refl_trans_action R x z
| rta_refl : forall x, clos_refl_trans_action R x x.

Inductive direct_clos_refl_trans {A} (R : relation A) : A -> A -> Prop :=
  drt_refl : forall x, direct_clos_refl_trans R x x
| drt_step : forall x y z, direct_clos_refl_trans R x y ->
                         R y z ->
                         direct_clos_refl_trans R x z.


Inductive Idirect_clos_refl_trans {A} (R : relation A) (x : A) : A -> Prop :=
  idrt_refl : Idirect_clos_refl_trans R x x
| idrt_step : forall y z, Idirect_clos_refl_trans R x y ->
                         R y z ->
                         Idirect_clos_refl_trans R x z.

Ltac index_family istep step :=
  let H := fresh in
  intros; split; intro H; induction H; solve [constructor | eapply istep; eauto | eapply step; eauto].

Lemma drt_family_iff_index : forall A (R : relation A) x y,
                               direct_clos_refl_trans R x y <->
                               Idirect_clos_refl_trans R x y.
Proof.
  index_family @idrt_step @drt_step.
Qed.

Lemma drt_prepend : forall A (R : relation A) x y,
                      direct_clos_refl_trans R x y ->
                      forall w, R w x ->
                                       direct_clos_refl_trans R w y.
Proof.
  intros ? ? ? ? H; induction H; intros.
  eapply drt_step; [constructor|auto].
  eapply drt_step; [apply IHdirect_clos_refl_trans|]; auto.
Qed.
Lemma drt_append : forall A (R : relation A) x y,
                     direct_clos_refl_trans R x y ->
                     forall z,
                     direct_clos_refl_trans R y z ->
                     direct_clos_refl_trans R x z.
Proof.
  intros A R x y Hy; induction Hy; intros z' Hz.
  assumption.
  apply IHHy.
  apply drt_prepend with (x := z); auto.
Qed.

Lemma drt_non_direct : forall A (R : relation A) x y,
                         clos_refl_trans _ R x y <->
                         direct_clos_refl_trans R x y.

Proof.
  intros; split; intro H; induction H.
  eapply (drt_step y); [apply drt_refl|]; auto.
  apply drt_refl.
  apply (drt_append IHclos_refl_trans1 IHclos_refl_trans2).

  apply rt_refl.
  eapply (@rt_trans _ _ _ y z);[|apply rt_step]; auto.
Qed.

Section ActionTraces.
Variables (Q Γ : Type) (R : action_relation Q Γ) (Allow : list Γ -> Γ -> Prop).

Inductive clos_refl_trans_action_with_actions (actions0 : list Γ) : Q -> list Γ -> Q -> Prop :=
  rtaa_refl : forall x, clos_refl_trans_action_with_actions actions0 x [] x
| rtaa_step : forall (x y z : Q) actions (a : Γ),
                clos_refl_trans_action_with_actions actions0 x actions y ->
                R y a z ->
                Allow (actions0 ++ actions) a ->
                clos_refl_trans_action_with_actions actions0 x (actions ++ [a]) z.

(* use indexed families for different induction schemes *)
Inductive Iclos_refl_trans_action_with_actions (actions0 : list Γ) (x : Q) : list Γ -> Q -> Prop :=
  irtaa_refl : Iclos_refl_trans_action_with_actions actions0 x [] x
| irtaa_step : forall (y z : Q) actions (a : Γ),
                Iclos_refl_trans_action_with_actions actions0 x actions y ->
                R y a z ->
                Allow (actions0 ++ actions) a -> Iclos_refl_trans_action_with_actions actions0 x (actions ++ [a]) z.

Lemma rtaa_family_iff_index : forall actions0 x actions y,
                                clos_refl_trans_action_with_actions actions0 x actions y <->
                                Iclos_refl_trans_action_with_actions actions0 x actions y.
Proof.
  index_family irtaa_step rtaa_step.
Qed.

Lemma rtaa_head : forall actions0 x actions z, actions <> nil ->
                                      clos_refl_trans_action_with_actions actions0 x actions z ->
                                      match actions with
                                          nil => False
                                        | hd::tl => exists y, R x hd y /\ Allow actions0 hd /\ clos_refl_trans_action_with_actions (actions0 ++ [hd]) y tl z
                                      end.
Proof.
  intros ? ? ? ? ? Hpath; induction Hpath; [bad_eq|].
case_eq actions.
- intro Hnil; subst;
 inverts Hpath;[simpl; exists z; split; [assumption|constructor; [autorewrite with list in *; auto|constructor]]|destruct actions; discriminate].
- intros a' actions' Haceq; subst;
simpl.
destruct IHHpath as [y' [xRy' [Hallow' pathy']]]; [discriminate|].
exists y'; repeat split; try solve [assumption].
eapply rtaa_step; [eauto|assumption|rewrite app_assoc_reverse; auto].
Qed.

Lemma rtaa_prepend : forall actions0 x actions y,
                        forall a,
                          clos_refl_trans_action_with_actions (actions0 ++ [a]) x actions y ->
                          forall w, R w a x -> Allow actions0 a ->
                                    clos_refl_trans_action_with_actions actions0 w (a::actions) y.
Proof.
  intros ? ? ? Aprop a Hy; induction Hy as [|x y z actions' a' noo IH Hred Hallow']; intros w Hw Hallow.
  apply (@rtaa_step _ w w x [] a (rtaa_refl _ _) Hw); rewrite app_nil_r; assumption.
  pose (L := (@rtaa_step _ w y z (a::actions') a' (IH _ Hw Hallow) Hred)).
  apply L.
  rewrite app_assoc_reverse in Hallow'.
  auto.
Qed.

Definition Reassociate_allow {l l' l'' a} (P : Allow (l ++ l' ++ l'') a) : Allow ((l ++ l') ++ l'') a.
rewrite app_assoc_reverse; exact P.
Defined.

Lemma rtaa_append : forall actions0 x actions y,
                      clos_refl_trans_action_with_actions actions0 x actions y ->
                     forall (actions' : list Γ) z,
                       actions' <> nil ->
                       match actions' with
                           nil => False
                         | hd::_ => Allow (actions0 ++ actions) hd
                       end ->
                       clos_refl_trans_action_with_actions (actions0 ++ actions) y actions' z ->
                       clos_refl_trans_action_with_actions actions0 x (actions ++ actions') z.
Proof.
  intros ? ? ? ? Hy; induction Hy; intros actions' z' Hannil Hallow Hz.
  rewrite app_nil_r in Hz; assumption.
  rewrite app_assoc_reverse.
  apply IHHy.
  discriminate.
  auto.
  simpl.
  apply rtaa_prepend with (x := z); auto.
  rewrite app_assoc_reverse; auto.
Qed.

Inductive Sub_action_trace : 
  forall actions0 q actions q',
    clos_refl_trans_action_with_actions actions0 q actions q' ->
    forall actions1 s actions' s',
    clos_refl_trans_action_with_actions actions1 s actions' s' -> Prop :=
empty_subtrace : forall actions0 actions s s'
                        (H: clos_refl_trans_action_with_actions actions0
                                                                s
                                                                actions
                                                                s'),
                   Sub_action_trace
                     (rtaa_refl (actions0 ++ actions) s') H
|  step_subtrace :
     forall actions0π sπ actionsπ s'π
            (π : clos_refl_trans_action_with_actions actions0π sπ actionsπ s'π)
            actions0 s actions s' a s''
            (Hss' : clos_refl_trans_action_with_actions actions0 s actions s')
            (Hsub : Sub_action_trace π Hss')
            (Hstep : R s' a s'')
            (Hallow : Allow (actions0 ++ actions) a),
       Sub_action_trace π (rtaa_step Hss' Hstep Hallow)
| ext_subtrace :
    forall actions0' s actions s' actions0 s'' s'''
           (sπ : clos_refl_trans_action_with_actions (actions0 ++ actions0') s actions s')
           (π : clos_refl_trans_action_with_actions
                   actions0 s''' (actions0' ++ actions) s')
           a
           (Hstep : R s' a s'')
           (Hallow : Allow (actions0 ++ actions0' ++ actions) a),
      Sub_action_trace sπ π ->
      Sub_action_trace (rtaa_step sπ Hstep (Reassociate_allow Hallow)) (rtaa_step π Hstep Hallow).

Generalizable All Variables.
 Lemma subtrace_structure : `{forall (H : clos_refl_trans_action_with_actions
                                           actions0 s actions s')
                                    (H' : clos_refl_trans_action_with_actions actions0' s'' actions' s'''),
                               Sub_action_trace H H' ->
                               exists actionsL actionsR,
                                 actions' = actionsL ++ actions ++ actionsR /\
                                 actions0 = actions0' ++ actionsL}.
Proof.
  do 10 intro; intro Hsub; induction Hsub.
  exists actions, []; repeat split.
  rewrite app_nil_r; reflexivity.

  destruct IHHsub as [actionsL [actionsR [Leq Req]]]; subst.
  exists actionsL,(actionsR ++ [a]); split;[do 3 rewrite app_assoc|]; reflexivity.

  destruct IHHsub as [actionsL [actionsR [Leq Req]]]; subst.
  apply app_inv_head in Req; subst; apply app_inv_head in Leq.
  cut (actions ++ [] = actions ++ actionsR).
  intro H; apply app_inv_head in H; clear Leq;
  exists actionsL,[]; split;[autorewrite with list; rewrite app_assoc|];reflexivity.
  rewrite app_nil_r; auto.
Qed.
  
End ActionTraces.
End TraceClosures.

Hint Constructors direct_clos_refl_trans clos_refl_trans_action clos_refl_trans_action_with_actions.
