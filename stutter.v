Require Import List Relation_Definitions RelationClasses Structures.Equalities Morphisms.
Import ListNotations.
Generalizable All Variables.
Set Implicit Arguments.

Inductive PR_Trace {State} (s0 : State) (step : State -> State -> Type) : list State -> Type :=
  | pr_initial : PR_Trace s0 step [s0]
  | pr_take_step : `{PR_Trace s0 step (ς :: π) ->
                  step ς ς' ->
                  PR_Trace s0 step (ς' :: (ς :: π))}.
Lemma PR_trace_app : forall State (s0 s1 : State) π step
                         (T1 : PR_Trace s0 step (s1 :: π))
                         π'
                         (T2 : PR_Trace s1 step π'),
                       PR_Trace s0 step (π' ++ π).
Proof.
  intros; induction T2;[|constructor]; assumption.
Qed.

Section PropTrace.
Variables (State : Type) (step : State -> State -> Prop) (s0 : State).
Inductive Trace : list State -> Prop :=
  | initial : Trace [s0]
  | take_step : `{Trace (ς :: π) ->
                  step ς ς' ->
                  Trace (ς' :: (ς :: π))}.

Theorem trace_shape : forall π, Trace π -> exists π', π = π' ++ [s0].
Proof.
  intros ? HT; induction HT;[exists []|destruct IHHT as [π' Heq]; exists (ς' :: π'); simpl; f_equal]; auto.
Qed.

Inductive OnlyStep : State -> State -> Prop :=
  only_step_intro : forall s s', step s s' -> (forall s'', step s s'' -> s' = s'') -> OnlyStep s s'.

Inductive OnlyTrace : list State -> Prop :=
  | only_initial : OnlyTrace [s0]
  | only_step : forall ς ς' π, OnlyTrace (ς :: π) -> OnlyStep ς ς' -> OnlyTrace (ς' :: (ς :: π)).

Inductive TraceTo (s1 : State) : Type :=
  intro_traceto : forall π, Trace (s1 :: π) -> TraceTo s1.

Inductive TraceRed : (list State) -> (list State) -> Prop :=
  tr_eps : TraceRed nil [s0]
| tr_take_step : `{TraceRed π (ς :: π) -> step ς ς' -> TraceRed (ς :: π) (ς' :: ς :: π)}.

Inductive TraceRed_Stutter : (list (nat * State)) -> (list (nat * State)) -> Prop :=
  str_eps : forall n, TraceRed_Stutter nil [(n, s0)]
| str_stutter : forall n n' ς π, n' < n -> TraceRed_Stutter ((n, ς) :: π) ((n', ς) :: (n, ς) :: π)
| str_take_step : forall n n' ς π ς',
                   TraceRed_Stutter π ((n,ς) :: π) -> step ς ς' ->
                   TraceRed_Stutter ((n,ς) :: π) ((n',ς') :: (n,ς) :: π).

(* if not stuck, then all steps are the same *)
Definition deterministic_modulo (P : State -> Prop) : Prop :=
  forall s s', P s -> step s s' -> OnlyStep s s'.

End PropTrace.

Definition lift_prop_to_trace {State} (P : State -> Prop) : list State -> Prop :=
  fun π => Forall P π.

Lemma deterministic_upto : forall (State : Type) (P : State -> list State -> Prop)
                                  (Pprop : forall s0 s s' π, P s0 (s' :: s :: π) -> P s0 (s :: π))
  (step : relation State),
  (forall s, P s [s]) ->
  (forall s0,
     (forall π s s', OnlyTrace step s0 (s :: π) -> P s0 (s :: π) -> step s s' ->
                     (P s0 (s' :: s :: π) /\ OnlyTrace step s0 (s' :: s :: π))) ->
     forall π, Trace step s0 π -> P s0 π -> OnlyTrace step s0 π).
Proof.
  intros State P Pprop step Pinitial s0 Pstep π HT Pπ.
  induction HT as [|ς π ς' HT IH Hstep].
  constructor.
  apply Pprop in Pπ.
  destruct (Pstep π ς ς' (IH Pπ) Pπ Hstep); auto.
Qed.

Theorem determinism_iff_only_traces : forall State (step : relation State)
                                      (P : State -> Prop)
                                      (Pinv : forall s s', P s -> step s s' -> P s'),
                                        (forall s0 π, P s0 -> Trace step s0 π -> OnlyTrace step s0 π) <->
                                        deterministic_modulo step P.
Proof.
  intros; split;
  [intros onlyπ s s' Ps sRs';
    assert (StepT : Trace step s [s'; s]) by (repeat constructor; auto);
    specialize (onlyπ s [s'; s] Ps StepT);
    inversion onlyπ; subst
  |intros Hdet s0 π P0 HT;
    assert (invπ : Forall P π) by
       (induction HT; [|rewrite Forall_forall in IHHT]; auto;
        rewrite Forall_forall; intros ς_ Hin;
        inversion Hin as [Heq|Hrest];
        [subst; apply (Pinv ς);[apply IHHT; left|]|]; auto);
    rewrite Forall_forall in invπ;
    induction HT; constructor; [apply IHHT; intros ? ?; apply invπ; right
                               |apply Hdet;[apply invπ; right;left|]]]; auto.
Qed.

Theorem deterministic_tracered_iff_det_trace : forall State (step : relation State) (s0 : State)
                                                      (P : State -> Prop),
                                                      (forall s0, P s0 -> deterministic_modulo (TraceRed step s0) (lift_prop_to_trace P))
                                                      <->
                                                      deterministic_modulo step P.
Proof.
  intros; split; 
  [intros Hdet s s' Ps Hstep;
    assert (LP : lift_prop_to_trace P [s]) by (constructor; auto);
    assert (HT : TraceRed step s [s] [s'; s]) by (constructor; [constructor|]; auto);
    specialize (Hdet s Ps [s] [s'; s] LP HT);
    inversion Hdet as [? ? HT' Heq]; subst;
    constructor; [|intros s'' Hstep']; auto;
    assert (Hneed : TraceRed step s [s] [s''; s]) by (constructor; [constructor|]; auto);
    specialize (Heq [s''; s] Hneed);
    injection Heq; intros; subst; auto
  |intros Hdet s Ps π π' Pπ HT].
  constructor;[|intros π'' HT']; auto.
  inversion HT; inversion HT'; subst; try solve [auto|discriminate].
  match goal with [H : cons ?x ?y = cons ?z ?w |- _] => injection H; intros; subst end.
  f_equal;
  rewrite Forall_forall in Pπ;
  match goal with [Hs : step ς ς' |- _] => specialize (Hdet _ _ (Pπ ς (or_introl (eq_refl _))) Hs); inversion Hdet as [? ? ? Heq]; subst; apply Heq; auto end.
Qed.
  
Lemma trace_app : forall State (s0 s1 : State) π step
                         (T1 : Trace step s0 (s1 :: π))
                         π'
                         (T2 : Trace step s1 π'),
                    Trace step s0 (π' ++ π).
Proof.
  intros; induction T2;[|constructor]; assumption.
Qed.

Inductive PR_TraceRed {State} (s0 : State) (step : State -> State -> Type) : (list State) -> (list State) -> Type :=
  pr_tr_eps : PR_TraceRed s0 step nil [s0]
| pr_tr_take_step : `{PR_TraceRed s0 step π (ς :: π) -> step ς ς' -> PR_TraceRed s0 step (ς :: π) (ς' :: ς :: π)}.

Lemma PR_trace_to_tracered : forall State (s0 : State) (step : State -> State -> Type) (π : list State)
                                 (HT: PR_Trace s0 step π),
                            match π return Type with
                              | nil => False
                              | s0_ :: nil => PR_TraceRed s0 step nil [s0_]
                              | s' :: s :: π => PR_TraceRed s0 step (s :: π) (s' :: s :: π)
                            end.
Proof.
  intros; induction HT; [|destruct π];constructor;auto.
Qed.  

Section SingleRel.
Variables (S : Type) (R : relation S) (step : relation S).
Variables (W : Type) (lew : relation W) (wfW : forall w : W, Acc lew w).
Variables (rankt : S -> S -> W) (rankl : S -> S -> S -> nat).

Notation "u '⋖' w" := (lew u w) (at level 70, right associativity).

Inductive StutterStep {s u w} (Hrel : R s w) (HstepA : step s u) : Prop :=
  step_B : forall v, step w v -> R u v -> StutterStep Hrel HstepA
| stutter_A : R u w -> rankt u w ⋖ rankt s w -> StutterStep Hrel HstepA
| stutter_B : forall v, step w v -> R s v -> rankl v s u < rankl w s u -> StutterStep Hrel HstepA.
End SingleRel.

Inductive Stutter {S} (R : relation S) (step : relation S) : Prop := 
  stutter_intro : forall W (lew: relation W) (wfW : forall w, Acc lew w) rankt rankl,
                    (forall s u w (Hrel : R s w) (HstepA : step s u), StutterStep R step lew rankt rankl Hrel HstepA)
                      -> Stutter R step.

Section Bisimulation.

Definition flip_rel {A B} (R : A -> B -> Prop) (b : B) (a : A) := R a b.
Hint Unfold flip_rel.

Variables (S : Type) (R : relation S) (step : relation S).
Definition Well_Bisim := Stutter R step /\ Stutter (flip_rel R) step.

Variables (W : Type) (lew : relation W) (wfW : forall w, Acc lew w).
Variables (erankt : S -> W) (erankl : S -> S -> nat) (equiv : Equivalence R).

Notation "u '⋖' w" := (lew u w) (at level 70, right associativity).

Inductive WEBStep {s u w} (Hrel : R s w) (HstepA : step s u) : Prop :=
  bstep_B : forall v, step w v -> R u v -> WEBStep Hrel HstepA
| bstutter_A : R u w -> erankt u ⋖ erankt s -> WEBStep Hrel HstepA
| bstutter_B : forall v, step w v -> R s v -> erankl v u < erankl w u -> WEBStep Hrel HstepA.
End Bisimulation.

Inductive WEB {S} (R : relation S) (step : relation S) : Prop := 
  web_intro : forall W (lew: relation W) (wfW : forall w, Acc lew w) erankt erankl
                     (equiv : Equivalence R),
                    (forall s u w (Hrel : R s w) (HstepA : step s u), WEBStep R step lew erankt erankl Hrel HstepA)
                      -> WEB R step.


Section SimRefinement.
Variables (S S' : Type) (step : relation S) (step' : relation S').
Inductive DisjRel : relation (S + S') :=
| step_l : forall s0 s1, step s0 s1 -> DisjRel (inl s0) (inl s1)
| step_r : forall s0' s1', step' s0' s1' -> DisjRel (inr s0') (inr s1').

Definition inj_rel (B : S -> S' -> Prop) : relation (S + S') :=
  fun ss'0 ss'1 =>
    match ss'0, ss'1 with
        inl s0, inr s1 => B s0 s1
      | _, _ => False
    end.

Definition Simulation_Refinement (r : S -> S') :=
  exists (B : S -> S' -> Prop), (forall s : S, B s (r s)) /\ Stutter (inj_rel B) DisjRel.

Definition WEB_Refinement (r : S -> S') :=
  exists (B : S -> S' -> Prop), (forall s : S, B s (r s)) /\ WEB (inj_rel B) DisjRel.

End SimRefinement.

Ltac flippy:=solve [auto | unfold flip_rel; symmetry; auto].
Theorem WEB_is_bisim : forall S (R : relation S) step (HWEB: WEB R step), Well_Bisim R step.
Proof.
  intros; inversion HWEB as [W lew wfW erankt erankl equiv Hinv];
  set (rankt := (fun (s u : S) => erankt s));
  set (rankl := (fun (s u w : S) => erankl s w));
  assert (subgoal : forall s u w (Hrel : R s w) (HstepA : step s u),
                       StutterStep R step lew rankt rankl Hrel HstepA)
         by
           (intros;
            pose (invinst := Hinv s u w Hrel HstepA);
            inversion invinst as [v | | v];
            [apply step_B with (v := v)
            |apply stutter_A
            |apply stutter_B with (v := v)]; auto);
  assert (subgoal' : forall s u w (Hrel : (flip_rel R) s w) (HstepA : step s u),
                       StutterStep (flip_rel R) step lew rankt rankl Hrel HstepA)
         by (intros;
             assert (Hrel' : R s w) by (symmetry; assumption);
             pose (invinst := Hinv s u w Hrel' HstepA);
             inversion invinst as [v| | v];
             [apply step_B with (v := v)
             |apply stutter_A
             |apply stutter_B with (v := v)]; flippy).
  split; [apply (stutter_intro wfW subgoal)
         |apply (stutter_intro wfW subgoal')].
Qed.