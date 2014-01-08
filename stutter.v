Require Import List Relation_Definitions RelationClasses Structures.Equalities Morphisms.
Import ListNotations.
Generalizable All Variables.
Set Implicit Arguments.

Inductive Trace {State} (s0 : State) (step : relation State) : list State -> Prop :=
  | initial : Trace s0 step (s0 :: nil)
  | take_step : `{Trace s0 step (ς :: π) ->
                  step ς ς' ->
                  Trace s0 step (ς' :: (ς :: π))}.

Definition TraceTo {State} (step : relation State) (s0 s1 : State) : Prop :=
  exists π, Trace s0 step (s1 :: π).

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