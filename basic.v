Require Import List.
Import ListNotations.
Generalizable All Variables.
Set Implicit Arguments.
(* useful tactics for the development *)
Ltac split_refl eq_dec a := let H:= fresh in destruct (eq_dec a a) as [H|bad]; [clear H|contradict bad]; auto.
Ltac split_refl2 eq_dec a a' := let H:= fresh in
                                destruct (eq_dec a a') as [bad|H]; [contradict bad|clear H]; auto.
Ltac bad_eq := match goal with [Hbad : ?a <> ?a |- _] => contradict Hbad; auto end.
Ltac inject_pair := match goal with [H: (?a, ?b) = (?c, ?d) |- _] => injection H; intros; subst end.
Ltac inverts H := inversion H; subst.
Ltac injects H := injection H; intros; subst.
Ltac disc := discriminate
           || (match goal with
                   [H : (?a :: ?b) = [] |- _] => (destruct a; discriminate H)
                 | [H : ?a ++ [?b] = [] |- _] => (destruct a; discriminate H)
                 | [H : [] = (?a :: ?b) |- _] => (destruct a; discriminate H)
                 | [H : [] = ?a ++ [?b] |- _] => (destruct a; discriminate H)
                 | [H : [] = (?a ++ ?b) ++ [?c] |- _] => (destruct a,b; discriminate H)
                 | [H : (?a ++ ?b) ++ [?c] = [] |- _] => (destruct a,b; discriminate H)
               end).
Ltac listac := repeat progress (disc || 
                                     (autorewrite with list in *;
                                 match goal with
                                     [H : ?l ++ [?a] = ?r ++ [?b] |- _] =>
                                     apply app_inj_tail in H; destruct H; try subst
                                  | [H : ?l ++ [?a] = ?b :: ?r ++ [?c] |- _] =>
                                    let F := fresh in
                                    let F' := fresh in
                                    pose (F := @app_assoc _ [b] r [c]);
                                     cut ([b] ++ r ++ [c] = (b::r)++[c]);
                                     [intro F'; rewrite F' in F; rewrite F in H; clear F F'
                                     |reflexivity]
                                  | [H : ?a :: ?l ++ [?b] = ?r ++ [?c] |- _] =>
                                    let F := fresh in
                                    let F' := fresh in
                                    pose (F := @app_assoc _ [a] l [b]);
                                     cut ([a] ++ l ++ [b] = (a::l)++[b]);
                                     [intro F'; rewrite F' in F; rewrite F in H; clear F F'
                                     |reflexivity]
                                  | [H : ?l ++ [?a; ?b] = ?r ++ [?c] |- _] =>
                                    let F := fresh in
                                    pose (F := @app_assoc _ l [a] [b]);
                                     simpl in F; rewrite F in H; clear F
                                  | [H : ?l ++ [?a] = ?r ++ [?b;?c] |- _] =>
                                    let F := fresh in
                                    pose (F := @app_assoc _ r [b] [c]);
                                     simpl in F; rewrite F in H; clear F
                                  | [H : In ?a [] |- _] => destruct H
                                 end)).

Notation "'dec_type' T" := (forall x y : T, {x=y}+{x<>y}) (at level 70, no associativity).

Inductive eqT {A} (x : A) : A -> Type :=
  reflT : eqT x x.

Inductive InT {A} (x : A) : list A -> Type :=
| int_first : `{eqT x y -> InT x (y :: l)}
| int_rest : `{InT x l -> InT x (a :: l)}.

Notation "x '=T' y" := (eqT x y) (at level 75, no associativity).
Hint Constructors eqT InT.
