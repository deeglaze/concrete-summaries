Generalizable All Variables.
Set Implicit Arguments.
(* useful tactics for the development *)
Ltac split_refl eq_dec a := let H:= fresh in destruct (eq_dec a a) as [H|bad]; [clear H|contradict bad]; auto.
Ltac split_refl2 eq_dec a a' := let H:= fresh in
                                destruct (eq_dec a a') as [bad|H]; [contradict bad|clear H]; auto.
Ltac bad_eq := match goal with [Hbad : ?a <> ?a |- _] => contradict Hbad; auto end.
Ltac inject_pair := match goal with [H: (?a, ?b) = (?c, ?d) |- _] => injection H; intros; subst end.
Ltac inverts H := inversion H; subst.

Notation "'dec_type' T" := (forall x y : T, {x=y}+{x<>y}) (at level 70, no associativity).

Inductive eqT {A} (x : A) : A -> Type :=
  reflT : eqT x x.

Inductive InT {A} (x : A) : list A -> Type :=
| int_first : `{eqT x y -> InT x (y :: l)}
| int_rest : `{InT x l -> InT x (a :: l)}.

Notation "x '=T' y" := (eqT x y) (at level 75, no associativity).
Hint Constructors eqT InT.
