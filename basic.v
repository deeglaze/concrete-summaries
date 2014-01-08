(* useful tactics for the development *)
Ltac split_refl eq_dec a := let H:= fresh in destruct (eq_dec a a) as [H|bad]; [clear H|contradict bad]; auto.
Ltac split_refl2 eq_dec a a' := let H:= fresh in
                                destruct (eq_dec a a') as [bad|H]; [contradict bad|clear H]; auto.
Ltac bad_eq := match goal with [Hbad : ?a <> ?a |- _] => contradict Hbad; auto end.
Ltac inject_pair := match goal with [H: (?a, ?b) = (?c, ?d) |- _] => injection H; intros; subst end.
Ltac inverts H := inversion H; subst.

Notation "'dec_type' T" := (forall x y : T, {x=y}+{x<>y}) (at level 70, no associativity).

