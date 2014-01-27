Require Import List ListSet basic.
Import ListNotations.

Section Definitions.

Definition union_map {A B} (eq_dec : dec_type B) (f : A -> set B) (s : set A) : set B :=
  set_fold_left (fun acc a => set_union eq_dec acc (f a)) s (empty_set _).

Definition Subset {A} (s s' : set A) := forall x, In x s -> In x s'.

End Definitions.

Lemma subset_refl : forall A (s : set A), Subset s s.
Proof. intros A s x Hin; auto. Qed.

Lemma subset_trans : forall A (s s' s'' : set A) (Hsub0 : Subset s s') (Hsub1 : Subset s' s''), Subset s s''.
Proof. intros; intros x Hin; apply Hsub0,Hsub1 in Hin; assumption. Qed.

Section Facts.
Variables (A : Type) (Aeq_dec : dec_type A).


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

Theorem fold_left_subset : forall B (f: B -> set A) (s : set B) (base : set A),
                             Subset base (set_fold_left (fun acc b =>
                                                           set_union Aeq_dec acc (f b))
                                                        s base).
Proof.
  induction s; intros b a' Hin.
  auto.
  simpl in *.
  apply IHs.
  apply set_union_intro1; auto.
Qed.

Theorem fold_left_subset_in : forall B (f: B -> set A) (s : set B) (base : set A) b,
                             In b s -> Subset (f b) (set_fold_left (fun acc b =>
                                                           set_union Aeq_dec acc (f b))
                                                        s base).
Proof.
  induction s; intros base b Hin a' Hin'.
  inversion Hin.
  simpl in *.
  inversion Hin as [Heq|Hrest].
  subst; apply fold_left_subset,set_union_intro2; auto.
  apply (IHs (set_union Aeq_dec base (f a)) b Hrest); auto.
Qed.

Theorem union_map_subset : forall B (f : B -> set A) s b, In b s -> Subset (f b) (union_map Aeq_dec f s).
Proof.
  intros; apply fold_left_subset_in; auto.
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