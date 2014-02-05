Require Import List reduction basic ZArith.
Import ListNotations.

Set Implicit Arguments.

Inductive Stack_Action (alphabet : Type) : Type :=
  eps_action : Stack_Action alphabet
| push_action : alphabet -> Stack_Action alphabet
| pop_action : alphabet -> Stack_Action alphabet.

Inductive Allow_SAs (A : Type) : list (Stack_Action A) -> Prop :=
| allow_empty : Allow_SAs []
| allow_eps : forall κ, Allow_SAs κ -> Allow_SAs (κ ++ [eps_action _])
| allow_push : forall κ γ, Allow_SAs κ -> Allow_SAs (κ ++ [push_action γ])
| allow_pop : forall κ γ, Allow_SAs (κ++[push_action γ]) -> Allow_SAs (κ++[push_action γ; pop_action γ]).

Definition Allow_SA (A : Type) : list (Stack_Action A) -> (Stack_Action A) -> Prop :=
  fun κ a => Allow_SAs (κ ++ [a]).
Definition kont_to_actions {A} (κ : list A) : list (Stack_Action A) := map (@push_action _) (rev κ).

Inductive Balanced_action_red (A : Type) : list (Stack_Action A) -> list (Stack_Action A) -> Prop :=
  balance_eps : forall las ras,
                  Balanced_action_red (las ++ (eps_action A :: ras)) (las ++ ras)
| balance_cancel : forall las ras γ,
                      Balanced_action_red (las ++ [push_action γ; pop_action γ] ++ ras)
                                          (las ++ ras).
Inductive Actions_form_kont (A : Type) : list (Stack_Action A) -> list A -> Prop :=
  mt_kont : Actions_form_kont [] []
| push_kont : forall actions γ κ, Actions_form_kont actions κ ->
                                  Actions_form_kont (actions ++ [push_action γ]) (γ :: κ).

Definition Balanced_actions (A : Type) := direct_clos_refl_trans (@Balanced_action_red A).
Definition Balance_to_kont_P (A : Type) (actions : list (Stack_Action A)) (κ : list A) :=
  fun actions' => Balanced_actions actions actions' /\ Actions_form_kont actions' κ.

Definition Balance_to_kont (A : Type) (actions : list (Stack_Action A)) (κ : list A) : Prop :=
  ex (Balance_to_kont_P actions κ).

(* one pass of cancellation *)
Fixpoint remove_cancel {A} (eq_dec : dec_type A) (l : list (Stack_Action A)) :=
  match l with
      nil => nil
    | eps_action::l' => (eps_action _)::l'
    | push_action γ::l' => match l' with
                             | pop_action γ'::l'' =>
                               if (eq_dec γ γ') then
                                 (remove_cancel eq_dec l'')
                               else 
                                 push_action γ :: pop_action γ' :: (remove_cancel eq_dec l'')
                             | _ => push_action γ :: (remove_cancel eq_dec l')
                           end
    | pop_action γ::l' => pop_action γ :: (remove_cancel eq_dec l')
  end.
Functional Scheme remove_cancel_ind := Induction for remove_cancel Sort Prop.

Fixpoint remove_cancel_n {A} (eq_dec : dec_type A) (n : nat)  (acc : list (Stack_Action A)) :=
  match n with
      0 => acc
    | S n' => remove_cancel_n eq_dec n' (remove_cancel eq_dec acc)
  end.

Lemma balance_actions_at_end : forall A (actions actions' : list (Stack_Action A)),
                                   Balanced_actions actions actions' ->
                                   forall actions'',
                                   Balanced_actions (actions ++ actions'') (actions' ++ actions'').
Proof.
  intros ? ? ? H; induction H as [|? ? ? ? ? Hred];intro actions''.
  constructor.
  inversion Hred;
  subst;
  eapply (drt_append (IHdirect_clos_refl_trans actions''));
  eapply drt_step; auto;
  do 2 rewrite <- app_assoc.
  eapply balance_eps.
  eapply balance_cancel.
Qed.

Lemma balance_actions_at_front : forall A (actions actions' : list (Stack_Action A)),
                                   Balanced_actions actions actions' ->
                                   forall actions'',
                                   Balanced_actions (actions'' ++ actions) (actions'' ++ actions').
Proof.
  intros ? ? ? H; induction H as [|? ? ? ? ? Hred];intro actions''.
  constructor.
  inversion Hred;
  subst;
  eapply (drt_append (IHdirect_clos_refl_trans actions''));
  eapply drt_step; auto;
  do 2 rewrite app_assoc.
  eapply balance_eps.
  eapply balance_cancel.
Qed.

Theorem remove_eps_balances : forall A (l : list (Stack_Action A)), Balanced_actions l (remove_eps l).
Proof.
  induction l;[constructor|simpl; destruct a as [|γ|γ]].
  eapply (drt_append _ IHl). (* grab _ at end *)
  eapply (balance_actions_at_front IHl [push_action γ]).
  eapply (balance_actions_at_front IHl [pop_action γ]).
Grab Existential Variables.
eapply drt_step; [apply drt_refl|apply (balance_eps [] l)].
Qed.

Theorem remove_cancel_balances : forall A (eq_dec : dec_type A) (l : list (Stack_Action A)),
                                   Balanced_actions l (remove_cancel eq_dec l).
Proof.
  intros ? ? l; apply remove_cancel_ind; intros; subst;
  try solve [constructor
            |simpl; apply drt_refl 
            |apply (balance_actions_at_front (drt_refl _ l') [eps_action _])
            |apply (balance_actions_at_front H [push_action γ])
            |apply (balance_actions_at_front H [pop_action γ])
            |apply (balance_actions_at_front H [push_action γ; pop_action γ'])].
  intros; subst; eapply (drt_append _ H).
  Grab Existential Variables.
  eapply drt_step; [apply drt_refl|apply (balance_cancel [] l'')].
Qed.

Lemma balance_length : forall A (l l' : list (Stack_Action A)),
                         l <> l' -> Balanced_action_red l l' -> length l' < length l.
Proof.
  intros ? ? ? Hneq H; hnf in H; inversion H; subst; do 2 rewrite app_length; simpl; omega.
Qed.

Lemma remove_cancel_le : forall A (eq_dec : dec_type A) (l : list (Stack_Action A)),
                           length (remove_cancel eq_dec l) <= length l.
Proof.
  intros ? ? l; apply remove_cancel_ind; intros; subst; try solve [auto | unfold length in *; omega].
Qed.  

Lemma remove_cancel_same_length_eq : forall A (eq_dec : dec_type A) (l : list (Stack_Action A)),
                                       length (remove_cancel eq_dec l) = length l ->
                                       remove_cancel eq_dec l = l.
Proof.
  intros ? ? l; apply remove_cancel_ind; intros; subst; auto.
  f_equal; apply H; auto.
  pose (contr := remove_cancel_le eq_dec l'');
  unfold length in *; elimtype False; omega.
  do 2 f_equal; apply H; simpl in H0; omega.
  f_equal; apply H; auto.
Qed. 

Lemma idempotent_remains : forall A (eq_dec : dec_type A) l, remove_cancel eq_dec l = l ->
                                                             forall n, remove_cancel_n eq_dec n l = l.
Proof.
  induction n; [|simpl; rewrite H,IHn];reflexivity.
Qed.

Theorem remove_cancel_n_idempotency : forall A (eq_dec : dec_type A) n' n l,
                                        length l <= n -> n <= n' ->
                                        remove_cancel_n eq_dec n l = remove_cancel_n eq_dec n' l.
Proof.
  induction n'.
  intros.
  inversion H0; subst; reflexivity.
  intros n l Hle HSnle.
  simpl.
  rewrite NPeano.Nat.le_lteq in HSnle.
  inversion HSnle as [Hnlt|Hneq]; [|subst; reflexivity].
  destruct n.
  cut (l = []); [clear IHn' HSnle Hnlt;
                  intros; subst; simpl; induction n'; simpl; [reflexivity|auto]
                |destruct l; [auto|elimtype False; simpl in Hle; omega]].
  rewrite NPeano.Nat.le_lteq in Hle.
  inversion Hle as [lenlt|crap].
  simpl; apply IHn'; [cut (length (remove_cancel eq_dec l) <= length l); [omega|apply remove_cancel_le]
                     |omega].
  cut (length (remove_cancel eq_dec l) <= S n).
  intro crap'; rewrite NPeano.Nat.le_lteq in crap'.
  inversion crap' as [less|idemp];
    [simpl; apply IHn'; omega
    |].
  rewrite <- crap in idemp.
  apply remove_cancel_same_length_eq in idemp.
  simpl. rewrite idemp; rewrite idempotent_remains; [rewrite idempotent_remains; [reflexivity|] |]; auto.
  pose (remove_cancel_le eq_dec l); omega.
Qed.

Lemma remove_eps_idemponent : forall A (l : list (Stack_Action A)), remove_eps (remove_eps l) = remove_eps l.
Proof.
  induction l; [reflexivity|simpl; destruct a; simpl; [|f_equal|f_equal]; rewrite IHl; try reflexivity].
Qed.

Conjecture confluent_eps : forall A (l l' : list (Stack_Action A)),
                          (remove_eps l) = (remove_eps l') ->
                          length l' <= length l ->
                          Balanced_actions l l'.

Ltac list_unit :=
  match goal with [H : ?l ++ ?r = [?x] |- _] => apply app_eq_unit in H; inversion_clear H as [[? ?]|[? ?]]; subst end.

Conjecture balance_remove_stuck : forall A (actions' actions : list (Stack_Action A)) γ,
                                    Balanced_actions (actions ++ [push_action γ]) (actions' ++ [push_action γ]) ->
                                    Balanced_actions actions actions'.
  
Lemma kont_to_actions_balanced : forall A (κ : list A), Balance_to_kont (kont_to_actions κ) κ.
Proof.
  induction κ as [|γ κ IH].
  exists []; repeat constructor.
  unfold kont_to_actions; rewrite map_rev; simpl.
  destruct IH as [actions [H0 H1]].
  exists (actions ++ [push_action γ]); split.
  eapply balance_actions_at_end; rewrite <- map_rev; auto.
  constructor; auto.
Qed.

Section ExtraListFacts.
Definition res A l := (fun l' : list A => {last : A & l = l' ++ [last]}).
Definition all_but_last {A} (lstart : list A) (nnilstart : lstart <> nil) : sigT (res lstart).
refine ((fix abl l (nnil : l <> nil) : sigT (res l) :=
          (match l as l_ return (l = l_ -> _) with
              nil => fun H : l = nil => match (nnil H) with end
            | a::l' => fun H : l = a::l' =>
                         (match l' as l'_ return (l' = l'_ -> sigT (res l)) with
                              nil => fun H' : l' = nil =>
                                       existT (res l) [] 
                                              (existT (fun lst : A => l = [] ++ [lst]) 
                                                      a
                                                      _ (* goal 1 *))
                            | a'::l'' => fun H' : l' = a'::l'' =>
                                           match (abl l' _ (* goal 2 *)) with
                                               | existT abll (existT last prf) =>
                                                 existT (res l)
                                                        (a::abll)
                                                        _ (* goal 3 *)
                                                        (*(existT (fun lst : A => l = l' ++ [lst]) last _)*)
                                           end
                          end (eq_refl l'))
          end (eq_refl l))) lstart nnilstart).
rewrite H' in H; assumption.
intro bad; rewrite bad in H'; discriminate.
exists last; rewrite H; simpl; f_equal; assumption.
Defined. 

Lemma nonempty_right_app_last' : forall A (r l res : list A) (last : A)
                                 (H : r <> nil)
                                 (Heq : l ++ r = res ++ [last])
                                 abl sub
                                 (ablH : (all_but_last H) = existT _ abl sub)
                                 last' Heq'
                                 (subeq : sub = existT _ last' Heq'),
                                   l ++ abl = res /\ last = last' /\ r = abl ++ [last].
Proof.
  induction r; intros.
  destruct abl; discriminate.
  subst.
  destruct r as [|a' r'].
  destruct (all_but_last H). 
  cut (abl = []);
    [intro; subst; simpl in Heq'; injects Heq';
     apply app_inj_tail in Heq; autorewrite with list; intuition (simpl; subst; auto)
    |destruct abl; [reflexivity
                   |simpl in Heq'; injects Heq'; destruct abl; discriminate]].
  specialize (IHr (l ++ [a]) res0 last).
  cut (a' :: r' <> []); [intro use|discriminate].
  rewrite app_assoc_reverse in IHr;
  case_eq (all_but_last use); intros lx Pr use';
  case_eq Pr; intros xa appeq use''; specialize (IHr use Heq _ _ use' _ _ use'').
  destruct IHr as [IHleq [IHlasteq IHableq]].
  subst.
  destruct (all_but_last H); injects ablH.
  destruct (exists_last use) as [l_ [a_ arlast]].
  rewrite arlast in *.
  apply app_inj_tail in IHableq.
  destruct IHableq as [leq_ aeq_]; subst.

  cut (abl = a :: lx /\ xa = last');
    [intros [Habl xalst]; subst abl; rewrite app_assoc_reverse; auto
    |clear ablH H0;
      rewrite appeq in Heq';
      cut ((a :: lx) ++ [xa] = abl ++ [last']);
      [intro Hinj; apply app_inj_tail in Hinj; destruct Hinj; auto
      |simpl; auto]].
Qed.

Lemma nonempty_right_app_last : forall A (r l res : list A) (last : A),
                                  r <> nil ->
                                  l ++ r = res ++ [last] ->
                                  exists r', r = r' ++ [last].
Proof.
  intros.
  case_eq (all_but_last H); intros x rr H1.
  case_eq rr; intros ? ? H2.
  pose (@nonempty_right_app_last' _ r l res0 last H H0 _ _ H1 _ _ H2).
  exists x; intuition.
Qed.
End ExtraListFacts.

Lemma push_end_remains : forall A actions actions' (γ : A),
                           Balanced_actions (actions ++ [push_action γ]) actions' ->
                           exists actions'', actions' = actions'' ++ [push_action γ].
Proof.
  intros ? ? ? ? H; unfold Balanced_actions in H; rewrite drt_family_iff_index in H; induction H as [|foo bar baz IH].
  exists actions; auto.
  rewrite <- drt_family_iff_index in baz.
  destruct IH as [actions'' Heq].
  subst.
  inversion H; subst.
  - revert actions'' baz H H1.
  induction las;
  intros actions'' bar H H1.
  destruct actions'' as [|act actions''']; simpl in H1; 
    [discriminate|exists actions'''; injects H1; auto].
  cut (eps_action _:: ras <> []);[|intro bad; discriminate].
  intro Hne; destruct (@nonempty_right_app_last _ (eps_action _ :: ras) (a :: las) actions'' (push_action γ) Hne H1) as [r' Hr'];
  destruct r' as [|ra r''];[discriminate|];
  exists ((a :: las) ++ r'');
  simpl in Hr'; injects Hr'; auto; simpl; rewrite app_assoc; auto.
  - revert actions'' baz H H1.
  induction las;
  intros actions'' bar H H1.
  destruct actions'' as [|act actions''']; simpl in H1; 
    [discriminate|destruct actions''' as [|act' actions''''];
                   [discriminate
                   |exists actions''''; simpl in H1; injects H1; auto]].  
  cut (push_action γ0 :: pop_action γ0 :: ras <> []);[|intro bad; discriminate].
  intro Hne; destruct (@nonempty_right_app_last _ (push_action γ0 :: pop_action γ0 :: ras) (a :: las) actions'' (push_action γ) Hne H1) as [r' Hr'];
  destruct r' as [|ra r''];[discriminate|destruct r'' as [|ra' r'''];[discriminate|]];
  exists ((a :: las) ++ r''');
  simpl in Hr'; injects Hr'.
simpl; f_equal. rewrite app_assoc; reflexivity.
Qed.

Hint Resolve kont_to_actions_balanced.
