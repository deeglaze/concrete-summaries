Require Vectors.Vector.
Require Import List ListSet Relation_Definitions Relation_Operators Lexicographic_Product.
Require Import basic finite reduction balance ListSetFacts.

Import ListNotations.
Generalizable All Variables.
Set Implicit Arguments.

Coercion bool_prop := (fun b => b = true).

Section Pushdown.
Variables (Q Γ : Type).

Inductive PDS : Type :=
  pds_intro : forall (isQ : Q -> bool) (isΓ : Γ -> bool)
                     (δ : action_relation Q (Stack_Action Γ))
                     (ε_within_bounds : forall q q', δ q (eps_action Γ) q' -> (isQ q) /\ (isQ q'))
                     (push_within_bounds :
                        forall q γ q', δ q (push_action γ) q' -> (isQ q) /\ (isΓ γ) /\ (isQ q'))
                     (pop_within_bounds :
                        forall q γ q', δ q (pop_action γ) q' -> (isQ q) /\ (isΓ γ) /\ (isQ q')),
                PDS.

Definition pds_rel (pds : PDS) : action_relation Q (Stack_Action Γ) :=
  match pds with pds_intro _ _ δ _ _ _ => δ end.
Definition pds_Q (pds : PDS) : Q -> bool :=
  match pds with pds_intro isQ _ _ _ _ _=> isQ end.
Definition pds_Γ (pds : PDS) : Γ -> bool :=
  match pds with pds_intro _ isΓ _ _ _ _ => isΓ end.

Inductive RPDS : Type :=
  rpds_intro : forall (pds : PDS) (q0 : Q), pds_Q pds q0 -> RPDS.

Definition rpds_pds (rpds : RPDS) := match rpds with rpds_intro pds _ _ => pds end.
Definition rpds_rel (rpds : RPDS) := (pds_rel (rpds_pds rpds)).
Definition rpds_Q (rpds : RPDS) := (pds_Q (rpds_pds rpds)).
Definition rpds_root (rpds : RPDS) := match rpds with rpds_intro _ q0 _ => q0 end.
Inductive PDS_step (pds : PDS) : (Q * list Γ) -> (Q * list Γ) -> Prop :=
  eps_trans : forall q q' κ, (pds_rel pds) q (eps_action Γ) q' -> PDS_step pds (q,κ) (q',κ)
| push_trans : forall q q' γ κ, (pds_rel pds) q (push_action γ) q' -> PDS_step pds (q,κ) (q',γ::κ)
| pop_trans : forall q q' γ κ, (pds_rel pds) q (pop_action γ) q' -> PDS_step pds (q,γ::κ) (q',κ).

Inductive PDS_legal_step (pds : PDS) : (Q * list Γ) -> (Stack_Action Γ) -> Q -> Prop :=
  eps_ltrans : forall q q' κ, (pds_rel pds) q (eps_action Γ) q' -> PDS_legal_step pds (q,κ) (eps_action Γ) q'
| push_ltrans : forall q q' γ κ, (pds_rel pds) q (push_action γ) q' -> PDS_legal_step pds (q,κ) (push_action γ) q'
| pop_ltrans : forall q q' γ κ, (pds_rel pds) q (pop_action γ) q' -> PDS_legal_step pds (q,γ::κ) (pop_action γ) q'.

Hint Constructors PDS_legal_step PDS_step.


(*
Inductive Balanced_actions (A : Type) : list (Stack_Action A) -> list A -> Prop :=
  balance_eps : forall las ras res, Balanced_actions (las ++ ras) res ->
                                    Balanced_actions (las ++ (eps_action A :: ras)) res
| balance_pushpop : forall las ras γ res,
                      Balanced_actions (las ++ ras) res ->
                      Balanced_actions (las ++ [push_action γ; pop_action γ] ++ ras) res
| balance_empty : Balanced_actions [] []
| balance_push : forall actions γ res,
                   Balanced_actions actions res ->
                   Balanced_actions (actions ++ [push_action γ]) (γ :: res).
*)

(*
Lemma remove_actions : forall pds q q',
                       (exists actions, clos_refl_trans_action_with_actions (pds_rel pds) q actions q')
                       <-> clos_refl_trans_action (pds_rel pds) q q'.
Proof.
  intros; split; [intro actpath; induction actpath|intro path; induction path].
*)

(*
(* this doesn't necessarily maintain trace structure, since dcrt is opaque *)
Lemma action_path_and_none : forall pds (qκ qκ' : Q * list Γ),
                               direct_clos_refl_trans (PDS_step pds) qκ qκ' <->
                               exists actions,
                                 clos_refl_trans_action_with_actions (pds_rel pds) (@PDS_Allow Γ) (fst qκ) actions (fst qκ') /\
                                 Balance_to_kont ((kont_to_actions (snd qκ)) ++ actions) (snd qκ').
Proof.
  intros; split; [intro Hpath|intros [actions [path Hbalanced]]].
  induction Hpath as [|[q κ] [q' κ'] [q'' κ''] Htrace IH Hstep].
  exists []; autorewrite with list; auto.
  destruct IH as [actions [IHtrace [IHactions [IHbalance IHformκ]]]].
  inversion Hstep as [? ? ? Hred| ? ? ? ? Hred|? ? ? ? Hred]; subst; simpl in *.

  exists (actions ++ [eps_action Γ]); split;
  [eapply (@rtaa_step _ _ _ _ _ _ _ actions _ _ Hred)
  |exists IHactions; split;
   [rewrite app_assoc; unfold Balanced_actions; eapply (drt_append _ IHbalance)
   |]]; auto.

  exists (actions ++ [push_action γ]); split;
  [eapply (@rtaa_step _ _ _ _ _ _ _ actions _ _ Hred)
  |exists (IHactions ++ [push_action γ]); split;
   [rewrite app_assoc; unfold Balanced_actions; apply balance_actions_at_end
   |constructor]]; auto.

  exists (actions ++ [pop_action γ]); split;
  [inversion IHformκ as [|actions' ? ? Hactions]; subst; eapply (@rtaa_step _ _ _ _ _ _ _ actions _ _ Hred)
  |inversion IHformκ as [|actions' ? ? Hactions]; subst;
   exists actions'; split;
   [apply balance_actions_at_end with (actions'' := [pop_action γ]) in IHbalance;
     do 2 rewrite <- app_assoc in IHbalance; simpl in IHbalance;
     eapply (drt_append IHbalance);
     eapply drt_step;[apply drt_refl
                     |set (H:= (balance_cancel actions' [] γ)); autorewrite with list in H; exact H]
   |assumption]].

inversion IHtrace; subst.
inversion Htrace. subst.

Lemma allow_pop_only_if_push_at_end : forall rpds actions q γ,
                                        Balanced_actions actions (actions' ++ [push_action γ])

Admitted.
*)
Definition Is_root_reachable_via rpds actions q : Prop :=
  clos_refl_trans_action_with_actions (rpds_rel rpds) (@Allow_SA Γ) [] (rpds_root rpds) actions q.

Definition Root_reachable_state (sys : RPDS) (q : Q) : Prop :=
  exists actions, Is_root_reachable_via sys actions q.

Lemma allow_preserves_balance : forall (actions : list (Stack_Action Γ)) a κ
                                      (Hbal : Balance_to_kont actions κ)
                                      (Hallow : Allow_SAs (actions ++ [a])),
                                 exists κ', Balance_to_kont (actions ++ [a]) κ'.
Proof.
  intros; inversion Hallow as [| | |actions']; listac;
  destruct Hbal as [actions_ [? Hκ]].
  exists κ, actions_; split;[eapply (drt_append _ H)|]; auto.
  exists (γ::κ), (actions_ ++ [push_action γ]); split; [apply balance_actions_at_end|constructor];auto.
  destruct (push_end_remains _ _ H) as [moo boo]; subst.
  inversion Hκ as [|? ? κ']; listac.
  exists κ', moo; split; auto.
  cut (Balanced_actions (actions' ++ [push_action γ; pop_action γ])
                        (moo ++ [push_action γ; pop_action γ])).
  intro pathpart.
  cut (Balanced_actions (moo ++ [push_action γ; pop_action γ]) moo);
    [intro pathpart'; apply (drt_append pathpart pathpart')
    |eapply drt_step; [eapply drt_refl | pose (grumble := (balance_cancel moo [])); simpl in grumble; rewrite app_nil_r in grumble; auto]].
  pose (L := @balance_actions_at_end _ _ _ H [pop_action γ]); do 2 rewrite app_assoc_reverse in L; auto.
Grab Existential Variables.
eapply drt_step; [apply drt_refl | pose (L := (balance_eps actions [])); rewrite app_nil_r in L; auto].
Qed.

Lemma list_split_tail : forall A (l : list A), l = [] \/ exists l' a, l = l' ++ [a].
Proof.
  induction l;
  [left
  |inversion IHl as [Hnil|[l' [a' htail]]]; subst; right;
   [exists [], a|exists (a :: l'), a']]; auto.
Qed.

Lemma Allow_SAs_prefix : forall A (l' l : list (Stack_Action A)),
                           Allow_SAs (l ++ l') -> Allow_SAs l.
Proof.
  induction l'; intros;
  [rewrite app_nil_r in H; auto
  |pose (L := IHl' (l ++ [a])); rewrite app_assoc_reverse in L; apply L in H;
   inversion H; listac; auto].
Qed.  
Lemma Allow_SA_segmentation : forall A (l l' : list (Stack_Action A)) a a',
                                Allow_SA (l ++ [a] ++ l') a' ->
                                Allow_SA l a.
Proof.
  intros.
  hnf in H.
  cut (Allow_SAs ((l ++ [a]) ++ (l' ++ [a']))).
  intro H'; apply Allow_SAs_prefix in H'; auto.
  rewrite app_assoc in *; auto.
Qed.

Lemma paths_preserve_balance : forall rpds actions0 q actions κ
                                      (Hbal : Balance_to_kont actions0 κ)
                                      (Hallow : match actions with
                                                    nil => True
                                                  | a::_ => Allow_SA actions0 a
                                                end)
                                      (q' : Q)
                                      (Hpath :
                                         clos_refl_trans_action_with_actions rpds (@Allow_SA Γ)
                                                                             actions0 q actions q'),
                                 exists κ', Balance_to_kont (actions0 ++ actions) κ'.
  intros; induction Hpath as [|? ? ? ? ? ? [κ_ [actionsb [Hbal' Hκ]]] ? Hallow_].
  exists κ; rewrite app_nil_r; auto.
  inverts Hpath.
  exact I.
  case_eq actions1.
  intro; subst; simpl; rewrite app_nil_r in *; auto.
  intros a' actions' Heq; subst; simpl.
  pose (Allow_SA_segmentation actions0 actions' a' H1); auto.
  inversion Hallow_ as [| |? γ|? γ]; listac.
  - exists κ_, actionsb; split;
  [cut (Balanced_actions (actions0 ++ actions ++ [eps_action _]) (actions0 ++ actions));
    [intro path; apply (drt_append path Hbal')
    |eapply drt_step; [apply drt_refl | pose (L := (balance_eps (actions0 ++ actions) [])); rewrite app_nil_r in L;  try rewrite app_assoc]]
  |]; auto.
  - exists (γ::κ_), (actionsb ++ [push_action γ]); split;
    [rewrite app_assoc; apply balance_actions_at_end|constructor]; auto.
  - listac.
    rewrite app_assoc, <- H0, <- app_assoc; simpl.
    rewrite <- H0 in Hbal',Hallow_.
    pose (L := (ex_intro (Balance_to_kont_P (κ0 ++ [push_action γ]) κ_) actionsb (conj Hbal' Hκ))).
    pose (L' := (allow_preserves_balance _ L Hallow_)).
    rewrite <- app_assoc in L'; auto.
Qed.
  
Remark reachable_balances_to_kont :
  forall rpds actions q, Is_root_reachable_via rpds actions q -> exists κ, Balance_to_kont actions κ.
Proof.
  intros ? ? ? H; hnf in H.
  induction H as [|? ? ? ? ? ? [κ IH] ? Hallow].
  exists [],[]; split; constructor.  
  apply (@allow_preserves_balance _ _ _ IH) in Hallow; auto.
Qed.

Definition frame_appears_in (γ : Γ) (actions : list (Stack_Action Γ)) : Prop :=
  Exists (fun γa => match γa with
                        eps_action => False
                      | push_action γ' => γ = γ'
                      | pop_action γ' => γ = γ'
                    end) actions.

Definition Root_reachable_frame (rpds : RPDS) (γ : Γ) : Prop :=
  exists actions q, Is_root_reachable_via rpds actions q /\ frame_appears_in γ actions.

Definition Balanced_path_with (rpds : RPDS) (q q' : Q) (actions0 actions : list (Stack_Action Γ)) :=
  clos_refl_trans_action_with_actions (rpds_rel rpds) (@Allow_SA Γ) actions0 q actions q'
  /\ Balanced_actions actions [].
Hint Unfold Balanced_path_with.

Definition Balanced_path (rpds : RPDS) (q q' : Q) :=
  exists actions0, Is_root_reachable_via rpds actions0 q /\
                   exists actions, Balanced_path_with rpds q q' actions0 actions.

Definition NE_Balanced_path (rpds : RPDS) (q q' : Q) :=
  exists actions0, Is_root_reachable_via rpds actions0 q /\
                   exists actions, actions <> nil /\ Balanced_path_with rpds q q' actions0 actions.

Inductive Epsilon_closure (rpds : RPDS) : relation Q -> Prop :=
  eps_closure : forall δε,
                  (forall s s',
                     (δε s s' <-> Balanced_path rpds s s')) ->
                  Epsilon_closure rpds δε.

Remark good_root : forall rpds (isQ' : Q -> bool) (goodQ : forall q, (isQ' q) <-> Root_reachable_state rpds q),
                     isQ' (rpds_root rpds).
intros; destruct (goodQ (rpds_root rpds)) as [_ H]; apply H; exists []; apply rtaa_refl.
Qed.

Inductive RPDS_compaction : RPDS -> RPDS -> Type :=
  compact_intro :
    forall rpds (isQ' : Q -> bool) (isΓ' : Γ -> bool),
      `{forall (GoodQ : (forall q, (isQ' q) <-> Root_reachable_state rpds q)),
        (forall γ, (isΓ' γ) <-> Root_reachable_frame rpds γ) ->
        (forall q γa q', (δ' q γa q') <-> exists actions, Is_root_reachable_via rpds actions q /\
                                                          (rpds_rel rpds q γa q') /\
                                                          exists κ, Balance_to_kont (actions ++ [γa]) κ) ->
    RPDS_compaction rpds (rpds_intro (pds_intro isQ' isΓ' δ' prf1 prf2 prf3)
                                     (rpds_root rpds)
                                     (good_root isQ' GoodQ))}.  

Lemma compaction_reachability_with_actions :
  forall rpds crpds,
    RPDS_compaction rpds crpds ->
    forall actions q,
      Is_root_reachable_via rpds actions q <-> Is_root_reachable_via crpds actions q.
Proof.
  intros rpds crpds Hcompact actions q;
  inversion_clear Hcompact as [? isQ' isΓ' δ' prf1 prf2 prf3 Qreach Γreach edgereach]; subst;
  split; intro Hreach.
  - hnf in Hreach; rewrite rtaa_family_iff_index in Hreach;
  induction Hreach as [|y z actions γa Hreach IH Hstep];[constructor|rewrite <- rtaa_family_iff_index in Hreach];
  eapply rtaa_step; eauto;
  rewrite edgereach;
  exists actions; repeat split; auto;
  inversion H as [| |? γ|actions' γ]; simpl in *; subst; listac;
  try solve
  [exists κ,actions_; split; listac;
   [eapply drt_append;
     [eapply balance_actions_at_end; eauto
     |eapply drt_step; [constructor|rewrite <- app_nil_r; eapply (balance_eps actions_ [])]]
   |auto]
  |exists (γ::κ),(actions_++[push_action γ]); split;
   [eapply balance_actions_at_end|constructor]; auto];
    (* part way *)
    destruct (reachable_balances_to_kont IH) as [? Hbal];
    pose (L := (allow_preserves_balance _ Hbal H));
    try rewrite app_assoc_reverse in L; auto.

  - hnf in Hreach; rewrite rtaa_family_iff_index in Hreach;
  induction Hreach as [|? ? ? ? Hreach IH Hstep];[constructor|rewrite <- rtaa_family_iff_index in Hreach];
    rewrite edgereach in Hstep;destruct Hstep as [? [? [yredz mumble]]];
    inverts H; listac; try solve
      [eapply rtaa_step; [exact IH |  |]; auto].
    pose (L := @rtaa_step _ _ (rpds_rel rpds) (@Allow_SA Γ) [] (rpds_root rpds) y z (κ ++ [push_action γ]) (pop_action γ) IH yredz H).
    rewrite app_assoc_reverse in L; simpl in L; auto.
Qed.

Lemma compaction_reachability_with_actions' :
  forall rpds crpds,
    RPDS_compaction rpds crpds ->
    forall actions q actions' q',
      Is_root_reachable_via rpds actions q /\
      clos_refl_trans_action_with_actions (rpds_rel rpds) (@Allow_SA Γ) actions q actions' q'
      <-> Is_root_reachable_via crpds actions q /\
          clos_refl_trans_action_with_actions (rpds_rel crpds) (@Allow_SA Γ) actions q actions' q'.
Proof.
  intros rpds crpds Hcompact actions q;
  inversion Hcompact as [? isQ' isΓ' δ' prf1 prf2 prf3 Qreach Γreach edgereach]; subst;
  split; intros [Hreach Hreach'].
  - split;
    [rewrite <- compaction_reachability_with_actions; [exact Hreach|exact Hcompact]
    |]. 
    rewrite rtaa_family_iff_index in Hreach';
      induction Hreach' as [|y z actions_ γa Hreach' IH Hstep];
      [constructor
      |rewrite <- rtaa_family_iff_index in Hreach'].
  destruct (reachable_balances_to_kont Hreach) as [κr Hr];
  pose (use := @paths_preserve_balance (rpds_rel rpds) actions q actions_ _ Hr);
  inversion H as [| |? γ|actions' γ]; simpl in *; subst; listac.
  (* empty case *)
  case_eq actions_; intros; subst;
    [inversion Hreach'; listac; subst|].
  rewrite app_nil_r in H.
  eapply rtaa_step; [exact IH| |].
  rewrite edgereach; exists actions; repeat split; auto.
  specialize (use I _ Hreach'); rewrite app_nil_r in use.
  destruct use as [κ' Hbal]; apply (allow_preserves_balance _ Hbal H).
  rewrite app_nil_r; auto.

  eapply rtaa_step;
    [exact IH
    |rewrite edgereach; exists (actions ++ (s :: l)); repeat split; 
     try solve [auto|eapply (rtaa_append Hreach _ _ Hreach')]
    |auto].
  (* eps action balances to kont *)
  destruct (reachable_balances_to_kont Hreach) as [κ0 Hbal];
  destruct (s :: l);
    [specialize (use I y Hreach');
      rewrite app_nil_r in *;
      destruct use as [κ' [actions' [Hbal_ Hform_]]];
      exists κ', actions'; split;
      [eapply (drt_append _ Hbal_)|auto]
    |cut (Allow_SA actions s0);
      [intro mum; destruct (use mum y Hreach') as [κ_ [actions_ [Hbal_ Hform_]]];
       exists κ_,actions_; split; [eapply (drt_append _ Hbal_)|]; auto
      |pose (use' := @Allow_SA_segmentation _ actions l0 s0 (eps_action _) H); auto]].
  (* push case *)
  eapply rtaa_step; [exact IH|rewrite edgereach; exists (actions ++ actions_); repeat split|]; auto.
  
  case_eq actions_; intros; subst;
  [inversion Hreach'; listac; subst; rewrite app_nil_r
  |listac; eapply (rtaa_append Hreach _ _ Hreach')]; auto.

  case_eq actions_; intros; subst;
  [rewrite app_nil_r in *; listac;
   destruct Hr as [actionsb [Hbal Hform]];
   exists (γ::κr),(actionsb++[push_action γ]); split; [apply balance_actions_at_end|constructor];auto
  |cut (Allow_SA actions s);
    [intro Ha; destruct (use Ha y Hreach') as [κ' [actionsb [Hbal Hform]]];
     listac;
     exists (γ::κ'),(actionsb ++ [push_action γ]); split; [apply balance_actions_at_end|constructor]; auto
    |apply (Allow_SA_segmentation _ _ _ H)]].

  (* pop case *)
  eapply rtaa_step; [exact IH|rewrite edgereach; exists (actions ++ actions_); repeat split |]; auto.
  case_eq actions_; intros; subst;
  [inversion Hreach'; listac; subst; rewrite app_nil_r
  |listac; eapply (rtaa_append Hreach _ _ Hreach')]; auto.

  case_eq actions_; intros; subst;
  [rewrite app_nil_r in *;
    apply (allow_preserves_balance _ Hr H)
  |].
  simpl in use.
  cut (Allow_SA actions s);[
      intro Ha; destruct (use Ha _ Hreach') as [κ' [actionsb [Hbal Hform]]]
     |].
  cut (actions ++ s :: l = actions' ++ [push_action γ]);
    [
  intros rew; subst; rewrite rew,<- app_assoc in *; simpl;
  destruct (push_end_remains _ _ Hbal) as [moo boo]; subst;
  inversion Hform; listac;
  exists κ, moo; split; auto;
  cut (Balanced_actions (actions' ++ [push_action γ; pop_action γ]) (moo ++ [push_action γ; pop_action γ]));
    [intro pathpart;
      cut (Balanced_actions (moo ++ [push_action γ; pop_action γ]) moo);
      [intro pathpart'; apply (drt_append pathpart pathpart')
      |eapply drt_step; [apply drt_refl | pose (L:= (balance_cancel moo [] γ)); repeat rewrite app_nil_r in L]]
    |pose (L := balance_actions_at_end Hbal [pop_action γ]); repeat rewrite app_assoc_reverse in L]; auto
  |cut (actions' ++ [push_action γ; pop_action γ] = (actions' ++ [push_action γ]) ++ [pop_action γ]);
    [intro Heq; listac
    |rewrite app_assoc_reverse] ;auto].
  apply (@Allow_SA_segmentation _ actions l s _ H).

  - split; [rewrite <- compaction_reachability_with_actions in Hreach; [exact Hreach|exact Hcompact]|].
    rewrite rtaa_family_iff_index in Hreach';
    induction Hreach' as [|? ? ? ? Hreach_ IH Hstep];[constructor|rewrite <- rtaa_family_iff_index in Hreach_].
    eapply rtaa_step; [exact IH |rewrite edgereach in Hstep; destruct Hstep as [? [? [? ?]]] | ]; auto.
Grab Existential Variables.
simpl; apply (Allow_SA_segmentation _ l s H).
discriminate.
simpl; apply (Allow_SA_segmentation _ l s H).
discriminate.
eapply drt_step; [apply drt_refl | pose (L := balance_eps (actions ++ s0 :: l0) []); repeat rewrite app_nil_r in L]; auto.
eapply drt_step; [apply drt_refl | pose (L := balance_eps actions []); repeat rewrite app_nil_r in L]; auto.
simpl; apply (Allow_SA_segmentation _ l s H).
discriminate.
Qed.

Lemma eps_closure_in_compaction : forall rpds crpds δε, Epsilon_closure rpds δε ->
                                                       RPDS_compaction rpds crpds ->
                                                       Epsilon_closure crpds δε.
Proof.
  intros rpds crpds δε Heps Hcompact;
  pose (HC := compaction_reachability_with_actions' Hcompact).
  inversion_clear Heps as [? epsinv];
  constructor.
  intros s s'; split;[intro Hε|intros [Hreachs Hbalanced]].

  rewrite epsinv in Hε; destruct Hε as [actions0 [reach0 [actions [path hbal]]]].

  pose (both := conj reach0 path); rewrite HC in both.
  destruct both; exists actions0; split; [|exists actions];auto.

  rewrite epsinv.
  destruct Hbalanced as [reachs [actions [path bal]]].
  pose (both := conj reachs path); rewrite <- HC in both.
  destruct both; exists Hreachs; split; [|exists actions]; auto.
Qed.
  
Definition WorkEdge := (Q * Γ * Q)%type.
Definition EpsEdge := (Q * Q)%type.

Inductive Working_rpds : Type :=
  working_rpds : forall (Qs : list Q)
                        (pushE : list WorkEdge)
                        (popE : list WorkEdge)
                        (epsE : list EpsEdge)
                        (q0 : Q)
                        (H : list EpsEdge)
                 (ΔQs : list Q)
                 (ΔpushE : list WorkEdge)
                 (ΔpopE : list WorkEdge)
                 (ΔepsE : list EpsEdge)
                 (ΔH : list EpsEdge),
                   Working_rpds.

Inductive Qs_contained (Qs : set Q) (ΔQs : set Q) (isQ : Q -> bool) : Prop :=
  qs_contained_intro : (forall q, In q Qs \/ In q ΔQs -> isQ q) -> Qs_contained Qs ΔQs isQ.

Inductive Edges_contained (Es : set WorkEdge) (ΔEs : set WorkEdge) (action : Γ -> Stack_Action Γ)
          (δ : action_relation Q (Stack_Action Γ)) : Prop :=
  es_contained_intro : (forall q γ q', In (q,γ,q') Es \/ In (q,γ,q') ΔEs -> δ q (action γ) q') -> 
                       Edges_contained Es ΔEs action δ.

Inductive Eps_contained (Es : set EpsEdge) (ΔEs : set EpsEdge) (δ : action_relation Q (Stack_Action Γ)) : Prop :=
  eps_contained_intro : (forall q q', In (q,q') Es \/ In (q,q') ΔEs -> δ q (eps_action Γ) q') ->
                        Eps_contained Es ΔEs δ.

Inductive EpsC_contained (Es : set EpsEdge) (ΔEs : set EpsEdge) (δε : relation Q) : Prop :=
  epsc_contained_intro : (forall q q', In (q,q') Es \/ In (q,q') ΔEs -> δε q q') -> EpsC_contained Es ΔEs δε.

Inductive Working_contained : Working_rpds -> forall (rpds : RPDS) (δε : relation Q),
                                                Epsilon_closure rpds δε -> Prop :=
  contained_intro : forall Qs pushE popE epsE q0 H ΔQs ΔpushE ΔpopE ΔepsE ΔH
                    (isQ : Q -> bool) (isΓ : Γ -> bool) (δ : action_relation Q (Stack_Action Γ)) prf1 prf2 prf3
                    q0isQ
                    (δε : relation Q) is_epsclosed,
                      Qs_contained Qs ΔQs isQ ->
                      Edges_contained pushE ΔpushE (@push_action Γ) δ ->
                      Edges_contained popE ΔpopE (@pop_action Γ) δ ->
                      Eps_contained epsE ΔepsE δ ->
                      EpsC_contained H ΔH δε ->
                      @Working_contained
                        (working_rpds Qs pushE popE epsE q0 H ΔQs ΔpushE ΔpopE ΔepsE ΔH)
                        (rpds_intro (pds_intro isQ isΓ δ prf1 prf2 prf3) q0 q0isQ)
                        δε is_epsclosed.

Section FiniteAssumptions.
Variables (Qeq_dec : dec_type Q) (Γeq_dec : dec_type Γ) (rpds : RPDS).
Definition pullback_true {A} (f : A -> bool) := sigT (fun a => f a = true).
Variables (fin_Q : NeFiniteT (pullback_true (pds_Q (rpds_pds rpds))))
          (fin_Γ : NeFiniteT (pullback_true (pds_Γ (rpds_pds rpds)))).
Variables (δsp : Q -> list (Q * (Stack_Action Γ))) (* eval *)
          (δp : Q -> Γ -> list Q) (* apply, though can't push immediately after pop *)
          (δsp_correspondence :
             forall q q',
               (((rpds_rel rpds) q (eps_action Γ) q') <-> In (q', (eps_action Γ)) (δsp q)) /\
               forall γ, (((rpds_rel rpds) q (push_action γ)  q') <-> In (q', (push_action γ)) (δsp q)) /\
                         (In (q', (pop_action γ)) (δsp q) -> False))
          (δp_correspondence : forall q γ q', ((rpds_rel rpds) q (pop_action γ) q') <-> In q' (δp q γ)).

Definition Edge := (Q * (Stack_Action Γ) * Q)%type.
Definition PushPred := (Q * Γ)%type.
Hint Immediate Qeq_dec Γeq_dec.
Definition stackact_eq_dec : dec_type (Stack_Action Γ). decide equality. Defined.
Hint Immediate stackact_eq_dec.
Definition edge_eq_dec : dec_type Edge. do 2 decide equality. Defined.
Definition eps_edge_eq_dec : dec_type EpsEdge. decide equality. Defined.
Definition work_edge_eq_dec : dec_type WorkEdge. do 2 decide equality. Defined.
Definition QΓ_eq_dec : dec_type PushPred. decide equality. Defined.
Hint Immediate edge_eq_dec eps_edge_eq_dec work_edge_eq_dec.
Definition working_eq_dec : dec_type Working_rpds. repeat decide equality. Defined.

Fixpoint push_eps_aux (q0 : Q) (todo : list (Q * (Stack_Action Γ)))
         (actions : list WorkEdge) (epss : list EpsEdge) (states : list Q) :=
  match todo with
      nil => (actions, epss, states)
    | (q,γa)::todo' => match γa with
                           eps_action => push_eps_aux q0 todo' actions ((q0,q)::epss) (q::states)
                         | push_action γ => push_eps_aux q0 todo' ((q0,γ,q)::actions) epss (q::states)
                         (* impossible *)
                         | pop_action _ => push_eps_aux q0 todo' actions epss states
                       end
  end.

Lemma push_eps_contained_inv :
  forall q0 todo actions epss states,
    (forall q, In q states -> rpds_Q rpds q) ->
    (forall γa q, In (q,γa) todo -> ((rpds_rel rpds) q0 γa q)) ->
    (forall q γ q', In (q,γ,q') actions -> (rpds_rel rpds) q (push_action γ) q') ->
    (forall q q', In (q,q') epss -> (rpds_rel rpds) q (eps_action _) q') ->
    match push_eps_aux q0 todo actions epss states with
        (actions',epss',states') =>
        (forall q, In q states' -> rpds_Q rpds q) /\
        (forall q γ q', In (q,γ,q') actions' -> (rpds_rel rpds) q (push_action γ) q') /\
        (forall q q', In (q,q') epss' -> (rpds_rel rpds) q (eps_action _) q')
    end.
Proof.
  destruct rpds as [[isQ isΓ δ prf1 prf2 prf3] s0 ?].

  induction todo as [|(q,γa) todo_ IH]; intros actions epss states Hstates Htodo Hactions Hepss; repeat split; auto.
  cut (forall γa q, In (q, γa) todo_ -> δ q0 γa q);[|intros; apply Htodo; right; auto].
  intro HT; simpl; destruct γa as [|γ|γ];
  [| |apply IH; solve [auto | intros γa q' Hin; apply Htodo; right; auto]].
  (* eps case *)
  case_eq (push_eps_aux q0 todo_ actions ((q0, q) :: epss) (q :: states)).
  specialize (IH actions ((q0,q)::epss) (q::states)).
  cut (forall q', In q' (q :: states) -> isQ q');
    [|intros q'' [Heq''|Hrest];
       [pose (Htodo' := Htodo (eps_action _) q (or_introl (eq_refl _)));
         subst; apply prf1 in Htodo'; intuition auto
       |apply Hstates; auto]].
  intro HQ; specialize (IH HQ HT Hactions).
  cut (forall q_ q', In (q_,q') ((q0,q)::epss) -> δ q_ (eps_action _) q');
    [|intros q_ q_' [eq_|Hrest];
       [injects eq_;apply (Htodo (eps_action _) q_' (or_introl (eq_refl _)))
       |apply Hepss; auto]].
  intro HE; specialize (IH HE).
  intros [actions' epss'] states' Hreceq; rewrite Hreceq in IH;
  destruct IH as [IHQ [IHE IHε]]; repeat split; auto.
  (* push case *)
  case_eq (push_eps_aux q0 todo_ ((q0,γ,q)::actions) epss (q :: states)).
  specialize (IH ((q0,γ,q)::actions) epss (q :: states)).
  cut (forall q', In q' (q :: states) -> isQ q');
    [|intros q'' [Heq''|Hrest];
       [pose (Htodo' := Htodo (push_action γ) q (or_introl (eq_refl _)));
         subst; apply prf2 in Htodo'; intuition auto
       |apply Hstates; auto]].
  intro HP; specialize (IH HP HT).
  cut (forall q' γ' q'', In (q', γ',q'') ((q0,γ,q)::actions) -> δ q' (push_action γ') q'');
    [|intros ? ? ? [Heq|Hrest];[injects Heq;apply (Htodo (push_action γ') q'' (or_introl (eq_refl _)))
                               |apply Hactions; auto]].
  intro HA; specialize (IH HA Hepss).
  intros [actions' epss'] states' Hreceq; rewrite Hreceq in IH; 
  destruct IH as [IHQ [IHE IHε]]; repeat split; auto.
Qed.

Definition sprout (q : Q) : (list WorkEdge * list EpsEdge * list Q):=
  push_eps_aux q (δsp q) nil nil nil.

Lemma sprout_contained_inv :
  forall q,
    match sprout q with
        (actions',epss',states') =>
        (Forall (rpds_Q rpds) states') /\
        (Forall (fun edge => match edge with (q, γ, q') => (rpds_rel rpds) q (push_action γ) q' end) actions') /\
        (Forall (fun eedge : EpsEdge => let (q,q'):=eedge in rpds_rel rpds q (eps_action _) q') epss')
    end.
Proof.
  intro q0; unfold sprout. 
  (* Have to give nil's types due to rewriting bug *)
  pose (L := @push_eps_contained_inv q0 (δsp q0) (@nil WorkEdge) (@nil EpsEdge) [] (fun q H => match H with end)).
  cut (forall γa q, In (q,γa) (δsp q0) -> rpds_rel rpds q0 γa q).
  intro Htodo; specialize (L Htodo (fun x y z H => match H with end) (fun x y H => match H with end)).  
  case_eq (push_eps_aux q0 (δsp q0) [] [] []); intros [actions' eps'] states' Heq.
  rewrite Heq in L; destruct L as [Hstates [Hactions Heps]].
  repeat rewrite Forall_forall; repeat split; auto.
  intros [[q γ] q']; apply Hactions.
  intros [q q']; apply Heps.
  intros γa q Hin;
  destruct (δsp_correspondence q0 q) as [Heps Haction];
   destruct γa as [|γ|γ];
   [rewrite Heps
   |destruct (Haction γ) as [Hpush Hpop]; rewrite Hpush
   |destruct (Haction γ) as [Hpush Hpop]; elimtype False; apply Hpop]; auto.
Qed.

Definition eps_grab (q : Q) (H : list EpsEdge) (acc : set Q) (backwards : bool) : set Q :=
  fold_left (fun acc (pair : Q * Q) =>
               let (q',q'') := pair in
               if backwards then
                 (if (Qeq_dec q q'') then
                    set_add Qeq_dec q' acc
                  else acc)
               else (if (Qeq_dec q q') then
                       set_add Qeq_dec q'' acc
                     else acc)) H acc.
Definition eps_pred (q : Q) (H : list EpsEdge) : list Q :=
  eps_grab q H nil true.

Definition eps_succ (q : Q) (H : list EpsEdge) : list Q :=
  eps_grab q H nil false.

Lemma eps_grab_acc : forall q (backwards : bool) H acc q',
                       In q' acc -> In q' (eps_grab q H acc backwards).
Proof.
  induction H as [|(q',q'') H' IH]; intros acc q_ Hin;
  auto; simpl.
  destruct backwards;
    [destruct (Qeq_dec q q'')|destruct (Qeq_dec q q')]; subst;
  apply IH; try solve [apply set_add_intro1; auto | auto].
Qed.

Lemma eps_grab_correct : forall q (backwards : bool) H acc,
                           if backwards then
                             forall q', In (q',q) H \/ In q' acc <-> In q' (eps_grab q H acc true)
                           else
                             forall q', In (q,q') H \/ In q' acc <-> In q' (eps_grab q H acc false).
Proof.
  induction H as [|(q',q'') H' IH]; intro acc; destruct backwards; try solve [intuition; listac].
  intros q_; split; intro H.
  - inversion H as [[topH|restH]|inAcc];
    [simpl; injects topH; split_refl Qeq_dec q;
     rewrite <- IH; right; apply set_add_intro2; auto;
     pose (restH' := or_introl (In q_ acc) restH);
     rewrite IH in restH'
     |simpl;
       destruct (Qeq_dec q q'');rewrite <- IH;
       [subst;left;auto|left; auto]
     |simpl;
       destruct (Qeq_dec q q'');rewrite <- IH;subst;
       right;[apply set_add_intro1|];auto].
  - simpl in H; destruct (Qeq_dec q q''); subst.
    rewrite <- IH in H; inversion H as [inH|inacc];
    [left;right;auto|].
    apply set_add_elim in inacc; inversion inacc as [Heq|Hin];
    [subst;left;left|]; auto.
    rewrite <- IH in H; inversion H;[subst;left;right|right]; auto.
  - intros q_; split; intro H; simpl.
    inversion H as [[topH|restH]|inacc];
      [injects topH; split_refl Qeq_dec q;
       rewrite <- IH; right; apply set_add_intro2; auto
      |destruct (Qeq_dec q q'); subst; rewrite <- IH; left; auto
      |destruct (Qeq_dec q q'); subst;
       rewrite <- IH; right; [apply set_add_intro1|]; auto].
    simpl in H.
    destruct (Qeq_dec q q'); subst; 
    rewrite <- IH in H;
    inversion H as [inH|inacc];
    [left; right
    |destruct (set_add_elim _ _ _ _ inacc) as [Heq|Hacc];
      [subst; left; left|right]; auto
    | |]; auto.
Qed.

Lemma eps_pred_correct : forall q H q', In (q',q) H <-> In q' (eps_pred q H).
Proof.
  intros; pose (L := @eps_grab_correct q true H nil q');
  simpl in L; split; intro X;
  [rewrite <- L;left; auto
  |rewrite <- L in X; inversion X; [auto|contradiction]].
Qed.

Lemma eps_succ_correct : forall q H q', In (q,q') H <-> In q' (eps_succ q H).
Proof.
  intros; pose (L := @eps_grab_correct q false H nil q');
  simpl in L; split; intro X;
  [rewrite <- L;left; auto
  |rewrite <- L in X; inversion X; [auto|contradiction]].
Qed.

Definition add_pops_from_pushes (s : Q) (q' : Q) (γ : Γ)
           (todo : list Q)
           (acc : list WorkEdge * list EpsEdge * list Q) :=
  fold_left (fun acc' q'' =>
               match acc' with
                   (ΔE,ΔH,ΔQ) =>
                   (* always pop actions *)
                   ((set_add work_edge_eq_dec (q', γ,q'') ΔE),
                    (set_add eps_edge_eq_dec (s,q'') ΔH),
                    (set_add Qeq_dec q'' ΔQ))
               end)
            todo acc.
Check Balanced_path_with.

Lemma push_balance_pop : forall actions (γ : Γ), Balanced_actions actions [] ->
                                           Balanced_actions (push_action γ :: actions ++ [pop_action γ]) [].
Proof.
  intros; hnf.
  cut (Balanced_actions ((push_action γ :: actions) ++ [pop_action γ]) ([push_action γ] ++ [pop_action γ]));
    [|apply balance_actions_at_end;
       hnf; pose (L := balance_actions_at_front H [push_action γ]); rewrite app_nil_r in L; auto].
  intro path;simpl in path.
  cut (Balanced_actions [push_action γ; pop_action γ] []).
  intro path'.
  apply (drt_append path path').
  eapply drt_step; [apply drt_refl|apply (balance_cancel [] [])].
Qed.

Lemma push_balance_pop' : forall actions0 q actions q' γ qprev q'post, Balanced_path_with rpds q q' (actions0 ++ [push_action γ])
                                                                            actions ->
                                                         rpds_rel rpds qprev (push_action γ) q ->
                                                         rpds_rel rpds q' (pop_action γ) q'post ->
                                                         Balanced_path_with rpds qprev q'post actions0 (actions ++ [pop_action γ]).
Admitted.

Lemma add_pops_from_pushes_contained_inv :
  forall s q'prev q' γ δε
         (εclosure : Epsilon_closure rpds δε)
         (push_edge : rpds_rel rpds s (push_action γ) q'prev)
         (q'path : δε q'prev q')
         (reachs : Root_reachable_state rpds s),
    forall todo ΔE ΔH ΔQ,
      (forall q, In q todo -> rpds_rel rpds q' (pop_action γ) q /\
      Root_reachable_state rpds q) ->
      (forall q γ q', In (q,γ,q') ΔE -> rpds_rel rpds q (pop_action γ) q') ->
      (forall q q', In (q,q') ΔH -> NE_Balanced_path rpds q q') ->
      (forall q, In q ΔQ -> rpds_Q rpds q) ->
      match add_pops_from_pushes s q' γ todo (ΔE,ΔH,ΔQ) with
          (ΔE,ΔH,ΔQ) => 
          (forall q γ q', In (q,γ,q') ΔE -> rpds_rel rpds q (pop_action γ) q') /\
          (forall q q', In (q,q') ΔH -> NE_Balanced_path rpds q q') /\
          (forall q, In q ΔQ -> rpds_Q rpds q)
      end.
Proof.
  induction todo as [|q todo' IH]; intros ΔE ΔH ΔQ.
  intuition (simpl; auto).
  intros HT HE HH HQ.
  simpl.
  case_eq (add_pops_from_pushes s q' γ todo' (set_add work_edge_eq_dec (q',γ,q) ΔE,
                                              set_add eps_edge_eq_dec (s,q) ΔH,
                                              set_add Qeq_dec q ΔQ)).
  intros [ΔE' ΔH'] ΔQ' Heq.
  specialize (IH (set_add work_edge_eq_dec (q',γ,q) ΔE) (set_add eps_edge_eq_dec (s,q) ΔH)
                 (set_add Qeq_dec q ΔQ)).
  cut (forall q, In q todo' -> rpds_rel rpds q' (pop_action γ) q /\ Root_reachable_state rpds q);
    [intro HT'; specialize (IH HT')|intros q_ Hin; apply HT; right; auto].
  cut (forall q_ γ_ q_', In (q_,γ_,q_') (set_add work_edge_eq_dec (q', γ, q) ΔE) ->
                         rpds_rel rpds q_ (pop_action γ_) q_');
    [intro HE'; specialize (IH HE')
    |intros ? ? ? Hin; destruct (set_add_elim _ _ _ _ Hin) as [Heq_|HErest];
      [injects Heq_; apply HT; left; reflexivity
      |apply HE; auto]].
  cut (forall q_ q_', In (q_,q_') (set_add eps_edge_eq_dec (s,q) ΔH) -> NE_Balanced_path rpds q_ q_');
    [intro HH'; specialize (IH HH')
    |intros ? ? Hin; destruct (set_add_elim _ _ _ _ Hin) as [Heq_|HHrest];[|apply HH; auto];
     injects Heq_;
     destruct (HT q (or_introl (eq_refl _))) as [Hstep [actions Hreach]];
     inversion εclosure as [? Hbal]; subst].
  Focus 2.
  rewrite Hbal in q'path.
  destruct q'path as [q'actions [q'reach [Hq'actions [Hq'path q'bal]]]].
  destruct reachs as [reachsactions srootreach].
  exists reachsactions; split; auto; exists (push_action γ :: Hq'actions ++ [pop_action γ]); split.
  discriminate.
  hnf.
  apply push_balance_pop.
  rewrite Hbal;
     destruct reachs as [actionss Hreachs];
     exists actionss; split; [assumption
                             |]].
  Focus 2.
  rewrite Hbal in q'path; destruct q'path as [qactions [Hprevreach [prevactions [Hqreach Hprevbal]]]].
  exists (push_action γ :: prevactions ++ [pop_action γ]);
    split.
  eapply (@rtaa_step _ _ _ _ _ s q' q (push_action γ :: prevactions) (pop_action γ)).
  eapply (@rtaa_step _ _ _ _ _ s s q' [] (push_action γ));
    [apply rtaa_refl
    |
    |rewrite app_nil_r; constructor;destruct Hreachs;[constructor|auto]].
     |auto
     |hnf;rewrite <- app_assoc; constructor;constructor; destruct Hreachs;[constructor|auto]]].
  cut (forall q_, In q_ (set_add Qeq_dec q ΔQ) -> rpds_Q rpds q_);
    [intro HQ'; specialize (IH HQ');
     (* invisible, but still matters *)  
     unfold WorkEdge,EpsEdge,set in Heq,IH; rewrite Heq in IH
    |intros ? Hin; destruct (set_add_elim _ _ _ _ Hin) as [Heq_|HQrest];
     [subst;
       destruct rpds as [[isQ isΓ δ prf1 prf2 prf3] s0 ?];
       destruct (HT q (or_introl (eq_refl _))) as [HTq _];
       apply prf3 in HTq; intuition auto
     |apply HQ;auto]].
  destruct IH as [IHE [IHH IHQ]].
  repeat split; auto.
Qed.

Definition add_pops_from (s : Q) (γ : Γ) (todo : list Q) (acc : list WorkEdge * list EpsEdge * list Q) :=
  fold_left (fun acc' q' =>
               add_pops_from_pushes s q' γ (δp q' γ) acc')
            todo acc.

Lemma add_pops_from_contained_inv :
  forall s q' γ δε
         (εclosure : Epsilon_closure rpds δε)
         (push_edge : rpds_rel rpds s (push_action γ) q')
         (reachs : Root_reachable_state rpds s),
    forall todo ΔE ΔH ΔQ,
      (forall q, In q todo -> rpds_rel rpds q' (pop_action γ) q /\
                              Root_reachable_state rpds q) ->
      (forall q γ q', In (q,γ,q') ΔE -> rpds_rel rpds q (pop_action γ) q') ->
      (forall q q', In (q,q') ΔH -> δε q q') ->
      (forall q, In q ΔQ -> rpds_Q rpds q) ->
      match add_pops_from s γ todo (ΔE,ΔH,ΔQ) with
          (ΔE,ΔH,ΔQ) => 
          (forall q γ q', In (q,γ,q') ΔE -> rpds_rel rpds q (pop_action γ) q') /\
          (forall q q', In (q,q') ΔH -> δε q q') /\
          (forall q, In q ΔQ -> rpds_Q rpds q)
      end.


Definition add_push (H : list EpsEdge) (sγq : WorkEdge) :=
  match sγq with
      (s, γ, q) => add_pops_from s γ (eps_succ q H) (nil,nil,nil)
  end.

Definition pushes_to_acc (s' : Q) (E : list WorkEdge) (acc : list (Q * Γ)) :=
  fold_left (fun acc edge =>
               match edge with
                   (q, γ, q') =>
                   if (Qeq_dec s' q') then
                     set_add QΓ_eq_dec (q,γ) acc
                   else acc end) E acc.
Definition pushes_to (s' : Q) (E : list WorkEdge) : list (Q * Γ) :=
  pushes_to_acc s' E nil.

Definition push_pred_acc (pushE : list WorkEdge) (s' : Q) (γ : Γ) (acc : list Q) :=
  fold_left (fun acc edge =>
               match edge with
                   (q, γ', q') =>
                   if (Γeq_dec γ γ') then
                     if (Qeq_dec s' q') then
                       set_add Qeq_dec q acc
                     else acc
                   else acc end) pushE acc.
Definition push_pred (pushE : list WorkEdge) (s' : Q) (γ : Γ) :=
  push_pred_acc pushE s' γ nil.

Definition add_eps_from (q : Q) (base : list Q) (acc : list EpsEdge) :=
  fold_left (fun acc' s => set_add eps_edge_eq_dec (s,q) acc') base acc.

Definition add_pop_acc (q : Q) (γ : Γ) (pushE : list WorkEdge) (base : list Q) (acc : list EpsEdge) :=
  fold_left (fun acc' s' => add_eps_from q (push_pred pushE s' γ) acc')
            base acc.
            
Definition add_pop (H : list EpsEdge) (pushE : list WorkEdge) (s''γq : WorkEdge) :=
  match s''γq with
      (s'',γ,q) => add_pop_acc q γ pushE (eps_pred s'' H) nil
  end.

Definition add_empty (H : list EpsEdge) (pushE : list WorkEdge) (s''s''' : EpsEdge) :=
  match s''s''' with
      (s'',s''') =>
      let post := (eps_succ s''' H) in
      fold_left
        (fun acc s' =>
           fold_left
             (fun (acc : list WorkEdge * list EpsEdge * list Q) s'''' =>
                match acc with
                    (ΔE,ΔH,ΔQ) =>
                    fold_left
                      (fun acc (sγ : PushPred) =>
                         let (s,γ) := sγ in
                         fold_left
                           (fun (acc : list WorkEdge * list EpsEdge * list Q) q =>
                              match acc with
                                  (ΔE,ΔH,ΔQ) =>
                                  (* all pop actions *)
                                  (set_add work_edge_eq_dec (s'''', γ, q) ΔE,
                                   set_add eps_edge_eq_dec (s,q) ΔH,
                                   set_add Qeq_dec q ΔQ)
                              end)
                           (δp s'''' γ)
                           acc)
                      (pushes_to s' pushE)
                      (ΔE, set_add eps_edge_eq_dec
                                   (s',s''')
                                   (set_add eps_edge_eq_dec
                                            (s'',s'''')
                                            (set_add eps_edge_eq_dec
                                                     (s',s'''') ΔH)), ΔQ)
                end)
             post acc)
        (eps_pred s'' H) (nil,nil,nil)
  end.
Definition WEQ_map {A} (f : A -> list WorkEdge * list EpsEdge * list Q) (l : list A) :=
  triple_union_map work_edge_eq_dec eps_edge_eq_dec Qeq_dec f l.
Definition wunion := set_union work_edge_eq_dec.
Definition eunion := set_union eps_edge_eq_dec.
Definition qunion := set_union Qeq_dec.
Definition step_wrpds (wrpds : Working_rpds) :=
  match wrpds with
      working_rpds Qs pushE popE epsE q0 H ΔQs ΔpushE ΔpopE ΔepsE ΔH =>
       match WEQ_map sprout ΔQs with
           (ΔpushE0, ΔepsE0, ΔQ0) =>
           match WEQ_map (add_push H) ΔpushE with
               (ΔpopE1, ΔepsE1, ΔQ1) =>
               let ΔepsE2 := union_map eps_edge_eq_dec (add_pop H pushE) ΔpopE in
               match WEQ_map (add_empty H pushE) ΔH with
                   (ΔpopE3, ΔepsE3,ΔQ3) =>
                   let Qs' := qunion Qs ΔQs in
                   let pushE' := wunion pushE ΔpushE in
                   let popE' := wunion popE ΔpopE in
                   let epsE' := eunion epsE ΔepsE in
                   let H' := eunion H ΔH in
                   let ΔpushE' := (set_diff work_edge_eq_dec ΔpushE0 pushE') in
                   let ΔpopE' := (set_diff work_edge_eq_dec (wunion ΔpopE1 ΔpopE3) popE') in
                   let ΔepsE' := (set_diff eps_edge_eq_dec ΔepsE0 epsE') in
                   let ΔQs' := (set_diff Qeq_dec
                                        (qunion ΔQ0 (qunion ΔQ1 (set_add Qeq_dec q0 ΔQ3)))
                                        Qs') in
                   let ΔH' := (set_diff eps_edge_eq_dec
                                        (set_union eps_edge_eq_dec
                                                   ΔepsE0
                                                   (set_union eps_edge_eq_dec
                                                              ΔepsE1
                                                              (set_union eps_edge_eq_dec
                                                                         ΔepsE2
                                                                         ΔepsE3)))
                                        H') in
                   working_rpds Qs' pushE' popE' epsE' q0 H' ΔQs' ΔpushE' ΔpopE' ΔepsE' ΔH'
               end
           end
       end
  end.

Definition Nonoverlapping {A} (s s' : list A) := forall a, In a s -> In a s' -> False.

Inductive Working_Inv : Working_rpds -> forall rpds crpds δε,
                                          Epsilon_closure rpds δε ->
                                          RPDS_compaction rpds crpds -> Prop :=
  inv_intro : forall Qs pushE popE epsE q0 H ΔQs ΔpushE ΔpopE ΔepsE ΔH
                     rpds crpds δε is_epsclosed (is_compact : RPDS_compaction rpds crpds),
                Nonoverlapping Qs ΔQs ->
                Nonoverlapping pushE ΔpushE ->
                Nonoverlapping popE ΔpopE ->
                Nonoverlapping epsE ΔepsE ->
                Nonoverlapping H ΔH ->
                @Working_contained (working_rpds Qs pushE popE epsE q0 H ΔQs ΔpushE ΔpopE ΔepsE ΔH)
                                   crpds δε (eps_closure_in_compaction is_epsclosed is_compact) ->
                @Working_Inv (working_rpds Qs pushE popE epsE q0 H ΔQs ΔpushE ΔpopE ΔepsE ΔH)
                             rpds crpds δε is_epsclosed is_compact.

Lemma nonoverlapping_diff : forall A (eq_dec : dec_type A) (l' l : set A), Nonoverlapping l (set_diff eq_dec l' l).
Proof.
  induction l'.
  intros ? ? ? bad; inversion bad.
  intros l a' Hin Hindiff;
  simpl in Hindiff.
  case_eq (set_mem eq_dec a l); intros H; rewrite H in Hindiff;
    [apply set_mem_correct1 in H;
     apply (IHl' _ _ Hin Hindiff)
    |apply set_mem_complete1 in H].
  apply set_add_elim in Hindiff.
  inversion Hindiff as [|H0];
    [subst; contradiction
    |apply (IHl' _ _ Hin H0)].
Qed.

Fixpoint ormap {A} (f : A -> bool) (l : list A) :=
  match l with
      nil => false
    | a::l' => orb (f a) (ormap f l')
  end.
Lemma ormap_Exists : forall A (f : A -> bool) (l : list A), ormap f l <-> Exists (fun a => f a = true) l.
Proof.
  induction l; split; intro H; try solve [inversion H].
  unfold ormap,orb in H;
  case_eq (f a); intros Heq; rewrite Heq in H;
    [apply Exists_cons_hd|rewrite IHl in H; apply Exists_cons_tl]; auto.
  inversion H as [? ? Heq|? ? Heq].
  unfold ormap,orb; rewrite Heq; reflexivity.
  rewrite <- IHl in Heq; unfold ormap,orb.
  rewrite Heq; destruct (f a); reflexivity.
Qed.

Lemma invariant : forall wrpds crpds δε
                         (εclosure : Epsilon_closure rpds δε)
                         (Hcompact : RPDS_compaction rpds crpds),
                    Working_Inv wrpds εclosure Hcompact ->
                    Working_Inv (step_wrpds wrpds) εclosure Hcompact.
Proof.
  destruct rpds as [[isQ isΓ δ prf1 prf2 prf3] s0 ?].
  intros wrpds crpds δε εclosure Hcompact Hinv.
  destruct crpds as [[isQc isΓc δc prf1c prf2c prf3c] cs0].
  cut (cs0 = s0); [intro;subst|inverts Hcompact; reflexivity].
  inversion Hcompact as [? ? ? ? δceps_good δcpush_good δcpop_good Qc_reach Γc_reach δc_reach]; subst.
  inversion Hinv as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Qnon pushnon popnon εnon hnon Hcontained]; subst;
  inversion Hcontained as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? InQs InPush InPop InEps InH]; subst;
  simpl.
  
  case_eq (WEQ_map sprout ΔQs); intros; subst;
  case_eq p; intros; subst;
  case_eq (WEQ_map (add_push H) ΔpushE); intros; subst;
  case_eq p; intros; subst;
  case_eq (WEQ_map (add_empty H pushE) ΔH); intros; subst;
  case_eq p; intros; subst; apply inv_intro;
  try solve [apply nonoverlapping_diff].
  pose (Goal := @contained_intro
                  (qunion Qs ΔQs) (wunion pushE ΔpushE) 
        (wunion popE ΔpopE) (eunion epsE ΔepsE) s0 
        (eunion H ΔH)
        (set_diff Qeq_dec (qunion s (qunion s3 (set_add Qeq_dec s0 s6)))
           (qunion Qs ΔQs))
        (set_diff work_edge_eq_dec s1 (wunion pushE ΔpushE))
        (set_diff work_edge_eq_dec (wunion s4 s7) (wunion popE ΔpopE))
        (set_diff eps_edge_eq_dec s2 (eunion epsE ΔepsE))
        (set_diff eps_edge_eq_dec
           (set_union eps_edge_eq_dec s2
              (set_union eps_edge_eq_dec s5
                 (set_union eps_edge_eq_dec
                    (union_map eps_edge_eq_dec (add_pop H pushE) ΔpopE) s8)))
           (eunion H ΔH)) isQ isΓ δ prf1 prf2 prf3 _ δε is_epsclosed).
  assert (isqc_imp_isq : forall q, isQc q -> isQ q)
         by (intro q; rewrite Qc_reach0;
             intros [? path];
             inversion path as [|? ? ? ? ? ? Hstep]; subst; [auto|compute in Hstep; destruct a; [eapply prf1|eapply prf2|eapply prf3]]; eauto).
  assert (subgoal1 :
            forall q : Q,
              In q (qunion Qs ΔQs) \/
              In q
                 (set_diff Qeq_dec (qunion s (qunion s3 (set_add Qeq_dec s0 s6)))
                           (qunion Qs ΔQs)) -> isQ q).
  - intros q [HqinU|Hqindiff];
    [unfold qunion in HqinU; destruct (set_union_elim _ _ _ _ HqinU) as [HinQs|HinΔQs];
     apply isqc_imp_isq; apply InQs; [left|right]; auto
    |].
  pose (Inqunion := set_diff_elim1 _ _ _ _ Hqindiff);
  pose (NotInqunion := set_diff_elim2 _ _ _ _ Hqindiff);
  unfold qunion in Inqunion; apply set_union_elim in Inqunion;
  inversion_clear Inqunion as [Hqins|Hmid];
    [|
     unfold qunion in Hmid; apply set_union_elim in Hmid;
     inversion_clear Hmid as [Hqins3|Hpost];
     [|apply set_add_elim in Hpost;
        inversion_clear Hpost as [qeqs0|Hqins6];
        [subst; auto|]]].

Admitted.

Definition Qsize : nat :=
  match fin_Q with
      existT n _ => n
end.
Definition Γsize : nat :=
  match fin_Γ with
      existT n _ => n
end.
          
Definition state_upperbound : nat := nat_expt 2 Qsize.
Definition eps_upperbound : nat := nat_expt 2 (Qsize * Qsize).
Definition edge_upperbound : nat := nat_expt 2 (Qsize * Qsize * Γsize).
Definition working_measure (wrpds : Working_rpds) : {_ : nat & {_ : nat & nat}} :=
  match wrpds with
      working_rpds Qs pushE popE epsE q0 H ΔQs ΔpushE ΔpopE ΔepsE ΔH =>
      existT _ 
             (state_upperbound - (length ΔQs))
             (existT _
                     ((edge_upperbound - (length pushE)) +
                      (edge_upperbound - (length popE)) +
                      (eps_upperbound - (length epsE)))
                     (eps_upperbound - (length H)))
  end.
Lemma nat_expt_pos : forall n m, n > 0 -> nat_expt n m > 0.
induction m; intro;
simpl. omega.
specialize (IHm H); unfold gt in *; apply NPeano.Nat.mul_pos_pos; auto.
Qed.
Lemma termination_measure : forall wrpds,

                              (step_wrpds wrpds = wrpds) \/
                              lexprod _ (fun _ => _) lt (fun _ => lexprod _ (fun _ => _) lt (fun _ => lt))
                                      (working_measure (step_wrpds wrpds))
                                      (working_measure wrpds).
Proof.
  intro; destruct (working_eq_dec (step_wrpds wrpds) wrpds); [left; auto|right].
  destruct wrpds; simpl;
  case_eq (WEQ_map sprout ΔQs); intros; subst;
  case_eq p; intros; subst;
  case_eq (WEQ_map (add_push H) ΔpushE); intros; subst;
  case_eq p; intros; subst;
  case_eq (WEQ_map (add_empty H pushE) ΔH); intros; subst;
  case_eq p; intros; subst; simpl.
  destruct ΔQs.
  destruct ΔpushE.
  destruct ΔpopE.
  destruct ΔepsE.
  destruct ΔH.
  simpl in n; case_eq (set_mem Qeq_dec q0 Qs); try solve [intro blah; rewrite blah in n; elimtype False; apply n; reflexivity].
  intro notin; rewrite notin in n.
  simpl in *; unfold WEQ_map,triple_union_map in H0,H1,H2; injects H0; injects H1; injects H2.
  constructor; simpl; rewrite notin; simpl. 
  unfold state_upperbound; pose (@nat_expt_pos 2 Qsize); cut (2 > 0); [intro|]; omega.
  simpl in *; unfold WEQ_map,triple_union_map in H0,H1,H2; injects H0; injects H1.
simpl in H2.
apply right_lex.
constructor.

Theorem lfp_working_complete : 
  
End FiniteAssumptions.



Remark example : Balanced_actions [eps_action bool ; push_action true ; eps_action bool ; pop_action true ; push_action false] [false].
assert (subgoal:  Balanced_actions
     [eps_action bool; push_action true; eps_action bool;
      pop_action true] [])
       by (apply (balance_eps [eps_action bool; push_action true] [pop_action true]),
                 (balance_pushpop [eps_action bool] [] true);
           autorewrite with list;
           apply (balance_eps [] []);
           simpl; constructor).
apply (balance_push _ subgoal).
Qed.