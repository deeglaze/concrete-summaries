Require Import List ListSet CpdtTactics basic fmaplist ListSetFacts.

Generalizable All Variables.
Set Implicit Arguments.

Definition in_list_list {A B} (l : list (A * (list B))) (a : A) (b : B) : Prop :=
  exists bs, (MapsTo l a bs) /\ (set_In b bs).

Definition subset_list_list {A B} (l : list (A * (list B))) (a : A) (b : list B) : Prop :=
  exists bs, (MapsTo l a bs) /\ (Subset b bs).

Section ListJoin.
Variables (A B C : Type) (eq_dec : dec_type A)
          (combine : list (A * B) -> B -> C -> B)
          (base : list (A * B) -> C -> B).
Fixpoint list_join  (l_orig : list (A * B))
         (a : A) (c : C)
         (l : list (A * B)) : list (A * B) :=
  match l with
      | nil => (a,base l_orig c)::nil
      | (a',b)::l' => if (eq_dec a a') then
                        (a,(combine l_orig b c))::l'
                      else (a',b)::(list_join l_orig a c l')
  end.
Definition singleton {A} (eq_dec : dec_type A) (x : A) : list A := set_add eq_dec x (empty_set _).
End ListJoin.

Inductive EntryLE {A B} (s : list (A * set B)) : A -> set B -> Prop :=
  entryle_intro : forall a vs vs' (Hmap : MapsTo s a vs') (Hsub : Subset vs vs'), EntryLE s a vs.
Definition MappingLE {A B} (s s' : list (A * set B)) := forall a vs (Hmap : MapsTo s a vs), EntryLE s' a vs.

Section ListJoin_facts.
Variables (A B C : Type) (eq_dec : dec_type A)
          (combine : list (A * list C) -> list C -> C -> list C)
          (base : list (A * list C) -> C -> list C)
          (combine' : list (A * list C) -> list C -> B -> list C)
          (base' : list (A * list C) -> B -> list C)
          (Hextensive : (forall l b c, In c (combine l b c)))
          (Hextensive' : (forall l cs b, Subset (base' l b) (combine' l cs b)))
          (Hsingleton : (forall l c, In c (base l c))).
Lemma in_list_join :
  forall l l' a c,
    (forall ab, In ab l -> In ab l') ->
  in_list_list (list_join eq_dec combine base l' a c l) a c.
Proof.
  intros l l' a c Hcontain;
  induction l as [|(a',b) l_ IH]; simpl;[
  exists (base l' c); split; [left|]; apply Hsingleton; auto
  |destruct (eq_dec a a') as [Heq | Hneq];
   [subst; exists (combine l' b c); split; [left|apply Hextensive]
   |assert (IHneed : (forall ab, In ab l_ -> In ab l')) by (intros (a_,bs') Hin; apply Hcontain; right; auto);
     set (mumble := (IH IHneed));
     inversion mumble as [wit Hwit]; subst; destruct Hwit as [Hmap Hin];
     exists wit; split; [apply map_rst|]]; auto].
Qed.

Lemma in_list_join' :
  forall l l' a c,
    (forall ab, In ab l -> In ab l') ->
  subset_list_list (list_join eq_dec combine' base' l' a c l) a (base' l' c).
Proof.
  intros l l' a c Hcontain;
  induction l as [|(a',b) l_ IH]; simpl;[
  exists (base' l' c); split; [left|]; apply subset_refl
  |destruct (eq_dec a a') as [Heq | Hneq];
   [subst; exists (combine' l' b c); split; [left|apply Hextensive']
   |assert (IHneed : (forall ab, In ab l_ -> In ab l')) by (intros (a_,bs') Hin; apply Hcontain; right; auto);
     set (mumble := (IH IHneed));
     inversion mumble as [wit Hwit]; subst; destruct Hwit as [Hmap Hin];
     exists wit; split; [apply map_rst|]]; auto].
Qed.

Hint Constructors MapsTo Unmapped.
Theorem list_join_mapsto_elim : forall l l' a c a' cs,
                           MapsTo (list_join eq_dec combine base l' a c l) a' cs ->
                           (a = a' /\ ((Unmapped l a /\ cs = (base l' c))
                                       \/
                                       (exists cs', MapsTo l a cs' /\ cs = (combine l' cs' c))))
                             \/
                           (a <> a' /\ MapsTo l a' cs).
Proof.
  induction l as [|(a_,b_) l_ IH]; intros.
  inversion H; subst; auto.

  simpl in H;
  destruct (eq_dec a a_) as [Heq|Hneq];
  [inversion H as [|? ? ? Hrest]; subst;
   [subst a_; left; split; [|right; exists b_]
   |right; inversion H; subst]; auto
  |].
  inversion H as [|? ? ? ? ? Hneq' Hmap]; subst;
  [auto
  |destruct (IH l' a c a' cs Hmap) as [[Haeq [[Hunmapped csbase]|[cs' [Hmap' cscombine]]]]|[Haneq Hmap']];
   [left|left; split; [|right; exists cs'] |]]; auto.
Qed.
 
Theorem list_join_mapsto_elim' : forall l l' a c a' cs,
                           MapsTo (list_join eq_dec combine' base' l' a c l) a' cs ->
                           (a = a' /\ ((Unmapped l a /\ cs = (base' l' c))
                                       \/
                                       (exists cs', MapsTo l a cs' /\ cs = (combine' l' cs' c))))
                             \/
                           (a <> a' /\ MapsTo l a' cs).
Proof.
  induction l as [|(a_,b_) l_ IH]; intros.
  inversion H; subst; auto.

  simpl in H;
  destruct (eq_dec a a_) as [Heq|Hneq];
  [inversion H as [|? ? ? Hrest]; subst;
   [subst a_; left; split; [|right; exists b_]
   |right; inversion H; subst]; auto
  |].
  inversion H as [|? ? ? ? ? Hneq' Hmap]; subst;
  [auto
  |destruct (IH l' a c a' cs Hmap) as [[Haeq [[Hunmapped csbase]|[cs' [Hmap' cscombine]]]]|[Haneq Hmap']];
   [left|left; split; [|right; exists cs'] |]]; auto.
Qed.

Lemma unmapped_join : `{Unmapped l a -> a <> a' -> Unmapped (list_join eq_dec combine base l' a' c l) a}.
Proof.
  induction l as [|(a,b) l_ IH]; intros a0 a' l' c H ?;
   simpl; [repeat constructor
          |destruct (eq_dec a' a) as [Heq|Hneq];
            [subst; inversion H; constructor
            |constructor;inversion H;[apply IH|]]]; auto.
Qed.

Lemma unmapped_join' : `{Unmapped l a -> a <> a' -> Unmapped (list_join eq_dec combine' base' l' a' c l) a}.
Proof.
  induction l as [|(a,b) l_ IH]; intros a0 a' l' c H ?;
   simpl; [repeat constructor
          |destruct (eq_dec a' a) as [Heq|Hneq];
            [subst; inversion H; constructor
            |constructor;inversion H;[apply IH|]]]; auto.
Qed.

Lemma mapsto_join_neq : `{MapsTo l a b -> a <> a' -> MapsTo (list_join eq_dec combine base l' a' c l) a b}.
Proof.
  induction l as [|(a_,b_) l_ IH]; intros a b a' l' c Hmap Hneq;
  inversion Hmap as [|? ? ? ? ? Hneq' Hmap']; subst; simpl.
  split_refl2 eq_dec a' a.
  destruct (eq_dec a' a_);
    [subst; apply map_rst; auto
    |apply map_rst,IH; auto].
Qed.

Lemma mapsto_join_neq' : `{MapsTo l a b -> a <> a' -> MapsTo (list_join eq_dec combine' base' l' a' c l) a b}.
Proof.
  induction l as [|(a_,b_) l_ IH]; intros a b a' l' c Hmap Hneq;
  inversion Hmap as [|? ? ? ? ? Hneq' Hmap']; subst; simpl.
  split_refl2 eq_dec a' a.
  destruct (eq_dec a' a_);
    [subst; apply map_rst; auto
    |apply map_rst,IH; auto].
Qed.

Lemma join_an_unmapped : `{Unmapped l a -> MapsTo (list_join eq_dec combine base l' a c l) a (base l' c)}.
Proof.
  induction l as [|(a,b) l_ IH]; intros; simpl;[constructor|].
  destruct (eq_dec a0 a) as [Heq | Hneq];
    [subst; inversion H; bad_eq
    |constructor; [|apply IH; inversion H]; auto].
Qed.  

Lemma join_an_unmapped' : `{Unmapped l a -> MapsTo (list_join eq_dec combine' base' l' a c l) a (base' l' c)}.
Proof.
  induction l as [|(a,b) l_ IH]; intros; simpl;[constructor|].
  destruct (eq_dec a0 a) as [Heq | Hneq];
    [subst; inversion H; bad_eq
    |constructor; [|apply IH; inversion H]; auto].
Qed.  

Lemma functional_join : `{Functional l -> Functional (list_join eq_dec combine base l' a c l)}.
Proof.
  induction l as [|(a,b) l_ IH]; simpl;
  [intros; repeat constructor
  |intros l' a' c F].
  destruct (eq_dec a' a) as [Heq|Hneq];
  [subst; apply functional_exchange with (b := b)
  |constructor; inversion F; [apply IH|apply unmapped_join]]; auto.
Qed.


Lemma maple_refl : forall (l : list (A * set C)), MappingLE l l.
Proof. 
  induction l as [|(a_,b_) l_ IH]; intros a' b' Hmap;
  [inversion Hmap
  |apply entryle_intro with (vs' := b'); [|apply subset_refl]; auto].
Qed.

Lemma maple_trans: forall (l l' l'' : list (A * set C)) (Hmap0 : MappingLE l l') (Hmap1 : MappingLE l' l''), MappingLE l l''.
Proof.
  intros; intros a cs Hmap;
  pose (mumble := Hmap0 a cs Hmap);
  inversion mumble as [? ? cs' map' sub']; subst;
  pose (grumble := Hmap1 a cs' map');
  inversion grumble as [? ? cs'' map'' sub'']; subst;
  exists cs'';[|transitivity cs']; auto.
Qed.

Lemma maple_top : forall (l : list (A * set C)) a b b', Subset b b' -> MappingLE ((a,b) :: l) ((a,b') :: l).
Proof.
  intros.
  intros a' b'' Hmap.
  inversion Hmap as [|? ? ? ? ? Hneq Hmap']; subst.
  apply entryle_intro with (vs' := b');[constructor|assumption].
  apply entryle_intro with (vs' := b'');[constructor; auto|apply subset_refl].
Qed.

Lemma maple_bottom : forall (l l' : list (A * set C)) ab (Htail : MappingLE l l'), MappingLE (ab :: l) (ab :: l').
Proof.
  intros. 
  intros ? ? Hmap; inversion Hmap as [|? ? ? ? ? Hneq Hmap']; subst;
  [exists vs; [constructor|apply subset_refl]
        |].
  pose (mumble := Htail a vs Hmap').
  inversion mumble as [? ? vs' Hmap_ Hsub_]; subst.
  exists vs'; [constructor|]; auto.
Qed.

Variable Hextensive2 : (forall l b c c', In c' b -> In c' (combine l b c)).
Lemma in_list_join2 :
  forall l l' a a' c c',
  in_list_list l a' c' ->
  in_list_list (list_join eq_dec combine base l' a c l) a' c'.
Proof.
  intros l l' a a' c c' Hold;
  induction l; simpl;
  inversion Hold as [bs Hwit]; destruct Hwit as [Hpairin Hsetin]; subst;
  [(* base case *) inversion Hpairin
  |destruct a0; destruct (eq_dec a a0) as [Heq | Hneq]; subst;
   [(* Heq *)
     subst; inversion Hpairin; subst;
    [exists (combine l' bs c); split; [left|apply Hextensive2]; auto
           |exists bs; split; [right|]; auto]
   |(* Hneq *)
    destruct (eq_dec a0 a') as [Heq' | Hneq'];
     inversion Hpairin as [|? ? ? ? ? ? Hmap']; subst;
    [exists bs; split; [constructor|]; auto
    |bad_eq
    |exists bs; constructor; [constructor|]; auto
    |assert (IHneed : in_list_list l a' c') by (exists bs; repeat constructor; auto);
     set (IHl_ := IHl IHneed);
     inversion IHl_ as [x Hwit]; destruct Hwit as [Hmap Hin];
     exists x; repeat constructor; auto]]].
Qed.

Lemma non_join_untouched : forall l l' a a' c b
                             (Hneq : a <> a')
                             (H: MapsTo (list_join eq_dec combine base l' a c l) a' b),
                             MapsTo l a' b.
Proof.
  induction l as [|(a_,b_) l_ IH]; intros;
  [inversion H; subst; [contradict Hneq|]; auto
  |
  simpl in H; inversion H as [? ? rst H'|? a'' ? ? ? Hneq'' map' Hinj]; subst;
  destruct (eq_dec a a_) as [Heq_|Hneq_];
  try (injection H'; intros; subst);
  try (injection Hinj; intros; subst);
  [
  (* Eq *)
  constructor; [auto
               |apply IH with (l' := l') (a := a_) (c := c);
                 [auto
                 |contradict Hneq; auto]]
  |constructor
  |subst; constructor; auto
  |constructor; [auto | apply IH with (l' := l') (a := a) (c := c); auto]]].
Qed.

Lemma non_join_untouched' : forall l l' a a' c b
                             (Hneq : a <> a')
                             (H: MapsTo (list_join eq_dec combine' base' l' a c l) a' b),
                             MapsTo l a' b.
Proof.
  induction l as [|(a_,b_) l_ IH]; intros;
  [inversion H; subst; [contradict Hneq|]; auto
  |
  simpl in H; inversion H as [? ? rst H'|? a'' ? ? ? Hneq'' map' Hinj]; subst;
  destruct (eq_dec a a_) as [Heq_|Hneq_];
  try (injection H'; intros; subst);
  try (injection Hinj; intros; subst);
  [
  (* Eq *)
  constructor; [auto
               |apply IH with (l' := l') (a := a_) (c := c);
                 [auto
                 |contradict Hneq; auto]]
  |constructor
  |subst; constructor; auto
  |constructor; [auto | apply IH with (l' := l') (a := a) (c := c); auto]]].
Qed.

Theorem join_mapsto_elim : forall l l' a a' c b
                                  (Hcontain : forall ab, In ab l -> In ab l')
                                  (H : MapsTo (list_join eq_dec combine base l' a c l) a' b),
                                  (a = a' /\ set_In c b) \/ (a <> a' /\ MapsTo l a' b).
Proof.
  intros; destruct (eq_dec a a') as [Heq|Hneq];
  [subst; left; split; [|destruct (in_list_join l l' a' c Hcontain) as [b' [Hmap' Hin']];
                          rewrite (MapsTo_same H Hmap')]
  |right; split; [|apply (non_join_untouched _ _ _ Hneq H)]]; auto.
Qed.

Theorem join_mapsto_elim' : forall l l' a a' c b
                                   (Hcontain : forall ab, In ab l -> In ab l')
                                   (H : MapsTo (list_join eq_dec combine' base' l' a c l) a' b),
                                  (a = a' /\ Subset (base' l' c) b) \/ (a <> a' /\ MapsTo l a' b).
Proof.
  intros; destruct (eq_dec a a') as [Heq|Hneq];
  [subst; left; split; [|destruct (in_list_join' l l' a' c Hcontain) as [b' [Hmap' Hin']];
                          rewrite (MapsTo_same H Hmap')]
  |right; split; [|apply (non_join_untouched' _ _ _ Hneq H)]]; auto.
Qed.

Lemma InDom_join : `{InDom (list_join eq_dec combine base l' a c l) a}.
Proof.
  induction l as [|(a_,b_) l_ IH];[constructor|simpl; destruct (eq_dec a a_); constructor; auto].
Qed.

Lemma InDom_join' : `{InDom (list_join eq_dec combine' base' l' a c l) a}.
Proof.
  induction l as [|(a_,b_) l_ IH];[constructor|simpl; destruct (eq_dec a a_); constructor; auto].
Qed.

Lemma InDom_join2 : `{InDom l a -> InDom (list_join eq_dec combine base l' a' c l) a}.
Proof.
  intros.
  induction H;
    [simpl; destruct (eq_dec a' a) as [Heq|Hneq];
     [subst; constructor
     |constructor]
    |simpl; destruct (eq_dec a' a'0) as [Heq|Hneq]; constructor; auto].
Qed.  

Lemma InDom_join2' : `{InDom l a -> InDom (list_join eq_dec combine' base' l' a' c l) a}.
Proof.
  intros.
  induction H;
    [simpl; destruct (eq_dec a' a) as [Heq|Hneq];
     [subst; constructor
     |constructor]
    |simpl; destruct (eq_dec a' a'0) as [Heq|Hneq]; constructor; auto].
Qed.  
  
(*
  
Lemma unmapped_join2 : forall l a a' b c l'
                             (Hcontain : (forall a c, in_list_list l a c -> in_list_list l' a c)
                                          \/ (b = (base l' c))),
                        Unmapped l a' ->
                        MapsTo (list_join eq_dec combine base l' a c l) a' b ->
                        (b = (base l' c)) /\ a = a'.
Proof.
  induction l as [|(a_,b_) l_ IH];
  simpl; intros a a' b c l' Hcontain Hunmap Hmap;
  [inversion Hmap as [|? ? ? ? ? ? Hbad]; subst; split; solve [auto|reflexivity|inversion Hbad]
  |].
  destruct (eq_dec a a_) as [Heq | Hneq];
    [inversion Hunmap as [|? ? ? ? Hunmap' Hneq]; subst;
     inversion Hmap as [|? ? ? ? ? ? Hbad]; split; try solve [reflexivity|
                                             rewrite unmapped_not_mapped in Hunmap';
                                             [apply Hunmap' in Hbad; contradiction
                                             |auto]]
    |].
  inversion Hmap as [|? ? ? ? ? ? Hbad]; subst; contradict Hneq; auto.
  apply IH with (b := b) (c := c) (l' := l').
  inversion Hcontain as [L|R].
  specialize L with a_ b_
  intros a_' c_' Hin; inversion Hin as [bs_ [Hmap_ Hsetin_]];
  apply Hcontain; destruct (eq_dec a_' a_) as [Heq_|Hneq_];
  [subst
    |exists bs_; repeat constructor]; auto.
  unfold in_list_list.
  Focus 2.
  
    [intros a_' c_' Hin
    |inversion Hunmap
    |]; auto.

; 
  inversion Hmap; [(* a_' = a_ *)
                   rewrite unmapped_not_mapped in Hunmap; [
                    (* rewritten *)
                    subst; match goal with [bad : ?a <> ?a |- _] => contradict bad; auto end
                    |(* satisfy hyp *)assumption]
                   |subst]. 
  Check unmapped_not_mapped.
                       
   [specialize Hunmap with b; contradict Hunmap; constructor
   |assumption
   |
   |assumption].
  .
  ; constructor; auto | auto].
    

 subst; repeat constructor|]
  constructor.
Qed.
Admitted.*)

End ListJoin_facts.
Section ListJoin_morefacts.
Variables (A C : Type) (eq_dec : dec_type A) (ceq_dec : dec_type C).
Definition joiner := (fun (_ : list (A * list C)) κs κ => (set_add ceq_dec κ κs)).
Definition singler := (fun (_ : list (A * list C)) c => (singleton ceq_dec c)).
Hint Unfold singleton singler.

(* set_In cc (joiner ll' cs cc) *)
Lemma In_same : forall l cs c (H : set_In c cs), (joiner l cs c) = cs.
Proof.
  induction cs; intros; simpl in H;[contradiction|inversion H as [L|R]];
  simpl; destruct (ceq_dec c a) as [Heq|Hneq];
  try solve [auto | contradict Hneq; auto | f_equal; apply IHcs; auto].
Qed.

Lemma In_neq : forall c c' l cs (Hin : set_In c' (joiner l cs c)) (Hneq : c <> c'), set_In c' cs.
Proof.
  induction cs as [|c_ l_ IH]; simpl; intros; [inversion Hin; auto|].
  destruct (ceq_dec c c_) as [Heq|Hneq_].
  inversion Hin; [left|right]; auto.
  inversion Hin; [left|]; auto.
Qed.

Lemma set_add_elim2 : forall a b ignore (l : set C) (H : set_In a (joiner ignore l b)),
                        (a = b /\ ~ set_In b l) \/ (set_In a l).
Proof.
  induction l; simpl; [intuition|].
  destruct (ceq_dec b a0) as [Heq|Hneq].
  (* eq *)
  subst; intros H';
  inversion H'; subst.
  destruct IHl as [[? Bad]|]; [apply set_add_intro2; auto|intuition|intuition].
  intuition.
  (* neq *)
  intros H'; inversion H'; subst; [intuition|].
  destruct IHl as [[? Bad]|]; intuition.
Qed.

Lemma in_list_join_set_split : forall (l l' : list (A * list C))
                                      (a a' : A)
                                      (c c' : C)
                                 (Hin : in_list_list (list_join eq_dec joiner singler l' a c l) a' c'),
                                 ((a = a') /\ (c = c') /\ (~ in_list_list l a c)) \/ (in_list_list l a' c').
Proof.
  induction l as [|(a,cs) l_ IH]; [intros|intros ll' aa aa' cc cc' Hin];
  simpl in *; 
  inversion Hin as [cs_ Hwit]; destruct Hwit as [map_ in_]; subst.
  (* base case *)
  inversion map_ as [bad0 bad1 bad2 bad3 bad4 bad5|bad0 bad1 bad2 bad3 bad4 bad5 bad6]; subst;
  [inversion in_ as [bad0|bad]; [subst; left; repeat split; intro bad;
                                 inversion bad as [bbad0 [bbad1 ?]]; auto; inversion bbad1
                                |inversion bad]
  |inversion bad6].

  destruct (eq_dec aa a) as [Heq|Hneq];
    inversion map_ as [|foo bar baz qux moo boo too];subst.
  subst.
  (* Eq case with inversion *)

  destruct (set_add_elim2 _ _ _ _ in_) as [Hceq|Hinrest];
       [destruct Hceq as [H H0]
       |subst; right; exists cs; repeat constructor; auto].
  
  left; repeat split; auto; intros [X [HH0 HH1]];
  assert (damn : X = cs) by
      (inversion HH0; subst; [|match goal with [bad : ?a <> ?a |- _] => contradict bad; auto end]; auto);
  subst; apply H0; auto.

  right; destruct Hin as [bad [Hbad0 Hbad1]];
  inversion Hbad0; subst; [contradict boo|]; auto;
  exists bad; split; [constructor|]; auto.

  right; exists cs_; split; [constructor|]; auto.
  destruct IH with (l' := ll') (a := aa) (a' := aa') (c := cc) (c' := cc') as [[? [? ?]]|[X [? ?]]];
    [exists cs_; split; auto
    |left; repeat split; auto; intro bad; inversion bad as [X [mum ble]]; inversion mum; subst; [bad_eq|apply H1; exists X; split; auto]
    |right; exists X; split; [constructor|]; auto].
Qed.

Lemma InDom_join_set_split : forall (l l' : list (A * list C))
                                    (a a' : A)
                                    (c : C)
                                 (Hin : InDom (list_join eq_dec joiner singler l' a c l) a'),
                                 ((a = a') /\ (~ in_list_list l a c)) \/ (InDom l a').
Proof.
intros.
rewrite (InDom_is_mapped eq_dec) in Hin; destruct Hin as [b Hmap].
induction l as [|(a_,b_) l_ IH].
inversion Hmap as [|? ? ? ? ? ? bad]; [subst; left;split;[reflexivity|intros [? [bad ?]]; inversion bad]
                                      |inversion bad].
simpl in Hmap; destruct (eq_dec a a_); subst; inversion Hmap as [|? ? ? ? ? Hneq Hrest]; subst;
try solve
    [right; constructor
    |apply (mapsto_join_neq eq_dec joiner singler (c := c) (l' := l') (a' := a_)) in Hrest; auto;
     destruct (IH Hrest) as [[? Hnin]|Hindom]; subst; right; constructor; auto].
destruct (IH Hrest) as [[? Hnin]|Hindom]; subst;
[left; split; [reflexivity|intros [bb [Hmap' ?]];inversion Hmap'; subst; [bad_eq|apply Hnin; exists bb; auto]]
|right; constructor; auto].
Qed.
End ListJoin_morefacts.

Inductive Dom_in_Dom {A B C} : list (A * B) -> list (A * C) -> Prop :=
  | no_dom : `{Dom_in_Dom nil l}
  | cons_dom : `{InDom l' a -> Dom_in_Dom l l' -> Dom_in_Dom ((a,b)::l) l'}.
Hint Constructors Dom_in_Dom.

Lemma list_join_ordering : forall (A B C : Type) (eq_dec : dec_type A)
                                  (combine : list (A * list B) -> list B -> C -> list B)
                                  (base : list (A * list B) -> C -> list B)
                                  (Hextensive' : (forall l b c c', In c' b -> In c' (combine l b c)))
                                  l l' a c,
                             MappingLE l (list_join eq_dec combine base l' a c l).
Proof.
  induction l as [|(a_,b_) l_ IH]; intros;
  [intros ? ? bad; inversion bad
  |simpl; destruct (eq_dec a a_) as [Heq|Hneq];
   [subst; apply maple_top; intros ? ?; apply Hextensive'; auto
   |apply maple_bottom, IH]].
Qed.

Lemma Dom_InDom : forall A B C (eq_dec : dec_type A) (l : list (A * B)) (l' : list (A * C)) (Hdom : Dom_in_Dom l l')
                         a
                         (Hindom : InDom l a), InDom l' a.
Proof.
induction l; intros; [inversion Hindom|inverts Hdom;destruct (eq_dec a1 a0) as [Heq|Hneq]; [subst; auto|inversion Hindom; [subst; contradict Hneq|apply IHl]; auto]].
Qed.

Theorem did_mapsto : forall A B C (eq_dec : dec_type A) (l : list (A * B)) (l' : list (A * C)) (Hdom : Dom_in_Dom l l') a b (Hmap : MapsTo l a b), exists c, MapsTo l' a c.
Proof.
  intros; assert (InDom l a) by (rewrite (InDom_In eq_dec); exists b; apply MapsTo_In; assumption).
  rewrite <- (InDom_is_mapped eq_dec); apply (Dom_InDom eq_dec (l := l)); auto.
Qed.

Lemma In_join : forall A B C (eq_dec : dec_type A) (l l' : list (A * B))
                        (f : list (A * B) -> B -> C -> B)  g a a' b b'
                        (Hcontain : (forall a b, In (a,b) l -> In (a,b) l'))
                        (H : In (a,b) l),
                  (exists b'', In (a,b'') (list_join eq_dec f g l' a' b' l)).
Proof.
  intros A B C eq_dec l l' f g a a' b b' Hcontain Hin; induction l as [|(a0,b0) l_ IH];
  inverts Hin;
  assert (IHneed : forall a b, In (a,b) l_ -> In (a,b) l') by
      (intros; apply Hcontain; right; auto);
  pose (rec := IH IHneed);
  [injection H; intros; subst;
   unfold list_join;
   destruct (eq_dec a' a) as [Heq | Hneq];[
     subst; exists (f l' b b')
   |exists b]; constructor; auto
  |unfold list_join;
    destruct (eq_dec a' a0) as [Heq | Hneq];[
      exists b; right; auto
           |destruct rec as [b'' Hb'']; auto; exists b''; right; auto]].
Qed.

Lemma Dom_join_right : forall A B C D (eq_dec : dec_type A) (l : list (A * B)) (l' : list (A * D))
                        (f : list (A * D) -> D -> C -> D)  g a b,
                   Dom_in_Dom l l' -> Dom_in_Dom l (list_join eq_dec f g l' a b l').
Proof.
  intros A B C D eq_dec l l' f g a b Hdom; induction Hdom as [|? ? ? ? H];
  constructor;
  (induction l';[rewrite InDom_In in H; auto; destruct H as [? bad]; inversion bad |]);
  [rewrite InDom_In in H; auto; destruct H as [b' Hb'];
   rewrite InDom_In; auto; apply In_join with (b := b')|]; auto.
Qed.

Lemma Dom_join_left : forall A B C D (eq_dec: dec_type A) (l l_ : list (A * B)) (l' : list (A * D))
                        (f : list (A * B) -> B -> C -> B)  g a b
                        (Hcontain: (forall ab, In ab l -> In ab l_)),
                   Dom_in_Dom l l' ->
                   (exists d, MapsTo l' a d) ->
                   Dom_in_Dom (list_join eq_dec f g l_ a b l) l'.
Proof.
  intros A B C D eq_dec l l_ l' f g a b Hcontain Hdom [d Hin]; induction Hdom.
  (* base *)
  repeat constructor; rewrite InDom_is_mapped; auto; exists d; auto.
    (* induction step *)
  simpl; destruct (eq_dec a a0) as [Heq|Hneq]; subst; simpl;
  [constructor; [rewrite InDom_is_mapped; auto; exists d|]; auto
  |].
  rewrite InDom_In in H; auto; destruct H as [d' Hin'].
  constructor;
    [rewrite InDom_In; auto; exists d'
    |apply IHHdom; [intros; apply Hcontain; right|]]; auto.
Qed.