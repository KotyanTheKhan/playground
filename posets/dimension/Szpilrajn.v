From Stdlib Require Import Ensembles Finite_sets Arith Classical.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From Coq Require Import Relations.Relation_Operators.
From ZornsLemma Require Import ZornsLemma EnsemblesImplicit.
From Posets Require Import PosetClasses.

(** Generalized: TC(M ∪ {(q,p)}) is a poset when p and q are incomparable in M. *)
Lemma add_incomparable_general :
  forall (A : Type) (M : A -> A -> Prop) `{HM : IsPoset A M} (p q : A),
  ~ (M p q \/ M q p) ->
  IsPoset A (@clos_trans A (fun a b => M a b \/ (a = q /\ b = p))).
Proof.
  intros A M HM p q Hinc.
  set (ext := fun a b => M a b \/ (a = q /\ b = p)).
  (* Path invariant: every path in TC(ext) from a to b satisfies
     M a b  \/  (M a q /\ M p b). *)
  assert (Hinv : forall a b,
    @clos_trans A ext a b -> M a b \/ (M a q /\ M p b)).
  { intros a b Htc.
    induction Htc as [a b Hstep | a m b _ IH1 _ IH2].
    - destruct Hstep as [HMab | [-> ->]].
      + left; exact HMab.
      + right; split; apply poset_refl.
    - destruct IH1 as [Ham | [Haq Hpm]],
               IH2 as [Hmb | [Hmq Hpb]].
      + left; eapply poset_trans; eauto.
      + right; split; [eapply poset_trans; eauto | auto].
      + right; split; [auto | eapply poset_trans; eauto].
      + exfalso; apply Hinc; left; eapply poset_trans; eauto. }
  constructor.
  - intro a; apply t_step; left; apply poset_refl.
  - intros a b Hab Hba.
    destruct (Hinv a b Hab) as [HMab | [Haq Hpb]],
             (Hinv b a Hba) as [HMba | [Hbq Hpa]].
    + eapply poset_antisym; eauto.
    + exfalso; apply Hinc; left;
        eapply poset_trans; [eapply poset_trans; [exact Hpa | exact HMab] | exact Hbq].
    + exfalso; apply Hinc; left;
        eapply poset_trans; [eapply poset_trans; [exact Hpb | exact HMba] | exact Haq].
    + exfalso; apply Hinc; left; eapply poset_trans; [exact Hpb | exact Hbq].
  - intros a b c Hab Hbc; eapply t_trans; eauto.
Qed.

(** SubRel is antisymmetric under propositional + functional extensionality. *)
Lemma SubRel_antisym : forall (A : Type) (P Q : A -> A -> Prop),
  (forall x y, P x y -> Q x y) ->
  (forall x y, Q x y -> P x y) ->
  P = Q.
Proof.
  intros A P Q HPQ HQP.
  apply functional_extensionality; intro x.
  apply functional_extensionality; intro y.
  apply propositional_extensionality; split; auto.
Qed.

Theorem szpilrajn_theorem :
  forall (A : Type) (R : A -> A -> Prop) `{HR : IsPoset A R},
  exists L : A -> A -> Prop,
    IsPoset A L /\
    (forall x y, L x y \/ L y x) /\
    (forall x y, R x y -> L x y).
Proof.
  intros A R HR.
  (* Work over the sigma type of poset-extensions of R. *)
  set (Ext := { P : A -> A -> Prop | IsPoset A P /\ forall x y, R x y -> P x y }).
  set (ExtOrd := fun s1 s2 : Ext =>
    forall x y, proj1_sig s1 x y -> proj1_sig s2 x y).

  (* ExtOrd is a partial order on Ext. *)
  assert (ExtOrd_order : order ExtOrd).
  { constructor; unfold ExtOrd, reflexive, transitive, antisymmetric.
    - auto.
    - eauto.
    - intros [P HP] [Q HQ] H12 H21.
      apply subset_eq_compat; simpl in *.
      apply SubRel_antisym; auto. }

  (* Every chain in (Ext, ExtOrd) has an upper bound. *)
  assert (ExtOrd_ub : forall C : Ensemble Ext, chain ExtOrd C ->
    exists ub : Ext, forall s : Ext, In C s -> ExtOrd s ub).
  { intros C HC.
    destruct (classic (Inhabited Ext C)) as [[s0 Hs0] | Hempty].
    - (* Non-empty: take the union. *)
      set (union_rel := fun x y => exists s : Ext, In C s /\ proj1_sig s x y).
      assert (union_poset : IsPoset A union_rel).
      { constructor.
        - intro x. exists s0. split; [exact Hs0 | apply (proj1 (proj2_sig s0)).(poset_refl)].
        - intros x y [s1 [Hs1 H1]] [s2 [Hs2 H2]].
          destruct (HC s1 s2 Hs1 Hs2) as [H12 | H21].
          + eapply (proj1 (proj2_sig s2)).(poset_antisym); eauto.
          + eapply (proj1 (proj2_sig s1)).(poset_antisym); eauto.
        - intros x y z [s1 [Hs1 H1]] [s2 [Hs2 H2]].
          destruct (HC s1 s2 Hs1 Hs2) as [H12 | H21].
          + exists s2. split; [exact Hs2 | eapply (proj1 (proj2_sig s2)).(poset_trans); [exact (H12 x y H1) | exact H2]].
          + exists s1. split; [exact Hs1 | eapply (proj1 (proj2_sig s1)).(poset_trans); [exact H1 | exact (H21 y z H2)]]. }
      assert (union_ext : forall x y, R x y -> union_rel x y).
      { intros x y HR'. exists s0. split; [exact Hs0 | exact (proj2 (proj2_sig s0) x y HR')]. }
      exists (exist _ union_rel (conj union_poset union_ext)).
      intros [P [HP Hext]] HPC. unfold ExtOrd; simpl.
      intros x y HPxy. exact (ex_intro _ (exist _ P (conj HP Hext)) (conj HPC HPxy)).
    - (* Empty: R itself is an upper bound vacuously. *)
      exists (exist _ R (conj HR (fun x y h => h))).
      intros s Hs. exfalso. apply Hempty. exists s. exact Hs. }

  (* Apply Zorn's lemma. *)
  destruct (ZornsLemma ExtOrd ExtOrd_order ExtOrd_ub) as [[M [HM_poset HM_ext]] HM_max].

  (* M is total: if not, the extension TC(M ∪ {(y,x)}) contradicts maximality. *)
  assert (M_total : forall x y, M x y \/ M y x).
  { intros x y.
    destruct (classic (M x y \/ M y x)) as [? | Hinc]; [auto |].
    exfalso.
    set (ext_step := fun a b => M a b \/ (a = y /\ b = x)).
    set (M' := @clos_trans A ext_step).
    assert (HM'_poset : IsPoset A M') by
      (apply add_incomparable_general; auto).
    assert (HM'_ext : forall a b, R a b -> M' a b).
    { intros a b Hab. apply t_step. left. exact (HM_ext a b Hab). }
    set (s_M' := exist _ M' (conj HM'_poset HM'_ext) : Ext).
    assert (HMM' : ExtOrd (exist _ M (conj HM_poset HM_ext)) s_M').
    { unfold ExtOrd, s_M'; simpl. intros a b Hmab. apply t_step. left. exact Hmab. }
    pose proof (HM_max s_M' HMM') as Heq.
    assert (HMeqM' : M = M') by exact (f_equal (@proj1_sig _ _) Heq).
    apply Hinc. right.
    rewrite HMeqM'. apply t_step. right. auto. }

  exact (ex_intro _ M (conj HM_poset (conj M_total HM_ext))).
Qed.
