(** * A finite poset's strict order is well-founded.

    Keystone for defining a longest-chain rank function by well-founded
    recursion (Mirsky's upper bound). Proof: strong induction on the size of the
    strict down-set [DownStrict x = {y | y < x}]; a strict predecessor [y] of [x]
    has [DownStrict y] strictly included in [DownStrict x] (transitivity gives
    inclusion; [y] itself is in the latter but not the former), so its size is
    smaller. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Wf_nat.
From Posets Require Import PosetClasses FinitePoset.

Section FinPosetWF.
  Context {A : Type} (R : A -> A -> Prop) {n : nat} `{IsFinitePoset A R n}.
  #[local] Existing Instance fp_is_poset.

  Definition StrictR (x y : A) : Prop := R x y /\ x <> y.
  Definition DownStrict (x : A) : Ensemble A := fun y => StrictR y x.

  Lemma full_finite : Finite A (Full_set A).
  Proof. apply (cardinal_finite A (Full_set A) n). exact fp_finite. Qed.

  Lemma downstrict_finite : forall x, Finite A (DownStrict x).
  Proof.
    intro x. apply (Finite_downward_closed A (Full_set A) full_finite).
    intros y _. constructor.
  Qed.

  Lemma downstrict_sub :
    forall x y, StrictR y x -> Included A (DownStrict y) (DownStrict x).
  Proof.
    intros x y [Hyx Hyne] z [Hzy Hzne]. split.
    - apply (poset_trans (R := R) z y x); assumption.
    - intro Hzx. subst z.
      assert (Hxy : x = y) by (apply (poset_antisym (R := R) x y); assumption).
      apply Hyne. symmetry. exact Hxy.
  Qed.

  Lemma downstrict_neq :
    forall x y, StrictR y x -> DownStrict y <> DownStrict x.
  Proof.
    intros x y Hyx Heq.
    assert (Hin : In A (DownStrict x) y) by exact Hyx.
    rewrite <- Heq in Hin. destruct Hin as [_ Hne]. apply Hne. reflexivity.
  Qed.

  Lemma fin_acc : forall m x, cardinal A (DownStrict x) m -> Acc StrictR x.
  Proof.
    apply (well_founded_ind lt_wf
            (fun m => forall x, cardinal A (DownStrict x) m -> Acc StrictR x)).
    intros m IHm x Hcardx. constructor. intros y Hyx.
    destruct (finite_cardinal A (DownStrict y) (downstrict_finite y)) as [my Hcardy].
    assert (Hlt : my < m).
    { apply (incl_st_card_lt A (DownStrict y) my Hcardy
               (DownStrict x) m Hcardx).
      split; [ apply downstrict_sub; exact Hyx | apply downstrict_neq; exact Hyx ]. }
    exact (IHm my Hlt y Hcardy).
  Qed.

  Theorem fin_strict_wf : well_founded StrictR.
  Proof.
    intro x.
    destruct (finite_cardinal A (DownStrict x) (downstrict_finite x)) as [m Hm].
    exact (fin_acc m x Hm).
  Qed.

End FinPosetWF.
