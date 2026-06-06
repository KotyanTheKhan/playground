(** * Dimension is self-dual: dim(P) = dim(P^d).

    Reversing every linear extension of a realizer of [R] yields a realizer of
    the dual order [dual R := fun x y => R y x] of the same cardinality, and the
    construction is involutive, so the two posets have equal dimension.

    Index entry: [dim-self-dual] in docs/references/dimension-index.md.
    The dimension classes (DimDefs) are parameterized by the bare relation, so
    no IsPoset instance is threaded through these statements. *)
From Stdlib Require Import Ensembles Finite_sets Image.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs Theorems.
From ZornsLemma Require Import EnsemblesExplicit.

Section DualDimension.
  Context {A : Type}.

  (** Reversal of a binary relation; involutive by eta. *)
  Definition rev (L : A -> A -> Prop) : A -> A -> Prop := fun x y => L y x.

  Lemma rev_involutive : forall L, rev (rev L) = L.
  Proof. intro L. reflexivity. Qed.

  Lemma rev_injective : forall L1 L2, rev L1 = rev L2 -> L1 = L2.
  Proof.
    intros L1 L2 Hr.
    rewrite <- (rev_involutive L1), <- (rev_involutive L2), Hr. reflexivity.
  Qed.

  (** The dual (opposite) order. *)
  Definition dual (R : A -> A -> Prop) : A -> A -> Prop := rev R.

  Lemma rev_poset : forall R, IsPoset A R -> IsPoset A (rev R).
  Proof.
    intros R HR. constructor; unfold rev.
    - intro x. apply (poset_refl (R := R)).
    - intros x y Hxy Hyx. apply (poset_antisym (R := R) x y); assumption.
    - intros x y z Hxy Hyz. apply (poset_trans (R := R) z y x); assumption.
  Qed.

  Lemma rev_total : forall L, IsTotalOrder L -> IsTotalOrder (rev L).
  Proof.
    intros L HL. constructor.
    - apply rev_poset. exact (total_is_poset (L := L)).
    - intros x y. unfold rev. destruct (total_comparable (L := L) y x); auto.
  Qed.

  Lemma rev_linear_extension :
    forall R L, IsLinearExtension R L -> IsLinearExtension (dual R) (rev L).
  Proof.
    intros R L HL. constructor.
    - apply rev_total. exact (linear_is_total HL).
    - intros x y Hd. unfold dual, rev in *. exact (linear_extends HL y x Hd).
  Qed.

  Lemma rev_realizer :
    forall R S, IsRealizer R S -> IsRealizer (dual R) (Im _ _ S rev).
  Proof.
    intros R S HS. constructor.
    - (* image members are linear extensions of the dual *)
      intros M HM. destruct HM as [L' HL' M0 Heq]. subst M0.
      apply rev_linear_extension. exact (realizer_linear HS L' HL').
    - (* intersection characterization *)
      intros x y. unfold dual, rev. split.
      + intros Hyx M HM. destruct HM as [L' HL' M0 Heq]. subst M0. unfold rev.
        exact (proj1 (realizer_intersection HS y x) Hyx L' HL').
      + intros Hall.
        apply (proj2 (realizer_intersection HS y x)).
        intros L' HL'.
        assert (Hmem : In _ (Im _ _ S rev) (rev L'))
          by (apply Im_intro with (x := L'); [exact HL' | reflexivity]).
        specialize (Hall (rev L') Hmem). unfold rev in Hall. exact Hall.
  Qed.

  Lemma rev_realizer_card :
    forall S n, cardinal _ S n -> cardinal _ (Im _ _ S rev) n.
  Proof.
    intros S n Hc.
    apply cardinal_Im_injective; [exact Hc|].
    intros x y _ _ Heq. apply rev_injective. exact Heq.
  Qed.

  (** Forward direction: the dual order has the same dimension. *)
  Lemma dual_dimension_forward :
    forall R d, PosetDimension R d -> PosetDimension (dual R) d.
  Proof.
    intros R d HD.
    refine {| dimension_realizer := Im _ _ (dimension_realizer HD) rev;
              dimension_is_realizer := _;
              dimension_cardinality := _;
              dimension_is_minimum := _ |}.
    - apply rev_realizer. exact (dimension_is_realizer HD).
    - apply rev_realizer_card. exact (dimension_cardinality HD).
    - intros r m Hr Hcard.
      (* rev r realizes dual (dual R) = R, with the same cardinality *)
      assert (Hr' : IsRealizer R (Im _ _ r rev)) by (apply (rev_realizer (dual R)); exact Hr).
      assert (Hc' : cardinal _ (Im _ _ r rev) m) by (apply rev_realizer_card; exact Hcard).
      exact (dimension_is_minimum HD (Im _ _ r rev) m Hr' Hc').
  Qed.

End DualDimension.

(** Dimension is self-dual. [PosetDimension] lives in [Type] (it carries an
    [Ensemble] realizer), so we state the equivalence as a pair of maps rather
    than a [Prop]-valued [<->]. (dual (dual R) is R definitionally.) *)
Theorem dual_dimension_iff {A : Type} (R : A -> A -> Prop) (d : nat) :
  (PosetDimension R d -> PosetDimension (dual R) d) *
  (PosetDimension (dual R) d -> PosetDimension R d).
Proof.
  split.
  - apply dual_dimension_forward.
  - intro HD. exact (dual_dimension_forward (dual R) d HD).
Qed.
