(** * Knaster–Tarski fixed-point theorem.

    On a complete lattice, every monotone (order-preserving) map has a least and
    a greatest fixed point: lfp = inf of the pre-fixpoints {x | f x ≤ x},
    gfp = sup of the post-fixpoints {x | x ≤ f x}.

    A complete lattice is presented as a poset [(A,R)] together with an arbitrary
    infimum operator [inf] and supremum operator [sup] (existence of all infima,
    equivalently all suprema, is exactly completeness).

    Index entry: [knaster-tarski] in docs/references/poset-facts-index.md. *)
From Stdlib Require Import Ensembles.
From Posets Require Import PosetClasses.

Section KnasterTarski.
  Context {A : Type} (R : A -> A -> Prop) `{IsPoset A R}.

  Definition IsLowerBound (S : Ensemble A) (m : A) : Prop :=
    forall x, In A S x -> R m x.
  Definition IsGLB (S : Ensemble A) (m : A) : Prop :=
    IsLowerBound S m /\ forall l, IsLowerBound S l -> R l m.

  Definition IsUpperBound (S : Ensemble A) (m : A) : Prop :=
    forall x, In A S x -> R x m.
  Definition IsLUB (S : Ensemble A) (m : A) : Prop :=
    IsUpperBound S m /\ forall u, IsUpperBound S u -> R m u.

  (** Completeness: every subset has an infimum and a supremum. *)
  Context (inf : Ensemble A -> A) (Hinf : forall S, IsGLB S (inf S)).
  Context (sup : Ensemble A -> A) (Hsup : forall S, IsLUB S (sup S)).

  (** A monotone endomap. *)
  Context (f : A -> A) (Hmono : forall x y, R x y -> R (f x) (f y)).

  (** Least fixed point. *)
  Definition prefix : Ensemble A := fun x => R (f x) x.
  Definition lfp : A := inf prefix.

  Theorem lfp_is_fixed : f lfp = lfp.
  Proof.
    destruct (Hinf prefix) as [Hlb Hgreatest].
    (* f lfp is a lower bound of the pre-fixpoints *)
    assert (Hflb : IsLowerBound prefix (f lfp)).
    { intros x Hx. unfold In, prefix in Hx.
      apply (poset_trans (R := R) (f lfp) (f x) x).
      - apply Hmono. apply Hlb. exact Hx.
      - exact Hx. }
    assert (Hfle : R (f lfp) lfp) by (apply Hgreatest; exact Hflb).
    (* hence f lfp is itself a pre-fixpoint, so lfp <= f lfp *)
    assert (Hpre : In A prefix (f lfp)).
    { unfold In, prefix. apply Hmono. exact Hfle. }
    assert (Hle : R lfp (f lfp)) by (apply Hlb; exact Hpre).
    apply (poset_antisym (R := R) (f lfp) lfp); assumption.
  Qed.

  Theorem lfp_least : forall y, f y = y -> R lfp y.
  Proof.
    intros y Hy. destruct (Hinf prefix) as [Hlb _].
    apply Hlb. unfold In, prefix. rewrite Hy. apply (poset_refl (R := R)).
  Qed.

  (** Greatest fixed point (dual). *)
  Definition postfix : Ensemble A := fun x => R x (f x).
  Definition gfp : A := sup postfix.

  Theorem gfp_is_fixed : f gfp = gfp.
  Proof.
    destruct (Hsup postfix) as [Hub Hleast].
    assert (Hfub : IsUpperBound postfix (f gfp)).
    { intros x Hx. unfold In, postfix in Hx.
      apply (poset_trans (R := R) x (f x) (f gfp)).
      - exact Hx.
      - apply Hmono. apply Hub. exact Hx. }
    assert (Hfge : R gfp (f gfp)) by (apply Hleast; exact Hfub).
    assert (Hpost : In A postfix (f gfp)).
    { unfold In, postfix. apply Hmono. exact Hfge. }
    assert (Hge : R (f gfp) gfp) by (apply Hub; exact Hpost).
    apply (poset_antisym (R := R) (f gfp) gfp); assumption.
  Qed.

  Theorem gfp_greatest : forall y, f y = y -> R y gfp.
  Proof.
    intros y Hy. destruct (Hsup postfix) as [Hub _].
    apply Hub. unfold In, postfix. rewrite Hy. apply (poset_refl (R := R)).
  Qed.

End KnasterTarski.
