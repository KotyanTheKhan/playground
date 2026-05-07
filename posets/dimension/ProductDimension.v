From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.

(** Theorem: Product Dimension
    The dimension of the Cartesian product of two posets is at most the sum of their dimensions. *)
Section ProductDimension.
  Context {A B : Type}.
  Context (RA : A -> A -> Prop) `{IsPoset A RA}.
  Context (RB : B -> B -> Prop) `{IsPoset B RB}.

  Definition ProductRel (x y : A * B) :=
    RA (fst x) (fst y) /\ RB (snd x) (snd y).

  Instance Product_IsPoset : IsPoset (A * B) ProductRel.
  Proof.
    constructor; unfold ProductRel; intros.
    - destruct x; split; apply poset_refl.
    - destruct x, y, H1, H2.
      f_equal; [eapply poset_antisym | eapply poset_antisym]; eauto.
    - destruct x, y, z, H1, H2.
      split; [eapply poset_trans | eapply poset_trans]; eauto.
  Qed.

  Theorem product_dimension_le :
    forall (dA dB dProd : nat),
    PosetDimension RA dA ->
    PosetDimension RB dB ->
    PosetDimension ProductRel dProd ->
    dProd <= dA + dB.
  Proof.
  Admitted.

End ProductDimension.
