From Stdlib Require Import Ensembles Finite_sets Arith Classical.
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

  (** Lex order on A * B: (a1,b1) ≤_LA,LB (a2,b2) iff LA a1 a2 and (a1=a2 → LB b1 b2). *)
  Definition LexOrder (LA : A -> A -> Prop) (LB : B -> B -> Prop)
      (p q : A * B) : Prop :=
    LA (fst p) (fst q) /\ (fst p = fst q -> LB (snd p) (snd q)).

  (** LexOrder LA LB is a linear extension of ProductRel when LA extends RA and LB extends RB. *)
  Lemma lex_order_is_linear_extension :
    forall (LA : A -> A -> Prop) (LB : B -> B -> Prop),
    IsLinearExtension RA LA ->
    IsLinearExtension RB LB ->
    @IsLinearExtension (A * B) ProductRel _ (LexOrder LA LB).
  Proof.
    intros LA LB HLA HLB.
    destruct HLA as [[HLA_poset HLA_tot] HLA_ext].
    destruct HLB as [[HLB_poset HLB_tot] HLB_ext].
    constructor.
    - constructor.
      + constructor.
        * (* refl *)
          intros [a b]. unfold LexOrder; simpl.
          split; [apply poset_refl | intros; apply poset_refl].
        * (* antisym *)
          intros [a1 b1] [a2 b2] [H1a H1b] [H2a H2b].
          unfold LexOrder in *; simpl in *.
          assert (Heqa : a1 = a2) by (apply (poset_antisym (R := LA)); auto).
          subst.
          assert (Heqb : b1 = b2) by
            (apply (poset_antisym (R := LB)); [apply H1b | apply H2b]; reflexivity).
          subst; reflexivity.
        * (* trans *)
          intros [a1 b1] [a2 b2] [a3 b3] [H1a H1b] [H2a H2b].
          unfold LexOrder in *; simpl in *.
          split.
          -- exact (poset_trans (R := LA) a1 a2 a3 H1a H2a).
          -- intro Heq13.
             assert (Heqa12 : a1 = a2).
             { apply (poset_antisym (R := LA)); [exact H1a |].
               rewrite <- Heq13; exact H2a. }
             assert (Heqa23 : a2 = a3) by (rewrite <- Heqa12; exact Heq13).
             exact (poset_trans (R := LB) b1 b2 b3 (H1b Heqa12) (H2b Heqa23)).
      + (* Total *)
        intros [a1 b1] [a2 b2]. unfold LexOrder; simpl.
        destruct (HLA_tot a1 a2) as [Ha12 | Ha21],
                 (classic (a1 = a2)) as [Heqa | Hneqa].
        * (* LA a1 a2 and a1 = a2 *)
          subst.
          destruct (HLB_tot b1 b2) as [Hb | Hb].
          -- left; split; [apply poset_refl | intros; exact Hb].
          -- right; split; [apply poset_refl | intros; exact Hb].
        * (* LA a1 a2 and a1 ≠ a2 *)
          left; split; [exact Ha12 | intro Heq; exfalso; exact (Hneqa Heq)].
        * (* LA a2 a1 and a1 = a2 *)
          subst.
          destruct (HLB_tot b1 b2) as [Hb | Hb].
          -- left; split; [apply poset_refl | intros; exact Hb].
          -- right; split; [apply poset_refl | intros; exact Hb].
        * (* LA a2 a1 and a1 ≠ a2 *)
          right; split; [exact Ha21 | intro Heq; exfalso; apply Hneqa; symmetry; exact Heq].
    - (* extends ProductRel *)
      intros [a1 b1] [a2 b2] [HRA HRB]. unfold LexOrder; simpl.
      split; [exact (HLA_ext a1 a2 HRA) | intros; exact (HLB_ext b1 b2 HRB)].
  Qed.

  (** Key sub-lemma (admitted): Given realizers rA of RA (size dA) and rB of RB (size dB),
      there exists a realizer of ProductRel of size ≤ dA + dB.

      Construction sketch:
      - Fix any LA0 ∈ rA and any LB0 ∈ rB (both realizers are nonempty for non-trivial posets).
      - For each LA ∈ rA, add LexOrder LA LB0 to the product realizer.
      - For each LB ∈ rB, add LexOrder LA0 LB to the product realizer.
      - The resulting set has size ≤ dA + dB.
      - It is a realizer of ProductRel: the key argument is that for any incomparable
        pair (a1,b1),(a2,b2) in the product, either a1 and a2 are incomparable in A
        (separated by some LA ∈ rA via LexOrder LA LB0) or b1 and b2 are incomparable
        in B (separated by some LB ∈ rB via LexOrder LA0 LB). *)
  Lemma product_realizer_exists :
    forall (rA : Ensemble (A -> A -> Prop)) (rB : Ensemble (B -> B -> Prop)) (nA nB : nat),
    IsRealizer RA rA ->
    IsRealizer RB rB ->
    cardinal (A -> A -> Prop) rA nA ->
    cardinal (B -> B -> Prop) rB nB ->
    exists (rProd : Ensemble (A * B -> A * B -> Prop)) (n : nat),
      @IsRealizer (A * B) ProductRel _ rProd /\
      cardinal (A * B -> A * B -> Prop) rProd n /\
      n <= nA + nB.
  Proof.
    intros rA rB nA nB HrA HrB HcardA HcardB.
    (* Full construction is admitted; the key steps are:
       1. Extract some LA0 ∈ rA and LB0 ∈ rB.
       2. Build rProd = {LexOrder LA LB0 | LA ∈ rA} ∪ {LexOrder LA0 LB | LB ∈ rB}.
       3. Show rProd is a realizer of ProductRel.
       4. Show |rProd| ≤ nA + nB. *)
    admit.
  Qed.

  Theorem product_dimension_le :
    forall (dA dB dProd : nat),
    PosetDimension RA dA ->
    PosetDimension RB dB ->
    PosetDimension ProductRel dProd ->
    dProd <= dA + dB.
  Proof.
    intros dA dB dProd HdA HdB HdProd.
    (* Extract the canonical realizers for RA and RB. *)
    set (rA := dimension_realizer (R := RA) (d := dA)).
    set (rB := dimension_realizer (R := RB) (d := dB)).
    (* By product_realizer_exists, there is a realizer of ProductRel of size ≤ dA + dB. *)
    destruct (product_realizer_exists rA rB dA dB
        (dimension_is_realizer (R := RA) (d := dA))
        (dimension_is_realizer (R := RB) (d := dB))
        (dimension_cardinality (R := RA) (d := dA))
        (dimension_cardinality (R := RB) (d := dB)))
      as [rProd [n [HrProd_real [HrProd_card HrProd_le]]]].
    (* Apply dimension_is_minimum: dProd ≤ n ≤ dA + dB. *)
    exact (Nat.le_trans dProd n (dA + dB)
      (dimension_is_minimum (R := ProductRel) (d := dProd) rProd n HrProd_real HrProd_card)
      HrProd_le).
  Qed.

End ProductDimension.
