From Stdlib Require Import Ensembles Finite_sets Arith Classical.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.

(* ------------------------------------------------------------------ *)
(* Helper lemmas (analogues of those in LinearSum.v)                   *)
(* ------------------------------------------------------------------ *)

Lemma pd_cardinal_pos_nonempty :
  forall (U : Type) (S : Ensemble U) (n : nat),
  cardinal U S n -> 0 < n -> exists x, In U S x.
Proof.
  intros U S n Hcard Hpos.
  induction Hcard.
  - inversion Hpos.
  - exists x. right. constructor.
Qed.

(** The image of a finite set under a function has cardinality ≤ that of the source. *)
Lemma cardinal_Im_le :
  forall (U V : Type) (S : Ensemble U) (f : U -> V) (n : nat),
  cardinal U S n ->
  exists m, cardinal V (Im U V S f) m /\ m <= n.
Proof.
  intros U V S f n Hcard.
  induction Hcard.
  - exists 0. split; [| lia].
    assert (Heq : Im U V (Empty_set U) f = Empty_set V).
    { apply Extensionality_Ensembles. split.
      - intros x [z Hz _]. destruct Hz.
      - intros x Hx. destruct Hx. }
    rewrite Heq. constructor.
  - destruct IHHcard as [m [Hcard_m Hle]].
    destruct (classic (In V (Im U V A0 f) (f x))) as [HIn | HNin].
    + exists m. split; [| lia].
      assert (Heq : Im U V (Add U A0 x) f = Im U V A0 f).
      { apply Extensionality_Ensembles. split.
        - intros y [z Hz Heqy]. destruct Hz as [z Hz | z Hz].
          + exists z; [exact Hz | exact Heqy].
          + destruct Hz. rewrite Heqy. exact HIn.
        - intros y [z Hz Heqy]. exists z; [left; exact Hz | exact Heqy]. }
      rewrite Heq. exact Hcard_m.
    + exists (S m). split; [| lia].
      assert (Heq : Im U V (Add U A0 x) f = Add V (Im U V A0 f) (f x)).
      { apply Extensionality_Ensembles. split.
        - intros y [z Hz Heqy]. destruct Hz as [z Hz | z Hz].
          + left. exists z; auto.
          + destruct Hz. right. rewrite Heqy. constructor.
        - intros y Hy. destruct Hy as [y Hy | y Hy].
          + destruct Hy as [z Hz Heqy]. exists z; [left; exact Hz | exact Heqy].
          + destruct Hy. exists x; [right; constructor | reflexivity]. }
      rewrite Heq. apply card_add; assumption.
Qed.

(** The union of two finite sets has cardinality ≤ the sum of their cardinalities. *)
Lemma cardinal_union_le :
  forall (U : Type) (S1 S2 : Ensemble U) (m n : nat),
  cardinal U S1 m -> cardinal U S2 n ->
  exists k, cardinal U (Union U S1 S2) k /\ k <= m + n.
Proof.
  intros U S1 S2 m n Hcard1 Hcard2.
  induction Hcard1.
  - exists n. split; [| lia].
    assert (Heq : Union U (Empty_set U) S2 = S2).
    { apply Extensionality_Ensembles. split.
      - intros x [x Hx | x Hx]; [destruct Hx | exact Hx].
      - intros x Hx. right. exact Hx. }
    rewrite Heq. exact Hcard2.
  - destruct IHHcard1 as [k [Hcard_k Hle]].
    destruct (classic (In U (Union U A0 S2) x)) as [HinU | HninU].
    + exists k. split; [| lia].
      assert (Heq : Union U (Add U A0 x) S2 = Union U A0 S2).
      { apply Extensionality_Ensembles. split.
        - intros y Hy. destruct Hy as [y Hy | y Hy].
          + destruct Hy as [y Hy | y Hy].
            * left. exact Hy.
            * destruct Hy. exact HinU.
          + right. exact Hy.
        - intros y Hy. destruct Hy as [y Hy | y Hy].
          + left. left. exact Hy.
          + right. exact Hy. }
      rewrite Heq. exact Hcard_k.
    + exists (S k). split; [| lia].
      assert (Heq : Union U (Add U A0 x) S2 = Add U (Union U A0 S2) x).
      { apply Extensionality_Ensembles. split.
        - intros y Hy. destruct Hy as [y Hy | y Hy].
          + destruct Hy as [y Hy | y Hy].
            * left. left. exact Hy.
            * destruct Hy. right. constructor.
          + left. right. exact Hy.
        - intros y Hy. destruct Hy as [y Hy | y Hy].
          + destruct Hy as [y Hy | y Hy].
            * left. left. exact Hy.
            * right. exact Hy.
          + destruct Hy. left. right. constructor. }
      rewrite Heq. apply card_add; assumption.
Qed.

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

  (** RevLex order on A * B: (a1,b1) ≤_LA,LB (a2,b2) iff LB b1 b2 and (b1=b2 → LA a1 a2).
      B-coordinate is the primary key, A-coordinate is the tiebreaker. *)
  Definition RevLex (LA : A -> A -> Prop) (LB : B -> B -> Prop)
      (p q : A * B) : Prop :=
    LB (snd p) (snd q) /\ (snd p = snd q -> LA (fst p) (fst q)).

  (** RevLex LA LB is a linear extension of ProductRel when LA extends RA and LB extends RB. *)
  Lemma revlex_is_linear_extension :
    forall (LA : A -> A -> Prop) (LB : B -> B -> Prop),
    IsLinearExtension RA LA ->
    IsLinearExtension RB LB ->
    @IsLinearExtension (A * B) ProductRel _ (RevLex LA LB).
  Proof.
    intros LA LB HLA HLB.
    destruct HLA as [[HLA_poset HLA_tot] HLA_ext].
    destruct HLB as [[HLB_poset HLB_tot] HLB_ext].
    constructor.
    - constructor.
      + constructor.
        * (* refl *)
          intros [a b]. unfold RevLex; simpl.
          split; [apply poset_refl | intros; apply poset_refl].
        * (* antisym *)
          intros [a1 b1] [a2 b2] [H1b H1a] [H2b H2a].
          unfold RevLex in *; simpl in *.
          assert (Heqb : b1 = b2) by (apply (poset_antisym (R := LB)); assumption).
          subst.
          assert (Heqa : a1 = a2) by
            (apply (poset_antisym (R := LA)); [apply H1a | apply H2a]; reflexivity).
          subst; reflexivity.
        * (* trans *)
          intros [a1 b1] [a2 b2] [a3 b3] [H1b H1a] [H2b H2a].
          unfold RevLex in *; simpl in *.
          split.
          -- exact (poset_trans (R := LB) b1 b2 b3 H1b H2b).
          -- intro Heq13.
             assert (Heqb12 : b1 = b2).
             { apply (poset_antisym (R := LB)); [exact H1b |].
               rewrite <- Heq13; exact H2b. }
             assert (Heqb23 : b2 = b3) by (rewrite <- Heqb12; exact Heq13).
             exact (poset_trans (R := LA) a1 a2 a3 (H1a Heqb12) (H2a Heqb23)).
      + (* Total *)
        intros [a1 b1] [a2 b2]. unfold RevLex; simpl.
        destruct (HLB_tot b1 b2) as [Hb12 | Hb21],
                 (classic (b1 = b2)) as [Heqb | Hneqb].
        * (* LB b1 b2 and b1 = b2 *)
          subst.
          destruct (HLA_tot a1 a2) as [Ha | Ha].
          -- left; split; [apply poset_refl | intros; exact Ha].
          -- right; split; [apply poset_refl | intros; exact Ha].
        * (* LB b1 b2 and b1 ≠ b2 *)
          left; split; [exact Hb12 | intro Heq; exfalso; exact (Hneqb Heq)].
        * (* LB b2 b1 and b1 = b2 *)
          subst.
          destruct (HLA_tot a1 a2) as [Ha | Ha].
          -- left; split; [apply poset_refl | intros; exact Ha].
          -- right; split; [apply poset_refl | intros; exact Ha].
        * (* LB b2 b1 and b1 ≠ b2 *)
          right; split; [exact Hb21 | intro Heq; exfalso; apply Hneqb; symmetry; exact Heq].
    - (* extends ProductRel *)
      intros [a1 b1] [a2 b2] [HRA HRB]. unfold RevLex; simpl.
      split; [exact (HLB_ext b1 b2 HRB) | intros; exact (HLA_ext a1 a2 HRA)].
  Qed.

  (** Key sub-lemma (admitted): Given realizers rA of RA (size nA) and rB of RB (size nB),
      both nonempty (0 < nA, 0 < nB), there exists a realizer of ProductRel of size ≤ nA + nB.

      WHY THE UNION/LEXORDER APPROACH IS INSUFFICIENT:
      The natural construction is
        rProd = {LexOrder LA LB0 | LA ∈ rA} ∪ {LexOrder LA0 LB | LB ∈ rB}
      where LA0 ∈ rA and LB0 ∈ rB are fixed representatives.  This set has size ≤ nA + nB
      and every element is a linear extension of ProductRel (by lex_order_is_linear_extension).
      However it fails the backward direction of realizer_intersection:
        - If RA a1 a2 strictly (a1 ≠ a2) and ¬RB b1 b2, then (a1,b1) and (a2,b2) are
          incomparable in ProductRel.  A realizer element must reverse them, i.e. put
          (a2,b2) ≤ (a1,b1).  But for every LA extending RA we have LA a1 a2, so
          LexOrder LA LB0 (a2,b2)(a1,b1) would require LA a2 a1, implying a1=a2 — contradiction.
          Similarly LexOrder LA0 LB (a2,b2)(a1,b1) requires LA0 a2 a1, which fails for the
          same reason.  Neither subfamily can separate this type of incomparable pair.

      CORRECT APPROACH (future work):
      The standard Dushnik–Miller proof that dim(P×Q) ≤ dim(P) + dim(Q) uses Szpilrajn's
      theorem (linear extension of any partial order) together with a critical-pair argument.
      For each incomparable pair ((a1,b1),(a2,b2)) in P×Q one exhibits a linear extension
      that reverses it; the key cases are covered by the nA+nB extensions obtained by
      interleaving the A-realizer and B-realizer in a way that is NOT purely lexicographic.
      Formalising this requires the full Szpilrajn machinery (already present in CriticalPairs)
      and a more delicate construction than zip-of-LexOrders. *)
  Lemma product_realizer_exists :
    forall (rA : Ensemble (A -> A -> Prop)) (rB : Ensemble (B -> B -> Prop)) (nA nB : nat),
    IsRealizer RA rA ->
    IsRealizer RB rB ->
    cardinal (A -> A -> Prop) rA nA ->
    cardinal (B -> B -> Prop) rB nB ->
    0 < nA -> 0 < nB ->
    exists (rProd : Ensemble (A * B -> A * B -> Prop)) (n : nat),
      @IsRealizer (A * B) ProductRel _ rProd /\
      cardinal (A * B -> A * B -> Prop) rProd n /\
      n <= nA + nB.
  Proof.
    intros rA rB nA nB HrA HrB HcardA HcardB HposA HposB.
    destruct HrA as [HrA_lin HrA_iff].
    destruct HrB as [HrB_lin HrB_iff].
    destruct (pd_cardinal_pos_nonempty _ rA nA HcardA HposA) as [LA0 HLA0].
    destruct (pd_cardinal_pos_nonempty _ rB nB HcardB HposB) as [MB0 HMB0].
    assert (HLA0_lin : IsLinearExtension RA LA0) := HrA_lin LA0 HLA0.
    assert (HMB0_lin : IsLinearExtension RB MB0) := HrB_lin MB0 HMB0.
    set (rProd_A := Im (A -> A -> Prop) (A * B -> A * B -> Prop) rA (fun LA => LexOrder LA MB0)).
    set (rProd_B := Im (B -> B -> Prop) (A * B -> A * B -> Prop) rB (fun LB => RevLex LA0 LB)).
    set (rProd := Union _ rProd_A rProd_B).
    destruct (cardinal_Im_le _ _ rA (fun LA => LexOrder LA MB0) nA HcardA) as [mA [HcardA' HleA]].
    destruct (cardinal_Im_le _ _ rB (fun LB => RevLex LA0 LB) nB HcardB) as [mB [HcardB' HleB]].
    destruct (cardinal_union_le _ rProd_A rProd_B mA mB HcardA' HcardB') as [n [Hcard_n Hle_n]].
    exists rProd, n.
    split; [| split; [exact Hcard_n | lia]].
    constructor.
    - (* Every L ∈ rProd is a linear extension of ProductRel *)
      intros L HL.
      destruct HL as [L HL | L HL].
      + destruct HL as [LA HLA HLeq]. rewrite <- HLeq.
        exact (lex_order_is_linear_extension LA MB0 (HrA_lin LA HLA) HMB0_lin).
      + destruct HL as [LB HLB HLeq]. rewrite <- HLeq.
        exact (revlex_is_linear_extension LA0 LB HLA0_lin (HrB_lin LB HLB)).
    - (* Intersection: ProductRel (a1,b1)(a2,b2) ↔ ∀ L ∈ rProd, L (a1,b1)(a2,b2) *)
      intros [a1 b1] [a2 b2]. split.
      + (* Forward: ProductRel → all L agree *)
        intros [HRA HRB] L HL.
        destruct HL as [L HL | L HL].
        * destruct HL as [LA HLA HLeq]. rewrite <- HLeq. unfold LexOrder; simpl.
          split; [exact (linear_extends a1 a2 HRA) |
                  intros; exact (linear_extends b1 b2 HRB)].
        * destruct HL as [LB HLB HLeq]. rewrite <- HLeq. unfold RevLex; simpl.
          split; [exact (linear_extends b1 b2 HRB) |
                  intros; exact (linear_extends a1 a2 HRA)].
      + (* Backward: all L agree → ProductRel *)
        intro Hall.
        split.
        * (* RA a1 a2: from all LexOrder Li MB0 agreeing *)
          apply HrA_iff. intros LA HLA.
          assert (Hex : LexOrder LA MB0 (a1, b1) (a2, b2)).
          { apply Hall. left. exists LA; [exact HLA | reflexivity]. }
          exact (proj1 Hex).
        * (* RB b1 b2: from all RevLex LA0 Mj agreeing *)
          apply HrB_iff. intros LB HLB.
          assert (Hex : RevLex LA0 LB (a1, b1) (a2, b2)).
          { apply Hall. right. exists LB; [exact HLB | reflexivity]. }
          exact (proj1 Hex).
  Qed.

  Theorem product_dimension_le :
    forall (dA dB dProd : nat),
    PosetDimension RA dA ->
    PosetDimension RB dB ->
    PosetDimension ProductRel dProd ->
    0 < dA -> 0 < dB ->
    dProd <= dA + dB.
  Proof.
    intros dA dB dProd HdA HdB HdProd HposA HposB.
    (* Extract the canonical realizers for RA and RB. *)
    set (rA := dimension_realizer (R := RA) (d := dA)).
    set (rB := dimension_realizer (R := RB) (d := dB)).
    (* By product_realizer_exists, there is a realizer of ProductRel of size ≤ dA + dB. *)
    destruct (product_realizer_exists rA rB dA dB
        (dimension_is_realizer (R := RA) (d := dA))
        (dimension_is_realizer (R := RB) (d := dB))
        (dimension_cardinality (R := RA) (d := dA))
        (dimension_cardinality (R := RB) (d := dB))
        HposA HposB)
      as [rProd [n [HrProd_real [HrProd_card HrProd_le]]]].
    (* Apply dimension_is_minimum: dProd ≤ n ≤ dA + dB. *)
    exact (Nat.le_trans dProd n (dA + dB)
      (dimension_is_minimum (R := ProductRel) (d := dProd) rProd n HrProd_real HrProd_card)
      HrProd_le).
  Qed.

End ProductDimension.
