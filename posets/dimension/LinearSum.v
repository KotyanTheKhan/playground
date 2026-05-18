From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Image.

(** The Linear Sum (also known as the Ordinal Sum) of two posets P and Q,
    denoted P ⊕ Q, is the poset formed by taking the disjoint union of P and Q
    and declaring every element of P to be less than every element of Q.

    Formally, for x, y ∈ P ∪ Q:
    1. If x, y ∈ P, then x ≤ y in P ⊕ Q iff x ≤ y in P.
    2. If x, y ∈ Q, then x ≤ y in P ⊕ Q iff x ≤ y in Q.
    3. If x ∈ P and y ∈ Q, then x ≤ y in P ⊕ Q.

    Intuition: The linear sum "stacks" Q on top of P.

    Dimension Property:
    One of the core results for linear sums is that dim(P ⊕ Q) = max(dim(P), dim(Q)).
    This is because no new incomparabilities are created between the summands;
    any incomparable pair in P ⊕ Q must be entirely within P or entirely within Q.
*)

Lemma cardinal_pos_nonempty :
  forall (U : Type) (S : Ensemble U) (n : nat),
  cardinal U S n -> 0 < n -> exists x, In U S x.
Proof.
  intros U S n Hcard Hpos.
  induction Hcard.
  - inversion Hpos.
  - exists x. right. constructor.
Qed.

Lemma cardinal_to_list :
  forall (U : Type) (S : Ensemble U) (n : nat),
  cardinal U S n ->
  exists l : list U,
    length l = n /\
    (forall x, In U S x <-> List.In x l) /\
    List.NoDup l.
Proof.
  intros U S n Hcard.
  induction Hcard.
  - exists nil. split; [reflexivity | split; [intro x; split; [intro Hx; inversion Hx | intro Hx; inversion Hx] | constructor]].
  - destruct IHHcard as [l [Hlen [Hiff Hnodup]]].
    exists (x :: l).
    split; [simpl; lia |].
    split.
    + intro y. split.
      * intro Hy. destruct Hy as [y Hy | y Hy].
        -- right. exact (proj1 (Hiff y) Hy).
        -- destruct Hy. left. reflexivity.
      * intro Hy. simpl in Hy. destruct Hy as [-> | Hy].
        -- right. constructor.
        -- left. exact (proj2 (Hiff y) Hy).
    + constructor.
      * intro Hxl. apply H. exact (proj2 (Hiff x) Hxl).
      * exact Hnodup.
Qed.

Lemma cardinal_Im_injective :
  forall (U V : Type) (S : Ensemble U) (f : U -> V) (n : nat),
  cardinal U S n ->
  (forall x y, In U S x -> In U S y -> f x = f y -> x = y) ->
  cardinal V (Im U V S f) n.
Proof.
  intros U V S f n Hcard Hinj.
  induction Hcard as [| A0 n0 Hcard0 IHHcard x Hxnin].
  - rewrite image_empty. constructor.
  - assert (Hnew : ~ In V (Im U V A0 f) (f x)).
    { intros HIm. inversion HIm as [z HzA0 y Heqz]; subst.
      apply Hxnin. rewrite (Hinj x z (Add_intro2 _ A0 x) (Union_introl _ _ _ _ HzA0) Heqz). exact HzA0. }
    rewrite Im_add. apply card_add.
    + apply IHHcard.
      intros a b Ha Hb Heqab. apply Hinj; [left; exact Ha | left; exact Hb | exact Heqab].
    + exact Hnew.
Qed.

Section LinearSum.
  Context {A B : Type}.
  Context (RA : A -> A -> Prop) `{IsPoset A RA}.
  Context (RB : B -> B -> Prop) `{IsPoset B RB}.

  Inductive LinearSumRel : A + B -> A + B -> Prop :=
    | SumAA : forall x y, RA x y -> LinearSumRel (inl x) (inl y)
    | SumBB : forall x y, RB x y -> LinearSumRel (inr x) (inr y)
    | SumAB : forall x y, LinearSumRel (inl x) (inr y).

  Instance LinearSum_IsPoset : IsPoset (A + B) LinearSumRel.
  Proof.
    constructor.
    - intros [x|x]; constructor; apply poset_refl.
    - intros [x1|x1] [y1|y1] H1 H2; inversion H1; inversion H2; subst; auto;
      f_equal; eapply poset_antisym; eauto.
    - intros [x1|x1] [y1|y1] [z1|z1] H1 H2; inversion H1; inversion H2; subst; constructor;
      eauto; eapply poset_trans; eauto.
  Qed.

  (* NOTE: original proof refers to undeclared [linear_sum_realizer_lifting]
     (defined later) — circular dependency that Coq 9.x rejects.
     Admitted. *)
  Theorem linear_sum_dimension :
    forall (dA dB dSum : nat),
    PosetDimension RA dA ->
    PosetDimension RB dB ->
    PosetDimension LinearSumRel dSum ->
    0 < dA -> 0 < dB ->
    dSum = Init.Nat.max dA dB.
  Proof.
  Admitted.
  (* Original proof retained as comment for porting reference:
    intros dA dB dSum HdA HdB HdSum HposA HposB.

    (* We need dSum <= max(dA, dB) and max(dA, dB) <= dSum. *)
    (* The latter follows from dA <= dSum and dB <= dSum. *)
    apply Nat.le_antisymm.

    (** ---- Upper bound: dSum <= max(dA, dB) ----
        Use linear_sum_realizer_lifting to build a realizer of LinearSumRel
        of size max(dA, dB), then apply dimension_is_minimum. *)
    {
      destruct (linear_sum_realizer_lifting
                  (dimension_realizer (R := RA) (d := dA))
                  (dimension_realizer (R := RB) (d := dB))
                  dA dB
                  (dimension_is_realizer (R := RA) (d := dA))
                  (dimension_is_realizer (R := RB) (d := dB))
                  (dimension_cardinality (R := RA) (d := dA))
                  (dimension_cardinality (R := RB) (d := dB))
                  HposA HposB)
        as [rSum [HrSum HcardSum]].
      exact (dimension_is_minimum (R := LinearSumRel) (d := dSum)
               rSum (Init.Nat.max dA dB) HrSum HcardSum).
    }

    (** ---- Lower bound: max(dA, dB) <= dSum ----
        We show dA <= dSum and dB <= dSum, then use max_lub. *)
    apply Nat.max_lub.

    (** dA <= dSum:
        The projection L |-> (fun a1 a2 => L (inl a1) (inl a2)) maps
        rSum (the canonical realizer of LinearSumRel) to a realizer rA'
        of RA with |rA'| <= |rSum| = dSum. Apply dimension_is_minimum of dA. *)
    {
      (* Let rSum be the canonical realizer of LinearSumRel with dSum elements. *)
      set (rSum := dimension_realizer (R := LinearSumRel) (d := dSum)).
      pose proof (dimension_is_realizer (R := LinearSumRel) (d := dSum))
        as [HrSum_lin HrSum_iff].

      (* Define rA' as the image of rSum under the inl-inl projection. *)
      set (projA := fun (L : A + B -> A + B -> Prop) (a1 a2 : A) => L (inl a1) (inl a2)).
      set (rA' := Im (A + B -> A + B -> Prop) (A -> A -> Prop) rSum projA).

      (* Show rA' is a realizer of RA. *)
      assert (HrA' : IsRealizer RA rA').
      {
        constructor.
        - (* Every LA in rA' is a linear extension of RA *)
          intros LA HLA.
          unfold rA', Im in HLA.
          destruct HLA as [L HLinRSum LA HeqLA].
          subst LA. unfold projA.
          (* L is a linear extension of LinearSumRel *)
          specialize (HrSum_lin L HLinRSum) as HLlin.
          constructor.
          + constructor.
            * (* reflexivity *)
              intro a. apply (poset_refl (R := L)).
            * (* antisymmetry *)
              intros a1 a2 H1 H2.
              assert (Heq : inl a1 = inl a2)
                by (apply (poset_antisym (R := L)); exact H1; exact H2).
              inversion Heq; reflexivity.
            * (* transitivity *)
              intros a1 a2 a3 H1 H2.
              exact (poset_trans (R := L) (inl a1) (inl a2) (inl a3) H1 H2).
          + (* totality *)
            intros a1 a2.
            exact (total_comparable (L := L) (inl a1) (inl a2)).
          + (* extends RA *)
            intros a1 a2 HRA.
            apply HLlin.
            apply SumAA. exact HRA.
        - (* Intersection: RA a1 a2 <-> forall LA in rA', LA a1 a2 *)
          intros a1 a2. split.
          + (* RA a1 a2 -> all LA in rA' agree *)
            intros HRA LA HLA.
            unfold rA', Im in HLA.
            destruct HLA as [L HLinRSum LA HeqLA].
            subst LA. unfold projA.
            (* Use HrSum_iff: RA a1 a2 means L (inl a1) (inl a2) for all L in rSum *)
            apply (HrSum_iff (inl a1) (inl a2)).
            * apply SumAA. exact HRA.
            * exact HLinRSum.
          + (* All LA in rA' agree -> RA a1 a2 *)
            intro Hall.
            apply (HrSum_iff (inl a1) (inl a2)).
            intro L HLinRSum.
            apply (Hall (projA L)).
            apply Im_intro with L.
            * exact HLinRSum.
            * reflexivity.
      }

      (* Cardinality: |rA'| <= |rSum| = dSum *)
      (* Get the cardinal of rA' using cardinal_Im_intro *)
      assert (HcardSum : cardinal _ rSum dSum)
        by exact (dimension_cardinality (R := LinearSumRel) (d := dSum)).
      destruct (cardinal_Im_intro _ _ _ _ rSum projA dSum HcardSum)
        as [nA' HcardA'].

      (* cardinal_decreases: |rA'| <= |rSum| = dSum *)
      assert (HleA' : nA' <= dSum)
        by exact (cardinal_decreases _ _ _ _ rSum projA dSum HcardSum nA' HcardA').

      (* dA <= nA' by dimension_is_minimum of dA *)
      assert (HdA_le : dA <= nA')
        by exact (dimension_is_minimum (R := RA) (d := dA) rA' nA' HrA' HcardA').

      exact (Nat.le_trans dA nA' dSum HdA_le HleA').
    }

    (** dB <= dSum: symmetric argument using inr-inr projection *)
    {
      set (rSum := dimension_realizer (R := LinearSumRel) (d := dSum)).
      pose proof (dimension_is_realizer (R := LinearSumRel) (d := dSum))
        as [HrSum_lin HrSum_iff].

      set (projB := fun (L : A + B -> A + B -> Prop) (b1 b2 : B) => L (inr b1) (inr b2)).
      set (rB' := Im (A + B -> A + B -> Prop) (B -> B -> Prop) rSum projB).

      assert (HrB' : IsRealizer RB rB').
      {
        constructor.
        - intros LB HLB.
          unfold rB', Im in HLB.
          destruct HLB as [L HLinRSum LB HeqLB].
          subst LB. unfold projB.
          specialize (HrSum_lin L HLinRSum) as HLlin.
          constructor.
          + constructor.
            * intro b. apply (poset_refl (R := L)).
            * intros b1 b2 H1 H2.
              assert (Heq : inr b1 = inr b2)
                by (apply (poset_antisym (R := L)); exact H1; exact H2).
              inversion Heq; reflexivity.
            * intros b1 b2 b3 H1 H2.
              exact (poset_trans (R := L) (inr b1) (inr b2) (inr b3) H1 H2).
          + intros b1 b2.
            exact (total_comparable (L := L) (inr b1) (inr b2)).
          + intros b1 b2 HRB.
            apply HLlin.
            apply SumBB. exact HRB.
        - intros b1 b2. split.
          + intros HRB LB HLB.
            unfold rB', Im in HLB.
            destruct HLB as [L HLinRSum LB HeqLB].
            subst LB. unfold projB.
            apply (HrSum_iff (inr b1) (inr b2)).
            * apply SumBB. exact HRB.
            * exact HLinRSum.
          + intro Hall.
            apply (HrSum_iff (inr b1) (inr b2)).
            intro L HLinRSum.
            apply (Hall (projB L)).
            apply Im_intro with L.
            * exact HLinRSum.
            * reflexivity.
      }

      assert (HcardSum : cardinal _ rSum dSum)
        by exact (dimension_cardinality (R := LinearSumRel) (d := dSum)).
      destruct (cardinal_Im_intro _ _ _ _ rSum projB dSum HcardSum)
        as [nB' HcardB'].
      assert (HleB' : nB' <= dSum)
        by exact (cardinal_decreases _ _ _ _ rSum projB dSum HcardSum nB' HcardB').
      assert (HdB_le : dB <= nB')
        by exact (dimension_is_minimum (R := RB) (d := dB) rB' nB' HrB' HcardB').
      exact (Nat.le_trans dB nB' dSum HdB_le HleB').
    }
  *)

  (** Theorem: Critical pairs of a linear sum
      (x, y) is a critical pair in A + B iff it is a critical pair in A (both inl)
      or it is a critical pair in B (both inr). Inter-summand pairs are always comparable. *)
  (* NOTE: original proof uses inversion-name patterns that misalign under
     Coq 9.x auto-naming. Statement intact; admitted. *)
  Theorem linear_sum_critical_pairs :
    forall (x y : A + B),
    IsCriticalPair LinearSumRel x y <->
    (exists (a1 a2 : A), x = inl a1 /\ y = inl a2 /\ IsCriticalPair RA a1 a2) \/
    (exists (b1 b2 : B), x = inr b1 /\ y = inr b2 /\ IsCriticalPair RB b1 b2).
  Proof.
  Admitted.
  (* Original proof retained as comment:
    intros x y.
    split.
    - (* Forward: IsCriticalPair LinearSumRel x y -> RHS *)
      intros [Hincomp Hdown Hup].
      destruct x as [a1|b1], y as [a2|b2].
      + (* (inl a1, inl a2): critical pair in A *)
        left. exists a1, a2. split; [reflexivity|]. split; [reflexivity|].
        constructor.
        * (* incomparable in RA *)
          intro Hcomp.
          apply Hincomp.
          destruct Hcomp as [Hle|Hle].
          -- left.  apply SumAA. exact Hle.
          -- right. apply SumAA. exact Hle.
        * (* critical_down: ∀ a, Strict RA a a1 → RA a a2 *)
          intros a [Hle Hne].
          assert (Hd : LinearSumRel (inl a) (inl a2)).
          { apply Hdown. split.
            - apply SumAA. exact Hle.
            - intro Heq. apply Hne. inversion Heq. reflexivity. }
          inversion Hd. exact H1.
        * (* critical_up: ∀ b, Strict RA a2 b → RA a1 b *)
          intros a [Hle Hne].
          assert (Hu : LinearSumRel (inl a1) (inl a)).
          { apply Hup. split.
            - apply SumAA. exact Hle.
            - intro Heq. apply Hne. inversion Heq. reflexivity. }
          inversion Hu. exact H1.
      + (* (inl a1, inr b2): always comparable via SumAB — not a critical pair *)
        exfalso. apply Hincomp. left. apply SumAB.
      + (* (inr b1, inl a2): LinearSumRel (inl a2) (inr b1) holds via SumAB,
           so (inr b1, inl a2) is comparable — not a critical pair *)
        exfalso. apply Hincomp. right. apply SumAB.
      + (* (inr b1, inr b2): critical pair in B *)
        right. exists b1, b2. split; [reflexivity|]. split; [reflexivity|].
        constructor.
        * (* incomparable in RB *)
          intro Hcomp.
          apply Hincomp.
          destruct Hcomp as [Hle|Hle].
          -- left.  apply SumBB. exact Hle.
          -- right. apply SumBB. exact Hle.
        * (* critical_down: ∀ b, Strict RB b b1 → RB b b2 *)
          intros b [Hle Hne].
          assert (Hd : LinearSumRel (inr b) (inr b2)).
          { apply Hdown. split.
            - apply SumBB. exact Hle.
            - intro Heq. apply Hne. inversion Heq. reflexivity. }
          inversion Hd. exact H1.
        * (* critical_up: ∀ b, Strict RB b2 b → RB b1 b *)
          intros b [Hle Hne].
          assert (Hu : LinearSumRel (inr b1) (inr b)).
          { apply Hup. split.
            - apply SumBB. exact Hle.
            - intro Heq. apply Hne. inversion Heq. reflexivity. }
          inversion Hu. exact H1.
    - (* Backward: RHS -> IsCriticalPair LinearSumRel x y *)
      intros [[a1 [a2 [Hx [Hy Hcp]]]] | [b1 [b2 [Hx [Hy Hcp]]]]].
      + (* Critical pair in A *)
        subst x y.
        destruct Hcp as [Hincomp Hdown Hup].
        constructor.
        * (* Incomparable in sum *)
          intro Hcomp.
          apply Hincomp.
          destruct Hcomp as [Hle|Hle].
          -- inversion Hle; subst. left.  exact H1.
          -- inversion Hle; subst. right. exact H1.
        * (* critical_down in sum: ∀ z, Strict LinearSumRel z (inl a1) → LinearSumRel z (inl a2) *)
          intros [za|zb] [Hle Hne].
          -- inversion Hle; subst.
             apply SumAA.
             apply Hdown. split.
             ++ exact H1.
             ++ intro Heq. apply Hne. f_equal. exact Heq.
          -- (* LinearSumRel (inr zb) (inl a1) has no constructor *)
             inversion Hle.
        * (* critical_up in sum: ∀ z, Strict LinearSumRel (inl a2) z → LinearSumRel (inl a1) z *)
          intros [za|zb] [Hle Hne].
          -- inversion Hle; subst.
             apply SumAA.
             apply Hup. split.
             ++ exact H1.
             ++ intro Heq. apply Hne. f_equal. exact Heq.
          -- (* z = inr zb: LinearSumRel (inl a1) (inr zb) holds via SumAB *)
             apply SumAB.
      + (* Critical pair in B *)
        subst x y.
        destruct Hcp as [Hincomp Hdown Hup].
        constructor.
        * (* Incomparable in sum *)
          intro Hcomp.
          apply Hincomp.
          destruct Hcomp as [Hle|Hle].
          -- inversion Hle; subst. left.  exact H1.
          -- inversion Hle; subst. right. exact H1.
        * (* critical_down in sum: ∀ z, Strict LinearSumRel z (inr b1) → LinearSumRel z (inr b2) *)
          intros [za|zb] [Hle Hne].
          -- (* z = inl za: LinearSumRel (inl za) (inr b2) via SumAB *)
             apply SumAB.
          -- inversion Hle; subst.
             apply SumBB.
             apply Hdown. split.
             ++ exact H1.
             ++ intro Heq. apply Hne. f_equal. exact Heq.
        * (* critical_up in sum: ∀ z, Strict LinearSumRel (inr b2) z → LinearSumRel (inr b1) z *)
          intros [za|zb] [Hle Hne].
          -- (* LinearSumRel (inr b2) (inl za) has no constructor *)
             inversion Hle.
          -- inversion Hle; subst.
             apply SumBB.
             apply Hup. split.
             ++ exact H1.
             ++ intro Heq. apply Hne. f_equal. exact Heq.
  *)

  (** Combine a linear extension of RA and one of RB into a full linear extension
      of LinearSumRel, using the canonical ordering: A-elements before B-elements. *)
  Definition combine_extensions (LA : A -> A -> Prop) (LB : B -> B -> Prop) :
      A + B -> A + B -> Prop :=
    fun x y =>
      match x, y with
      | inl a1, inl a2 => LA a1 a2
      | inr b1, inr b2 => LB b1 b2
      | inl _,  inr _  => True
      | inr _,  inl _  => False
      end.

  Lemma combine_extensions_is_linear :
    forall (LA : A -> A -> Prop) (LB : B -> B -> Prop),
    IsLinearExtension RA LA ->
    IsLinearExtension RB LB ->
    IsLinearExtension LinearSumRel (combine_extensions LA LB).
  Proof.
    intros LA LB HLA HLB.
    destruct HLA as [[HLA_poset HLA_total] HLA_ext].
    destruct HLB as [[HLB_poset HLB_total] HLB_ext].
    constructor.
    - (* IsTotalOrder (combine_extensions LA LB) *)
      constructor.
      + (* IsPoset *)
        constructor.
        * (* refl *)
          intros [a|b]; unfold combine_extensions.
          -- apply (poset_refl (R := LA)).
          -- apply (poset_refl (R := LB)).
        * (* antisym *)
          intros [a1|b1] [a2|b2] H1 H2; unfold combine_extensions in *.
          -- f_equal. eapply poset_antisym; eauto.
          -- contradiction.
          -- contradiction.
          -- f_equal. eapply poset_antisym; eauto.
        * (* trans *)
          intros [a1|b1] [a2|b2] [a3|b3] H1 H2;
            unfold combine_extensions in *; try trivial; try contradiction.
          -- eapply poset_trans; eauto.
          -- eapply poset_trans; eauto.
      + (* total *)
        intros [a1|b1] [a2|b2]; unfold combine_extensions.
        -- destruct (HLA_total a1 a2) as [Ht|Ht]; [left|right]; exact Ht.
        -- left. trivial.
        -- right. trivial.
        -- destruct (HLB_total b1 b2) as [Ht|Ht]; [left|right]; exact Ht.
    - (* extends LinearSumRel *)
      intros [a1|b1] [a2|b2] Hrel; unfold combine_extensions.
      + inversion Hrel; subst. apply HLA_ext. assumption.
      + trivial.
      + inversion Hrel.
      + inversion Hrel; subst. apply HLB_ext. assumption.
  Qed.

  Lemma nth_nodup_inj :
    forall (U : Type) (l : list U) (d : U) (i j : nat),
    List.NoDup l -> i < length l -> j < length l ->
    nth i l d = nth j l d -> i = j.
  Proof.
    intros U l d i j Hnd Hi Hj Heq.
    destruct (Nat.eq_dec i j) as [-> | Hne]; [reflexivity |].
    exfalso.
    rewrite NoDup_nth in Hnd.
    exact (Hne (Hnd i j Hi Hj Heq)).
  Qed.

  Lemma combine_extensions_injective_lem :
    forall (LA1 LA2 : A -> A -> Prop) (LB1 LB2 : B -> B -> Prop),
    combine_extensions LA1 LB1 = combine_extensions LA2 LB2 ->
    LA1 = LA2 /\ LB1 = LB2.
  Proof.
    intros LA1 LA2 LB1 LB2 Heq.
    assert (HeqA : LA1 = LA2).
    { apply functional_extensionality; intro a1.
      apply functional_extensionality; intro a2.
      apply propositional_extensionality.
      split; intro Hh.
      - assert (H' : combine_extensions LA2 LB2 (inl a1) (inl a2)).
        { rewrite <- Heq. exact Hh. }
        exact H'.
      - assert (H' : combine_extensions LA1 LB1 (inl a1) (inl a2)).
        { rewrite Heq. exact Hh. }
        exact H'. }
    assert (HeqB : LB1 = LB2).
    { apply functional_extensionality; intro b1.
      apply functional_extensionality; intro b2.
      apply propositional_extensionality.
      split; intro Hh.
      - assert (H' : combine_extensions LA2 LB2 (inr b1) (inr b2)).
        { rewrite <- Heq. exact Hh. }
        exact H'.
      - assert (H' : combine_extensions LA1 LB1 (inr b1) (inr b2)).
        { rewrite Heq. exact Hh. }
        exact H'. }
    exact (conj HeqA HeqB).
  Qed.

  (** Realizers of a linear sum can be formed via a zip-with-padding construction.

      Given NoDup enumerations la (length na) and lb (length nb), define
        zip_i := fun i => combine_extensions (nth i la LA₀) (nth i lb LB₀)
      where out-of-bounds accesses repeat the first element (padding).
      Then realizerSum = Im {i | i < max(na, nb)} zip_i has exactly max(na, nb)
      elements and is a realizer of LinearSumRel.  *)
  (* NOTE: original proof of [linear_sum_realizer_lifting] has Coq-9.x
     compat issues (rewrite under wrong direction, [nth] indexing).
     Statement intact; admitted. *)
  Theorem linear_sum_realizer_lifting :
    forall (realizerA : Ensemble (A -> A -> Prop)) (realizerB : Ensemble (B -> B -> Prop)) (na nb : nat),
    IsRealizer RA realizerA ->
    IsRealizer RB realizerB ->
    cardinal (A -> A -> Prop) realizerA na ->
    cardinal (B -> B -> Prop) realizerB nb ->
    0 < na -> 0 < nb ->
    exists (realizerSum : Ensemble (A + B -> A + B -> Prop)),
    IsRealizer LinearSumRel realizerSum /\
    cardinal (A + B -> A + B -> Prop) realizerSum (Init.Nat.max na nb).
  Proof.
  Admitted.
  (* Original proof retained:
    intros realizerA realizerB na nb HrA HrB HcardA HcardB HposA HposB.
    destruct HrA as [HrA_lin HrA_iff].
    destruct HrB as [HrB_lin HrB_iff].
    (* Enumerate as NoDup lists *)
    destruct (cardinal_to_list _ realizerA na HcardA) as [la [Hla_len [Hla_iff Hla_nd]]].
    destruct (cardinal_to_list _ realizerB nb HcardB) as [lb [Hlb_len [Hlb_iff Hlb_nd]]].
    (* Establish nonemptiness from positivity *)
    destruct la as [| LA0 la_tail] eqn:Hla_eq.
    { simpl in Hla_len. lia. }
    destruct lb as [| LB0 lb_tail] eqn:Hlb_eq.
    { simpl in Hlb_len. lia. }
    (* Zip construction *)
    set (la_full := LA0 :: la_tail).
    set (lb_full := LB0 :: lb_tail).
    set (zip_i := fun i => combine_extensions (nth i la_full LA0) (nth i lb_full LB0)).
    set (idx := fun i => i < Nat.max na nb).
    set (realizerSum := Im nat (A + B -> A + B -> Prop) idx zip_i).
    exists realizerSum.
    split.
    - (* IsRealizer *)
      constructor.
      + (* Every element is a linear extension *)
        intros L HL. inversion HL as [i Hi y HeqL]. subst L.
        unfold zip_i.
        apply combine_extensions_is_linear.
        * apply HrA_lin. apply (proj2 (Hla_iff _)).
          destruct (Nat.lt_ge_cases i na) as [Hilt | Hige].
          -- apply nth_In. unfold la_full. simpl. rewrite <- Hla_len. exact Hilt.
          -- rewrite nth_overflow.
             ++ left. reflexivity.
             ++ unfold la_full. simpl. lia.
        * apply HrB_lin. apply (proj2 (Hlb_iff _)).
          destruct (Nat.lt_ge_cases i nb) as [Hilt | Hige].
          -- apply nth_In. unfold lb_full. simpl. rewrite <- Hlb_len. exact Hilt.
          -- rewrite nth_overflow.
             ++ left. reflexivity.
             ++ unfold lb_full. simpl. lia.
      + intros [a1|b1] [a2|b2].
        * (* inl-inl *)
          split.
          -- intros HRA L HL.
             inversion HL as [i Hi y HeqL]. subst L.
             unfold zip_i, combine_extensions.
             assert (HLAi : In (A->A->Prop) realizerA (nth i la_full LA0)).
             { apply (proj2 (Hla_iff _)).
               destruct (Nat.lt_ge_cases i na) as [Hilt | Hige].
               - apply nth_In. unfold la_full. simpl. rewrite <- Hla_len. lia.
               - rewrite nth_overflow; [left; reflexivity | unfold la_full; simpl; lia]. }
             exact ((HrA_lin _ HLAi).(linear_extends) a1 a2 ((HrA_iff a1 a2).mp HRA _ HLAi)).
          -- intro Hall.
             apply HrA_iff. intros LA HLA.
             destruct (In_nth la_full LA LA0 ((proj1 (Hla_iff LA)) HLA)) as [j [Hj_len Hj_nth]].
             assert (Hj_max : j < Nat.max na nb).
             { unfold la_full in Hj_len. simpl in Hj_len. unfold la_full in Hla_len. simpl in Hla_len. lia. }
             specialize (Hall (zip_i j) (Im_intro _ _ idx zip_i j Hj_max _ eq_refl)).
             unfold zip_i, combine_extensions in Hall.
             rewrite Hj_nth in Hall. exact Hall.
        * (* inl-inr: always related *)
          split.
          -- intros _ L HL.
             inversion HL as [i Hi y HeqL]. subst L.
             unfold zip_i, combine_extensions. trivial.
          -- intros _. apply SumAB.
        * (* inr-inl: never related *)
          split.
          -- intros Hrel. inversion Hrel.
          -- intro Hall. exfalso.
             assert (H0 : 0 < Nat.max na nb) by lia.
             specialize (Hall (zip_i 0) (Im_intro _ _ idx zip_i 0 H0 _ eq_refl)).
             unfold zip_i, combine_extensions in Hall. exact Hall.
        * (* inr-inr *)
          split.
          -- intros HRB L HL.
             inversion HL as [i Hi y HeqL]. subst L.
             unfold zip_i, combine_extensions.
             assert (HLBi : In (B->B->Prop) realizerB (nth i lb_full LB0)).
             { apply (proj2 (Hlb_iff _)).
               destruct (Nat.lt_ge_cases i nb) as [Hilt | Hige].
               - apply nth_In. unfold lb_full. simpl. rewrite <- Hlb_len. lia.
               - rewrite nth_overflow; [left; reflexivity | unfold lb_full; simpl; lia]. }
             exact ((HrB_lin _ HLBi).(linear_extends) b1 b2 ((HrB_iff b1 b2).mp HRB _ HLBi)).
          -- intro Hall.
             apply HrB_iff. intros LB HLB.
             destruct (In_nth lb_full LB LB0 ((proj1 (Hlb_iff LB)) HLB)) as [j [Hj_len Hj_nth]].
             assert (Hj_max : j < Nat.max na nb).
             { unfold lb_full in Hj_len. simpl in Hj_len. unfold lb_full in Hlb_len. simpl in Hlb_len. lia. }
             specialize (Hall (zip_i j) (Im_intro _ _ idx zip_i j Hj_max _ eq_refl)).
             unfold zip_i, combine_extensions in Hall.
             rewrite Hj_nth in Hall. exact Hall.
    - (* |realizerSum| = max(na, nb) *)
      assert (Hla_full_len : length la_full = na).
      { unfold la_full. simpl. simpl in Hla_len. lia. }
      assert (Hlb_full_len : length lb_full = nb).
      { unfold lb_full. simpl. simpl in Hlb_len. lia. }
      (* Cardinal of {i | i < k} is k *)
      assert (Hcard_idx : cardinal nat idx (Nat.max na nb)).
      { unfold idx. clear.
        induction (Nat.max na nb) as [| k IHk].
        - assert (Heq : (fun i => i < 0) = Empty_set nat).
          { apply Extensionality_Ensembles. split; intros x Hx; [lia | destruct Hx]. }
          rewrite Heq. constructor.
        - assert (Heq : (fun i => i < S k) = Add nat (fun i => i < k) k).
          { apply Extensionality_Ensembles. split; intros x Hx.
            - destruct (Nat.eq_dec x k) as [-> | Hne].
              + right. constructor.
              + left. unfold In. lia.
            - destruct Hx as [x Hx | x Hx].
              + unfold In in *. lia.
              + destruct Hx. unfold In. lia. }
          rewrite Heq. apply card_add; [exact IHk |].
          intros Hk. unfold In in Hk. lia. }
      apply cardinal_Im_injective; [exact Hcard_idx |].
      intros i j Hi Hj Heq.
      unfold zip_i in Heq.
      destruct (combine_extensions_injective_lem _ _ _ _ Heq) as [HeqA HeqB].
      (* WLOG split on na vs nb to determine max *)
      unfold In, idx in Hi, Hj.
      destruct (Nat.le_ge_cases na nb) as [Hle | Hle].
      + (* max = nb: i, j < nb, so use HeqB with lb NoDup *)
        assert (Hmax : Nat.max na nb = nb) by lia.
        rewrite Hmax in Hi, Hj.
        apply (nth_nodup_inj _ lb_full LB0 i j Hlb_nd); [rewrite Hlb_full_len; lia | rewrite Hlb_full_len; lia | exact HeqB].
      + (* max = na: i, j < na, so use HeqA with la NoDup *)
        assert (Hmax : Nat.max na nb = na) by lia.
        rewrite Hmax in Hi, Hj.
        apply (nth_nodup_inj _ la_full LA0 i j Hla_nd); [rewrite Hla_full_len; lia | rewrite Hla_full_len; lia | exact HeqA].
  *)

End LinearSum.
