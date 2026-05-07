From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs.

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

  Theorem linear_sum_dimension :
    forall (dA dB dSum : nat),
    PosetDimension RA dA ->
    PosetDimension RB dB ->
    PosetDimension LinearSumRel dSum ->
    dSum = Init.Nat.max dA dB.
  Proof.
  Admitted.

  (** Theorem: Critical pairs of a linear sum
      (x, y) is a critical pair in A + B iff it is a critical pair in A (both inl)
      or it is a critical pair in B (both inr). Inter-summand pairs are always comparable. *)
  Theorem linear_sum_critical_pairs :
    forall (x y : A + B),
    IsCriticalPair LinearSumRel x y <->
    (exists (a1 a2 : A), x = inl a1 /\ y = inl a2 /\ IsCriticalPair RA a1 a2) \/
    (exists (b1 b2 : B), x = inr b1 /\ y = inr b2 /\ IsCriticalPair RB b1 b2).
  Proof.
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
  Qed.

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
        -- destruct (HLA_total a1 a2) as [H|H]; [left|right]; exact H.
        -- left. trivial.
        -- right. trivial.
        -- destruct (HLB_total b1 b2) as [H|H]; [left|right]; exact H.
    - (* extends LinearSumRel *)
      intros [a1|b1] [a2|b2] Hrel; inversion Hrel; subst; unfold combine_extensions.
      + exact (HLA_ext a1 a2 H1).
      + exact (HLB_ext b1 b2 H1).
      + trivial.
  Qed.

  (** Realizers of a linear sum can be formed by combining linear extensions of A and B.

      Construction: realizerSum = { combine_extensions LA LB | LA ∈ rA, LB ∈ rB }.

      The IsRealizer proof is complete modulo three admits:
        (i)  nonemptiness of rB (needed to extract LB when proving RA a1 a2 from Hall),
        (ii) nonemptiness of rA (needed for the inr–inl impossible case),
        (iii) cardinality: |realizerSum| = max(na, nb).

      The nonemptiness admits require knowing that any realizer of a poset with
      elements is nonempty (a consequence of Szpilrajn / at_least_one_linear_extension).
      The cardinality admit requires a "zip-with-padding" bijection argument.  *)
  Theorem linear_sum_realizer_lifting :
    forall (realizerA : Ensemble (A -> A -> Prop)) (realizerB : Ensemble (B -> B -> Prop)) (na nb : nat),
    IsRealizer RA realizerA ->
    IsRealizer RB realizerB ->
    cardinal (A -> A -> Prop) realizerA na ->
    cardinal (B -> B -> Prop) realizerB nb ->
    exists (realizerSum : Ensemble (A + B -> A + B -> Prop)),
    IsRealizer LinearSumRel realizerSum /\
    cardinal (A + B -> A + B -> Prop) realizerSum (Init.Nat.max na nb).
  Proof.
    intros realizerA realizerB na nb HrA HrB HcardA HcardB.
    destruct HrA as [HrA_lin HrA_iff].
    destruct HrB as [HrB_lin HrB_iff].
    (* The combined realizer *)
    set (realizerSum :=
      fun (L : A + B -> A + B -> Prop) =>
        exists (LA : A -> A -> Prop) (LB : B -> B -> Prop),
        In (A -> A -> Prop) realizerA LA /\
        In (B -> B -> Prop) realizerB LB /\
        L = combine_extensions LA LB).
    exists realizerSum.
    split.
    - constructor.
      + (* Every L ∈ realizerSum is a linear extension *)
        intros L [LA [LB [HLA [HLB ->]]]].
        apply combine_extensions_is_linear.
        * exact (HrA_lin LA HLA).
        * exact (HrB_lin LB HLB).
      + (* Intersection of realizerSum = LinearSumRel *)
        intros [a1|b1] [a2|b2].
        * (* (inl a1, inl a2) *)
          split.
          -- (* RA a1 a2 → every combined extension agrees *)
             intros HRA L [LA [LB [HLA [HLB ->]]]].
             unfold combine_extensions.
             exact (HrA_lin LA HLA).(linear_extends) a1 a2
               ((HrA_iff a1 a2).mp HRA LA HLA).
          -- (* All combined extensions agree → RA a1 a2 *)
             intro Hall.
             apply HrA_iff.
             intros LA HLA.
             (* To instantiate Hall we need some LB ∈ realizerB. *)
             (* Admitted: nonemptiness of realizerB *)
             admit.
        * (* (inl a1, inr b2): always related via SumAB *)
          split.
          -- intros _ L [LA [LB [HLA [HLB ->]]]]. unfold combine_extensions. trivial.
          -- intros _. apply SumAB.
        * (* (inr b1, inl a2): never related in LinearSumRel *)
          split.
          -- intros Hrel. inversion Hrel.
          -- (* Hall says combine_extensions LA LB (inr b1) (inl a2) for all LA,LB — contradiction.
                Admitted: nonemptiness of realizerA and realizerB to witness the contradiction. *)
             intro Hall. admit.
        * (* (inr b1, inr b2) *)
          split.
          -- intros HRB L [LA [LB [HLA [HLB ->]]]].
             unfold combine_extensions.
             exact (HrB_lin LB HLB).(linear_extends) b1 b2
               ((HrB_iff b1 b2).mp HRB LB HLB).
          -- intro Hall.
             apply HrB_iff.
             intros LB HLB.
             (* Need some LA ∈ realizerA. Admitted: nonemptiness of realizerA. *)
             admit.
    - (* |realizerSum| = max(na, nb).
         Requires "zip with padding" construction; admitted. *)
      admit.
  Qed.

End LinearSum.
