(* dimension invariance under order-isomorphism *)
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical ProofIrrelevance.
From Stdlib Require Import FunctionalExtensionality PropExtensionality.
From Stdlib Require Import Image.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs LinearSum.

(** * Dimension is invariant under order-isomorphism. *)

Section DimIso.

  (** Transport a relation on [A] to a relation on [B] using [g : B -> A]. *)
  Definition transport_rel {A B : Type} (g : B -> A) (L : A -> A -> Prop)
    : B -> B -> Prop :=
    fun b b' => L (g b) (g b').

  (** A linear extension transports to a linear extension under an
      order-isomorphism. *)
  Lemma transport_linear_extension :
    forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
           `{IsPoset A R} `{IsPoset B S}
           (f : A -> B) (g : B -> A),
      (forall a, g (f a) = a) -> (forall b, f (g b) = b) ->
      (forall a a', R a a' <-> S (f a) (f a')) ->
      forall L, IsLinearExtension R L ->
                IsLinearExtension S (transport_rel g L).
  Proof.
    intros A B R S HRposet HSposet f g Hgf Hfg Hiso L HL.
    assert (HLposet0 : IsPoset A L).
    { destruct HL as [[HLp ?] ?]. exact HLp. }
    unfold transport_rel.
    constructor.
    - (* IsTotalOrder S (fun b b' => L (g b) (g b')) *)
      constructor.
      + (* IsPoset *)
        constructor.
        * (* refl *)
          intro b. apply poset_refl.
        * (* antisym *)
          intros b b' Hbb' Hb'b.
          assert (Heq : g b = g b').
          { apply (poset_antisym (R := L)); assumption. }
          (* g b = g b' -> f (g b) = f (g b') -> b = b' *)
          assert (Hf : f (g b) = f (g b')) by (rewrite Heq; reflexivity).
          rewrite !Hfg in Hf. exact Hf.
        * (* trans *)
          intros b1 b2 b3 H12 H23.
          apply (poset_trans (R := L) (g b1) (g b2) (g b3)); assumption.
      + (* total_comparable *)
        intros b b'.
        destruct HL as [HLtot HLext].
        destruct HLtot as [HLposet HLcomp].
        apply (HLcomp (g b) (g b')).
    - (* linear_extends: S b b' -> L (g b) (g b') *)
      intros b b' Hbb'.
      destruct HL as [HLtot HLext].
      apply HLext.
      (* need R (g b) (g b') from S b b' *)
      apply (Hiso (g b) (g b')).
      rewrite !Hfg. exact Hbb'.
  Qed.

  (** The image of a realizer of [R] under transport is a realizer of [S]. *)
  Lemma transport_realizer :
    forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
           `{IsPoset A R} `{IsPoset B S}
           (f : A -> B) (g : B -> A),
      (forall a, g (f a) = a) -> (forall b, f (g b) = b) ->
      (forall a a', R a a' <-> S (f a) (f a')) ->
      forall r, IsRealizer R r ->
                IsRealizer S (Im _ _ r (transport_rel g)).
  Proof.
    intros A B R S HRposet HSposet f g Hgf Hfg Hiso r Hr.
    constructor.
    - (* realizer_linear: every member of the image is a linear extension *)
      intros M HM.
      inversion HM as [L HLr M' HMeq]; subst.
      apply (transport_linear_extension A B R S f g Hgf Hfg Hiso).
      apply (realizer_linear Hr). exact HLr.
    - (* realizer_intersection *)
      intros b b'.
      split.
      + (* S b b' -> forall M in image, M b b' *)
        intros Hbb' M HM.
        inversion HM as [L HLr M' HMeq]; subst.
        unfold transport_rel.
        (* need L (g b) (g b'); use R intersection at g b, g b' *)
        apply (proj1 (realizer_intersection Hr (g b) (g b'))).
        * apply (Hiso (g b) (g b')). rewrite !Hfg. exact Hbb'.
        * exact HLr.
      + (* (forall M in image, M b b') -> S b b' *)
        intros Hall.
        (* derive R (g b) (g b') from intersection over r *)
        assert (HR : R (g b) (g b')).
        { apply (proj2 (realizer_intersection Hr (g b) (g b'))).
          intros L HLr.
          specialize (Hall (transport_rel g L)).
          unfold transport_rel in Hall.
          apply Hall.
          apply Im_intro with (x := L); [exact HLr | reflexivity]. }
        apply (Hiso (g b) (g b')) in HR.
        rewrite !Hfg in HR. exact HR.
  Qed.

  (** Transport is injective on a realizer (because [g] is surjective). *)
  Lemma transport_injective :
    forall (A B : Type) (g : B -> A) (f : A -> B),
      (forall a, g (f a) = a) ->
      forall L1 L2 : A -> A -> Prop,
        transport_rel g L1 = transport_rel g L2 -> L1 = L2.
  Proof.
    intros A B g f Hgf L1 L2 Heq.
    apply functional_extensionality; intro a.
    apply functional_extensionality; intro a'.
    (* every a is g (f a); read off pointwise from Heq at (f a) (f a') *)
    assert (Hpt : transport_rel g L1 (f a) (f a')
                  = transport_rel g L2 (f a) (f a')).
    { rewrite Heq. reflexivity. }
    unfold transport_rel in Hpt.
    rewrite !Hgf in Hpt. exact Hpt.
  Qed.

  Theorem dimension_iso :
    forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
           `{IsPoset A R} `{IsPoset B S}
           (f : A -> B) (g : B -> A),
      (forall a, g (f a) = a) -> (forall b, f (g b) = b) ->
      (forall a a', R a a' <-> S (f a) (f a')) ->
      forall d, PosetDimension R d -> PosetDimension S d.
  Proof.
    intros A B R S HRposet HSposet f g Hgf Hfg Hiso d Hd.
    (* The realizer of S: image of R's realizer under transport. *)
    set (r := dimension_realizer Hd).
    set (rS := Im _ _ r (transport_rel g)).
    assert (HrR : IsRealizer R r) by exact (dimension_is_realizer Hd).
    (* rS is a realizer of S *)
    assert (HrS : IsRealizer S rS).
    { apply (transport_realizer A B R S f g Hgf Hfg Hiso). exact HrR. }
    (* rS has cardinality d *)
    assert (HcardS : cardinal _ rS d).
    { unfold rS.
      apply (cardinal_Im_injective _ _ r (transport_rel g) d).
      - exact (dimension_cardinality Hd).
      - intros L1 L2 HL1 HL2 Heq.
        apply (transport_injective A B g f Hgf L1 L2 Heq). }
    (* minimality of d *)
    refine {| dimension_realizer := rS;
              dimension_is_realizer := HrS;
              dimension_cardinality := HcardS;
              dimension_is_minimum := _ |}.
    (* Pull back any realizer of S to a realizer of R of same cardinality. *)
    intros rS' n HrS' Hcard'.
    (* transport along the inverse iso: g' := f, f' := g, R' := S, S' := R *)
    pose (rR' := Im _ _ rS' (transport_rel f)).
    assert (HrR' : IsRealizer R rR').
    { apply (transport_realizer B A S R g f Hfg Hgf).
      - (* order iso in the reverse direction: S b b' <-> R (g b) (g b') *)
        intros b b'.
        split.
        + intro Hbb'. apply (Hiso (g b) (g b')). rewrite !Hfg. exact Hbb'.
        + intro Hgg. apply (Hiso (g b) (g b')) in Hgg. rewrite !Hfg in Hgg. exact Hgg.
      - exact HrS'. }
    assert (HcardR' : cardinal _ rR' n).
    { unfold rR'.
      apply (cardinal_Im_injective _ _ rS' (transport_rel f) n).
      - exact Hcard'.
      - intros M1 M2 HM1 HM2 Heq.
        apply (transport_injective B A f g Hfg M1 M2 Heq). }
    exact (dimension_is_minimum Hd rR' n HrR' HcardR').
  Qed.

End DimIso.
