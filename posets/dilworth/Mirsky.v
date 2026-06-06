(** * Mirsky's theorem — infrastructure (lower-bound direction).

    Mirsky's theorem: in a finite poset the minimum number of antichains needed
    to cover P equals the height (length of a longest chain).

    This file starts the track with the *lower-bound* direction, which is clean
    and reusable:

      [chain_le_antichain_cover] : any chain has size <= any antichain cover,
      hence height <= (antichain) cover number.

    Pigeonhole: send each chain element to an antichain of the cover containing
    it; distinct chain elements are comparable, so they cannot land in the same
    antichain — the map is injective, so |chain| <= |cover|.

    The *upper-bound* direction (build a height-sized antichain cover via a
    longest-chain rank function) needs a rank/well-founded-recursion layer the
    repo does not yet have; it is the documented next step (see the track status
    doc). Index entry: [mirsky] in docs/references/poset-facts-index.md. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image ClassicalEpsilon.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.

Section Mirsky.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Injective image preserves cardinality (local copy; Stdlib-only). *)
  Lemma cardinal_Im_inj :
    forall (U V : Type) (S : Ensemble U) (f : U -> V) (n : nat),
      cardinal U S n ->
      (forall x y, In U S x -> In U S y -> f x = f y -> x = y) ->
      cardinal V (Im U V S f) n.
  Proof.
    intros U V S f n Hcard Hinj.
    induction Hcard as [| A0 n0 Hcard0 IHHcard x Hxnin].
    - assert (Heq : Im U V (Empty_set U) f = Empty_set V).
      { apply Extensionality_Ensembles. split.
        - intros y [z Hz _Heqy]. destruct Hz.
        - intros y Hy. destruct Hy. }
      rewrite Heq. constructor.
    - assert (Hnew : ~ In V (Im U V A0 f) (f x)).
      { intros HIm. inversion HIm as [z HzA0 y Heqz]; subst.
        apply Hxnin.
        rewrite (Hinj x z (Add_intro2 _ A0 x) (Union_introl _ _ _ _ HzA0) Heqz).
        exact HzA0. }
      assert (Heq : Im U V (Add U A0 x) f = Add V (Im U V A0 f) (f x)).
      { apply Extensionality_Ensembles. split.
        - intros y [z Hz y_unused Heqy]. destruct Hz as [z Hz | z Hz].
          + left. exists z; auto.
          + destruct Hz. right. rewrite Heqy. constructor.
        - intros y Hy. destruct Hy as [y Hy | y Hy].
          + destruct Hy as [z Hz y_unused Heqy]. exists z; [left; exact Hz | exact Heqy].
          + destruct Hy. exists x; [right; constructor | reflexivity]. }
      rewrite Heq. apply card_add.
      + apply IHHcard.
        intros a b Ha Hb Heqab.
        apply Hinj; [left; exact Ha | left; exact Hb | exact Heqab].
      + exact Hnew.
  Qed.

  (** Lower bound: a chain is no larger than any antichain cover. *)
  Theorem chain_le_antichain_cover :
    forall (chain : Ensemble A) (cover : Ensemble (Ensemble A)) (h k : nat),
      IsChain R chain ->
      IsAntichainCover R (Full_set A) cover ->
      cardinal A chain h ->
      cardinal (Ensemble A) cover k ->
      h <= k.
  Proof.
    intros chain cover h k Hchain Hcover Hch Hck.
    destruct Hchain as [_ Hcmp].
    destruct Hcover as [Hanti _ Hcov].
    (* choose, for each x, an antichain of the cover containing x *)
    pose (sel := fun x : A =>
            constructive_indefinite_description _ (Hcov x (Full_intro A x))).
    pose (pick := fun x : A => proj1_sig (sel x)).
    assert (Hpick1 : forall x, In (Ensemble A) cover (pick x))
      by (intro x; exact (proj1 (proj2_sig (sel x)))).
    assert (Hpick2 : forall x, In A (pick x) x)
      by (intro x; exact (proj2 (proj2_sig (sel x)))).
    (* pick is injective on the chain *)
    assert (Hinj : forall a b, In A chain a -> In A chain b -> pick a = pick b -> a = b).
    { intros a b Ha Hb Heq.
      assert (Hain : In A (pick a) a) by apply Hpick2.
      assert (Hbin : In A (pick a) b) by (rewrite Heq; apply Hpick2).
      destruct (Hanti (pick a) (Hpick1 a)) as [_ Hinc].
      apply Hinc; [exact Hain | exact Hbin |].
      apply Hcmp; assumption. }
    (* image of the chain is a subfamily of the cover, of the same size *)
    assert (Hcard_Im : cardinal (Ensemble A) (Im A (Ensemble A) chain pick) h)
      by (apply cardinal_Im_inj; [exact Hch | exact Hinj]).
    assert (Hsub : Included (Ensemble A) (Im A (Ensemble A) chain pick) cover).
    { intros c Hc. destruct Hc as [x Hx c0 Heqc]. subst c0. apply Hpick1. }
    exact (incl_card_le (Ensemble A) (Im A (Ensemble A) chain pick) cover h k
             Hcard_Im Hck Hsub).
  Qed.

End Mirsky.
