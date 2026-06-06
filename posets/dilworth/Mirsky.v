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
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image ClassicalEpsilon Arith Lia.
From Posets Require Import PosetClasses FinitePoset FiniteMax FinPosetWF FinPosetRank.
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

(** Cardinality of the integer interval [1 .. H]. *)
Lemma cardinal_nat_interval :
  forall H, cardinal nat (fun k => 1 <= k /\ k <= H) H.
Proof.
  induction H as [| H IH].
  - assert (Heq : (fun k => 1 <= k /\ k <= 0) = Empty_set nat).
    { apply Extensionality_Ensembles. split; intros k Hk.
      - destruct Hk as [H1 H2]. lia.
      - destruct Hk. }
    rewrite Heq. constructor.
  - assert (Heq : (fun k => 1 <= k /\ k <= S H)
                  = Add nat (fun k => 1 <= k /\ k <= H) (S H)).
    { apply Extensionality_Ensembles. split; intros k Hk.
      - destruct Hk as [H1 H2]. destruct (Nat.eq_dec k (S H)) as [He | Hne].
        + right. rewrite He. constructor.
        + left. split; lia.
      - destruct Hk as [k Hk | k Hk].
        + destruct Hk as [H1 H2]. split; lia.
        + destruct Hk. split; lia. }
    rewrite Heq. apply card_add; [exact IH | intros [H1 H2]; lia].
Qed.

(** ** Upper bound: the rank-level antichain cover. *)
Section MirskyUpper.
  Context {A : Type} (R : A -> A -> Prop) {n : nat} `{IsFinitePoset A R n}.
  #[local] Existing Instance fp_is_poset.

  (** Rank level [k]: the elements of rank exactly [k]. *)
  Definition Level (k : nat) : Ensemble A := fun x => rank R x = k.

  (** A nonempty level is an antichain (equal rank + comparable ⇒ equal). *)
  Lemma level_antichain : forall k, Inhabited A (Level k) -> IsAntichain R (Level k).
  Proof.
    intros k Hinh. constructor.
    - exact Hinh.
    - intros x y Hx Hy Hcmp. unfold In, Level in Hx, Hy.
      apply (rank_level_antichain R x y); [ rewrite Hx, Hy; reflexivity | exact Hcmp ].
  Qed.

  (** The cover: the nonempty rank levels [1 .. height]. *)
  Definition mirsky_cover : Ensemble (Ensemble A) :=
    fun C => exists k, 1 <= k /\ k <= height R /\ Inhabited A (Level k) /\ C = Level k.

  Theorem mirsky_cover_is_cover : IsAntichainCover R (Full_set A) mirsky_cover.
  Proof.
    constructor.
    - (* each member is an antichain *)
      intros C HC. destruct HC as [k [_ [_ [Hinh Heq]]]]. subst C.
      apply level_antichain. exact Hinh.
    - (* each member is included in the ground set *)
      intros C _ x _. constructor.
    - (* every element is covered, by its own level *)
      intros x _. exists (Level (rank R x)). split.
      + exists (rank R x). split; [apply rank_pos | split; [apply rank_le_height | split]].
        * exists x. unfold In, Level. reflexivity.
        * reflexivity.
      + unfold In, Level. reflexivity.
  Qed.

  (** When the height is positive, it is attained by some element. *)
  Lemma height_attained : 1 <= height R -> exists x0, rank R x0 = height R.
  Proof.
    intro Hpos.
    assert (Hinh : Inhabited A (Full_set A)).
    { destruct (classic (Inhabited A (Full_set A))) as [Hi | Hni]; [exact Hi |].
      exfalso. unfold height in Hpos.
      destruct (the_lub_is_lub (Full_set A) (full_finite R) (rank R)) as [_ Hleast].
      assert (the_lub (Full_set A) (full_finite R) (rank R) <= 0).
      { apply Hleast. intros z _. exfalso. apply Hni. exists z. constructor. }
      lia. }
    destruct (finite_max_achieved (Full_set A) (full_finite R) (rank R) Hinh)
      as [x0 [_ Hx0]]. exists x0. exact Hx0.
  Qed.

  (** Every level in [1 .. height] is nonempty (contiguity of ranks). *)
  Lemma levels_nonempty :
    forall k, 1 <= k -> k <= height R -> Inhabited A (Level k).
  Proof.
    intros k Hk1 Hkh.
    destruct (height_attained (Nat.le_trans 1 k (height R) Hk1 Hkh)) as [x0 Hx0].
    destruct (rank_achieves R x0 k Hk1 (eq_ind_r (fun h => k <= h) Hkh Hx0)) as [z Hz].
    exists z. unfold In, Level. exact Hz.
  Qed.

  Definition Iv : Ensemble nat := fun k => 1 <= k /\ k <= height R.

  Lemma cover_eq_image : mirsky_cover = Im nat (Ensemble A) Iv Level.
  Proof.
    apply Extensionality_Ensembles. split.
    - intros C HC. destruct HC as [k [Hk1 [Hkh [_ Heq]]]].
      apply Im_intro with (x := k); [ split; assumption | exact Heq ].
    - intros C HC. destruct HC as [k Hk C0 Heq]. subst C0.
      exists k. destruct Hk as [Hk1 Hkh].
      repeat split; try assumption.
      apply levels_nonempty; assumption.
  Qed.

  Lemma Level_inj :
    forall k k', In nat Iv k -> In nat Iv k' -> Level k = Level k' -> k = k'.
  Proof.
    intros k k' [Hk1 Hkh] _ Heq.
    destruct (levels_nonempty k Hk1 Hkh) as [z Hz].
    assert (Hz' : In A (Level k') z) by (rewrite <- Heq; exact Hz).
    unfold In, Level in Hz, Hz'. transitivity (rank R z); [symmetry; exact Hz | exact Hz'].
  Qed.

  Theorem mirsky_cover_cardinal :
    cardinal (Ensemble A) mirsky_cover (height R).
  Proof.
    rewrite cover_eq_image.
    apply cardinal_Im_inj; [ exact (cardinal_nat_interval (height R)) | exact Level_inj ].
  Qed.

  (** Capstone: the rank-level cover is an antichain cover of size [height], and
      (by the lower bound) no chain exceeds [height]. So the minimum antichain
      cover number equals [height], and [height] bounds every chain — Mirsky's
      theorem with [height] = max rank as the height invariant. *)
  Theorem mirsky_height_cover :
    IsAntichainCover R (Full_set A) mirsky_cover /\
    cardinal (Ensemble A) mirsky_cover (height R).
  Proof. split; [ exact mirsky_cover_is_cover | exact mirsky_cover_cardinal ]. Qed.

  Theorem chain_card_le_height :
    forall chain h, IsChain R chain -> cardinal A chain h -> h <= height R.
  Proof.
    intros chain h Hchain Hcard.
    exact (chain_le_antichain_cover R chain mirsky_cover h (height R)
             Hchain mirsky_cover_is_cover Hcard mirsky_cover_cardinal).
  Qed.

End MirskyUpper.
