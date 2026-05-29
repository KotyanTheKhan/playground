(** Edge-count / comparability identities shared by the higher edge-count
    cases (counts 5-9) of the n=5 dispatcher.

    Kept in a SEPARATE file from [EdgeCount] so that adding these lemmas does
    not invalidate the heavy [EdgeCount4_*] cascade caches that depend on
    [EdgeCount]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Dimension.N5Exhaustive Require Import EdgeCount.

Section EdgeCountIncomp.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  (** A comparable pair of distinct elements contributes exactly 1 to the
      edge count (one direction is a strict edge, the other is not). *)
  Lemma comparable_indicator_sum :
    forall x y, x <> y -> (R2 x y \/ R2 y x) ->
      strict_indicator R2 x y + strict_indicator R2 y x = 1.
  Proof.
    intros x y Hxy [HR | HR].
    - rewrite (strict_indicator_eq_1 R2 x y HR Hxy).
      assert (strict_indicator R2 y x = 0) as ->.
      { apply strict_indicator_eq_0. intros [HRyx _].
        apply Hxy. exact (poset_antisym x y HR HRyx). }
      lia.
    - assert (Hyx : y <> x) by (intro Heq; apply Hxy; symmetry; exact Heq).
      rewrite (strict_indicator_eq_1 R2 y x HR Hyx).
      assert (strict_indicator R2 x y = 0) as ->.
      { apply strict_indicator_eq_0. intros [HRxy _].
        apply Hxy. exact (poset_antisym x y HRxy HR). }
      lia.
  Qed.

  (** If the edge count is at most 9 then some pair is incomparable
      (otherwise every one of the 10 pairs would contribute 1, forcing the
      count to be 10).  Witnesses are carrier elements via the cover. *)
  Lemma incomp_carrier_exists :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e <= 9 ->
      exists x y : B, @Incomparable B R2 x y.
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hle.
    apply NNPP. intro Hno.
    assert (Hcomp : forall x y, x <> y -> R2 x y \/ R2 y x).
    { intros x y Hxy. apply NNPP. intro Hnc.
      apply Hno. exists x, y. exact Hnc. }
    pose proof (comparable_indicator_sum a b Hab (Hcomp a b Hab)).
    pose proof (comparable_indicator_sum a c Hac (Hcomp a c Hac)).
    pose proof (comparable_indicator_sum a d Had (Hcomp a d Had)).
    pose proof (comparable_indicator_sum a e Hae (Hcomp a e Hae)).
    pose proof (comparable_indicator_sum b c Hbc (Hcomp b c Hbc)).
    pose proof (comparable_indicator_sum b d Hbd (Hcomp b d Hbd)).
    pose proof (comparable_indicator_sum b e Hbe (Hcomp b e Hbe)).
    pose proof (comparable_indicator_sum c d Hcd (Hcomp c d Hcd)).
    pose proof (comparable_indicator_sum c e Hce (Hcomp c e Hce)).
    pose proof (comparable_indicator_sum d e Hde (Hcomp d e Hde)).
    unfold edge_count_5 in Hle. lia.
  Qed.

  (** Two incomparable pairs sharing the vertex [u] (so [{u,v}] and [{u,w}]
      with [v <> w]) force the edge count down to at most 8: both pairs
      contribute 0, and the remaining eight pairs contribute at most 1 each. *)
  Lemma two_incomp_le_8 :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      forall u v w : B,
        @Incomparable B R2 u v -> @Incomparable B R2 u w -> v <> w ->
        edge_count_5 R2 a b c d e <= 8.
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
           u v w Huv Huw Hvw.
    assert (Zuv : strict_indicator R2 u v = 0)
      by (apply strict_indicator_eq_0; intros [HR _]; apply Huv; left; exact HR).
    assert (Zvu : strict_indicator R2 v u = 0)
      by (apply strict_indicator_eq_0; intros [HR _]; apply Huv; right; exact HR).
    assert (Zuw : strict_indicator R2 u w = 0)
      by (apply strict_indicator_eq_0; intros [HR _]; apply Huw; left; exact HR).
    assert (Zwu : strict_indicator R2 w u = 0)
      by (apply strict_indicator_eq_0; intros [HR _]; apply Huw; right; exact HR).
    pose proof (strict_indicator_antisym R2 a b Hab).
    pose proof (strict_indicator_antisym R2 a c Hac).
    pose proof (strict_indicator_antisym R2 a d Had).
    pose proof (strict_indicator_antisym R2 a e Hae).
    pose proof (strict_indicator_antisym R2 b c Hbc).
    pose proof (strict_indicator_antisym R2 b d Hbd).
    pose proof (strict_indicator_antisym R2 b e Hbe).
    pose proof (strict_indicator_antisym R2 c d Hcd).
    pose proof (strict_indicator_antisym R2 c e Hce).
    pose proof (strict_indicator_antisym R2 d e Hde).
    unfold edge_count_5.
    destruct (Hcov u) as [Hu|[Hu|[Hu|[Hu|Hu]]]];
    destruct (Hcov v) as [Hv|[Hv|[Hv|[Hv|Hv]]]];
    destruct (Hcov w) as [Hw|[Hw|[Hw|[Hw|Hw]]]];
    subst;
    try (exfalso; apply Hvw; reflexivity);
    try (exfalso; apply Huv; left; apply poset_refl);
    try (exfalso; apply Huw; left; apply poset_refl);
    lia.
  Qed.

  (** Down-count rank: [dle z x] is 1 iff [z <= x], and [rk] sums it over the
      five carrier elements (= number of elements at or below [x]). *)
  Definition dle (z x : B) : nat :=
    if excluded_middle_informative (R2 z x) then 1 else 0.

  Definition rk (a b c d e x : B) : nat :=
    dle a x + dle b x + dle c x + dle d x + dle e x.

  Lemma dle_mono : forall z x y, R2 x y -> dle z x <= dle z y.
  Proof.
    intros z x y HR. unfold dle.
    destruct (excluded_middle_informative (R2 z x)) as [Hzx|]; [|lia].
    destruct (excluded_middle_informative (R2 z y)) as [|Hnzy]; [lia|].
    exfalso. apply Hnzy. exact (poset_trans z x y Hzx HR).
  Qed.

  Lemma dle_self : forall x, dle x x = 1.
  Proof.
    intro x. unfold dle.
    destruct (excluded_middle_informative (R2 x x)) as [|N];
      [reflexivity | exfalso; apply N; apply poset_refl].
  Qed.

  Lemma dle_zero_of_not : forall z x, ~ R2 z x -> dle z x = 0.
  Proof.
    intros z x H. unfold dle.
    destruct (excluded_middle_informative (R2 z x)); [contradiction | reflexivity].
  Qed.

  (** [rk] is strictly monotone along strict edges. *)
  Lemma rk_strict_mono :
    forall a b c d e,
      (forall w : B, w = a \/ w = b \/ w = c \/ w = d \/ w = e) ->
      forall x y, R2 x y -> x <> y -> rk a b c d e x < rk a b c d e y.
  Proof.
    intros a b c d e Hcov x y HR Hxy.
    pose proof (dle_mono a x y HR).
    pose proof (dle_mono b x y HR).
    pose proof (dle_mono c x y HR).
    pose proof (dle_mono d x y HR).
    pose proof (dle_mono e x y HR).
    assert (Hyx0 : dle y x = 0).
    { apply dle_zero_of_not. intro Hyx. apply Hxy. exact (poset_antisym x y HR Hyx). }
    assert (Hyy1 : dle y y = 1) by (apply dle_self).
    unfold rk.
    destruct (Hcov y) as [Ey|[Ey|[Ey|[Ey|Ey]]]]; subst y; lia.
  Qed.

  (** General twin lemma: if [x], [y] are incomparable and every other carrier
      element is comparable to BOTH, then they have equal down-count rank.
      Off-pair elements sit on the same side of [x] and [y] (else transitivity
      makes [x],[y] comparable); [x] and [y] swap their (1,0)/(0,1)
      contributions.  This is the matching-incomparability case, independent of
      the exact edge count. *)
  Lemma twin_rk_eq_gen :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall w : B, w = a \/ w = b \/ w = c \/ w = d \/ w = e) ->
      forall x y, @Incomparable B R2 x y ->
        (forall z, z <> x -> z <> y -> R2 z x \/ R2 x z) ->
        (forall z, z <> x -> z <> y -> R2 z y \/ R2 y z) ->
        rk a b c d e x = rk a b c d e y.
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov x y Hxy Hcx Hcy.
    assert (Hxy_ne : x <> y) by (intro E; subst; apply Hxy; left; apply poset_refl).
    assert (Hdz : forall z, z <> x -> z <> y -> dle z x = dle z y).
    { intros z Hzx Hzy.
      destruct (Hcx z Hzx Hzy) as [A|A]; destruct (Hcy z Hzx Hzy) as [Bb|Bb].
      - unfold dle.
        destruct (excluded_middle_informative (R2 z x)) as [|N];
          [|exfalso; apply N; exact A].
        destruct (excluded_middle_informative (R2 z y)) as [|N];
          [reflexivity|exfalso; apply N; exact Bb].
      - exfalso. apply Hxy. right. exact (poset_trans y z x Bb A).
      - exfalso. apply Hxy. left. exact (poset_trans x z y A Bb).
      - unfold dle.
        destruct (excluded_middle_informative (R2 z x)) as [Rzx|];
          [exfalso; apply Hzx; exact (poset_antisym z x Rzx A)|].
        destruct (excluded_middle_informative (R2 z y)) as [Rzy|];
          [exfalso; apply Hzy; exact (poset_antisym z y Rzy Bb)|reflexivity]. }
    assert (Hxx1 : dle x x = 1) by (apply dle_self).
    assert (Hyy1 : dle y y = 1) by (apply dle_self).
    assert (Hxy0 : dle x y = 0)
      by (apply dle_zero_of_not; intro H; apply Hxy; left; exact H).
    assert (Hyx0 : dle y x = 0)
      by (apply dle_zero_of_not; intro H; apply Hxy; right; exact H).
    unfold rk.
    destruct (Hcov x) as [Ex|[Ex|[Ex|[Ex|Ex]]]];
    destruct (Hcov y) as [Ey|[Ey|[Ey|[Ey|Ey]]]];
    subst x y;
    try (exfalso; apply Hxy_ne; reflexivity);
    try (rewrite (Hdz a) by congruence);
    try (rewrite (Hdz b) by congruence);
    try (rewrite (Hdz c) by congruence);
    try (rewrite (Hdz d) by congruence);
    try (rewrite (Hdz e) by congruence);
    rewrite ?Hxx1, ?Hyy1, ?Hxy0, ?Hyx0;
    lia.
  Qed.

  (** Twin lemma for the unique-incomparable-pair case (edge count 9): every
      other element is comparable to both (else a second incomparable pair,
      contradicting [two_incomp_le_8]), so [twin_rk_eq_gen] applies. *)
  Lemma twin_rk_eq :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall w : B, w = a \/ w = b \/ w = c \/ w = d \/ w = e) ->
      edge_count_5 R2 a b c d e = 9 ->
      forall x y, @Incomparable B R2 x y ->
        rk a b c d e x = rk a b c d e y.
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec x y Hxy.
    apply (twin_rk_eq_gen a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
             Hcov x y Hxy).
    - intros z Hzx Hzy. apply NNPP. intro Hnc.
      assert (Hxz : @Incomparable B R2 x z)
        by (intros [H|H]; apply Hnc; [right|left]; exact H).
      pose proof (two_incomp_le_8 a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
                    Hcov x y z Hxy Hxz (fun E => Hzy (eq_sym E))) as H8. lia.
    - intros z Hzx Hzy. apply NNPP. intro Hnc.
      assert (Hyx : @Incomparable B R2 y x)
        by (intros [H|H]; apply Hxy; [right|left]; exact H).
      assert (Hyz : @Incomparable B R2 y z)
        by (intros [H|H]; apply Hnc; [right|left]; exact H).
      pose proof (two_incomp_le_8 a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
                    Hcov y x z Hyx Hyz (fun E => Hzx (eq_sym E))) as H8. lia.
  Qed.

  (** When the edge count is 8 there is a SECOND incomparable pair, distinct
      (as an unordered pair) from any given one [{u,v}].  If [{u,v}] were the
      only incomparable pair, the other nine pairs would each contribute 1,
      forcing the count to 9. *)
  Lemma second_incomp_of_8 :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall w : B, w = a \/ w = b \/ w = c \/ w = d \/ w = e) ->
      edge_count_5 R2 a b c d e = 8 ->
      forall u v, @Incomparable B R2 u v ->
        exists x y, @Incomparable B R2 x y
                    /\ ~ (x = u /\ y = v) /\ ~ (x = v /\ y = u).
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec u v Huv.
    apply NNPP. intro Hno.
    assert (Hcomp : forall p q, ~ (p = u /\ q = v) -> ~ (p = v /\ q = u) ->
                    R2 p q \/ R2 q p).
    { intros p q H1 H2. apply NNPP. intro Hnc.
      apply Hno. exists p, q. split; [exact Hnc | split; [exact H1 | exact H2]]. }
    assert (Huv0a : strict_indicator R2 u v = 0)
      by (apply strict_indicator_eq_0; intros [HR _]; apply Huv; left; exact HR).
    assert (Huv0b : strict_indicator R2 v u = 0)
      by (apply strict_indicator_eq_0; intros [HR _]; apply Huv; right; exact HR).
    destruct (Hcov u) as [Eu|[Eu|[Eu|[Eu|Eu]]]];
    destruct (Hcov v) as [Ev|[Ev|[Ev|[Ev|Ev]]]];
    subst u v;
    first
      [ apply Huv; left; apply poset_refl
      | ( try pose proof (comparable_indicator_sum a b Hab (Hcomp a b ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum a c Hac (Hcomp a c ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum a d Had (Hcomp a d ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum a e Hae (Hcomp a e ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum b c Hbc (Hcomp b c ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum b d Hbd (Hcomp b d ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum b e Hbe (Hcomp b e ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum c d Hcd (Hcomp c d ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum c e Hce (Hcomp c e ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          try pose proof (comparable_indicator_sum d e Hde (Hcomp d e ltac:(intros [E1 E2]; congruence) ltac:(intros [E1 E2]; congruence)));
          unfold edge_count_5 in Hec; lia ) ].
  Qed.

End EdgeCountIncomp.
