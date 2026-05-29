(** edge_count_5 = 9 case for the n=5 dispatcher.

    A 5-element poset with exactly 9 comparable pairs has exactly one
    incomparable pair {u,v}; u and v are "twins" (identical relations to the
    other three elements), so the down-count ranking [rk] gives them equal
    rank.  Two linear extensions [rk1 = 6*rk + lab] and [rk2 = 6*rk + (4-lab)]
    (lab a tie-break by carrier label) order every comparable pair the same
    way and the twin pair oppositely, so their intersection is exactly R2 and
    {L1,L2} is a 2-realizer (via [n5_two_realizer_framework]).

    Uses the reusable rank machinery in [EdgeCountIncomp]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount EdgeCountIncomp.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount9.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma n5_edge_count_9_two_realizer :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 9 ->
      exists r : Ensemble (B -> B -> Prop),
        IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    set (lab := fun x : B =>
      if excluded_middle_informative (x = a) then 0
      else if excluded_middle_informative (x = b) then 1
      else if excluded_middle_informative (x = c) then 2
      else if excluded_middle_informative (x = d) then 3
      else 4).
    set (rk1 := fun x : B => 6 * rk R2 a b c d e x + lab x).
    set (rk2 := fun x : B => 6 * rk R2 a b c d e x + (4 - lab x)).
    (* Label values. *)
    assert (La : lab a = 0).
    { unfold lab. destruct (excluded_middle_informative (a = a)) as [|N];
        [reflexivity | exfalso; apply N; reflexivity]. }
    assert (Lb : lab b = 1).
    { unfold lab.
      destruct (excluded_middle_informative (b = a)) as [E|];
        [exfalso; apply Hab; symmetry; exact E|].
      destruct (excluded_middle_informative (b = b)) as [|N];
        [reflexivity | exfalso; apply N; reflexivity]. }
    assert (Lc : lab c = 2).
    { unfold lab.
      destruct (excluded_middle_informative (c = a)) as [E|];
        [exfalso; apply Hac; symmetry; exact E|].
      destruct (excluded_middle_informative (c = b)) as [E|];
        [exfalso; apply Hbc; symmetry; exact E|].
      destruct (excluded_middle_informative (c = c)) as [|N];
        [reflexivity | exfalso; apply N; reflexivity]. }
    assert (Ld : lab d = 3).
    { unfold lab.
      destruct (excluded_middle_informative (d = a)) as [E|];
        [exfalso; apply Had; symmetry; exact E|].
      destruct (excluded_middle_informative (d = b)) as [E|];
        [exfalso; apply Hbd; symmetry; exact E|].
      destruct (excluded_middle_informative (d = c)) as [E|];
        [exfalso; apply Hcd; symmetry; exact E|].
      destruct (excluded_middle_informative (d = d)) as [|N];
        [reflexivity | exfalso; apply N; reflexivity]. }
    assert (Le : lab e = 4).
    { unfold lab.
      destruct (excluded_middle_informative (e = a)) as [E|];
        [exfalso; apply Hae; symmetry; exact E|].
      destruct (excluded_middle_informative (e = b)) as [E|];
        [exfalso; apply Hbe; symmetry; exact E|].
      destruct (excluded_middle_informative (e = c)) as [E|];
        [exfalso; apply Hce; symmetry; exact E|].
      destruct (excluded_middle_informative (e = d)) as [E|];
        [exfalso; apply Hde; symmetry; exact E|].
      reflexivity. }
    assert (Hlab_le : forall x, lab x <= 4).
    { intro x. unfold lab.
      repeat destruct (excluded_middle_informative _); lia. }
    assert (Hlab_inj : forall x y,
              (x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
              (y = a \/ y = b \/ y = c \/ y = d \/ y = e) ->
              lab x = lab y -> x = y).
    { intros x y Hx Hy Hl.
      destruct Hx as [|[|[|[|]]]]; destruct Hy as [|[|[|[|]]]]; subst;
        rewrite ?La, ?Lb, ?Lc, ?Ld, ?Le in Hl;
        first [ reflexivity | discriminate ]. }
    (* Extract the unique incomparable pair and its equal rank. *)
    assert (Hle9 : edge_count_5 R2 a b c d e <= 9) by lia.
    destruct (incomp_carrier_exists R2 a b c d e
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hle9)
      as [u [v Huv]].
    assert (Huv_ne : u <> v)
      by (intro E; subst; apply Huv; left; apply poset_refl).
    assert (Hruv : rk R2 a b c d e u = rk R2 a b c d e v)
      by (apply (twin_rk_eq R2 a b c d e
                   Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec u v Huv)).
    (* Apply the rank-based realizer framework. *)
    apply (n5_two_realizer_framework R2 a b c d e
             Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov rk1 rk2).
    (* 20 pairwise-distinctness goals (rk1 then rk2). *)
    all: try (unfold rk1, rk2;
              rewrite ?La, ?Lb, ?Lc, ?Ld, ?Le; intro Heq; lia).
    (* rk1 monotone. *)
    - intros x y HR. unfold rk1.
      destruct (classic (x = y)) as [E|Hne]; [subst; lia|].
      pose proof (rk_strict_mono R2 a b c d e Hcov x y HR Hne).
      pose proof (Hlab_le x); pose proof (Hlab_le y); lia.
    (* rk2 monotone. *)
    - intros x y HR. unfold rk2.
      destruct (classic (x = y)) as [E|Hne]; [subst; lia|].
      pose proof (rk_strict_mono R2 a b c d e Hcov x y HR Hne).
      pose proof (Hlab_le x); pose proof (Hlab_le y); lia.
    (* Intersection: rk1 x<=rk1 y -> rk2 x<=rk2 y -> R2 x y. *)
    - intros x y H1 H2. unfold rk1, rk2 in H1, H2.
      pose proof (Hlab_le x); pose proof (Hlab_le y).
      destruct (Nat.eq_dec (rk R2 a b c d e x) (rk R2 a b c d e y))
        as [Heq|Hrkne].
      + (* equal rank -> equal label -> equal element. *)
        assert (Hlxy : lab x = lab y) by lia.
        rewrite (Hlab_inj x y (Hcov x) (Hcov y) Hlxy). apply poset_refl.
      + (* strict rank -> must be the comparable direction. *)
        assert (Hlt : rk R2 a b c d e x < rk R2 a b c d e y) by lia.
        apply NNPP. intro HnR.
        destruct (classic (R2 y x)) as [Hyx|Hnyx].
        * destruct (classic (x = y)) as [E|Hne].
          { subst. apply HnR. apply poset_refl. }
          { pose proof (rk_strict_mono R2 a b c d e Hcov y x Hyx
                          (fun E => Hne (eq_sym E))). lia. }
        * assert (Hinc : @Incomparable B R2 x y)
            by (intros [Hor|Hor]; [apply HnR; exact Hor | apply Hnyx; exact Hor]).
          pose proof (twin_rk_eq R2 a b c d e
                        Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                        x y Hinc). lia.
    (* Distinguishing pair: the twins u, v. *)
    - assert (Hlab_uv : lab u <> lab v)
        by (intro E; apply Huv_ne;
            apply (Hlab_inj u v (Hcov u) (Hcov v) E)).
      pose proof (Hlab_le u); pose proof (Hlab_le v).
      destruct (lt_eq_lt_dec (lab u) (lab v)) as [[Hlt|Heq]|Hgt].
      + exists u, v. unfold rk1, rk2. split; lia.
      + exfalso. apply Hlab_uv; exact Heq.
      + exists v, u. unfold rk1, rk2. split; lia.
  Qed.

End EdgeCount9.
