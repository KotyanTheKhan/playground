(** Reusable cover lemma for the count-8 (and 5/6/7) handlers: five
    pairwise-distinct elements of a cardinal-5 carrier exhaust it.  Proved
    once via [carrier_5_destructure] + a 3-element pigeonhole, so each
    per-pattern handler can [apply n5_two_realizer_framework] over its own
    five shape elements. *)

From Stdlib Require Import Classical.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Lemma five_distinct_cover : forall {B : Type} (p q r s t : B),
  cardinal B (Full_set B) 5 ->
  p <> q -> p <> r -> p <> s -> p <> t ->
  q <> r -> q <> s -> q <> t ->
  r <> s -> r <> t -> s <> t ->
  forall x, x = p \/ x = q \/ x = r \/ x = s \/ x = t.
Proof.
  intros B p q r s t Hcard Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst.
  destruct (@carrier_5_destructure B p q Hcard Hpq)
    as [r0 [s0 [t0 [Hpr0 [Hps0 [Hpt0 [Hqr0 [Hqs0 [Hqt0
        [Hr0s0 [Hr0t0 [Hs0t0 Hcov5]]]]]]]]]]]].
  assert (Hr_in : r = r0 \/ r = s0 \/ r = t0).
  { destruct (Hcov5 r) as [H|[H|[H|[H|H]]]].
    - contradiction Hpr; symmetry; exact H.
    - contradiction Hqr; symmetry; exact H.
    - left; exact H. - right; left; exact H. - right; right; exact H. }
  assert (Hs_in : s = r0 \/ s = s0 \/ s = t0).
  { destruct (Hcov5 s) as [H|[H|[H|[H|H]]]].
    - contradiction Hps; symmetry; exact H.
    - contradiction Hqs; symmetry; exact H.
    - left; exact H. - right; left; exact H. - right; right; exact H. }
  assert (Ht_in : t = r0 \/ t = s0 \/ t = t0).
  { destruct (Hcov5 t) as [H|[H|[H|[H|H]]]].
    - contradiction Hpt; symmetry; exact H.
    - contradiction Hqt; symmetry; exact H.
    - left; exact H. - right; left; exact H. - right; right; exact H. }
  assert (Hr0_in : r0 = r \/ r0 = s \/ r0 = t).
  { destruct Hr_in as [Hr|[Hr|Hr]];
    destruct Hs_in as [Hs|[Hs|Hs]];
    destruct Ht_in as [Ht|[Ht|Ht]];
    try (left; symmetry; exact Hr);
    try (right; left; symmetry; exact Hs);
    try (right; right; symmetry; exact Ht);
    try (exfalso; apply Hrs; rewrite Hr, Hs; reflexivity);
    try (exfalso; apply Hrt; rewrite Hr, Ht; reflexivity);
    try (exfalso; apply Hst; rewrite Hs, Ht; reflexivity). }
  assert (Hs0_in : s0 = r \/ s0 = s \/ s0 = t).
  { destruct Hr_in as [Hr|[Hr|Hr]];
    destruct Hs_in as [Hs|[Hs|Hs]];
    destruct Ht_in as [Ht|[Ht|Ht]];
    try (left; symmetry; exact Hr);
    try (right; left; symmetry; exact Hs);
    try (right; right; symmetry; exact Ht);
    try (exfalso; apply Hrs; rewrite Hr, Hs; reflexivity);
    try (exfalso; apply Hrt; rewrite Hr, Ht; reflexivity);
    try (exfalso; apply Hst; rewrite Hs, Ht; reflexivity). }
  assert (Ht0_in : t0 = r \/ t0 = s \/ t0 = t).
  { destruct Hr_in as [Hr|[Hr|Hr]];
    destruct Hs_in as [Hs|[Hs|Hs]];
    destruct Ht_in as [Ht|[Ht|Ht]];
    try (left; symmetry; exact Hr);
    try (right; left; symmetry; exact Hs);
    try (right; right; symmetry; exact Ht);
    try (exfalso; apply Hrs; rewrite Hr, Hs; reflexivity);
    try (exfalso; apply Hrt; rewrite Hr, Ht; reflexivity);
    try (exfalso; apply Hst; rewrite Hs, Ht; reflexivity). }
  intro x. destruct (Hcov5 x) as [H|[H|[H|[H|H]]]].
  - left; exact H.
  - right; left; exact H.
  - subst x. destruct Hr0_in as [E|[E|E]];
      [ right; right; left | right; right; right; left
      | right; right; right; right ]; exact E.
  - subst x. destruct Hs0_in as [E|[E|E]];
      [ right; right; left | right; right; right; left
      | right; right; right; right ]; exact E.
  - subst x. destruct Ht0_in as [E|[E|E]];
      [ right; right; left | right; right; right; left
      | right; right; right; right ]; exact E.
Qed.
