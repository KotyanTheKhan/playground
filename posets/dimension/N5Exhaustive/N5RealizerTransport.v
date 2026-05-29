(** Bridge for the uniform Fin.t 5 route to the n=5 two-realizer.

    [two_realizer_from_fin_ranks] reduces "the abstract 5-element poset [R2]
    has a 2-realizer" to "there are two rank functions [rho1], [rho2] on
    [Fin.t 5] that 2-realize the boolean matrix [R2_matrix]".  This lets each
    edge-count case be discharged by a CONCRETE, decidable construction on
    [Fin.t 5] (where the 10 pairs are literal f0..f4), feeding the abstract
    [n5_two_realizer_framework] via the [N5Transport] bijection. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import N5Reflect N5Transport.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section N5RealizerTransport.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma two_realizer_from_fin_ranks :
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      forall rho1 rho2 : Fin.t 5 -> nat,
        (forall i j, rho1 i = rho1 j -> i = j) ->
        (forall i j, rho2 i = rho2 j -> i = j) ->
        (forall i j, R2_matrix R2 a b c d e i j = true -> rho1 i <= rho1 j) ->
        (forall i j, R2_matrix R2 a b c d e i j = true -> rho2 i <= rho2 j) ->
        (forall i j, rho1 i <= rho1 j -> rho2 i <= rho2 j ->
                     R2_matrix R2 a b c d e i j = true) ->
        (exists i j, rho1 i <= rho1 j /\ rho2 j < rho2 i) ->
        exists r : Ensemble (B -> B -> Prop),
          IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
           rho1 rho2 Hr1inj Hr2inj Hr1mono Hr2mono Hinter Hdist.
    (* to_fin sends the carrier to f0..f4. *)
    assert (Ta : to_fin a b c d a = f0).
    { unfold to_fin. destruct (excluded_middle_informative (a = a)) as [_|N];
        [reflexivity | exfalso; apply N; reflexivity]. }
    assert (Tb : to_fin a b c d b = f1).
    { unfold to_fin.
      destruct (excluded_middle_informative (b = a)) as [E|_];
        [exfalso; apply Hab; symmetry; exact E|].
      destruct (excluded_middle_informative (b = b)) as [_|N];
        [reflexivity | exfalso; apply N; reflexivity]. }
    assert (Tc : to_fin a b c d c = f2).
    { unfold to_fin.
      destruct (excluded_middle_informative (c = a)) as [E|_];
        [exfalso; apply Hac; symmetry; exact E|].
      destruct (excluded_middle_informative (c = b)) as [E|_];
        [exfalso; apply Hbc; symmetry; exact E|].
      destruct (excluded_middle_informative (c = c)) as [_|N];
        [reflexivity | exfalso; apply N; reflexivity]. }
    assert (Td : to_fin a b c d d = f3).
    { unfold to_fin.
      destruct (excluded_middle_informative (d = a)) as [E|_];
        [exfalso; apply Had; symmetry; exact E|].
      destruct (excluded_middle_informative (d = b)) as [E|_];
        [exfalso; apply Hbd; symmetry; exact E|].
      destruct (excluded_middle_informative (d = c)) as [E|_];
        [exfalso; apply Hcd; symmetry; exact E|].
      destruct (excluded_middle_informative (d = d)) as [_|N];
        [reflexivity | exfalso; apply N; reflexivity]. }
    assert (Te : to_fin a b c d e = f4).
    { unfold to_fin.
      destruct (excluded_middle_informative (e = a)) as [E|_];
        [exfalso; apply Hae; symmetry; exact E|].
      destruct (excluded_middle_informative (e = b)) as [E|_];
        [exfalso; apply Hbe; symmetry; exact E|].
      destruct (excluded_middle_informative (e = c)) as [E|_];
        [exfalso; apply Hce; symmetry; exact E|].
      destruct (excluded_middle_informative (e = d)) as [E|_];
        [exfalso; apply Hde; symmetry; exact E|].
      reflexivity. }
    (* Transport: R2 x y <-> R2_matrix on the images under to_fin. *)
    assert (HT : forall x y, R2 x y <->
                 R2_matrix R2 a b c d e (to_fin a b c d x) (to_fin a b c d y) = true).
    { intros x y. rewrite R2_matrix_true_iff.
      rewrite (from_to_fin a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov x).
      rewrite (from_to_fin a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov y).
      reflexivity. }
    apply (n5_two_realizer_framework R2 a b c d e
             Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
             (fun x => rho1 (to_fin a b c d x))
             (fun x => rho2 (to_fin a b c d x))).
    all: cbv beta.
    all: try (rewrite ?Ta, ?Tb, ?Tc, ?Td, ?Te; intro Heq;
              first [apply Hr1inj in Heq | apply Hr2inj in Heq]; discriminate).
    - intros x y HR. apply Hr1mono. apply (proj1 (HT x y)). exact HR.
    - intros x y HR. apply Hr2mono. apply (proj1 (HT x y)). exact HR.
    - intros x y H1 H2. apply (proj2 (HT x y)). apply Hinter; assumption.
    - destruct Hdist as [i [j [Hij1 Hij2]]].
      exists (from_fin a b c d e i), (from_fin a b c d e j).
      rewrite (to_from_fin a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov i).
      rewrite (to_from_fin a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov j).
      split; assumption.
  Qed.

End N5RealizerTransport.
