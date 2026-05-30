(** * Hiraguchi's bound, directly — dim(P) ≤ ⌊n/2⌋ for n ≥ 4.

    The sound proof, independent of the OPEN Removable Pair Conjecture
    (cf. [RemovablePairs.v]'s [hiraguchi_bound], which routes through it).

    Route (Trotter survey, Thm 5.2):
      dim ≤ width                         [dimension_le_width, WidthBound.v]
      dim ≤ max{2, |P − A|}  (A max ac)    [antichain_complement_dim_bound]
      combine via w + (n−w) = n            [hiraguchi_combine]
    using [width_exists] for the maximum antichain A (|A| = w).

    Remaining admit on this path: only [small_complement_le_2] (Trotter's
    Lemma 3 base case), inside [antichain_complement_dim_bound]. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs Theorems WidthBound AntichainDimBound
                              AntichainComplement WidthExists.

Theorem hiraguchi_bound_direct :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R} (n d : nat),
    cardinal A (Full_set A) n ->
    n >= 4 ->
    PosetDimension R d ->
    d <= n / 2.
Proof.
  intros A R HR n d Hcard Hn4 Hdim.
  (* the carrier is inhabited (n >= 4 > 0) *)
  assert (Hinh : Inhabited A (Full_set A)).
  { destruct (card_inhabited A (Full_set A) n Hcard ltac:(lia)) as [a Ha].
    exists a; exact Ha. }
  (* a maximum antichain of size w = width exists *)
  destruct (width_exists R n Hcard Hinh) as [w [W]].
  (* (I)  dim ≤ width *)
  assert (Hdw : d <= w) by exact (@dimension_le_width A R HR n d w Hcard Hdim W).
  (* unpack the maximum antichain [la] *)
  destruct W as [la Hla].
  destruct Hla as [Hla_anti Hla_incl Hla_card Hla_max].
  assert (Hwn : w <= n)
    by exact (incl_card_le A la (Full_set A) w n Hla_card Hcard Hla_incl).
  (* |P − la| = n − w *)
  assert (Hcompl : cardinal A (Setminus A (Full_set A) la) (n - w))
    by exact (cardinal_setminus A la w Hla_card (Full_set A) n Hcard Hla_incl).
  assert (Hfin : Finite A (Full_set A)) by exact (cardinal_finite A (Full_set A) n Hcard).
  (* (II)  dim ≤ max{2, n − w} *)
  assert (Hdm : d <= Nat.max 2 (n - w))
    by exact (@antichain_complement_dim_bound (n - w) A R HR la d Hfin Hla_anti Hdim Hcompl).
  (* combine *)
  exact (hiraguchi_combine d n w (n - w) Hn4 ltac:(lia) Hdw Hdm).
Qed.

(** Print Assumptions hiraguchi_bound_direct.  (Expected: standard classical
    axioms + [small_complement_le_2] + [subtype_remove_data is now Qed] ...
    i.e. only the base case admit remains on this path; NO dependence on the
    Removable Pair Conjecture.) *)
