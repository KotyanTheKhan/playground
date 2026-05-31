(* Rank — structural acyclicity of the execution order.

   A RankedProgram bundles a Program with a rank function on raw (p,i)
   pairs that strictly increases across every direct edge.  Then any
   non-trivial hb-step strictly increases rank, so hb is antisymmetric
   with no separate acyclicity hypothesis. *)

From Stdlib Require Import List Arith Lia Relation_Operators.
From Execution Require Import Op Event Edges.

Record RankedProgram := {
  rp_prog :> Program;
  rp_rank : nat * nat -> nat;
  (* strictly increases across every direct edge *)
  rp_rank_mono :
    forall (a b : Event rp_prog), edge rp_prog a b ->
      rp_rank (proj1_sig a) < rp_rank (proj1_sig b)
}.

(* The key disjunction: every hb-step is either trivial or strictly
   rank-increasing. *)
Lemma hb_eq_or_rank_lt :
  forall (R : RankedProgram) (a b : Event R),
    hb R a b -> a = b \/ rp_rank R (proj1_sig a) < rp_rank R (proj1_sig b).
Proof.
  intros R a b H.
  unfold hb in H.
  induction H as [x y Hedge | x | x y z Hxy IHxy Hyz IHyz].
  - (* rt_step: edge R x y *)
    right. apply rp_rank_mono. exact Hedge.
  - (* rt_refl: x = x *)
    left. reflexivity.
  - (* rt_trans through y *)
    destruct IHxy as [Heq1 | Hlt1]; destruct IHyz as [Heq2 | Hlt2].
    + left. subst. reflexivity.
    + right. subst. exact Hlt2.
    + right. subst. exact Hlt1.
    + right. lia.
Qed.

(* rank is monotone (non-strict) along hb *)
Lemma rank_hb_le :
  forall (R : RankedProgram) (a b : Event R),
    hb R a b -> rp_rank R (proj1_sig a) <= rp_rank R (proj1_sig b).
Proof.
  intros R a b H.
  destruct (hb_eq_or_rank_lt R a b H) as [Heq | Hlt].
  - subst. apply Nat.le_refl.
  - apply Nat.lt_le_incl. exact Hlt.
Qed.

(* hb that is not equality strictly increases rank *)
Lemma hb_neq_rank_lt :
  forall (R : RankedProgram) (a b : Event R),
    hb R a b -> a <> b -> rp_rank R (proj1_sig a) < rp_rank R (proj1_sig b).
Proof.
  intros R a b Hhb Hneq.
  destruct (hb_eq_or_rank_lt R a b Hhb) as [Heq | Hlt].
  - exfalso. apply Hneq. exact Heq.
  - exact Hlt.
Qed.

(* antisymmetry, the payoff *)
Lemma hb_antisym :
  forall (R : RankedProgram) (a b : Event R),
    hb R a b -> hb R b a -> a = b.
Proof.
  intros R a b Hab Hba.
  destruct (hb_eq_or_rank_lt R a b Hab) as [Heq | Hlt].
  - exact Heq.
  - destruct (hb_eq_or_rank_lt R b a Hba) as [Heq2 | Hlt2].
    + symmetry. exact Heq2.
    + exfalso. lia.
Qed.
