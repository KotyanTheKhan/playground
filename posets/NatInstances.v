(* Nat-related lattice and semilattice instances *)
Require Import Nat.
From Stdlib Require Import PeanoNat.
Require Import PosetClasses.


Definition nat_meet (x y : nat) := Nat.min x y.
Definition nat_join (x y : nat) := Nat.max x y.

(* Use the standard library's properties *)
Lemma le_antisymm : forall x y, x <= y -> y <= x -> x = y.
Proof.
  intros x y. generalize dependent x.
  induction y; intros x H1 H2.
  - inversion H1. reflexivity.
  - destruct x.
    + inversion H2.
    + apply le_S_n in H1. apply le_S_n in H2.
      f_equal. apply IHy; assumption.
Qed.

Lemma le_trans_helper : forall x y z, x <= y -> y <= z -> x <= z.
Proof.
  intros x y z H1 H2.
  induction H1.
  - assumption.
  - apply IHle. clear IHle.
    (* From S m <= z, derive m <= z *)
    induction H2.
    + apply le_S. apply le_n.
    + apply le_S. assumption.
Qed.

Instance nat_poset : IsPoset nat le.
Proof.
  constructor.
  - (* reflexivity *) intros x. apply le_n.
  - (* antisymmetry *) intros x y H1 H2. apply le_antisymm; assumption.
  - (* transitivity *) intros x y z H1 H2. 
    apply le_trans_helper with y; assumption.
Qed.

Lemma nat_min_properties : forall x y z,
  Nat.min (Nat.min x y) z = Nat.min x (Nat.min y z) /\
  Nat.min x y = Nat.min y x /\
  Nat.min x x = x.
Proof.
  intros. split; [| split].
  - symmetry. apply Nat.min_assoc.
  - apply Nat.min_comm.
  - apply Nat.min_id.
Qed.

Lemma nat_max_properties : forall x y z,
  Nat.max (Nat.max x y) z = Nat.max x (Nat.max y z) /\
  Nat.max x y = Nat.max y x /\
  Nat.max x x = x.
Proof.
  intros. split; [| split].
  - symmetry. apply Nat.max_assoc.
  - apply Nat.max_comm.
  - apply Nat.max_id.
Qed.

Lemma nat_lattice_properties : forall x y,
  Nat.min x (Nat.max x y) = x /\
  Nat.max x (Nat.min x y) = x.
Proof.
  intros. split.
  - apply Nat.min_l. apply Nat.le_max_l.
  - apply Nat.max_l. apply Nat.le_min_l.
Qed.

Lemma nat_distrib_properties : forall x y z,
  Nat.min x (Nat.max y z) = Nat.max (Nat.min x y) (Nat.min x z) /\
  Nat.max x (Nat.min y z) = Nat.min (Nat.max x y) (Nat.max x z).
Proof.
  intros. split.
  - apply Nat.min_max_distr.
  - apply Nat.max_min_distr.
Qed.

Instance nat_meet_semilattice : IsMeetSemilattice nat nat_meet.
Proof.
  constructor.
  - (* associativity *) intros x y z. unfold nat_meet. apply (nat_min_properties x y z).
  - (* commutativity *) intros x y. unfold nat_meet. apply (nat_min_properties x y 0).
  - (* idempotency *) intro x. unfold nat_meet. apply (nat_min_properties x x 0).
Qed.

Instance nat_join_semilattice : IsJoinSemilattice nat nat_join.
Proof.
  constructor.
  - (* associativity *) intros x y z. unfold nat_join. apply (nat_max_properties x y z).
  - (* commutativity *) intros x y. unfold nat_join. apply (nat_max_properties x y 0).
  - (* idempotency *) intro x. unfold nat_join. apply (nat_max_properties x x 0).
Qed.

Instance nat_lattice_semi : IsLattice nat nat_meet nat_join.
Proof.
  constructor.
  - (* absorption: meet x (join x y) = x *)
    intros x y. unfold nat_meet, nat_join. apply (nat_lattice_properties x y).
  - (* absorption: join x (meet x y) = x *)
    intros x y. unfold nat_meet, nat_join. apply (nat_lattice_properties x y).
Qed.

Instance nat_distrib_semi : IsDistributiveLattice nat nat_meet nat_join.
Proof.
  constructor.
  - (* distributivity: meet x (join y z) = join (meet x y) (meet x z) *)
    intros x y z. unfold nat_meet, nat_join. apply (nat_distrib_properties x y z).
  - (* distributivity: join x (meet y z) = meet (join x y) (join x z) *)
    intros x y z. unfold nat_meet, nat_join. apply (nat_distrib_properties x y z).
Qed.
