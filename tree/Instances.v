(* Poset and lattice instances for trees *)
Require Import Posets.PosetClasses.
Require Import Posets.LatticeClasses.
Require Import Tree.Structure.
Require Import Tree.Operations.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

(* ========== Helper Lemmas ========== *)

Lemma tree_head_val_eq : forall t1 t2, t1 = t2 -> tree_head_val t1 = tree_head_val t2.
Proof.
  intros. subst. reflexivity.
Qed.

(* Use standard library lemmas for min/max:
   - Nat.min_comm, Nat.min_assoc, Nat.min_id
   - Nat.max_comm, Nat.max_assoc, Nat.max_id
*)

(* ========== Poset Instance ========== *)

Instance tree_poset : IsPoset Tree tree_le.
Proof.
  constructor.
  - (* reflexivity *)
    intro x. induction x; simpl; auto.
  - (* antisymmetry *)
    intros x y. generalize dependent y.
    induction x; intros y H1 H2; destruct y; simpl in *; auto; try contradiction.
    * f_equal. lia.
    * destruct H1, H2. f_equal; auto.
  - (* transitivity *)
    intros x y z Hxy Hyz.
    generalize dependent z. generalize dependent y.
    induction x; intros y Hxy z Hyz; destruct y; destruct z; simpl in *; auto; try contradiction; try lia.
    destruct Hxy, Hyz. split; eauto.
Qed.

(* ========== Meet Semilattice Instance ========== *)

Instance tree_meet_semilattice : IsMeetSemilattice Tree tree_meet.
Proof.
  constructor.
  - (* meet_assoc *)
    intros x y z. revert y z.
    induction x as [nx|lx IHlx rx IHrx]; intros y z.
    { (* x = Leaf nx *)
      destruct y as [ny|ly ry].
      { (* y = Leaf ny *)
        destruct z as [nz|lz rz].
        { (* z = Leaf nz *)
          simpl. rewrite Nat.min_assoc. reflexivity.
        }
        { (* z = Node lz rz *)
          simpl. reflexivity.
        }
      }
      { (* y = Node ly ry *)
        destruct z; simpl; reflexivity.
      }
    }
    { (* x = Node lx rx *)
      destruct y; destruct z; simpl; try reflexivity.
      f_equal.
      - apply IHlx.
      - apply IHrx.
    }
  - (* meet_comm *)
    intros x y. revert y.
    induction x as [nx|lx IHlx rx IHrx]; intros y; destruct y as [ny|ly ry]; simpl; try reflexivity.
    + rewrite Nat.min_comm. reflexivity.
    + f_equal; auto.
  - (* meet_idem *)
    intros x.
    induction x as [nx|lx IHlx rx IHrx]; simpl; try reflexivity.
    + rewrite Nat.min_id. reflexivity.
    + f_equal; auto.
Qed.

(* ========== Join Semilattice Instance ========== *)

Instance tree_join_semilattice : IsJoinSemilattice Tree tree_join.
Proof.
  constructor.
  - (* join_assoc *)
    intros x y z. revert y z.
    induction x as [nx|lx IHlx rx IHrx]; intros y z.
    { (* x = Leaf nx *)
      destruct y as [ny|ly ry].
      { (* y = Leaf ny *)
        destruct z as [nz|lz rz].
        { (* z = Leaf nz *)
          simpl. rewrite Nat.max_assoc. reflexivity.
        }
        { (* z = Node lz rz *)
          simpl. reflexivity.
        }
      }
      { (* y = Node ly ry *)
        destruct z; simpl; reflexivity.
      }
    }
    { (* x = Node lx rx *)
      destruct y; destruct z; simpl; try reflexivity.
      f_equal.
      - apply IHlx.
      - apply IHrx.
    }
  - (* join_comm *)
    intros x y. revert y.
    induction x as [nx|lx IHlx rx IHrx]; intros y; destruct y as [ny|ly ry]; simpl; try reflexivity.
    + rewrite Nat.max_comm. reflexivity.
    + f_equal; auto.
  - (* join_idem *)
    intros x.
    induction x as [nx|lx IHlx rx IHrx]; simpl; try reflexivity.
    + rewrite Nat.max_id. reflexivity.
    + f_equal; auto.
Qed.

(* ========== Lattice Instance ========== *)

Instance tree_lattice : IsLattice Tree tree_meet tree_join.
Proof.
  constructor.
  - (* absorption_meet: x ⊓ (x ⊔ y) = x *)
    intros x y. revert y.
    induction x as [nx|lx IHlx rx IHrx]; intros y.
    { (* x = Leaf nx *)
      destruct y as [ny|ly ry]; simpl.
      + replace (Nat.min nx (Nat.max nx ny)) with nx by lia. reflexivity.
      + reflexivity.
    }
    { (* x = Node lx rx *)
      destruct y as [ny|ly ry]; simpl.
      + repeat rewrite meet_idem. reflexivity.
      + f_equal.
        * apply IHlx.
        * apply IHrx.
    }
  - (* absorption_join: x ⊔ (x ⊓ y) = x *)
    intros x y. revert y.
    induction x as [nx|lx IHlx rx IHrx]; intros y.
    { (* x = Leaf nx *)
      destruct y as [ny|ly ry]; simpl.
      + replace (Nat.max nx (Nat.min nx ny)) with nx by lia. reflexivity.
      + replace (Nat.max nx nx) with nx by lia. reflexivity.
    }
    { (* x = Node lx rx *)
      destruct y as [ny|ly ry]; simpl.
      + reflexivity.
      + f_equal.
        * apply IHlx.
        * apply IHrx.
    }
Qed.

(* ========== Distributive Lattice Instance ========== *)

Instance tree_distrib_lattice : IsDistributiveLattice Tree tree_meet tree_join.
Proof.
  constructor.
  - (* distrib_meet: x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) *)
    intros x y z. revert y z.
    induction x as [nx|lx IHlx rx IHrx]; intros y z.
    { (* x = Leaf nx *)
      destruct y as [ny|ly ry]; destruct z as [nz|lz rz]; simpl.
      + rewrite Nat.min_max_distr. reflexivity.
      + replace (Nat.max (Nat.min nx ny) nx) with nx by lia. reflexivity.
      + replace (Nat.max nx (Nat.min nx nz)) with nx by lia. reflexivity.
      + replace (Nat.max nx nx) with nx by lia. reflexivity.
    }
    { (* x = Node lx rx *)
      destruct y as [ny|ly ry]; destruct z as [nz|lz rz]; simpl.
      + repeat rewrite join_idem. reflexivity.
      + reflexivity.
      + reflexivity.
      + f_equal.
        * apply IHlx.
        * apply IHrx.
    }
  - (* distrib_join: x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) *)
    intros x y z. revert y z.
    induction x as [nx|lx IHlx rx IHrx]; intros y z.
    { (* x = Leaf nx *)
      destruct y as [ny|ly ry]; destruct z as [nz|lz rz]; simpl.
      + rewrite Nat.max_min_distr. reflexivity.
      + replace (Nat.max (Nat.min nx ny) nx) with nx by lia. reflexivity.
      + replace (Nat.max nx (Nat.min nx nz)) with nx by lia. reflexivity.
      + replace (Nat.max nx nx) with nx by lia. reflexivity.
    }
    { (* x = Node lx rx *)
      destruct y as [ny|ly ry]; destruct z as [nz|lz rz]; simpl.
      + repeat rewrite meet_idem. reflexivity.
      + repeat rewrite absorption_meet. reflexivity.
      + f_equal; symmetry; rewrite meet_comm; apply absorption_meet.
      + f_equal.
        * apply IHlx.
        * apply IHrx.
    }
Qed.
