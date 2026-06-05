From Stdlib Require Import Fin Arith Lia.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Execution Require Import DimTwoGeneric.
From ExecClock Require Import FinPosetBool WitnessData.

(* ===================================================================== *)
(*  Poset laws for the repair relation (19 events, N=4,                  *)
(*  syncs=[(0,1),(2,3),(0,3),(0,2),(1,3)])                               *)
(* ===================================================================== *)

Lemma Rb_repair_refl : forall x, Rb_repair x x = true.
Proof.
  apply forallb_finT_spec. vm_compute. reflexivity.
Qed.

Lemma Rb_repair_antisym : forall x y,
  Rb_repair x y = true -> Rb_repair y x = true -> x = y.
Proof.
  intros x y Hxy Hyx.
  assert (Hdec : forall x y : Fin.t 19,
    implb (Rb_repair x y && Rb_repair y x) (Fin.eqb x y) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  apply Fin.eqb_eq.
  specialize (Hdec x y). rewrite Hxy, Hyx in Hdec. exact Hdec.
Qed.

Lemma Rb_repair_trans : forall x y z,
  Rb_repair x y = true -> Rb_repair y z = true -> Rb_repair x z = true.
Proof.
  intros x y z Hxy Hyz.
  assert (Htr : forall x y z : Fin.t 19,
    implb (Rb_repair x y && Rb_repair y z) (Rb_repair x z) = true).
  { apply forallb_finT3_spec. vm_compute. reflexivity. }
  specialize (Htr x y z). rewrite Hxy, Hyz in Htr. exact Htr.
Qed.

Instance repair_isposet : IsPoset (Fin.t 19) (fun x y => Rb_repair x y = true).
Proof.
  constructor.
  - exact Rb_repair_refl.
  - exact Rb_repair_antisym.
  - exact Rb_repair_trans.
Qed.

(* ===================================================================== *)
(*  Key monotonicity / injectivity lemmas (split into top-level lemmas   *)
(*  to keep each Qed tractable at the 19-element scale)                  *)
(* ===================================================================== *)

Lemma k1_repair_inj : forall x y, k1_repair x = k1_repair y -> x = y.
Proof.
  intros x y H.
  assert (Hdec : forall x y : Fin.t 19,
    implb (Nat.eqb (k1_repair x) (k1_repair y)) (Fin.eqb x y) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  apply Fin.eqb_eq. specialize (Hdec x y).
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hdec. exact Hdec.
Qed.

Lemma k2_repair_inj : forall x y, k2_repair x = k2_repair y -> x = y.
Proof.
  intros x y H.
  assert (Hdec : forall x y : Fin.t 19,
    implb (Nat.eqb (k2_repair x) (k2_repair y)) (Fin.eqb x y) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  apply Fin.eqb_eq. specialize (Hdec x y).
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hdec. exact Hdec.
Qed.

Lemma repair_ext_keys : forall x y,
  Rb_repair x y = true -> k1_repair x <= k1_repair y /\ k2_repair x <= k2_repair y.
Proof.
  intros x y H.
  assert (Hb : forall x y : Fin.t 19,
    implb (Rb_repair x y)
          (Nat.leb (k1_repair x) (k1_repair y) && Nat.leb (k2_repair x) (k2_repair y)) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  specialize (Hb x y). rewrite H in Hb. simpl in Hb.
  apply andb_prop in Hb. destruct Hb as [H1 H2].
  split; apply Nat.leb_le; assumption.
Qed.

Lemma repair_int_keys : forall x y,
  k1_repair x <= k1_repair y -> k2_repair x <= k2_repair y -> Rb_repair x y = true.
Proof.
  intros x y H1 H2.
  assert (Hb : forall x y : Fin.t 19,
    implb (Nat.leb (k1_repair x) (k1_repair y) && Nat.leb (k2_repair x) (k2_repair y))
          (Rb_repair x y) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  specialize (Hb x y).
  rewrite (proj2 (Nat.leb_le _ _) H1), (proj2 (Nat.leb_le _ _) H2) in Hb.
  simpl in Hb. exact Hb.
Qed.

(* ===================================================================== *)
(*  dim <= 2                                                              *)
(* ===================================================================== *)

Theorem repair_dim_le_2 :
  exists d, inhabited (PosetDimension (fun x y => Rb_repair x y = true) d) /\ d <= 2.
Proof.
  apply (realizer_keys_dim_le2 Rb_repair k1_repair k2_repair).
  - exact repair_isposet.
  - exact k1_repair_inj.
  - exact k2_repair_inj.
  - exact repair_ext_keys.
  - exact repair_int_keys.
  - (* Hdiff: events 8 and 9.
       k1_repair 8 = 3, k2_repair 8 = 15
       k1_repair 9 = 4, k2_repair 9 = 8
       So k1 8 <= k1 9 (3 <= 4) but ~ (k2 8 <= k2 9) (~ 15 <= 8). *)
    exists (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))),
           (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))).
    vm_compute. split; lia.
Qed.

(* ===================================================================== *)
(*  dim >= 2  (incomparable pair 8 and 9)                                *)
(* ===================================================================== *)

(* Events 8 and 9 are incomparable:
   Rb_repair 8 9 = false (8 goes to {8,13,14,15} only)
   Rb_repair 9 8 = false (9 does not go back to 8) *)
Lemma repair_incomparable_8_9 :
  Incomparable (fun x y => Rb_repair x y = true)
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))).
Proof.
  unfold Incomparable. intro Hor. destruct Hor as [H | H].
  - vm_compute in H. discriminate.
  - vm_compute in H. discriminate.
Qed.

Theorem repair_dim_ge_2 :
  forall d, inhabited (PosetDimension (fun x y => Rb_repair x y = true) d) -> 2 <= d.
Proof.
  intros d [Hd].
  apply (dim_ge_2_of_incomparable
           (fun x y => Rb_repair x y = true)
           (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))
           (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))
           repair_incomparable_8_9 d Hd).
Qed.

(* ===================================================================== *)
(*  dim = 2  (combining le_2 and ge_2)                                   *)
(* ===================================================================== *)

Theorem repair_dim_eq_2 :
  exists d, inhabited (PosetDimension (fun x y => Rb_repair x y = true) d) /\ d = 2.
Proof.
  destruct repair_dim_le_2 as [d [[Hd] Hle]].
  exists d. split.
  - exact (inhabits Hd).
  - apply Nat.le_antisymm.
    + exact Hle.
    + exact (repair_dim_ge_2 d (inhabits Hd)).
Qed.

(* ===================================================================== *)
(*  W_crown: the crown poset (N=4, syncs=[(0,1),(2,3),(0,2),(1,3)])      *)
(*  This is W_repair minus the inserted repairing sync (0,3).            *)
(*  By the z3 oracle (nomadim/data/frontier-sync/CLOCK_RESULTS.md) it   *)
(*  has dimension 3 — so NO 2-coordinate clock characterises its         *)
(*  happened-before. We do NOT prove dim>=3 here: concrete PG crowns     *)
(*  contain no induced crown3, and the alternating-cycle certificate is  *)
(*  deferred. The obstruction *type* is the abstract 3-crown, already    *)
(*  proven dim>=3 as FrontierCompose.crown3_dim_ge_3.                    *)
(* ===================================================================== *)

Definition W_crown_order (x y : Fin.t 16) : Prop := Rb_crown x y = true.
