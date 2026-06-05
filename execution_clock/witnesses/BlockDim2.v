From Stdlib Require Import Fin Arith Lia.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Execution Require Import DimTwoGeneric.
From ExecClock Require Import FinPosetBool WitnessData.

(* ===================================================================== *)
(*  Poset laws for the block relation (5 events, N=2, sync (0,1))        *)
(* ===================================================================== *)

Lemma Rb_block_refl : forall x, Rb_block x x = true.
Proof.
  apply forallb_finT_spec. vm_compute. reflexivity.
Qed.

Lemma Rb_block_antisym : forall x y,
  Rb_block x y = true -> Rb_block y x = true -> x = y.
Proof.
  intros x y Hxy Hyx.
  assert (Hdec : forall x y : Fin.t 5,
    implb (Rb_block x y && Rb_block y x) (Fin.eqb x y) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  apply Fin.eqb_eq.
  specialize (Hdec x y). rewrite Hxy, Hyx in Hdec. exact Hdec.
Qed.

Lemma Rb_block_trans : forall x y z,
  Rb_block x y = true -> Rb_block y z = true -> Rb_block x z = true.
Proof.
  intros x y z Hxy Hyz.
  assert (Htr : forall x y z : Fin.t 5,
    implb (Rb_block x y && Rb_block y z) (Rb_block x z) = true).
  { apply forallb_finT3_spec. vm_compute. reflexivity. }
  specialize (Htr x y z). rewrite Hxy, Hyz in Htr. exact Htr.
Qed.

Instance block_isposet : IsPoset (Fin.t 5) (fun x y => Rb_block x y = true).
Proof.
  constructor.
  - exact Rb_block_refl.
  - exact Rb_block_antisym.
  - exact Rb_block_trans.
Qed.

(* ===================================================================== *)
(*  Key monotonicity / injectivity lemmas                                *)
(* ===================================================================== *)

Lemma k1_block_inj : forall x y, k1_block x = k1_block y -> x = y.
Proof.
  intros x y H.
  assert (Hdec : forall x y : Fin.t 5,
    implb (Nat.eqb (k1_block x) (k1_block y)) (Fin.eqb x y) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  apply Fin.eqb_eq. specialize (Hdec x y).
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hdec. exact Hdec.
Qed.

Lemma k2_block_inj : forall x y, k2_block x = k2_block y -> x = y.
Proof.
  intros x y H.
  assert (Hdec : forall x y : Fin.t 5,
    implb (Nat.eqb (k2_block x) (k2_block y)) (Fin.eqb x y) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  apply Fin.eqb_eq. specialize (Hdec x y).
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hdec. exact Hdec.
Qed.

Lemma block_ext_keys : forall x y,
  Rb_block x y = true -> k1_block x <= k1_block y /\ k2_block x <= k2_block y.
Proof.
  intros x y H.
  assert (Hb : forall x y : Fin.t 5,
    implb (Rb_block x y)
          (Nat.leb (k1_block x) (k1_block y) && Nat.leb (k2_block x) (k2_block y)) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  specialize (Hb x y). rewrite H in Hb. simpl in Hb.
  apply andb_prop in Hb. destruct Hb as [H1 H2].
  split; apply Nat.leb_le; assumption.
Qed.

Lemma block_int_keys : forall x y,
  k1_block x <= k1_block y -> k2_block x <= k2_block y -> Rb_block x y = true.
Proof.
  intros x y H1 H2.
  assert (Hb : forall x y : Fin.t 5,
    implb (Nat.leb (k1_block x) (k1_block y) && Nat.leb (k2_block x) (k2_block y))
          (Rb_block x y) = true).
  { apply forallb_finT2_spec. vm_compute. reflexivity. }
  specialize (Hb x y).
  rewrite (proj2 (Nat.leb_le _ _) H1), (proj2 (Nat.leb_le _ _) H2) in Hb.
  simpl in Hb. exact Hb.
Qed.

(* ===================================================================== *)
(*  dim <= 2                                                              *)
(* ===================================================================== *)

Theorem block_dim_le_2 :
  exists d, inhabited (PosetDimension (fun x y => Rb_block x y = true) d) /\ d <= 2.
Proof.
  apply (realizer_keys_dim_le2 Rb_block k1_block k2_block).
  - exact block_isposet.
  - exact k1_block_inj.
  - exact k2_block_inj.
  - exact block_ext_keys.
  - exact block_int_keys.
  - (* Hdiff: events 3 and 4 are incomparable.
       k1_block 3 = 3, k2_block 3 = 4
       k1_block 4 = 4, k2_block 4 = 3
       So k1 3 <= k1 4 (3 <= 4) but ~ (k2 3 <= k2 4) (~ 4 <= 3). *)
    exists (Fin.FS (Fin.FS (Fin.FS Fin.F1))),
           (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
    vm_compute. split; lia.
Qed.

(* ===================================================================== *)
(*  dim >= 2  (incomparable pair 3 and 4)                                *)
(* ===================================================================== *)

(* Events 3 and 4 are incomparable: neither Rb_block 3 4 nor Rb_block 4 3. *)
Lemma block_incomparable_3_4 :
  Incomparable (fun x y => Rb_block x y = true)
    (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
Proof.
  unfold Incomparable. intro Hor. destruct Hor as [H | H].
  - vm_compute in H. discriminate.
  - vm_compute in H. discriminate.
Qed.

Theorem block_dim_ge_2 :
  forall d, inhabited (PosetDimension (fun x y => Rb_block x y = true) d) -> 2 <= d.
Proof.
  intros d [Hd].
  apply (dim_ge_2_of_incomparable
           (fun x y => Rb_block x y = true)
           (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
           (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
  - exact block_incomparable_3_4.
  - exact Hd.
Qed.

(* ===================================================================== *)
(*  dim = 2  (combining le_2 and ge_2)                                   *)
(* ===================================================================== *)

Theorem block_dim_eq_2 :
  exists d, inhabited (PosetDimension (fun x y => Rb_block x y = true) d) /\ d = 2.
Proof.
  destruct block_dim_le_2 as [d [[Hd] Hle]].
  exists d. split.
  - exact (inhabits Hd).
  - apply Nat.le_antisymm.
    + exact Hle.
    + exact (block_dim_ge_2 d (inhabits Hd)).
Qed.
