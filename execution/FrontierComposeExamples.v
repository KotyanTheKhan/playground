(* Frontier composition dichotomy: worked instances (test-only). *)
From Stdlib Require Import List Arith Lia Fin.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Execution Require Import FrontierCompose.
Import ListNotations.

(* a non-crossing (threshold) frontier on Fin 2 / Fin 2: F i j := idx i <= idx j *)
Definition phi2 (a : Fin.t 2) : nat := proj1_sig (Fin.to_nat a).
Definition psi2 (b : Fin.t 2) : nat := proj1_sig (Fin.to_nat b).
Definition Fstair (a b : Fin.t 2) : Prop := phi2 a <= psi2 b.

Example stair_ferrers : Ferrers Fstair.
Proof. apply (threshold_Ferrers phi2 psi2 Fstair). intros a b. unfold Fstair. reflexivity. Qed.

Example stair_dim_le2 : forall d, PosetDimension (compose_le Fstair) d -> d <= 2.
Proof. apply (threshold_dim_le2 phi2 psi2 Fstair). intros a b. unfold Fstair. reflexivity. Qed.

(* the crown is NOT non-crossing, and its composite has dim >= 3 *)
Example crown_not_ferrers : ~ Ferrers crownF.
Proof.
  unfold Ferrers, crownF. intro HF.
  specialize (HF Fin.F1 (Fin.FS Fin.F1) (Fin.FS Fin.F1) Fin.F1).
  destruct HF as [H|H].
  - intro C; discriminate C.
  - intro C; discriminate C.
  - apply H; reflexivity.
  - apply H; reflexivity.
Qed.

Example crown_dim_ge_3 : forall d, PosetDimension crown3 d -> 3 <= d.
Proof. exact crown3_dim_ge_3. Qed.
