(* reduction framework examples (test-only)

   Concrete E_min block-reduction instances:
   the Umin block of E_min reduces dimension to E_min itself, and so the
   block has dimension <= 2; plus a composability demo exercising
   [iso_preserves_dim] + [reduces_dim_trans]. *)

From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimIso Ordinal
                              DimExamples FrontierExamples Reduction.

#[local] Existing Instance hb_IsPoset.

(* ------------------------------------------------------------------ *)
(* The Umin block reduces dimension to E_min                           *)
(* ------------------------------------------------------------------ *)

Example E_min_block_reduces :
  ReducesDim {z | Ensembles.In _ Umin z}
             (fun x y => ep_order E_min (proj1_sig x) (proj1_sig y))
             (ep_carrier E_min) (ep_order E_min).
Proof.
  apply (subposet_reduces_dim (ep_carrier E_min) (ep_order E_min) Umin).
Qed.

(* ------------------------------------------------------------------ *)
(* The Umin block therefore has dimension <= 2                         *)
(* ------------------------------------------------------------------ *)

Example E_min_block_dim_le_2 :
  exists d,
    inhabited (PosetDimension
                 (fun x y : {z | Ensembles.In _ Umin z} =>
                    ep_order E_min (proj1_sig x) (proj1_sig y)) d)
    /\ d <= 2.
Proof.
  destruct E_min_dim_2 as [Hd2].
  destruct (subposet_dimension_le (ep_order E_min) Umin 2 Hd2)
    as [dq [Hinh Hle]].
  apply (reduces_dim2 _ _ _ _ E_min_block_reduces).
  - exists dq. exact Hinh.
  - exists 2. split; [exact E_min_dim_2 | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Composability demo: block -> E_min -> E_min (identity iso)          *)
(* ------------------------------------------------------------------ *)

(* dimension of E_min exists (wrapped in [inhabited], as the reduction
   lemmas require). *)
Lemma exec_dim_min : exists d, inhabited (PosetDimension (ep_order E_min) d).
Proof.
  destruct (exec_dimension_exists E_min) as [d Hd].
  exists d. exact Hd.
Qed.

Example reduction_chain_demo :
  ReducesDim {z | Ensembles.In _ Umin z}
             (fun x y => ep_order E_min (proj1_sig x) (proj1_sig y))
             (ep_carrier E_min) (ep_order E_min).
Proof.
  (* identity order-isomorphism on E_min preserves dimension *)
  pose proof
    (iso_preserves_dim (ep_carrier E_min) (ep_carrier E_min)
       (ep_order E_min) (ep_order E_min)
       (fun x => x) (fun x => x)
       (fun _ => eq_refl) (fun _ => eq_refl)
       (fun a a' => iff_refl _)) as Hpres.
  (* turn the identity dim-preservation into a dim-reduction *)
  pose proof
    (preserves_dim_reduces (ep_carrier E_min) (ep_order E_min)
       (ep_carrier E_min) (ep_order E_min) exec_dim_min Hpres) as Hid_red.
  (* compose: block -> E_min (block reduction) -> E_min (identity) *)
  exact (reduces_dim_trans
           {z | Ensembles.In _ Umin z}
           (fun x y => ep_order E_min (proj1_sig x) (proj1_sig y))
           (ep_carrier E_min) (ep_order E_min)
           (ep_carrier E_min) (ep_order E_min)
           exec_dim_min E_min_block_reduces Hid_red).
Qed.
