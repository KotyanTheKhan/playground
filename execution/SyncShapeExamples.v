(* sync-shape examples (test-only)

   A concrete 2x2 fully-synchronizing schedule s_demo.

   s_demo desugars to:
     Frontier 0 = [(0,1)] : proc0 -> proc1 (tag 0)
     Frontier 1 = [(1,0)] : proc1 -> proc0 (tag 1)
   Events (process, index):
     a=(0,0) Send 1 0     b=(1,0) Recv 0 0
     c=(0,1) Recv 1 1     d=(1,1) Send 0 1
   Direct edges:
     a -> c (proc0 prog),  b -> d (proc1 prog),
     a -> b (msg frontier0), d -> c (msg frontier1).
   Index-0 block {a,b}, index-1 block {c,d}.  Every index-0 event
   precedes every index-1 event:
     a < c (prog), a < d (a<b<d), b < c (b<d<c), b < d (prog). *)

From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical
                           Relation_Operators ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Frontier
                              FullySync Schedule SyncShape.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.

Definition s_demo : Schedule :=
  {| sch_nprocs := 2; sch_frontiers := [ [(0,1)] ; [(1,0)] ] |}.

(* ------------------------------------------------------------------ *)
(* sync-shaped: immediate from the generic lemma                        *)
(* ------------------------------------------------------------------ *)

Example s_demo_sync_shaped : sync_shaped (desugar_prog s_demo).
Proof. apply desugar_sync_shaped. Qed.

(* ------------------------------------------------------------------ *)
(* Concrete events                                                      *)
(* ------------------------------------------------------------------ *)

Lemma valid_a : Ensembles.In (nat*nat) (ValidSet (desugar s_demo)) (0,0).
Proof. vm_compute. split; lia. Qed.
Lemma valid_b : Ensembles.In (nat*nat) (ValidSet (desugar s_demo)) (1,0).
Proof. vm_compute. split; lia. Qed.
Lemma valid_c : Ensembles.In (nat*nat) (ValidSet (desugar s_demo)) (0,1).
Proof. vm_compute. split; lia. Qed.
Lemma valid_d : Ensembles.In (nat*nat) (ValidSet (desugar s_demo)) (1,1).
Proof. vm_compute. split; lia. Qed.

Definition da : ep_carrier (exec_of_schedule s_demo) := exist _ (0,0) valid_a.
Definition db : ep_carrier (exec_of_schedule s_demo) := exist _ (1,0) valid_b.
Definition dc : ep_carrier (exec_of_schedule s_demo) := exist _ (0,1) valid_c.
Definition dd : ep_carrier (exec_of_schedule s_demo) := exist _ (1,1) valid_d.

(* ------------------------------------------------------------------ *)
(* The carrier has exactly four events                                  *)
(* ------------------------------------------------------------------ *)

Lemma valid_event_demo_cases :
  forall x : ep_carrier (exec_of_schedule s_demo),
    let pi := proj1_sig x in
    pi = (0,0) \/ pi = (1,0) \/ pi = (0,1) \/ pi = (1,1).
Proof.
  intros [[p i] Hpi]. simpl.
  unfold ep_carrier, exec_of_schedule, In, ValidSet, Valid in Hpi.
  simpl in Hpi. destruct Hpi as [Hp Hi].
  assert (Hp2 : p < 2) by (revert Hp; vm_compute; lia).
  assert (Hi2 : i < 2).
  { revert Hi. vm_compute. destruct p as [|[|p']]; simpl; lia. }
  destruct p as [|[|p']]; [ | | lia ];
    destruct i as [|[|i']]; try lia.
  - left. reflexivity.
  - right; right; left. reflexivity.
  - right; left. reflexivity.
  - right; right; right. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Event equality from equal raw pairs (proof-irrelevance)              *)
(* ------------------------------------------------------------------ *)

Lemma event_demo_eq_of_proj :
  forall x y : ep_carrier (exec_of_schedule s_demo),
    proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros [px Hpx] [py Hpy] Heq. simpl in Heq. subst py.
  f_equal. apply proof_irrelevance.
Qed.

Lemma eq_da : forall x : ep_carrier (exec_of_schedule s_demo),
    proj1_sig x = (0,0) -> x = da.
Proof. intros x H. apply event_demo_eq_of_proj. exact H. Qed.
Lemma eq_db : forall x : ep_carrier (exec_of_schedule s_demo),
    proj1_sig x = (1,0) -> x = db.
Proof. intros x H. apply event_demo_eq_of_proj. exact H. Qed.
Lemma eq_dc : forall x : ep_carrier (exec_of_schedule s_demo),
    proj1_sig x = (0,1) -> x = dc.
Proof. intros x H. apply event_demo_eq_of_proj. exact H. Qed.
Lemma eq_dd : forall x : ep_carrier (exec_of_schedule s_demo),
    proj1_sig x = (1,1) -> x = dd.
Proof. intros x H. apply event_demo_eq_of_proj. exact H. Qed.

(* ------------------------------------------------------------------ *)
(* Direct hb edges                                                      *)
(* ------------------------------------------------------------------ *)

(* a -> c : proc0 program order (0,0) -> (0,1) *)
Lemma hb_a_c : ep_order (exec_of_schedule s_demo) da dc.
Proof.
  unfold ep_order, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. left. split; reflexivity.
Qed.

(* b -> d : proc1 program order (1,0) -> (1,1) *)
Lemma hb_b_d : ep_order (exec_of_schedule s_demo) db dd.
Proof.
  unfold ep_order, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. left. split; reflexivity.
Qed.

(* a -> b : message, frontier 0, tag 0 *)
Lemma hb_a_b : ep_order (exec_of_schedule s_demo) da db.
Proof.
  unfold ep_order, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. right. exists 0.
  split; vm_compute; reflexivity.
Qed.

(* d -> c : message, frontier 1, tag 1 *)
Lemma hb_d_c : ep_order (exec_of_schedule s_demo) dd dc.
Proof.
  unfold ep_order, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. right. exists 1.
  split; vm_compute; reflexivity.
Qed.

(* derived edges *)
Lemma hb_a_d : ep_order (exec_of_schedule s_demo) da dd.
Proof. eapply hb_trans. apply hb_a_b. apply hb_b_d. Qed.

Lemma hb_b_c : ep_order (exec_of_schedule s_demo) db dc.
Proof. eapply hb_trans. apply hb_b_d. apply hb_d_c. Qed.

(* ------------------------------------------------------------------ *)
(* Fully synchronizing                                                  *)
(* ------------------------------------------------------------------ *)

Example s_demo_fully_synchronizing : FullySynchronizing s_demo.
Proof.
  unfold FullySynchronizing. intros x y Hlt.
  pose proof (valid_event_demo_cases x) as Hx.
  pose proof (valid_event_demo_cases y) as Hy.
  simpl in Hx, Hy.
  (* index of x must be 0 and index of y must be 1 *)
  destruct Hx as [Hx|[Hx|[Hx|Hx]]];
    [ rewrite (eq_da x Hx) in *
    | rewrite (eq_db x Hx) in *
    | rewrite (eq_dc x Hx) in *
    | rewrite (eq_dd x Hx) in * ];
    (destruct Hy as [Hy|[Hy|[Hy|Hy]]];
      [ rewrite (eq_da y Hy) in *
      | rewrite (eq_db y Hy) in *
      | rewrite (eq_dc y Hy) in *
      | rewrite (eq_dd y Hy) in * ]);
    vm_compute in Hlt;
    try (exfalso; lia).
  - apply hb_a_c.
  - apply hb_a_d.
  - apply hb_b_c.
  - apply hb_b_d.
Qed.

(* ------------------------------------------------------------------ *)
(* IsFullySync via the bridge                                           *)
(* ------------------------------------------------------------------ *)

Example s_demo_is_fully_sync :
  IsFullySync (exec_of_schedule s_demo) (frontier_blocks s_demo).
Proof.
  apply (fully_synchronizing_is_fully_sync s_demo s_demo_fully_synchronizing).
  vm_compute. lia.
Qed.
