(* execution dimension bridge — DimExamples (test-only)

   A concrete minimal execution poset of dimension exactly 2.

   sched_min desugars to:
     proc0 = [Send 1 0; Local]   events a=(0,0), b=(0,1)
     proc1 = [Recv 0 0; Local]   events c=(1,0), d=(1,1)
   Direct edges: a->b (prog), c->d (prog), a->c (message tag 0).
   So hb: a < b, a < c, a < d, c < d; b || c, b || d. *)

From Stdlib Require Import List Arith Lia Ensembles Finite_sets Classical Relation_Operators ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset Schedule.
From Execution Require Import DimBridge.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.

Definition sched_min : Schedule :=
  {| sch_nprocs := 2; sch_frontiers := [ [(0,1)] ; [] ] |}.
Definition E_min : ExecPoset := exec_of_schedule sched_min.

Definition key1_min (pi : nat * nat) : nat :=
  match pi with (0,0) => 0 | (0,1) => 1 | (1,0) => 2 | (1,1) => 3 | _ => 99 end.
Definition key2_min (pi : nat * nat) : nat :=
  match pi with (0,0) => 0 | (1,0) => 1 | (1,1) => 2 | (0,1) => 3 | _ => 99 end.

Definition L1_min (x y : ep_carrier E_min) : Prop :=
  key1_min (proj1_sig x) <= key1_min (proj1_sig y).
Definition L2_min (x y : ep_carrier E_min) : Prop :=
  key2_min (proj1_sig x) <= key2_min (proj1_sig y).

(* ------------------------------------------------------------------ *)
(* The carrier has exactly four events                                  *)
(* ------------------------------------------------------------------ *)

Lemma valid_event_min_cases :
  forall x : ep_carrier E_min,
    let pi := proj1_sig x in
    pi = (0,0) \/ pi = (0,1) \/ pi = (1,0) \/ pi = (1,1).
Proof.
  intros [[p i] Hpi]. simpl.
  unfold ep_carrier, E_min, exec_of_schedule, In, ValidSet, Valid in Hpi.
  simpl in Hpi.
  destruct Hpi as [Hp Hi].
  (* nprocs (desugar sched_min) = 2 ; proc_len ... p = 2 *)
  assert (Hp2 : p < 2) by (revert Hp; vm_compute; lia).
  assert (Hi2 : i < 2).
  { revert Hi. vm_compute.
    destruct p as [|[|p']]; simpl; lia. }
  destruct p as [|[|p']]; [ | | lia ];
    destruct i as [|[|i']]; try lia.
  - left. reflexivity.
  - right; left. reflexivity.
  - right; right; left. reflexivity.
  - right; right; right. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Key monotonicity along hb                                            *)
(* ------------------------------------------------------------------ *)

(* On a single edge, both keys are non-decreasing. *)
Lemma key_min_edge :
  forall x y : ep_carrier E_min,
    edge (desugar sched_min) x y ->
    key1_min (proj1_sig x) <= key1_min (proj1_sig y) /\
    key2_min (proj1_sig x) <= key2_min (proj1_sig y).
Proof.
  intros x y Hedge.
  pose proof (valid_event_min_cases x) as Hx.
  pose proof (valid_event_min_cases y) as Hy.
  simpl in Hx, Hy.
  destruct x as [[px ix] Hpx]; destruct y as [[py iy] Hpy].
  simpl in Hx, Hy. simpl proj1_sig.
  unfold edge in Hedge. simpl in Hedge.
  (* enumerate the source/target pairs and discharge per edge *)
  destruct Hx as [Hx|[Hx|[Hx|Hx]]];
    destruct Hy as [Hy|[Hy|[Hy|Hy]]];
    injection Hx as Hpx' Hix'; injection Hy as Hpy' Hiy';
    subst px ix py iy;
    destruct Hedge as [[Hpe Hse] | [t [Hsend Hrecv]]];
    try (vm_compute in Hpe; vm_compute in Hse; try discriminate);
    try (vm_compute in Hsend; vm_compute in Hrecv; try discriminate);
    vm_compute; lia.
Qed.

Lemma key1_min_mono :
  forall x y : ep_carrier E_min,
    ep_order E_min x y -> key1_min (proj1_sig x) <= key1_min (proj1_sig y).
Proof.
  intros x y H.
  unfold ep_order, E_min, exec_of_schedule, exec_of in H. simpl in H.
  unfold hb in H.
  induction H as [x y Hedge | x | x y z Hxy IHxy Hyz IHyz].
  - apply (proj1 (key_min_edge x y Hedge)).
  - apply Nat.le_refl.
  - eapply Nat.le_trans; eassumption.
Qed.

Lemma key2_min_mono :
  forall x y : ep_carrier E_min,
    ep_order E_min x y -> key2_min (proj1_sig x) <= key2_min (proj1_sig y).
Proof.
  intros x y H.
  unfold ep_order, E_min, exec_of_schedule, exec_of in H. simpl in H.
  unfold hb in H.
  induction H as [x y Hedge | x | x y z Hxy IHxy Hyz IHyz].
  - apply (proj2 (key_min_edge x y Hedge)).
  - apply Nat.le_refl.
  - eapply Nat.le_trans; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Event equality from equal raw pairs                                  *)
(* ------------------------------------------------------------------ *)

Lemma event_min_eq_of_proj :
  forall x y : ep_carrier E_min,
    proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros [px Hpx] [py Hpy] Heq. simpl in Heq. subst py.
  f_equal. apply proof_irrelevance.
Qed.

(* injectivity of key1 on the four valid pairs *)
Lemma key1_min_inj :
  forall x y : ep_carrier E_min,
    key1_min (proj1_sig x) = key1_min (proj1_sig y) -> proj1_sig x = proj1_sig y.
Proof.
  intros x y Hkey.
  pose proof (valid_event_min_cases x) as Hx.
  pose proof (valid_event_min_cases y) as Hy.
  simpl in Hx, Hy.
  destruct x as [px Hpx]; destruct y as [py Hpy]; simpl in *.
  destruct Hx as [Hx|[Hx|[Hx|Hx]]]; subst px;
    destruct Hy as [Hy|[Hy|[Hy|Hy]]]; subst py;
    vm_compute in Hkey; try discriminate; reflexivity.
Qed.

Lemma key2_min_inj :
  forall x y : ep_carrier E_min,
    key2_min (proj1_sig x) = key2_min (proj1_sig y) -> proj1_sig x = proj1_sig y.
Proof.
  intros x y Hkey.
  pose proof (valid_event_min_cases x) as Hx.
  pose proof (valid_event_min_cases y) as Hy.
  simpl in Hx, Hy.
  destruct x as [px Hpx]; destruct y as [py Hpy]; simpl in *.
  destruct Hx as [Hx|[Hx|[Hx|Hx]]]; subst px;
    destruct Hy as [Hy|[Hy|[Hy|Hy]]]; subst py;
    vm_compute in Hkey; try discriminate; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* L1_min and L2_min are linear extensions                              *)
(* ------------------------------------------------------------------ *)

Lemma L1_min_linext : IsLinearExtension (ep_order E_min) L1_min.
Proof.
  constructor.
  - constructor.
    + constructor.
      * intro x. unfold L1_min. apply Nat.le_refl.
      * intros x y Hxy Hyx. unfold L1_min in *.
        apply event_min_eq_of_proj. apply key1_min_inj. lia.
      * intros x y z Hxy Hyz. unfold L1_min in *. lia.
    + intros x y. unfold L1_min. lia.
  - intros x y Hxy. unfold L1_min. apply key1_min_mono. exact Hxy.
Qed.

Lemma L2_min_linext : IsLinearExtension (ep_order E_min) L2_min.
Proof.
  constructor.
  - constructor.
    + constructor.
      * intro x. unfold L2_min. apply Nat.le_refl.
      * intros x y Hxy Hyx. unfold L2_min in *.
        apply event_min_eq_of_proj. apply key2_min_inj. lia.
      * intros x y z Hxy Hyz. unfold L2_min in *. lia.
    + intros x y. unfold L2_min. lia.
  - intros x y Hxy. unfold L2_min. apply key2_min_mono. exact Hxy.
Qed.

(* ------------------------------------------------------------------ *)
(* Concrete events and their validity proofs                            *)
(* ------------------------------------------------------------------ *)

Lemma valid_a : In (nat*nat) (ValidSet (desugar sched_min)) (0,0).
Proof. vm_compute. split; lia. Qed.
Lemma valid_b : In (nat*nat) (ValidSet (desugar sched_min)) (0,1).
Proof. vm_compute. split; lia. Qed.
Lemma valid_c : In (nat*nat) (ValidSet (desugar sched_min)) (1,0).
Proof. vm_compute. split; lia. Qed.
Lemma valid_d : In (nat*nat) (ValidSet (desugar sched_min)) (1,1).
Proof. vm_compute. split; lia. Qed.

Definition ev_a : ep_carrier E_min := exist _ (0,0) valid_a.
Definition ev_b : ep_carrier E_min := exist _ (0,1) valid_b.
Definition ev_c : ep_carrier E_min := exist _ (1,0) valid_c.
Definition ev_d : ep_carrier E_min := exist _ (1,1) valid_d.

(* Canonicalize an event from its raw pair (proof-irrelevance). *)
Lemma eq_ev_a : forall x : ep_carrier E_min, proj1_sig x = (0,0) -> x = ev_a.
Proof. intros x H. apply event_min_eq_of_proj. exact H. Qed.
Lemma eq_ev_b : forall x : ep_carrier E_min, proj1_sig x = (0,1) -> x = ev_b.
Proof. intros x H. apply event_min_eq_of_proj. exact H. Qed.
Lemma eq_ev_c : forall x : ep_carrier E_min, proj1_sig x = (1,0) -> x = ev_c.
Proof. intros x H. apply event_min_eq_of_proj. exact H. Qed.
Lemma eq_ev_d : forall x : ep_carrier E_min, proj1_sig x = (1,1) -> x = ev_d.
Proof. intros x H. apply event_min_eq_of_proj. exact H. Qed.

(* The three direct hb-steps as concrete proofs. *)
Lemma hb_a_b : ep_order E_min ev_a ev_b.
Proof.
  unfold ep_order, E_min, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. left. split; reflexivity.
Qed.

Lemma hb_a_c : ep_order E_min ev_a ev_c.
Proof.
  unfold ep_order, E_min, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. right. exists 0.
  split; vm_compute; reflexivity.
Qed.

Lemma hb_c_d : ep_order E_min ev_c ev_d.
Proof.
  unfold ep_order, E_min, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. left. split; reflexivity.
Qed.

Lemma hb_a_d : ep_order E_min ev_a ev_d.
Proof.
  eapply hb_trans. apply hb_a_c. apply hb_c_d.
Qed.

(* ------------------------------------------------------------------ *)
(* The realizer: hb = L1_min ∩ L2_min                                   *)
(* ------------------------------------------------------------------ *)

Lemma hb_min_realizer :
  forall x y : ep_carrier E_min,
    ep_order E_min x y <-> (L1_min x y /\ L2_min x y).
Proof.
  intros x y. split.
  - intro H. split.
    + apply key1_min_mono. exact H.
    + apply key2_min_mono. exact H.
  - intros [H1 H2]. unfold L1_min, L2_min in H1, H2.
    pose proof (valid_event_min_cases x) as Hx.
    pose proof (valid_event_min_cases y) as Hy.
    simpl in Hx, Hy.
    (* Replace x and y by canonical events; then keys compute to literals,
       killing the contradictory combos and leaving the eight real ones. *)
    destruct Hx as [Hx|[Hx|[Hx|Hx]]];
      [ rewrite (eq_ev_a x Hx) in *
      | rewrite (eq_ev_b x Hx) in *
      | rewrite (eq_ev_c x Hx) in *
      | rewrite (eq_ev_d x Hx) in * ];
      (destruct Hy as [Hy|[Hy|[Hy|Hy]]];
        [ rewrite (eq_ev_a y Hy) in *
        | rewrite (eq_ev_b y Hy) in *
        | rewrite (eq_ev_c y Hy) in *
        | rewrite (eq_ev_d y Hy) in * ]);
      vm_compute in H1, H2;
      try (exfalso; lia).
    (* surviving combos: a-a,a-b,a-c,a-d,b-b,c-c,c-d,d-d *)
    + apply poset_refl.
    + apply hb_a_b.
    + apply hb_a_c.
    + apply hb_a_d.
    + apply poset_refl.
    + apply poset_refl.
    + apply hb_c_d.
    + apply poset_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Incomparability of b and c                                           *)
(* ------------------------------------------------------------------ *)

Lemma incomp_b_c : Incomparable (ep_order E_min) ev_b ev_c.
Proof.
  unfold Incomparable. intros [Hbc | Hcb].
  - apply hb_min_realizer in Hbc. destruct Hbc as [_ H2].
    unfold L2_min in H2. vm_compute in H2. lia.
  - apply hb_min_realizer in Hcb. destruct Hcb as [H1 _].
    unfold L1_min in H1. vm_compute in H1. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem                                                         *)
(* ------------------------------------------------------------------ *)

Theorem E_min_dim_2 : exec_has_dimension E_min 2.
Proof.
  apply exec_dim_eq_2_of_realizer.
  - exists L1_min, L2_min. split; [exact L1_min_linext|].
    split; [exact L2_min_linext|]. exact hb_min_realizer.
  - exists ev_b, ev_c. exact incomp_b_c.
Qed.
