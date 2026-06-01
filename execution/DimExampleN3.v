(* execution dimension bridge — DimExampleN3 (test-only)

   The N=3 execution poset has dimension exactly 2.

   sched_n3 desugars to:
     proc0 = [Send 1 0; Local]   events a=(0,0), b=(0,1)
     proc1 = [Recv 0 0; Send 2 1] events c=(1,0), d=(1,1)
     proc2 = [Local; Recv 1 1]   events e=(2,0), f=(2,1)
   Direct edges: a->b (prog), c->d (prog), e->f (prog),
                 a->c (message tag 0), d->f (message tag 1).
   So hb strict pairs: a<b, a<c, a<d, a<f, c<d, c<f, d<f, e<f.
   Incomparable pairs include (a,e), (b,c), (b,d), (b,e), (b,f), (c,e), (d,e). *)

From Stdlib Require Import List Arith Lia Ensembles Finite_sets Classical ProofIrrelevance Relation_Operators.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset Schedule Examples.
From Execution Require Import DimBridge.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.

Definition E_n3 : ExecPoset := exec_of_schedule sched_n3.

Definition key1_n3 (pi : nat * nat) : nat :=
  match pi with
  | (0,0) => 0 | (0,1) => 1 | (1,0) => 2 | (1,1) => 3 | (2,0) => 4 | (2,1) => 5
  | _ => 99
  end.
Definition key2_n3 (pi : nat * nat) : nat :=
  match pi with
  | (0,0) => 1 | (0,1) => 5 | (1,0) => 2 | (1,1) => 3 | (2,0) => 0 | (2,1) => 4
  | _ => 99
  end.

Definition L1_n3 (x y : ep_carrier E_n3) : Prop :=
  key1_n3 (proj1_sig x) <= key1_n3 (proj1_sig y).
Definition L2_n3 (x y : ep_carrier E_n3) : Prop :=
  key2_n3 (proj1_sig x) <= key2_n3 (proj1_sig y).

(* ------------------------------------------------------------------ *)
(* The carrier has exactly six events                                   *)
(* ------------------------------------------------------------------ *)

Lemma valid_event_n3_cases :
  forall x : ep_carrier E_n3,
    let pi := proj1_sig x in
    pi = (0,0) \/ pi = (0,1) \/ pi = (1,0) \/ pi = (1,1)
    \/ pi = (2,0) \/ pi = (2,1).
Proof.
  intros [[p i] Hpi]. simpl.
  unfold ep_carrier, E_n3, exec_of_schedule, In, ValidSet, Valid in Hpi.
  simpl in Hpi.
  destruct Hpi as [Hp Hi].
  assert (Hp3 : p < 3) by (revert Hp; vm_compute; lia).
  assert (Hi2 : i < 2).
  { revert Hi. vm_compute.
    destruct p as [|[|[|p']]]; simpl; lia. }
  destruct p as [|[|[|p']]]; [ | | | lia ];
    destruct i as [|[|i']]; try lia.
  - left. reflexivity.
  - right; left. reflexivity.
  - right; right; left. reflexivity.
  - right; right; right; left. reflexivity.
  - right; right; right; right; left. reflexivity.
  - right; right; right; right; right. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Key monotonicity along hb                                            *)
(* ------------------------------------------------------------------ *)

Lemma key_n3_edge :
  forall x y : ep_carrier E_n3,
    edge (desugar sched_n3) x y ->
    key1_n3 (proj1_sig x) <= key1_n3 (proj1_sig y) /\
    key2_n3 (proj1_sig x) <= key2_n3 (proj1_sig y).
Proof.
  intros x y Hedge.
  pose proof (valid_event_n3_cases x) as Hx.
  pose proof (valid_event_n3_cases y) as Hy.
  simpl in Hx, Hy.
  destruct x as [[px ix] Hpx]; destruct y as [[py iy] Hpy].
  simpl in Hx, Hy. simpl proj1_sig.
  unfold edge in Hedge. simpl in Hedge.
  destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]];
    destruct Hy as [Hy|[Hy|[Hy|[Hy|[Hy|Hy]]]]];
    injection Hx as Hpx' Hix'; injection Hy as Hpy' Hiy';
    subst px ix py iy;
    destruct Hedge as [[Hpe Hse] | [t [Hsend Hrecv]]];
    try (vm_compute in Hpe; vm_compute in Hse; try discriminate);
    try (vm_compute in Hsend; vm_compute in Hrecv; try discriminate);
    vm_compute; lia.
Qed.

Lemma key1_n3_mono :
  forall x y : ep_carrier E_n3,
    ep_order E_n3 x y -> key1_n3 (proj1_sig x) <= key1_n3 (proj1_sig y).
Proof.
  intros x y H.
  unfold ep_order, E_n3, exec_of_schedule, exec_of in H. simpl in H.
  unfold hb in H.
  induction H as [x y Hedge | x | x y z Hxy IHxy Hyz IHyz].
  - apply (proj1 (key_n3_edge x y Hedge)).
  - apply Nat.le_refl.
  - eapply Nat.le_trans; eassumption.
Qed.

Lemma key2_n3_mono :
  forall x y : ep_carrier E_n3,
    ep_order E_n3 x y -> key2_n3 (proj1_sig x) <= key2_n3 (proj1_sig y).
Proof.
  intros x y H.
  unfold ep_order, E_n3, exec_of_schedule, exec_of in H. simpl in H.
  unfold hb in H.
  induction H as [x y Hedge | x | x y z Hxy IHxy Hyz IHyz].
  - apply (proj2 (key_n3_edge x y Hedge)).
  - apply Nat.le_refl.
  - eapply Nat.le_trans; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Event equality from equal raw pairs                                  *)
(* ------------------------------------------------------------------ *)

Lemma event_n3_eq_of_proj :
  forall x y : ep_carrier E_n3,
    proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros [px Hpx] [py Hpy] Heq. simpl in Heq. subst py.
  f_equal. apply proof_irrelevance.
Qed.

Lemma key1_n3_inj :
  forall x y : ep_carrier E_n3,
    key1_n3 (proj1_sig x) = key1_n3 (proj1_sig y) -> proj1_sig x = proj1_sig y.
Proof.
  intros x y Hkey.
  pose proof (valid_event_n3_cases x) as Hx.
  pose proof (valid_event_n3_cases y) as Hy.
  simpl in Hx, Hy.
  destruct x as [px Hpx]; destruct y as [py Hpy]; simpl in *.
  destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]; subst px;
    destruct Hy as [Hy|[Hy|[Hy|[Hy|[Hy|Hy]]]]]; subst py;
    vm_compute in Hkey; try discriminate; reflexivity.
Qed.

Lemma key2_n3_inj :
  forall x y : ep_carrier E_n3,
    key2_n3 (proj1_sig x) = key2_n3 (proj1_sig y) -> proj1_sig x = proj1_sig y.
Proof.
  intros x y Hkey.
  pose proof (valid_event_n3_cases x) as Hx.
  pose proof (valid_event_n3_cases y) as Hy.
  simpl in Hx, Hy.
  destruct x as [px Hpx]; destruct y as [py Hpy]; simpl in *.
  destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]; subst px;
    destruct Hy as [Hy|[Hy|[Hy|[Hy|[Hy|Hy]]]]]; subst py;
    vm_compute in Hkey; try discriminate; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* L1_n3 and L2_n3 are linear extensions                                *)
(* ------------------------------------------------------------------ *)

Lemma L1_n3_linext : IsLinearExtension (ep_order E_n3) L1_n3.
Proof.
  constructor.
  - constructor.
    + constructor.
      * intro x. unfold L1_n3. apply Nat.le_refl.
      * intros x y Hxy Hyx. unfold L1_n3 in *.
        apply event_n3_eq_of_proj. apply key1_n3_inj. lia.
      * intros x y z Hxy Hyz. unfold L1_n3 in *. lia.
    + intros x y. unfold L1_n3. lia.
  - intros x y Hxy. unfold L1_n3. apply key1_n3_mono. exact Hxy.
Qed.

Lemma L2_n3_linext : IsLinearExtension (ep_order E_n3) L2_n3.
Proof.
  constructor.
  - constructor.
    + constructor.
      * intro x. unfold L2_n3. apply Nat.le_refl.
      * intros x y Hxy Hyx. unfold L2_n3 in *.
        apply event_n3_eq_of_proj. apply key2_n3_inj. lia.
      * intros x y z Hxy Hyz. unfold L2_n3 in *. lia.
    + intros x y. unfold L2_n3. lia.
  - intros x y Hxy. unfold L2_n3. apply key2_n3_mono. exact Hxy.
Qed.

(* ------------------------------------------------------------------ *)
(* Concrete events and their validity proofs                            *)
(* ------------------------------------------------------------------ *)

Lemma valid_a3 : In (nat*nat) (ValidSet (desugar sched_n3)) (0,0).
Proof. vm_compute. split; lia. Qed.
Lemma valid_b3 : In (nat*nat) (ValidSet (desugar sched_n3)) (0,1).
Proof. vm_compute. split; lia. Qed.
Lemma valid_c3 : In (nat*nat) (ValidSet (desugar sched_n3)) (1,0).
Proof. vm_compute. split; lia. Qed.
Lemma valid_d3 : In (nat*nat) (ValidSet (desugar sched_n3)) (1,1).
Proof. vm_compute. split; lia. Qed.
Lemma valid_e3 : In (nat*nat) (ValidSet (desugar sched_n3)) (2,0).
Proof. vm_compute. split; lia. Qed.
Lemma valid_f3 : In (nat*nat) (ValidSet (desugar sched_n3)) (2,1).
Proof. vm_compute. split; lia. Qed.

Definition ev_a3 : ep_carrier E_n3 := exist _ (0,0) valid_a3.
Definition ev_b3 : ep_carrier E_n3 := exist _ (0,1) valid_b3.
Definition ev_c3 : ep_carrier E_n3 := exist _ (1,0) valid_c3.
Definition ev_d3 : ep_carrier E_n3 := exist _ (1,1) valid_d3.
Definition ev_e3 : ep_carrier E_n3 := exist _ (2,0) valid_e3.
Definition ev_f3 : ep_carrier E_n3 := exist _ (2,1) valid_f3.

Lemma eq_ev_a3 : forall x : ep_carrier E_n3, proj1_sig x = (0,0) -> x = ev_a3.
Proof. intros x H. apply event_n3_eq_of_proj. exact H. Qed.
Lemma eq_ev_b3 : forall x : ep_carrier E_n3, proj1_sig x = (0,1) -> x = ev_b3.
Proof. intros x H. apply event_n3_eq_of_proj. exact H. Qed.
Lemma eq_ev_c3 : forall x : ep_carrier E_n3, proj1_sig x = (1,0) -> x = ev_c3.
Proof. intros x H. apply event_n3_eq_of_proj. exact H. Qed.
Lemma eq_ev_d3 : forall x : ep_carrier E_n3, proj1_sig x = (1,1) -> x = ev_d3.
Proof. intros x H. apply event_n3_eq_of_proj. exact H. Qed.
Lemma eq_ev_e3 : forall x : ep_carrier E_n3, proj1_sig x = (2,0) -> x = ev_e3.
Proof. intros x H. apply event_n3_eq_of_proj. exact H. Qed.
Lemma eq_ev_f3 : forall x : ep_carrier E_n3, proj1_sig x = (2,1) -> x = ev_f3.
Proof. intros x H. apply event_n3_eq_of_proj. exact H. Qed.

(* The direct hb-steps as concrete proofs. *)
Lemma hb_a_b3 : ep_order E_n3 ev_a3 ev_b3.
Proof.
  unfold ep_order, E_n3, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. left. split; reflexivity.
Qed.

Lemma hb_a_c3 : ep_order E_n3 ev_a3 ev_c3.
Proof.
  unfold ep_order, E_n3, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. right. exists 0.
  split; vm_compute; reflexivity.
Qed.

Lemma hb_c_d3 : ep_order E_n3 ev_c3 ev_d3.
Proof.
  unfold ep_order, E_n3, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. left. split; reflexivity.
Qed.

Lemma hb_d_f3 : ep_order E_n3 ev_d3 ev_f3.
Proof.
  unfold ep_order, E_n3, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. right. exists 1.
  split; vm_compute; reflexivity.
Qed.

Lemma hb_e_f3 : ep_order E_n3 ev_e3 ev_f3.
Proof.
  unfold ep_order, E_n3, exec_of_schedule, exec_of. simpl.
  apply rt_step. unfold edge. simpl. left. split; reflexivity.
Qed.

Lemma hb_a_d3 : ep_order E_n3 ev_a3 ev_d3.
Proof. eapply hb_trans. apply hb_a_c3. apply hb_c_d3. Qed.

Lemma hb_c_f3 : ep_order E_n3 ev_c3 ev_f3.
Proof. eapply hb_trans. apply hb_c_d3. apply hb_d_f3. Qed.

Lemma hb_a_f3 : ep_order E_n3 ev_a3 ev_f3.
Proof. eapply hb_trans. apply hb_a_d3. apply hb_d_f3. Qed.

(* ------------------------------------------------------------------ *)
(* The realizer: hb = L1_n3 ∩ L2_n3                                     *)
(* ------------------------------------------------------------------ *)

Lemma hb_n3_realizer :
  forall x y : ep_carrier E_n3,
    ep_order E_n3 x y <-> (L1_n3 x y /\ L2_n3 x y).
Proof.
  intros x y. split.
  - intro H. split.
    + apply key1_n3_mono. exact H.
    + apply key2_n3_mono. exact H.
  - intros [H1 H2]. unfold L1_n3, L2_n3 in H1, H2.
    pose proof (valid_event_n3_cases x) as Hx.
    pose proof (valid_event_n3_cases y) as Hy.
    simpl in Hx, Hy.
    destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]];
      [ rewrite (eq_ev_a3 x Hx) in *
      | rewrite (eq_ev_b3 x Hx) in *
      | rewrite (eq_ev_c3 x Hx) in *
      | rewrite (eq_ev_d3 x Hx) in *
      | rewrite (eq_ev_e3 x Hx) in *
      | rewrite (eq_ev_f3 x Hx) in * ];
      (destruct Hy as [Hy|[Hy|[Hy|[Hy|[Hy|Hy]]]]];
        [ rewrite (eq_ev_a3 y Hy) in *
        | rewrite (eq_ev_b3 y Hy) in *
        | rewrite (eq_ev_c3 y Hy) in *
        | rewrite (eq_ev_d3 y Hy) in *
        | rewrite (eq_ev_e3 y Hy) in *
        | rewrite (eq_ev_f3 y Hy) in * ]);
      vm_compute in H1, H2;
      try (exfalso; lia);
      (* surviving combos are the reflexive diagonal and the 8 strict hb pairs *)
      try (apply poset_refl);
      [ apply hb_a_b3
      | apply hb_a_c3
      | apply hb_a_d3
      | apply hb_a_f3
      | apply hb_c_d3
      | apply hb_c_f3
      | apply hb_d_f3
      | apply hb_e_f3 ].
Qed.

(* ------------------------------------------------------------------ *)
(* Incomparability of a and e                                          *)
(* ------------------------------------------------------------------ *)

Lemma incomp_a_e3 : Incomparable (ep_order E_n3) ev_a3 ev_e3.
Proof.
  unfold Incomparable. intros [Hae | Hea].
  - apply hb_n3_realizer in Hae. destruct Hae as [_ H2].
    unfold L2_n3 in H2. vm_compute in H2. lia.
  - apply hb_n3_realizer in Hea. destruct Hea as [H1 _].
    unfold L1_n3 in H1. vm_compute in H1. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem                                                         *)
(* ------------------------------------------------------------------ *)

Theorem E_n3_dim_2 : exec_has_dimension E_n3 2.
Proof.
  apply exec_dim_eq_2_of_realizer.
  - exists L1_n3, L2_n3. split; [exact L1_n3_linext|].
    split; [exact L2_n3_linext|]. exact hb_n3_realizer.
  - exists ev_a3, ev_e3. exact incomp_a_e3.
Qed.
