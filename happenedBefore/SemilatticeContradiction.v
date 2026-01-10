(* Proof that happened_before is NOT a semilattice *)
Require Import EventStructure.
Require Import CausalRelation.
Require Import Posets.PosetClasses.
Require Import LatticeOperations.

(* 
  We want to show that there exists a history h (specifically nil) 
  and two events e1, e2 such that they have NO greatest lower bound.
*)

Lemma hb_nil_implies_same_process : forall e1 e2,
  happened_before nil e1 e2 -> process e1 = process e2.
Proof.
  intros e1 e2 H.
  remember nil as h.
  induction H.
  - (* hb_refl *) reflexivity.
  - (* hb_message *)
    subst. destruct H as [m [Hin _]]. inversion Hin.
  - (* hb_trans *)
    subst. transitivity (process e2); auto.
Qed.

Lemma no_lower_bound_for_distinct_processes : forall e1 e2 x,
  process e1 <> process e2 ->
  happened_before nil x e1 ->
  happened_before nil x e2 ->
  False.
Proof.
  intros e1 e2 x Hneq H1 H2.
  apply hb_nil_implies_same_process in H1.
  apply hb_nil_implies_same_process in H2.
  rewrite <- H1 in Hneq.
  rewrite <- H2 in Hneq.
  apply Hneq. reflexivity.
Qed.

Definition is_glb (R : Event -> Event -> Prop) (x y m : Event) : Prop :=
  R m x /\ R m y /\ forall z, R z x -> R z y -> R z m.

Definition is_meet_semilattice_poset (R : Event -> Event -> Prop) : Prop :=
  forall x y, exists m, is_glb R x y m.

Theorem happened_before_not_poset_semilattice :
  ~ is_meet_semilattice_poset (happened_before nil).
Proof.
  intro H.
  unfold is_meet_semilattice_poset in H.
  (* Take e1=<0> and e2=<1> *)
  let e1 := constr:(⟨0⟩) in
  let e2 := constr:(⟨1⟩) in
  destruct (H e1 e2) as [m [Hm1 [Hm2 Hgreatest]]].
  
  (* m must be <= e1 and m <= e2 *)
  (* In nil history, m <= e1 => process m = process e1 = 0 *)
  apply hb_nil_implies_same_process in Hm1.
  (* In nil history, m <= e2 => process m = process e2 = 1 *)
  apply hb_nil_implies_same_process in Hm2.
  
  (* Contradiction: 0 = process m = 1 *)
  rewrite Hm1 in Hm2.
  simpl in Hm2.
  discriminate.
Qed.

Theorem happened_before_cannot_be_meet_semilattice_instance :
  forall (meet : Event -> Event -> Event),
  IsMeetSemilattice Event meet ->
  (forall x y, is_glb (happened_before nil) x y (meet x y)) ->
  False.
Proof.
  intros meet H_inst H_glb.
  apply happened_before_not_poset_semilattice.
  unfold is_meet_semilattice_poset.
  intros x y.
  exists (meet x y).
  apply H_glb.
Qed.

Theorem lex_meet_not_causal_glb :
  ~ (forall x y, is_glb (happened_before nil) x y (lex_meet nil x y)).
Proof.
  intro H.
  (* Use the same counterexample *)
  let e1 := constr:(⟨0⟩) in
  let e2 := constr:(⟨1⟩) in
  specialize (H e1 e2).
  destruct H as [H1 [H2 _]].
  (* lex_meet nil e1 e2 = e1 because 0 < 1 *)
  (* So H2 says e1 <= e2 *)
  (* But e1 <= e2 implies process e1 = process e2, which is 0 = 1, contradiction *)
  apply hb_nil_implies_same_process in H2.
  simpl in H2.
  discriminate.
Qed.

(* ========== Join Semilattice Impossibility ========== *)

Definition is_lub (R : Event -> Event -> Prop) (x y j : Event) : Prop :=
  R x j /\ R y j /\ forall z, R x z -> R y z -> R j z.

Definition is_join_semilattice_poset (R : Event -> Event -> Prop) : Prop :=
  forall x y, exists j, is_lub R x y j.

Theorem happened_before_not_join_semilattice_poset :
  ~ is_join_semilattice_poset (happened_before nil).
Proof.
  intro H.
  unfold is_join_semilattice_poset in H.
  (* Take e1=<0> and e2=<1> *)
  let e1 := constr:(⟨0⟩) in
  let e2 := constr:(⟨1⟩) in
  destruct (H e1 e2) as [j [Hj1 [Hj2 Hleast]]].
  
  (* e1 <= j and e2 <= j *)
  (* In nil history, e1 <= j => process e1 = process j = 0 *)
  apply hb_nil_implies_same_process in Hj1.
  (* In nil history, e2 <= j => process e2 = process j = 1 *)
  apply hb_nil_implies_same_process in Hj2.
  
  (* Contradiction: 0 = process j = 1 *)
  rewrite <- Hj1 in Hj2.
  simpl in Hj2.
  discriminate.
Qed.

Theorem happened_before_cannot_be_join_semilattice_instance :
  forall (join : Event -> Event -> Event),
  IsJoinSemilattice Event join ->
  (forall x y, is_lub (happened_before nil) x y (join x y)) ->
  False.
Proof.
  intros join H_inst H_lub.
  apply happened_before_not_join_semilattice_poset.
  unfold is_join_semilattice_poset.
  intros x y.
  exists (join x y).
  apply H_lub.
Qed.

Theorem lex_join_not_causal_lub :
  ~ (forall x y, is_lub (happened_before nil) x y (lex_join nil x y)).
Proof.
  intro H.
  (* Use the same counterexample *)
  let e1 := constr:(⟨0⟩) in
  let e2 := constr:(⟨1⟩) in
  specialize (H e1 e2).
  destruct H as [H1 [H2 _]].
  (* lex_join nil e1 e2 = e2 because 0 < 1 *)
  (* So H1 says e1 <= e2 *)
  (* But e1 <= e2 implies process e1 = process e2, which is 0 = 1, contradiction *)
  apply hb_nil_implies_same_process in H1.
  simpl in H1.
  discriminate.
Qed.

(* ========== Lattice Impossibility ========== *)

Theorem happened_before_cannot_be_lattice_instance :
  forall (meet join : Event -> Event -> Event)
  (H_meet : IsMeetSemilattice Event meet)
  (H_join : IsJoinSemilattice Event join),
  IsLattice Event meet join ->
  (forall x y, is_glb (happened_before nil) x y (meet x y)) ->
  False.
Proof.
  intros meet join H_meet H_join H_lat H_glb.
  eapply (@happened_before_cannot_be_meet_semilattice_instance meet H_meet).
  exact H_glb.
Qed.

(* ========== Distributive Lattice Impossibility ========== *)

Theorem happened_before_cannot_be_distributive_lattice_instance :
  forall (meet join : Event -> Event -> Event)
  (H_meet : IsMeetSemilattice Event meet)
  (H_join : IsJoinSemilattice Event join)
  (H_lat : IsLattice Event meet join),
  IsDistributiveLattice Event meet join ->
  (forall x y, is_glb (happened_before nil) x y (meet x y)) ->
  False.
Proof.
  intros meet join H_meet H_join H_lat H_dist H_glb.
  eapply (@happened_before_cannot_be_meet_semilattice_instance meet H_meet).
  exact H_glb.
Qed.
