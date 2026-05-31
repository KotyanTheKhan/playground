(* ordinal-sum decomposition of executions *)

From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimCriticalPairs Frontier.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* Execution order restricted to a sub-ensemble S — a sub-poset. *)
Definition sub_order (E : ExecPoset) (S : Ensemble (ep_carrier E))
  : {x : ep_carrier E | Ensembles.In _ S x} -> {x | Ensembles.In _ S x} -> Prop :=
  fun x y => ep_order E (proj1_sig x) (proj1_sig y).

Instance sub_order_poset (E : ExecPoset) (S : Ensemble (ep_carrier E))
  : IsPoset _ (sub_order E S) := subtype_is_poset (ep_order E) S.

Definition no_alt_cycle (A : Type) (R : A -> A -> Prop) : Prop :=
  ~ (exists cycle,
       (forall p, List.In p cycle -> IsCriticalPair R (fst p) (snd p))
       /\ IsAlternatingCycle R cycle).

(* A poset's dimension is unique. *)
Lemma posdim_unique :
  forall (A : Type) (R : A -> A -> Prop) `{IsPoset A R} d d',
    PosetDimension R d -> PosetDimension R d' -> d = d'.
Proof.
  intros A R HP d d' Hd Hd'.
  apply Nat.le_antisymm.
  - apply (dimension_is_minimum Hd (dimension_realizer Hd')
             d' (dimension_is_realizer Hd') (dimension_cardinality Hd')).
  - apply (dimension_is_minimum Hd' (dimension_realizer Hd)
             d (dimension_is_realizer Hd) (dimension_cardinality Hd)).
Qed.

Lemma barrier_critical_pairs :
  forall E L U, IsBarrier E L U ->
    forall x y, IsCriticalPair (ep_order E) x y ->
      (Ensembles.In _ L x /\ Ensembles.In _ L y) \/
      (Ensembles.In _ U x /\ Ensembles.In _ U y).
Proof.
  intros E L U HB x y Hcp.
  assert (Hinc : Incomparable (ep_order E) x y) by exact Hcp.(critical_incomparable).
  unfold Incomparable in Hinc.
  destruct HB as [Hcov [_ [_ [_ Hbelow]]]].
  destruct (Hcov x) as [HxL | HxU]; destruct (Hcov y) as [HyL | HyU].
  - left. split; assumption.
  - exfalso. apply Hinc. left. apply Hbelow; assumption.
  - exfalso. apply Hinc. right. apply Hbelow; assumption.
  - right. split; assumption.
Qed.

Lemma barrier_dim_ge :
  forall E L U, IsBarrier E L U ->
    forall dL dU d,
      PosetDimension (sub_order E L) dL ->
      PosetDimension (sub_order E U) dU ->
      PosetDimension (ep_order E) d ->
      Nat.max dL dU <= d.
Proof.
  intros E L U HB dL dU d HdimL HdimU Hd.
  (* L block *)
  destruct (subposet_dimension_le (ep_order E) L d Hd)
    as [d_qL [HdimL_inh HleL]].
  destruct HdimL_inh as [HdimL_q].
  assert (HeqL : dL = d_qL)
    by exact (posdim_unique _ (sub_order E L) dL d_qL HdimL HdimL_q).
  (* U block *)
  destruct (subposet_dimension_le (ep_order E) U d Hd)
    as [d_qU [HdimU_inh HleU]].
  destruct HdimU_inh as [HdimU_q].
  assert (HeqU : dU = d_qU)
    by exact (posdim_unique _ (sub_order E U) dU d_qU HdimU HdimU_q).
  lia.
Qed.

(* The ensemble of critical pairs of a poset [R], as an [Ensemble (_ * _)]. *)
Definition S_cp {A : Type} (R : A -> A -> Prop) : Ensemble (A * A) :=
  fun p => IsCriticalPair R (fst p) (snd p).

(* A whole-poset critical pair lying entirely inside a sub-ensemble [S]
   restricts to a critical pair of the induced sub-poset. *)
Lemma critical_pair_in_block :
  forall E (S : Ensemble (ep_carrier E)) x y
         (Hx : Ensembles.In _ S x) (Hy : Ensembles.In _ S y),
    IsCriticalPair (ep_order E) x y ->
    IsCriticalPair (sub_order E S) (exist _ x Hx) (exist _ y Hy).
Proof.
  intros E S x y Hx Hy Hcp.
  constructor.
  - (* critical_incomparable *)
    unfold Incomparable, sub_order. simpl.
    exact Hcp.(critical_incomparable).
  - (* critical_down *)
    intros a HStrict.
    destruct a as [a Ha].
    destruct HStrict as [HRax Hane].
    unfold sub_order in *. simpl in *.
    apply (Hcp.(critical_down) a).
    split.
    + exact HRax.
    + intro Heq. apply Hane. subst a. f_equal. apply proof_irrelevance.
  - (* critical_up *)
    intros b HStrict.
    destruct b as [b Hb].
    destruct HStrict as [HRyb Hyne].
    unfold sub_order in *. simpl in *.
    apply (Hcp.(critical_up) b).
    split.
    + exact HRyb.
    + intro Heq. apply Hyne. subst b. f_equal. apply proof_irrelevance.
Qed.

Lemma barrier_no_alt_cycle_propagation :
  forall E L U, IsBarrier E L U ->
    no_alt_cycle _ (sub_order E L) ->
    no_alt_cycle _ (sub_order E U) ->
    no_alt_cycle _ (ep_order E).
Proof.
  intros E L U HB HnL HnU.
  (* Destructure the barrier. *)
  pose proof HB as HB'.
  destruct HB' as [Hcov [Hdisj [HinhL [HinhU Hbelow]]]].
  (* Block reversers from the two no-alt-cycle hypotheses. *)
  assert (HrevL :
    exists Lr, IsLinearExtension (sub_order E L) Lr /\
      forall x y, Ensembles.In _ (S_cp (sub_order E L)) (x, y) -> Lr y x).
  { apply (critical_pairs_reversible_iff_no_alternating_cycle
             (sub_order E L) (S_cp (sub_order E L)) (fun p H => H)).
    exact HnL. }
  assert (HrevU :
    exists Lr, IsLinearExtension (sub_order E U) Lr /\
      forall x y, Ensembles.In _ (S_cp (sub_order E U)) (x, y) -> Lr y x).
  { apply (critical_pairs_reversible_iff_no_alternating_cycle
             (sub_order E U) (S_cp (sub_order E U)) (fun p H => H)).
    exact HnU. }
  destruct HrevL as [LL_rel [LL HLL]].
  destruct HrevU as [LU_rel [LU HLU]].
  (* The whole-poset reverser. *)
  pose (P := fun x y : ep_carrier E =>
       (exists (Hx : Ensembles.In _ L x)(Hy : Ensembles.In _ L y),
            LL_rel (exist _ x Hx) (exist _ y Hy))
    \/ (exists (Hx : Ensembles.In _ U x)(Hy : Ensembles.In _ U y),
            LU_rel (exist _ x Hx) (exist _ y Hy))
    \/ (Ensembles.In _ L x /\ Ensembles.In _ U y)).
  (* Convenience: the block reversers are posets. *)
  pose proof (LL.(linear_is_total).(total_is_poset)) as HLLpos.
  pose proof (LU.(linear_is_total).(total_is_poset)) as HLUpos.
  (* --- IsLinearExtension (ep_order E) P --- *)
  assert (HposP : IsPoset _ P).
  { constructor.
        * (* refl *)
          intro x. destruct (Hcov x) as [HxL | HxU].
          -- left. exists HxL, HxL.
             exact (HLLpos.(poset_refl) (exist _ x HxL)).
          -- right; left. exists HxU, HxU.
             exact (HLUpos.(poset_refl) (exist _ x HxU)).
        * (* antisym *)
          intros x y Hxy Hyx.
          destruct Hxy as [ [HxL [HyL HLxy]] | [ [HxU [HyU HUxy]] | [HxL HyU] ] ];
          destruct Hyx as [ [HyL' [HxL' HLyx]] | [ [HyU' [HxU' HUyx]] | [HyL' HxU'] ] ].
          -- (* both L both directions *)
             assert (Heq : exist (fun z => Ensembles.In _ L z) x HxL
                         = exist _ y HyL).
             { apply (HLLpos.(poset_antisym)).
               - exact HLxy.
               - (* need LL_rel (exist y HyL)(exist x HxL); have HLyx with HyL' HxL' *)
                 rewrite (proof_irrelevance _ HyL HyL').
                 rewrite (proof_irrelevance _ HxL HxL').
                 exact HLyx. }
             exact (f_equal (@proj1_sig _ _) Heq).
          -- (* L-direction and U-direction: x∈L,y∈L and y∈U,x∈U → Hdisj *)
             exfalso. apply (Hdisj x). split; assumption.
          -- (* x∈L,y∈L and third (y∈L,x∈U) → Hdisj x *)
             exfalso. apply (Hdisj x). split; assumption.
          -- (* x∈U,y∈U and L-direction (y∈L,x∈L) → Hdisj x *)
             exfalso. apply (Hdisj x). split; assumption.
          -- (* both U both directions *)
             assert (Heq : exist (fun z => Ensembles.In _ U z) x HxU
                         = exist _ y HyU).
             { apply (HLUpos.(poset_antisym)).
               - exact HUxy.
               - rewrite (proof_irrelevance _ HyU HyU').
                 rewrite (proof_irrelevance _ HxU HxU').
                 exact HUyx. }
             exact (f_equal (@proj1_sig _ _) Heq).
          -- (* x∈U,y∈U and third (y∈L,x∈U) → Hdisj y *)
             exfalso. apply (Hdisj y). split; assumption.
          -- (* third (x∈L,y∈U) and L-direction (y∈L,x∈L) → Hdisj y *)
             exfalso. apply (Hdisj y). split; assumption.
          -- (* third (x∈L,y∈U) and U-direction (y∈U,x∈U) → Hdisj x *)
             exfalso. apply (Hdisj x). split; assumption.
          -- (* third both ways: x∈L,y∈U and y∈L,x∈U → Hdisj x *)
             exfalso. apply (Hdisj x). split; assumption.
        * (* trans *)
          intros x y z Hxy Hyz.
          destruct Hxy as [ [HxL [HyL HLxy]] | [ [HxU [HyU HUxy]] | [HxL HyU] ] ];
          destruct Hyz as [ [HyL' [HzL HLyz]] | [ [HyU' [HzU HUyz]] | [HyL' HzU] ] ].
          -- (* L,L → L *)
             left. exists HxL, HzL.
             rewrite (proof_irrelevance _ HyL' HyL) in HLyz.
             exact (HLLpos.(poset_trans) _ _ _ HLxy HLyz).
          -- (* x,y∈L ; y∈U,z∈U → Hdisj y *)
             exfalso. apply (Hdisj y). split; assumption.
          -- (* x,y∈L ; y∈L,z∈U → third *)
             right; right. split; assumption.
          -- (* x,y∈U ; y,z∈L → Hdisj y *)
             exfalso. apply (Hdisj y). split; assumption.
          -- (* U,U → U *)
             right; left. exists HxU, HzU.
             rewrite (proof_irrelevance _ HyU' HyU) in HUyz.
             exact (HLUpos.(poset_trans) _ _ _ HUxy HUyz).
          -- (* x,y∈U ; y∈L,z∈U → Hdisj y *)
             exfalso. apply (Hdisj y). split; assumption.
          -- (* x∈L,y∈U ; y,z∈L → Hdisj y *)
             exfalso. apply (Hdisj y). split; assumption.
          -- (* x∈L,y∈U ; y,z∈U → third *)
             right; right. split; assumption.
          -- (* x∈L,y∈U ; y∈L,z∈U → Hdisj y *)
             exfalso. apply (Hdisj y). split; assumption. }
  assert (HtotP : IsTotalOrder P).
  { refine {| total_is_poset := HposP; total_comparable := _ |}.
        intros x y.
        destruct (Hcov x) as [HxL | HxU]; destruct (Hcov y) as [HyL | HyU].
        * destruct (LL.(linear_is_total).(total_comparable)
                      (exist _ x HxL) (exist _ y HyL)) as [Hc | Hc].
          -- left. left. exists HxL, HyL. exact Hc.
          -- right. left. exists HyL, HxL. exact Hc.
        * left. right; right. split; assumption.
        * right. right; right. split; assumption.
        * destruct (LU.(linear_is_total).(total_comparable)
                      (exist _ x HxU) (exist _ y HyU)) as [Hc | Hc].
          -- left. right; left. exists HxU, HyU. exact Hc.
          -- right. right; left. exists HyU, HxU. exact Hc. }
  assert (HlinP : IsLinearExtension (ep_order E) P).
  { refine {| linear_is_total := HtotP; linear_extends := _ |}.
      intros x y Hxy.
      destruct (Hcov x) as [HxL | HxU]; destruct (Hcov y) as [HyL | HyU].
      + left. exists HxL, HyL.
        exact (LL.(linear_extends) (exist _ x HxL) (exist _ y HyL) Hxy).
      + right; right. split; assumption.
      + (* x∈U, y∈L, ep_order E x y → contradiction *)
        exfalso. exact (barrier_upper_disjoint_below E L U HB x y HxU HyL Hxy).
      + right; left. exists HxU, HyU.
        exact (LU.(linear_extends) (exist _ x HxU) (exist _ y HyU) Hxy). }
  (* --- P reverses every whole critical pair --- *)
  assert (HrevP : forall x y, Ensembles.In _ (S_cp (ep_order E)) (x, y) -> P y x).
  { intros x y Hcp. unfold S_cp, Ensembles.In in Hcp. simpl in Hcp.
    destruct (barrier_critical_pairs E L U HB x y Hcp) as [[HxL HyL] | [HxU HyU]].
    - (* within L *)
      left. exists HyL, HxL.
      apply HLL.
      unfold S_cp, Ensembles.In. simpl.
      exact (critical_pair_in_block E L x y HxL HyL Hcp).
    - (* within U *)
      right; left. exists HyU, HxU.
      apply HLU.
      unfold S_cp, Ensembles.In. simpl.
      exact (critical_pair_in_block E U x y HxU HyU Hcp). }
  (* Conclude no alternating cycle for the whole poset. *)
  apply (critical_pairs_reversible_iff_no_alternating_cycle
           (ep_order E) (S_cp (ep_order E)) (fun p H => H)).
  exists P. split.
  - exact HlinP.
  - exact HrevP.
Qed.

Lemma barrier_dim2 :
  forall E L U, IsBarrier E L U ->
    no_alt_cycle _ (sub_order E L) ->
    no_alt_cycle _ (sub_order E U) ->
    exists d, exec_has_dimension E d /\ d <= 2.
Proof.
  intros E L U HB HnL HnU.
  apply exec_dim_le_2_of_no_alt_cycle.
  pose proof (barrier_no_alt_cycle_propagation E L U HB HnL HnU) as Hno.
  unfold no_alt_cycle in Hno.
  intro Hex. apply Hno.
  destruct Hex as [cycle [Hin Halt]].
  exists cycle. split; [| exact Halt].
  intros p Hp. unfold exec_critical_pair in Hin. exact (Hin p Hp).
Qed.
