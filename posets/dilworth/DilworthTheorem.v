From Stdlib Require Import Lia Ensembles Finite_sets.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions WidthLowerBound WidthUpperBound.

Section DilworthTheorem.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* Width and ChainCoverNumber are now classes from Definitions.v *)

  (* ========================================================================= *)
  (* Main Theorem                                                              *)
  (* ========================================================================= *)

  Theorem Dilworth : forall (n w k : nat),
    cardinal A (Full_set A) n ->
    Width R (Full_set A) w ->
    ChainCoverNumber R (Full_set A) k ->
    w = k.
  Proof.
    intros n w k Hcard_n Hw Hk.
    destruct Hw as [la Hla].
    destruct Hk as [cover Hcc_smallest].
    
    (* Use DilworthA to show w <= k *)
    assert (Hw_le_k : w <= k).
    {
      destruct Hla as [Hanti Hincl_la Hcard_w Hmax_anti].
      destruct Hcc_smallest as [Hcc Hcard_k Hmin_cover].
      apply (DilworthA R (Full_set A) cover la k w Hcc Hanti Hincl_la Hcard_k Hcard_w).
    }
    
    (* Use DilworthB to show k <= w *)
    assert (Hk_le_w : k <= w).
    {
      (* By DilworthB, there exists a chain cover of size w *)
      destruct (DilworthB R n (Full_set A) w la Hcard_n Hla) as [cover_w [Hcc_w Hcard_cover_w]].
      (* Since cover is the smallest, k <= w *)
      destruct Hcc_smallest as [_ _ Hmin_cover].
      apply (Hmin_cover cover_w w Hcc_w Hcard_cover_w).
    }
    
    (* Combine both directions *)
    lia.
  Qed.

  (* ========================================================================= *)
  (* Corollaries and Alternative Formulations                                  *)
  (* ========================================================================= *)

  (** Alternative formulation: Width and chain cover number are equal *)
  Corollary dilworth_width_equals_cover : forall n w,
    cardinal A (Full_set A) n ->
    Width R (Full_set A) w ->
    ChainCoverNumber R (Full_set A) w.
  Proof.
    intros n w Hcard_n [la Hla].
    destruct (DilworthB R n (Full_set A) w la Hcard_n Hla) as [cover [Hcc Hcard]].
    refine {| cover_number_cover := cover |}.
    constructor.
    - exact Hcc.
    - exact Hcard.
    - intros cv k Hcv Hcard_cv.
      destruct Hla as [Hanti Hincl_la Hcard_w Hmax].
      apply (DilworthA R (Full_set A) cv la k w Hcv Hanti Hincl_la Hcard_cv Hcard_w).
  Qed.

  (** If we know the width, we can compute the minimum chain cover size *)
  Corollary width_determines_cover_size : forall n w,
    cardinal A (Full_set A) n ->
    Width R (Full_set A) w ->
    forall cover k, IsSmallestChainCover R (Full_set A) cover k -> w = k.
  Proof.
    intros n w Hcard_n Hw cover k Hsmallest.
    eapply Dilworth.
    - exact Hcard_n.
    - exact Hw.
    - exists cover. exact Hsmallest.
  Qed.

End DilworthTheorem.
