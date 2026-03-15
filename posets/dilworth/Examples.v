(** Examples demonstrating Dilworth's Theorem 
    
    This file shows how to use the Dilworth module to:
    1. Understand the key definitions (chains, antichains, covers)
    2. Apply Dilworth's theorem
    3. Use the corollaries and helper lemmas
*)

From Stdlib Require Import Ensembles Finite_sets Lia.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions WidthLowerBound WidthUpperBound DilworthTheorem.

(* ========================================================================= *)
(* Example 1: Understanding the Key Definitions                              *)
(* ========================================================================= *)

Section UnderstandingDefinitions.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.
  
  (* A chain is a set where any two elements are comparable *)
  Check @Definitions.IsChain.
  (*  IsChain : Ensemble A -> Prop *)
  
  (* An antichain is a set where any two distinct elements are incomparable *)
  Check @Definitions.IsAntichain.
  (*  IsAntichain : Ensemble A -> Prop *)
  
  (* A chain cover is a collection of disjoint chains covering all elements *)
  Check @Definitions.IsChainCover.
  (*  IsChainCover : Ensemble (Ensemble A) -> Prop *)
  
  (* Width is the size of the largest antichain *)
  Check @Definitions.Width.
  (*  Width : nat -> Type *)
  
  (* Chain cover number is the size of the smallest chain cover *)
  Check @Definitions.ChainCoverNumber.
  (*  ChainCoverNumber : nat -> Type *)
  
End UnderstandingDefinitions.

(* ========================================================================= *)
(* Example 2: Using Dilworth's Main Theorem                                  *)
(* ========================================================================= *)

Section ApplyingDilworth.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.
  
  (* The main theorem: width equals chain cover number *)
  Check @Dilworth.
  (*  Dilworth : forall w k : nat,
                 Width R w -> ChainCoverNumber R k -> w = k *)
  
  (* Example usage: If we can prove both width w and chain cover number k,
     then Dilworth tells us w = k *)
  Theorem my_poset_dilworth_application : 
    forall w k,
      Width R (Full_set A) w ->
      ChainCoverNumber R (Full_set A) k ->
      w = k.
  Proof.
    intros w k Hw Hk.
    apply (Dilworth R w k Hw Hk).
  Qed.
  
End ApplyingDilworth.

(* ========================================================================= *)
(* Example 3: Using the Corollaries                                          *)
(* ========================================================================= *)

Section UsingCorollaries.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.
  
  (* Corollary 1: If we know the width, we get a chain cover of that size *)
  Check @dilworth_width_equals_cover.
  (*  dilworth_width_equals_cover : forall w : nat,
                                      Width R w -> ChainCoverNumber R w *)
  
  Example construct_cover_from_width : 
    forall w,
      Width R (Full_set A) w ->
      ChainCoverNumber R (Full_set A) w.
  Proof.
    intros w Hw.
    apply (dilworth_width_equals_cover R w Hw).
  Qed.
  
  (* Corollary 2: Width and chain cover determine each other *)
  Check @width_determines_cover_size.
  (*  width_determines_cover_size : 
        forall w : nat, Width R w ->
        forall (cover : Ensemble (Ensemble A)) (k : nat),
        IsSmallestChainCover R cover k -> w = k *)
  
End UsingCorollaries.

(* ========================================================================= *)
(* Example 4: Using the Fundamental Bounds                                   *)
(* ========================================================================= *)

Section FundamentalBounds.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.
  
  (* DilworthA: Any antichain size ≤ any chain cover size *)
  Check @DilworthA.
  (*  DilworthA : forall (cover : Ensemble (Ensemble A)) 
                         (la : Ensemble A) (k w : nat),
                    IsChainCover R (Full_set A) cover ->
                    IsAntichain R la ->
                    cardinal (Ensemble A) cover k ->
                    cardinal A la w ->
                    w <= k *)
  
  (* This gives us a lower bound on chain cover size *)
  Lemma antichain_bounds_cover : 
    forall (antichain : Ensemble A) (cover : Ensemble (Ensemble A)) (w k : nat),
      IsAntichain R antichain ->
      IsChainCover R (Full_set A) cover ->
      cardinal A antichain w ->
      cardinal (Ensemble A) cover k ->
      w <= k.
  Proof.
    intros antichain cover w k Ha Hc Hw Hk.
    apply (DilworthA R (Full_set A) cover antichain k w Hc Ha (fun x _ => Full_intro A x) Hk Hw).
  Qed.
  
  (* DilworthB: From any largest antichain, we can construct a chain cover *)
  Check @DilworthB.
  (*  DilworthB : forall (la : Ensemble A) (w : nat),
                    IsLargestAntichain R la w ->
                    { cover : Ensemble (Ensemble A) |
                      IsChainCover R (Full_set A) cover /\ cardinal (Ensemble A) cover w } *)
  
  (* This gives us an upper bound on chain cover size *)
  Lemma width_gives_cover : 
    forall (la : Ensemble A) (w : nat),
      IsLargestAntichain R (Full_set A) la w ->
      { cover : Ensemble (Ensemble A) | 
        IsChainCover R (Full_set A) cover /\ 
        cardinal (Ensemble A) cover w }.
  Proof.
    intros la w Hla.
    apply (DilworthB R w la Hla).
  Qed.
  
End FundamentalBounds.

(* ========================================================================= *)
(* Example 5: Practical Workflow for Proving Width                          *)
(* ========================================================================= *)

Section PracticalWorkflow.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.
  
  (* To prove a poset has width w:
     
     Step 1: Construct an antichain of size w
     Step 2: Prove it's an antichain
     Step 3: Construct a chain cover of size w  
     Step 4: Prove it's a chain cover
     Step 5: Prove your antichain is largest (any other antichain has size ≤ w)
     Step 6: Prove your chain cover is smallest (any other cover has size ≥ w)
     Step 7: Apply Dilworth's theorem
     
     The beauty of Dilworth: Steps 5 and 6 verify each other!
     - If you have an antichain of size w and a chain cover of size w,
       then by DilworthA, no antichain can be larger than w
       and by DilworthB, no chain cover can be smaller than w
  *)
  
  (* Suppose we have both constructions *)
  Variable my_antichain : Ensemble A.
  Variable my_cover : Ensemble (Ensemble A).
  Variable w : nat.
  
  Hypothesis antichain_is_antichain : IsAntichain R my_antichain.
  Hypothesis antichain_has_size_w : cardinal A my_antichain w.
  
  Hypothesis cover_is_cover : IsChainCover R (Full_set A) my_cover.
  Hypothesis cover_has_size_w : cardinal (Ensemble A) my_cover w.
  
  (* Then we can prove both optimality conditions *)
  Lemma antichain_is_largest : 
    forall s n,
      IsAntichain R s ->
      Included A s (Full_set A) ->
      cardinal A s n ->
      n <= w.
  Proof.
    intros s n Hs Hincl Hn.
    (* Use DilworthA with our cover *)
    apply (DilworthA R (Full_set A) my_cover s w n);
      assumption.
  Qed.
  
  Lemma cover_is_smallest : 
    forall cv n,
      IsChainCover R (Full_set A) cv ->
      cardinal (Ensemble A) cv n ->
      w <= n.
  Proof.
    intros cv n Hcv Hn.
    (* Use DilworthA with our antichain *)
    apply (DilworthA R (Full_set A) cv my_antichain n w Hcv antichain_is_antichain (fun x _ => Full_intro A x) Hn antichain_has_size_w).
  Qed.
  
  (* Therefore, we can prove width = w *)
  Theorem proved_width : Width R (Full_set A) w.
  Proof.
    refine {| width_la := my_antichain |}.
    constructor; [exact antichain_is_antichain | exact (fun x _ => Full_intro A x) | exact antichain_has_size_w | apply antichain_is_largest].
  Qed.
  
  (* And chain cover number = w *)
  Theorem proved_chain_cover_number : ChainCoverNumber R (Full_set A) w.
  Proof.
    refine {| cover_number_cover := my_cover |}.
    constructor; [exact cover_is_cover | exact cover_has_size_w | apply cover_is_smallest].
  Qed.
  
  Variable n : nat.
  Hypothesis full_set_has_size_n : cardinal A (Full_set A) n.
  
  (* And they are equal by Dilworth *)
  Theorem width_equals_cover_number : w = w.
  Proof.
    apply (Dilworth R n w w full_set_has_size_n proved_width proved_chain_cover_number).
  Qed.
  
End PracticalWorkflow.
