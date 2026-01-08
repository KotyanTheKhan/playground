(* Poset instance for lists *)
Require Import Posets.PosetClasses.
From List Require Import Structure.
From List Require Import Operations.
Require Import Helpers.
From Stdlib Require Import Lia.

Instance list_poset : IsPoset List list_le.
Proof.
  constructor.
  - (* reflexivity *)
    unfold list_le.
    (* This unfolds to: length l < length l \/ (length l = length l /\ list_lex_le l l) *)
    
    intros l.
    (* Introduce the arbitrary list l *)
    
    right.
    (* Choose the right side of OR, since length l < length l is false *)
    
    split.
    (* Split the conjunction: need to prove length l = length l AND list_lex_le l l *)
    
    + (* length_List l = length_List l *)
      reflexivity.
      (* Trivial by reflexivity of equality *)
      
    + (* list_lex_le l l *)
      induction l as [| a l' IH].
      (* Induction on list structure for lexicographic reflexivity *)
      
      * (* Base case: Nil *)
        simpl.
        (* After simpl, goal is True *)
        trivial.
        (* True is trivially provable *)
        
      * (* Inductive case: Cons a l' *)
        simpl.
        (* After simpl, goal is: a < a \/ (a = a /\ list_lex_le l' l') *)
        
        right.
        (* Choose right side since a < a is false *)
        
        split.
        (* Split into a = a and list_lex_le l' l' *)
        
        -- (* a = a *)
           reflexivity.
           
        -- (* list_lex_le l' l' *)
           apply IH.
           (* Use inductive hypothesis *)
           
  - (* antisymmetry *)
    unfold list_le.
    (* Unfold: length l1 < length l2 \/ (length l1 = length l2 /\ list_lex_le l1 l2) *)
    
    intros l1 l2 H12 H21.
    (* H12: l1 ≤ l2, H21: l2 ≤ l1 *)
    
    destruct H12 as [Hlt12 | [Heq12 Hlex12]].
    (* Case analysis on H12: either length l1 < length l2, or equal with lex order *)
    
    + (* Case: length l1 < length l2 *)
      destruct H21 as [Hlt21 | [Heq21 Hlex21]].
      (* Case analysis on H21 *)
      
      * (* Subcase: length l2 < length l1 *)
        (* Contradiction: l1 < l2 and l2 < l1 *)
        lia.
        
      * (* Subcase: length l2 = length l1 *)
        (* Contradiction: l1 < l2 and l2 = l1 implies l1 < l1 *)
        lia.
        
    + (* Case: length l1 = length l2 /\ list_lex_le l1 l2 *)
      destruct H21 as [Hlt21 | [Heq21 Hlex21]].
      (* Case analysis on H21 *)
      
      * (* Subcase: length l2 < length l1 *)
        (* Contradiction: l1 = l2 and l2 < l1 *)
        lia.
        
      * (* Subcase: length l2 = length l1 /\ list_lex_le l2 l1 *)
        (* Now: lengths equal and both lexicographic orders hold *)
        (* Need to prove l1 = l2 by lexicographic antisymmetry *)
        
        clear Heq21.
        (* Clean up: Heq21 is symmetric to Heq12 *)
        
        generalize dependent l2.
        (* Prepare for induction on l1 *)
        
        induction l1 as [| a1 l1' IH].
        (* Induction on l1 structure *)
        
        -- (* Base case: l1 = Nil *)
           intros l2 Heq12 Hlex12 Hlex21.
           destruct l2 as [| a2 l2'].
           
           ++ (* l2 = Nil *)
              reflexivity.
              (* Nil = Nil *)
              
           ++ (* l2 = Cons a2 l2' - impossible *)
              simpl in Heq12.
              (* 0 = S (length l2') is contradictory *)
              discriminate.
              
        -- (* Inductive case: l1 = Cons a1 l1' *)
           intros l2 Heq12 Hlex12 Hlex21.
           destruct l2 as [| a2 l2'].
           
           ++ (* l2 = Nil - impossible *)
              simpl in Heq12.
              (* S (length l1') = 0 is contradictory *)
              discriminate.
              
           ++ (* l2 = Cons a2 l2' *)
              (* Both lists are Cons, need to show heads and tails equal *)
              (* Hlex12: list_lex_le (Cons a1 l1') (Cons a2 l2') *)
              (* Hlex21: list_lex_le (Cons a2 l2') (Cons a1 l1') *)
              
              assert (Hlex12_orig := Hlex12).
              assert (Hlex21_orig := Hlex21).
              (* Save copies before simpl changes them *)
              
              simpl in Hlex12.
              (* Simplify: becomes a1 < a2 \/ (a1 = a2 /\ list_lex_le l1' l2') *)
              
              simpl in Hlex21.
              (* Simplify: becomes a2 < a1 \/ (a2 = a1 /\ list_lex_le l2' l1') *)
              
              destruct Hlex12 as [Hlt12 | [Heq_a Hlex12']].
              (* Case split on lexicographic comparison of l1 to l2 *)
              
              ** (* Case: a1 < a2 *)
                 destruct Hlex21 as [Hlt21 | [Heq_a' Hlex21']].
                 
                 +++ (* a1 < a2 and a2 < a1 - impossible *)
                     lia.
                     
                 +++ (* a1 < a2 and a2 = a1 - impossible *)
                     subst.
                     (* Substitute a2 = a1, then a1 < a1 *)
                     lia.
                     
              ** (* Case: a1 = a2 /\ list_lex_le l1' l2' *)
                 destruct Hlex21 as [Hlt21 | [Heq_a' Hlex21']].
                 
                 +++ (* a1 = a2 and a2 < a1 - impossible *)
                     subst.
                     (* Substitute a1 = a2, then a2 < a2 *)
                     lia.
                     
                 +++ (* a1 = a2 and a2 = a1 - both heads equal *)
                     f_equal.
                     (* Prove Cons a1 l1' = Cons a2 l2' by constructor equality *)
                     
                     *** (* Show a1 = a2 *)
                         assumption.
                         (* We have Heq_a: a1 = a2 *)
                         
                     *** (* Show l1' = l2' *)
                         apply IH.
                         (* Use inductive hypothesis: needs 3 arguments *)
                         
                         ---- (* Show length l1' = length l2' *)
                              simpl in Heq12.
                              (* Heq12: S (length l1') = S (length l2') *)
                              injection Heq12 as Heq12'.
                              (* Extract: length l1' = length l2' *)
                              assumption.
                              
                         ---- (* Show list_lex_le l1' l2' *)
                              assumption.
                              (* We have Hlex12': list_lex_le l1' l2' *)
                              
                         ---- (* Show list_lex_le l2' l1' *)
                              assumption.
                              (* We have Hlex21': list_lex_le l2' l1' *)
                              
  - (* transitivity *)
    unfold list_le.
    (* Unfold to see the definition *)
    
    intros l1 l2 l3 H12 H23.
    (* Introduce three lists and two hypotheses *)
    (* H12: l1 ≤ l2, H23: l2 ≤ l3 *)
    
    destruct H12 as [Hlt12 | [Heq12 Hlex12]];
    destruct H23 as [Hlt23 | [Heq23 Hlex23]].
    (* Four cases based on whether we use length or lex comparison *)
    
    + (* Case: length l1 < length l2 and length l2 < length l3 *)
      left.
      (* Choose left: length l1 < length l3 *)
      lia.
      (* Transitivity of < *)
      
    + (* Case: length l1 < length l2 and length l2 = length l3 *)
      left.
      (* Choose left: length l1 < length l3 *)
      lia.
      (* Since l1 < l2 and l2 = l3, we have l1 < l3 *)
      
    + (* Case: length l1 = length l2 and length l2 < length l3 *)
      left.
      (* Choose left: length l1 < length l3 *)
      lia.
      (* Since l1 = l2 and l2 < l3, we have l1 < l3 *)
      
    + (* Case: length l1 = length l2 and length l2 = length l3 *)
      (* All three lists have same length, use lex transitivity *)
      right.
      split.
      
      * (* Show length l1 = length l3 *)
        lia.
        (* From l1 = l2 and l2 = l3 *)
        
      * (* Show list_lex_le l1 l3 *)
        (* Need lexicographic transitivity: l1 ≤ₗₑₓ l2 ≤ₗₑₓ l3 → l1 ≤ₗₑₓ l3 *)
        
        generalize dependent l3.
        generalize dependent l2.
        (* Generalize for induction on l1 *)
        
        induction l1 as [| a1 l1' IH].
        
        -- (* Base case: l1 = Nil *)
           intros l2 l3 Heq12 Heq23 Hlex12 Hlex23.
           simpl.
           (* list_lex_le Nil l3 = True *)
           trivial.
           
        -- (* Inductive case: l1 = Cons a1 l1' *)
           intros l2 Heq12 Hlex12 l3 Heq23 Hlex23.
           
           destruct l2 as [| a2 l2'].
           
           ++ (* l2 = Nil - impossible *)
              simpl in Heq12.
              (* S (length l1') = 0 *)
              discriminate.
              
           ++ (* l2 = Cons a2 l2' *)
              destruct l3 as [| a3 l3'].
              
              ** (* l3 = Nil - impossible *)
                 simpl in Heq23.
                 (* S (length l2') = 0 *)
                 discriminate.
                 
              ** (* l3 = Cons a3 l3' *)
                 (* All three lists are Cons *)
                 (* Hlex12: list_lex_le (Cons a1 l1') (Cons a2 l2') *)
                 (* Hlex23: list_lex_le (Cons a2 l2') (Cons a3 l3') *)
                 
                 simpl in Hlex12, Hlex23.
                 (* Hlex12: a1 < a2 \/ (a1 = a2 /\ list_lex_le l1' l2') *)
                 (* Hlex23: a2 < a3 \/ (a2 = a3 /\ list_lex_le l2' l3') *)
                 
                 simpl.
                 (* Goal: a1 < a3 \/ (a1 = a3 /\ list_lex_le l1' l3') *)
                 
                 destruct Hlex12 as [Hlt12 | [Heq_a12 Hlex12']].
                 
                 +++ (* Case: a1 < a2 *)
                     destruct Hlex23 as [Hlt23 | [Heq_a23 Hlex23']].
                     
                     *** (* a1 < a2 and a2 < a3 *)
                         left.
                         (* a1 < a3 by transitivity *)
                         lia.
                         
                     *** (* a1 < a2 and a2 = a3 *)
                         left.
                         (* a1 < a2 = a3, so a1 < a3 *)
                         lia.
                         
                 +++ (* Case: a1 = a2 /\ list_lex_le l1' l2' *)
                     destruct Hlex23 as [Hlt23 | [Heq_a23 Hlex23']].
                     
                     *** (* a1 = a2 and a2 < a3 *)
                         left.
                         (* a1 = a2 < a3, so a1 < a3 *)
                         lia.
                         
                     *** (* a1 = a2 and a2 = a3 *)
                         right.
                         (* a1 = a2 = a3, need to show list_lex_le l1' l3' *)
                         
                         split.
                         
                         ---- (* Show a1 = a3 *)
                              lia.
                              (* From a1 = a2 and a2 = a3 *)
                              
                         ---- (* Show list_lex_le l1' l3' *)
                              apply (IH l2').
                              (* Use inductive hypothesis with middle list l2' *)
                              
                              +++++ (* Show length l1' = length l2' *)
                                    simpl in Heq12.
                                    injection Heq12 as Heq12'.
                                    exact Heq12'.
                                    
                              +++++ (* Show list_lex_le l1' l2' *)
                                    exact Hlex12'.
                                    
                              +++++ (* Show length l2' = length l3' *)
                                    simpl in Heq23.
                                    injection Heq23 as Heq23'.
                                    exact Heq23'.
                                    
                              +++++ (* Show list_lex_le l2' l3' *)
                                    exact Hlex23'.
Qed.
