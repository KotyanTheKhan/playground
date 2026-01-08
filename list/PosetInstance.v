(* Poset instance for lists *)
Require Import Posets.PosetClasses.
From List Require Import Structure.
From List Require Import Operations.
Require Import Helpers.
From Stdlib Require Import Lia.

Instance list_poset : IsPoset List list_le.
Proof.
  constructor.
  
  (* ========== REFLEXIVITY ========== *)
  (* Goal: ∀ x, x ≤ x *)
  - (* reflexivity *)
    intro x.
    (* Introduce the list x *)
    
    unfold list_le.
    (* Unfold definition: length x < length x \/ (length x = length x /\ list_lex_le x x) *)
    
    right.
    (* Choose right side: (length x = length x /\ list_lex_le x x)
       The left side (length x < length x) is impossible *)
    
    split; auto.
    (* Split conjunction into two goals:
       1. length x = length x  [solved by 'auto']
       2. list_lex_le x x      [need to prove] *)
    
    apply list_lex_le_refl.
    (* Apply the lemma proving lexicographic reflexivity
       (This lemma contains the induction proof we wrote manually in pi.v) *)
    
  (* ========== ANTISYMMETRY ========== *)
  (* Goal: ∀ x y, x ≤ y → y ≤ x → x = y *)
  - (* antisymmetry *)
    intros x y H1 H2.
    (* Introduce lists x, y and hypotheses H1: x ≤ y, H2: y ≤ x *)
    
    unfold list_le in *.
    (* Unfold both hypotheses:
       H1: length x < length y \/ (length x = length y /\ list_lex_le x y)
       H2: length y < length x \/ (length y = length x /\ list_lex_le y x) *)
    
    destruct H1 as [H1 | [H1 H1']]; destruct H2 as [H2 | [H2 H2']]; try lia.
    (* Case analysis on both hypotheses (4 cases):
       1. H1: length x < length y, H2: length y < length x  → Contradiction! [lia]
       2. H1: length x < length y, H2: length y = length x  → Contradiction! [lia]
       3. H1: length x = length y, H2: length y < length x  → Contradiction! [lia]
       4. H1: length x = length y, H2: length y = length x  → Need antisymmetry
       
       'try lia' automatically solves the three contradictory cases *)
    
    apply list_lex_le_antisym; auto.
    (* Apply lexicographic antisymmetry lemma with:
       - H1: length x = length y
       - H1': list_lex_le x y
       - H2': list_lex_le y x
       'auto' automatically provides these hypotheses *)
    
  (* ========== TRANSITIVITY ========== *)
  (* Goal: ∀ x y z, x ≤ y → y ≤ z → x ≤ z *)
  - (* transitivity *)
    intros x y z H1 H2.
    (* Introduce lists x, y, z and hypotheses H1: x ≤ y, H2: y ≤ z *)
    
    unfold list_le in *.
    (* Unfold both hypotheses:
       H1: length x < length y \/ (length x = length y /\ list_lex_le x y)
       H2: length y < length z \/ (length y = length z /\ list_lex_le y z) *)
    
    destruct H1 as [H1 | [H1 H1']]; destruct H2 as [H2 | [H2 H2']].
    (* Case analysis on both hypotheses (4 cases):
       Each case represents a combination of length/lex comparisons *)
    
    + (* Case 1: length x < length y AND length y < length z *)
      left.
      (* Choose left: length x < length z *)
      lia.
      (* By transitivity of <: x < y < z implies x < z *)
      
    + (* Case 2: length x < length y AND length y = length z *)
      left.
      (* Choose left: length x < length z *)
      lia.
      (* Since x < y and y = z, we have x < z *)
      
    + (* Case 3: length x = length y AND length y < length z *)
      left.
      (* Choose left: length x < length z *)
      lia.
      (* Since x = y and y < z, we have x < z *)
      
    + (* Case 4: length x = length y AND length y = length z *)
      right.
      (* Choose right: (length x = length z /\ list_lex_le x z)
         All lengths are equal, so use lexicographic transitivity *)
      
      split; try lia.
      (* Split conjunction:
         1. length x = length z  [solved by 'lia' from x = y = z]
         2. list_lex_le x z      [need to prove] *)
      
      eapply list_lex_le_trans; eauto.
      (* Apply lexicographic transitivity with y as the middle element:
         - list_lex_le x y  (from H1')
         - list_lex_le y z  (from H2')
         - Conclude: list_lex_le x z
         
         'eapply' allows Coq to infer the middle element
         'eauto' automatically finds and applies H1' and H2' *)
Qed.

(* ========== PROOF EXPLANATION ========== *)
(*
This proof is significantly more concise than pi.v because it uses helper lemmas:

1. list_lex_le_refl: Proves lexicographic reflexivity
   (Encapsulates the induction proof we wrote manually)

2. list_lex_le_antisym: Proves lexicographic antisymmetry
   (Encapsulates the nested induction and case analysis)

3. list_lex_le_trans: Proves lexicographic transitivity
   (Encapsulates the induction with middle element)

Key Tactics Used:
- 'auto': Automatically solves simple goals using available hypotheses
- 'try lia': Attempts to solve with linear arithmetic, continues if it fails
- 'eapply ... eauto': Apply lemma with automatic hypothesis matching
- 'split; try lia': Split conjunction, attempting lia on each part

Proof Strategy:
1. Unfold list_le to see the length/lex disjunction
2. Use case analysis (destruct) to handle all combinations
3. Eliminate impossible cases with 'lia'
4. Apply appropriate helper lemmas for lexicographic properties

This demonstrates good Coq practice: prove helper lemmas separately,
then compose them for clean, readable main proofs.

Compare with pi.v which proves everything inline for educational purposes.
*)
