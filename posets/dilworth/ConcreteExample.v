(** Concrete Example of Dilworth's Theorem
    
    This file demonstrates Dilworth's Theorem using the Standard Example S(3, 1).
    
    Dilworth's Theorem states:
      For any finite partially ordered set, the maximum size of an antichain
      equals the minimum number of chains needed to cover the poset.
    
    The Standard Example S(3,1):
    ============================
    
    Visual representation (Hasse diagram):
    
                 BB0 -------- BB1 -------- BB2
                 /|\         /|\         /|\
                / | \       / | \       / | \
               /  |  \     /  |  \     /  |  \
              /   |   \   /   |   \   /   |   \
             ↑    ↑    ↘ ↑    ↑    ↘ ↑    ↑    ↘
            AA0  AA0   AA1   AA1   AA2   AA2  (AA0)
             ↑         ↑           ↑
             └─────────┴───────────┘
                (cyclic arrows)
    
            Top row (BB elements):    BB0, BB1, BB2  (form an antichain)
            Bottom row (AA elements): AA0, AA1, AA2  (form an antichain)
            
            Complete arrow diagram showing all covering relations:
            
                   BB0 ←───── BB1 ←───── BB2
                   ↑ ↖        ↑ ↖        ↑ ↖
                   │   ╲      │   ╲      │   ╲
                   │     ╲    │     ╲    │     ╲
                   │       ╲  │       ╲  │       ╲
                  AA0 ────→ AA1 ────→ AA2 ────→ (wraps to AA0)
                   │         │         │
                   └─────→ BB1       BB2
                             └─────→ BB0 (wrap)
            
            Edges show the partial order (pointing upward):
              - AA0 ≤ BB0  (direct)
              - AA0 ≤ BB1  (via cyclic relation)
              - AA1 ≤ BB1  (direct)
              - AA1 ≤ BB2  (via cyclic relation)
              - AA2 ≤ BB2  (direct)
              - AA2 ≤ BB0  (via cyclic relation - wraps around)
    
    Elements: {AA0, AA1, AA2, BB0, BB1, BB2} (6 total)
    
    Partial Order Relations: 
      - Reflexivity: x ≤ x for all x (every element relates to itself)
      - Cross relations: AAi ≤ BBj if and only if j ∈ {i, (i+1) mod 3}
        
        In other words:
        • Each AA element is below exactly 2 BB elements
        • Each BB element is above exactly 2 AA elements
        • The "1" in S(3,1) means each bottom element connects to its
          immediate neighbor +1 position in the cyclic order
    
    Key properties:
      - Maximum antichain size (width) = 3 
        Example antichain: {AA0, AA1, AA2} (all bottom elements)
      - Minimum chain cover size = 3
        Example cover: {{AA0,BB0}, {AA1,BB1}, {AA2,BB2}} (three vertical chains)
      
      This demonstrates Dilworth's equality: width = minimum chain cover = 3
    
    Structure:
      1. Poset Definition - Define S(3,1) as a poset
      2. Antichain Construction - Build a maximum antichain of size 3
      3. Chain Cover Construction - Build a minimum chain cover of size 3
      4. Dilworth Verification - Prove width = chain cover number = 3
*)
From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith.
From Posets Require Import PosetClasses.
From Dilworth Require Import Package.

(* ========================================================================== *)
(** * General Ltac Tactics *)
(* ========================================================================== *)

(** [solve_not_in_empty] - Proves goals of the form [~ In _ (Empty_set _) _].
    
    The Empty_set contains no elements, so membership is always false.
    We simply invert the membership hypothesis to derive a contradiction. *)
Ltac solve_not_in_empty := intros H; inversion H.

Section ConcreteExample.

(* ========================================================================== *)
(** ** 1. Poset Definition *)
(* ========================================================================== *)

(** We define S(3,1) using indices {I0, I1, I2} which represent positions
    in a cyclic group Z/3Z. The "1" in S(3,1) refers to the fact that each
    element in the bottom row (AA) is related to exactly 2 elements in the
    top row (BB): itself and the next one cyclically. *)

  (** Index type representing Z/3Z = {0, 1, 2} *)
  Inductive Index := I0 | I1 | I2.

  (** Decidable equality for indices - needed for some automation *)
  Definition eq_dec_Index (x y : Index) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  (** Cyclic successor function: i ↦ (i + 1) mod 3
      This creates the cycle: I0 → I1 → I2 → I0 *)
  Definition next_index (i : Index) : Index :=
    match i with
    | I0 => I1
    | I1 => I2
    | I2 => I0
    end.

  (** [IndexRel i j] holds when j ∈ {i, next(i)}.
      This defines which BB elements each AA element is below.
      For example: IndexRel I0 I0 and IndexRel I0 I1, but not IndexRel I0 I2. *)
  Definition IndexRel (i j : Index) : Prop :=
    i = j \/ j = next_index i.

  (** The carrier set has two "rows":
      - Bottom row: AA I0, AA I1, AA I2 (the "A" elements)
      - Top row: BB I0, BB I1, BB I2 (the "B" elements) *)
  Inductive Element := 
    | AA (i : Index)  (* Bottom row element with index i *)
    | BB (j : Index). (* Top row element with index j *)

  Definition eq_dec_Element (x y : Element) : {x = y} + {x <> y}.
  Proof. decide equality; apply eq_dec_Index. Defined.

  (** The partial order on S(3,1).
      
      Two constructors:
      - [S31_Refl]: Every element is related to itself (reflexivity)
      - [S31_Le]: AA i <= BB j when IndexRel i j
      
      Note: There are NO relations between:
      - Different AA elements (they form an antichain)
      - Different BB elements (they form an antichain)  
      - BB elements to AA elements (no "downward" edges) *)
  Inductive S31Rel : Element -> Element -> Prop :=
    | S31_Refl : forall x, S31Rel x x
    | S31_Le : forall i j, IndexRel i j -> S31Rel (AA i) (BB j).

  (** --- Poset Axiom Proofs --- *)
  
  (** Reflexivity: Every element is related to itself.
      Immediate from the S31_Refl constructor. *)
  Lemma S31_refl : forall x, S31Rel x x.
  Proof. apply S31_Refl. Qed.

  (** Antisymmetry: If x <= y and y <= x, then x = y.
      
      Proof sketch:
      - If x <= y by S31_Refl, then x = y immediately.
      - If x <= y by S31_Le (so x = AA i, y = BB j), then y <= x would require
        BB j <= AA i, but S31_Le only goes from AA to BB, contradiction. *)
  Lemma S31_antisym : forall x y, S31Rel x y -> S31Rel y x -> x = y.
  Proof.
    intros x y Hxy Hyx.
    destruct Hxy; [reflexivity | inversion Hyx].
  Qed.

  (** Transitivity: If x <= y and y <= z, then x <= z.
      
      Proof sketch:
      - If x <= y by S31_Refl, then x = y, so x <= z follows from y <= z.
      - If x <= y by S31_Le (x = AA i, y = BB j), then for y <= z:
        * S31_Le would require BB j <= BB k which can only be S31_Refl,
          so z = BB j, and we already have AA i <= BB j. *)
  Lemma S31_trans : forall x y z, S31Rel x y -> S31Rel y z -> S31Rel x z.
  Proof.
    intros x y z Hxy Hyz.
    destruct Hxy; [assumption |].
    (* Now: Hxy: AA i <= BB j (via S31_Le), need: AA i <= z
       Since BB j <= z and S31_Le requires AA on the left,
       the only possibility is S31_Refl, meaning z = BB j. *)
    inversion Hyz; subst.
    apply S31_Le; assumption.
  Qed.

  (** Bundle the three axioms into a Poset instance *)
  Instance S31_IsPoset : IsPoset Element S31Rel.
  Proof.
    split; [apply S31_refl | apply S31_antisym | apply S31_trans].
  Qed.

(* ========================================================================== *)
(** ** 2. Antichain Construction *)
(* ========================================================================== *)

(** An antichain is a set of pairwise incomparable elements.
    Two elements are incomparable if neither x <= y nor y <= x.
    
    The bottom row {AA I0, AA I1, AA I2} forms a maximum antichain because:
    1. They are pairwise incomparable (no AA-to-AA relations except reflexivity)
    2. No larger antichain exists (we'll prove this via Dilworth's theorem) *)

  (** The maximum antichain: all elements from the bottom row *)
  Definition MyAntichain : Ensemble Element :=
    fun x => exists i : Index, x = AA i.

  (** Proof that MyAntichain is indeed an antichain.
      
      We must show:
      1. Non-empty: There exists at least one element (AA I0)
      2. Pairwise incomparable: For any x, y in MyAntichain, if x <= y or y <= x,
         then x = y (i.e., the only relations are reflexive) *)
  Instance MyAntichain_IsAntichain : IsAntichain S31Rel MyAntichain.
  Proof.
    constructor.
    - (* Non-empty: witness is AA I0 *)
      exists (AA I0); exists I0; reflexivity.
    - (* Pairwise incomparable: For AA i and AA j, if one is related to the other,
         it must be via S31_Refl (since S31_Le requires AA -> BB).
         S31_Refl implies they are equal. *)
      intros x y [i Hx] [j Hy] Hrel; subst.
      destruct Hrel as [H | H]; inversion H; reflexivity.
  Qed.

  (** Cardinality proof: MyAntichain has exactly 3 elements.
      
      Strategy:
      1. Show MyAntichain equals the explicit set {AA I0, AA I1, AA I2}
      2. Use [cardinal] definition: |∅| = 0, |S ∪ {x}| = |S| + 1 if x ∉ S
      
      The [cardinal] predicate from Finite_sets is defined inductively:
      - card_empty: cardinal _ (Empty_set _) 0
      - card_add: cardinal _ A n → ¬In _ A x → cardinal _ (Add _ A x) (S n) *)
  Lemma MyAntichain_Size : cardinal Element MyAntichain 3.
  Proof.
    (* Step 1: Express MyAntichain as an explicit finite set using Add *)
    assert (Heq: MyAntichain = 
      Add Element (Add Element (Add Element (Empty_set Element) (AA I0)) (AA I1)) (AA I2)).
    { apply Extensionality_Ensembles; intros e; split.
      (* -> direction: e ∈ MyAntichain implies e ∈ {AA I0, AA I1, AA I2} *)
      - intros [i H]; subst; destruct i;
        [left; left; right | left; right | right]; constructor.
      (* <- direction: e ∈ {AA I0, AA I1, AA I2} implies e ∈ MyAntichain *)
      - intros H; inversion H; subst; clear H.
        + inversion H0; subst; clear H0.
          * inversion H; subst; clear H;
            [inversion H0 | exists I0; inversion H0; reflexivity].
          * exists I1; inversion H; reflexivity.
        + exists I2; inversion H0; reflexivity. }
    rewrite Heq.
    (* Step 2: Build up cardinality: |∅| = 0 → |{AA I0}| = 1 → ... → |{...}| = 3 *)
    apply card_add; [apply card_add; [apply card_add |] |].
    - apply card_empty.  (* |∅| = 0 *)
    - solve_not_in_empty.  (* AA I0 ∉ ∅ *)
    - (* AA I1 ∉ {AA I0}: by discriminating the constructors *)
      intros H; inversion H; subst; [inversion H0; subst; inversion H1 | inversion H0].
    - (* AA I2 ∉ {AA I0, AA I1}: similar discrimination *)
      intros H; inversion H; subst;
      [inversion H0; subst; [inversion H1; subst; inversion H2 | inversion H1] 
      | inversion H0; subst; inversion H1].
  Qed.

(* ========================================================================== *)
(** ** 3. Chain Cover Construction *)
(* ========================================================================== *)

(** A chain is a set of pairwise comparable elements (a totally ordered subset).
    A chain cover is a collection of chains whose union equals the whole poset.
    
    For S(3,1), the minimum chain cover has 3 chains:
    - Chain0 = {AA I0, BB I0} - vertical chain through index 0
    - Chain1 = {AA I1, BB I1} - vertical chain through index 1  
    - Chain2 = {AA I2, BB I2} - vertical chain through index 2
    
    Each chain has 2 elements with AA i <= BB i (since IndexRel i i holds).
    These chains are disjoint and together cover all 6 elements. *)

  (** The three vertical chains, each containing one AA and one BB with same index *)
  Definition Chain0 : Ensemble Element := fun x => x = AA I0 \/ x = BB I0.
  Definition Chain1 : Ensemble Element := fun x => x = AA I1 \/ x = BB I1.
  Definition Chain2 : Ensemble Element := fun x => x = AA I2 \/ x = BB I2.

  (** [solve_simple_chain_ischain witness] - Proves IsChain for 2-element chains.
      
      For a chain {AA i, BB i}, we need to show:
      1. Non-empty (using witness AA i)
      2. Totality: for any x, y in the chain, either x <= y or y <= x
         - Case AA i, AA i: reflexivity
         - Case AA i, BB i: AA i <= BB i via S31_Le (since IndexRel i i)
         - Case BB i, AA i: symmetric, so BB i >= AA i
         - Case BB i, BB i: reflexivity *)
  Ltac solve_simple_chain_ischain witness :=
    constructor;
    [ exists witness; left; reflexivity
    | intros x y Hx Hy;
      destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy]; subst;
      [ left; constructor  (* AA i <= AA i by reflexivity *)
      | left; apply S31_Le; unfold IndexRel; left; reflexivity  (* AA i <= BB i *)
      | right; apply S31_Le; unfold IndexRel; left; reflexivity (* BB i >= AA i *)
      | left; constructor  (* BB i <= BB i by reflexivity *)
      ]
    ].

  (** Each vertical chain is indeed a chain (total order) *)
  Instance Chain0_IsChain : IsChain S31Rel Chain0.
  Proof. solve_simple_chain_ischain (AA I0). Qed.

  Instance Chain1_IsChain : IsChain S31Rel Chain1.
  Proof. solve_simple_chain_ischain (AA I1). Qed.

  Instance Chain2_IsChain : IsChain S31Rel Chain2.
  Proof. solve_simple_chain_ischain (AA I2). Qed.

  (** The chain cover: the set containing our three chains.
      Represented using [Add] from Ensembles:
      MyCover = ∅ ∪ {Chain0} ∪ {Chain1} ∪ {Chain2} = {Chain0, Chain1, Chain2} *)
  Definition MyCover : Ensemble (Ensemble Element) :=
    Add (Ensemble Element) 
      (Add (Ensemble Element) 
        (Add (Ensemble Element) (Empty_set (Ensemble Element)) Chain0) 
        Chain1) 
      Chain2.

  (** Proof that MyCover is a valid chain cover.
      
      A chain cover must satisfy three properties:
      1. Every member of the cover is a chain
      2. Every chain is a subset of the carrier (Full_set)
      3. Every element of the poset is in some chain (coverage)
      
      The proof proceeds by case analysis on which chain we're considering,
      using the nested structure of Add/Union/Singleton. *)
  Instance MyCover_IsChainCover : IsChainCover S31Rel (Full_set Element) MyCover.
  Proof.
    constructor.
    - (* Property 1: All members are chains
         We unfold MyCover and analyze which chain c is (Chain0, Chain1, or Chain2) *)
      intros c H; unfold MyCover, Add in H.
      inversion H as [c' Hleft Heq | c' Hright Heq]; subst; clear H.
      + inversion Hleft as [c'' Hleft' Heq | c'' Hright' Heq]; subst; clear Hleft.
        * inversion Hleft' as [c''' Hempty Heq | c''' Hsin Heq]; subst; clear Hleft'.
          -- inversion Hempty.  (* c ∈ ∅ is impossible *)
          -- inversion Hsin; apply Chain0_IsChain.
        * inversion Hright'; apply Chain1_IsChain.
      + inversion Hright; apply Chain2_IsChain.
    - (* Property 2: All chains are subsets of Full_set (the carrier)
         For each chain, every element is of type Element, hence in Full_set *)
      intros c H; unfold MyCover, Add in H.
      inversion H as [c' Hleft Heq | c' Hright Heq]; subst; clear H.
      + inversion Hleft as [c'' Hleft' Heq | c'' Hright' Heq]; subst; clear Hleft.
        * inversion Hleft' as [c''' Hempty Heq | c''' Hsin Heq]; subst; clear Hleft'.
          -- inversion Hempty.
          -- inversion Hsin; unfold Chain0; intros x Hx; destruct Hx; subst; apply Full_intro.
        * inversion Hright'; unfold Chain1; intros x Hx; destruct Hx; subst; apply Full_intro.
      + inversion Hright; unfold Chain2; intros x Hx; destruct Hx; subst; apply Full_intro.
    - (* Property 3: Every element is covered by some chain
         Case split on the element (AA i or BB i) and its index *)
      intros x H; destruct x as [i | i]; destruct i.
      (* For each of the 6 elements, show it belongs to the appropriate chain:
         - AA I0, BB I0 ∈ Chain0
         - AA I1, BB I1 ∈ Chain1
         - AA I2, BB I2 ∈ Chain2 *)
      + exists Chain0; split; [unfold MyCover, Add, In; left; left; right; apply In_singleton | simpl; left; reflexivity].
      + exists Chain1; split; [unfold MyCover, Add, In; left; right; apply In_singleton | simpl; left; reflexivity].
      + exists Chain2; split; [unfold MyCover, Add, In; right; apply In_singleton | simpl; left; reflexivity].
      + exists Chain0; split; [unfold MyCover, Add, In; left; left; right; apply In_singleton | simpl; right; reflexivity].
      + exists Chain1; split; [unfold MyCover, Add, In; left; right; apply In_singleton | simpl; right; reflexivity].
      + exists Chain2; split; [unfold MyCover, Add, In; right; apply In_singleton | simpl; right; reflexivity].
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *** Chain Distinctness Lemmas
      
      To prove |MyCover| = 3, we need to show the three chains are distinct.
      We prove Chain_i ≠ Chain_j by finding a witness element that is in one
      chain but not the other. For example, AA I0 ∈ Chain0 but AA I0 ∉ Chain1
      (since Chain1 only contains AA I1 and BB I1). *)
  (* ------------------------------------------------------------------------ *)
  
  (** Proof technique: Assume Chain0 = Chain1, then AA I0 ∈ Chain0 implies
      AA I0 ∈ Chain1, but Chain1 = {AA I1, BB I1}, and AA I0 ≠ AA I1, AA I0 ≠ BB I1 *)
  Lemma Chain0_neq_Chain1 : Chain0 <> Chain1.
  Proof.
    intros H.
    (* Witness: AA I0 is in Chain0 *)
    assert (Hwit : Chain0 (AA I0)) by (left; reflexivity).
    (* By assumption H, AA I0 must also be in Chain1 *)
    rewrite H in Hwit.
    (* But Chain1 only contains AA I1 and BB I1, neither equals AA I0 *)
    destruct Hwit; discriminate.
  Qed.

  Lemma Chain0_neq_Chain2 : Chain0 <> Chain2.
  Proof.
    intros H.
    assert (Hwit : Chain0 (AA I0)) by (left; reflexivity).
    rewrite H in Hwit; destruct Hwit; discriminate.
  Qed.

  Lemma Chain1_neq_Chain2 : Chain1 <> Chain2.
  Proof.
    intros H.
    assert (Hwit : Chain1 (AA I1)) by (left; reflexivity).
    rewrite H in Hwit; destruct Hwit; discriminate.
  Qed.

  (** [solve_not_in_chain_set] - Proves goals of form [~ In ChainX (Add ... ChainY ...)]
      
      Strategy: Invert the Add/Union structure to find which chain ChainX supposedly
      equals, then apply the appropriate distinctness lemma to derive contradiction. *)
  Ltac solve_not_in_chain_set :=
    intros H;
    repeat match goal with
    | H : In _ (Add _ _ _) _ |- _ => inversion H; subst; clear H
    | H : In _ (Empty_set _) _ |- _ => inversion H
    | H : In _ (Singleton _ _) _ |- _ => inversion H; subst; clear H
    end;
    match goal with
    | [ Heq : ?C1 = ?C2 |- _ ] =>
      first [ exact (Chain0_neq_Chain1 Heq)
            | exact (Chain0_neq_Chain2 Heq)
            | exact (Chain1_neq_Chain2 Heq)
            | symmetry in Heq; exact (Chain0_neq_Chain1 Heq)
            | symmetry in Heq; exact (Chain0_neq_Chain2 Heq)
            | symmetry in Heq; exact (Chain1_neq_Chain2 Heq)
            ]
    end.

  (** Non-membership lemmas needed for cardinality proof *)
  
  Lemma Chain0_not_in_empty : 
    ~ In (Ensemble Element) (Empty_set (Ensemble Element)) Chain0.
  Proof. solve_not_in_empty. Qed.

  Lemma Chain1_not_in_singleton_Chain0 : 
    ~ In (Ensemble Element) (Add (Ensemble Element) (Empty_set (Ensemble Element)) Chain0) Chain1.
  Proof. solve_not_in_chain_set. Qed.

  Lemma Chain2_not_in_two_chains :
    ~ In (Ensemble Element) 
      (Add (Ensemble Element) 
        (Add (Ensemble Element) (Empty_set (Ensemble Element)) Chain0) Chain1) Chain2.
  Proof. solve_not_in_chain_set. Qed.

  (** Cardinality of the chain cover: |{Chain0, Chain1, Chain2}| = 3
      
      Uses the same technique as MyAntichain_Size:
      |∅| = 0 → |{C0}| = 1 → |{C0,C1}| = 2 → |{C0,C1,C2}| = 3
      Each step requires proving the new chain is not already in the set. *)
  Lemma MyCover_Size : cardinal (Ensemble Element) MyCover 3.
  Proof.
    unfold MyCover.
    apply card_add; [apply card_add; [apply card_add |] |].
    - apply card_empty.              (* |∅| = 0 *)
    - apply Chain0_not_in_empty.     (* Chain0 ∉ ∅ *)
    - apply Chain1_not_in_singleton_Chain0.  (* Chain1 ∉ {Chain0} *)
    - apply Chain2_not_in_two_chains.        (* Chain2 ∉ {Chain0, Chain1} *)
  Qed.

(* ========================================================================== *)
(** ** 4. Dilworth Verification *)
(* ========================================================================== *)

(** Dilworth's Theorem states: For any finite poset P,
      width(P) = minimum chain cover number
    
    where:
    - width(P) = size of the largest antichain
    - minimum chain cover number = smallest k such that P can be partitioned
      into k chains
    
    Our verification strategy:
    1. Show width >= 3 by exhibiting an antichain of size 3 (MyAntichain)
    2. Show chain cover number <= 3 by exhibiting a cover of size 3 (MyCover)
    3. Use DilworthA lemma: any antichain has size <= any chain cover
       This gives width <= chain cover number
    4. Combined: 3 <= width <= chain cover number <= 3, so both equal 3 *)

  (** Width of S(3,1) is 3.
      
      The Width record bundles:
      - A witness antichain (MyAntichain)
      - Proof it's an antichain
      - Proof it has the claimed size
      - Proof no antichain is larger (via DilworthA) *)
  Theorem S31_Width_3 : Width S31Rel (Full_set Element) 3.
  Proof.
    refine {| width_la := MyAntichain |}.
    constructor.
    - apply MyAntichain_IsAntichain.  (* MyAntichain is an antichain *)
    - intros x Hx; apply Full_intro.
    - apply MyAntichain_Size.          (* |MyAntichain| = 3 *)
    - (* No antichain has size > 3: by DilworthA, any antichain has size <= 
         any chain cover. Our cover has size 3, so no antichain exceeds 3. *)
      intros s n Hs Hincl Hn. 
      eapply DilworthA; 
        [apply MyCover_IsChainCover | apply Hs | apply Hincl | apply MyCover_Size | apply Hn].
  Qed.

  (** Minimum chain cover number of S(3,1) is 3.
      
      The ChainCoverNumber record bundles:
      - A witness chain cover (MyCover)
      - Proof it's a valid chain cover
      - Proof it has the claimed size
      - Proof no chain cover is smaller (via DilworthA) *)
  Theorem S31_ChainCoverNumber_3 : ChainCoverNumber S31Rel (Full_set Element) 3.
  Proof.
    refine {| cover_number_cover := MyCover |}.
    constructor.
    - apply MyCover_IsChainCover.  (* MyCover is a chain cover *)
    - apply MyCover_Size.           (* |MyCover| = 3 *)
    - (* No chain cover has size < 3: by DilworthA, any chain cover has size >=
         any antichain. Our antichain has size 3, so no cover is smaller. *)
      intros cv n Hcv Hn.
      eapply DilworthA; 
        [apply Hcv | apply MyAntichain_IsAntichain | intros x Hx; apply Full_intro | apply Hn | apply MyAntichain_Size].
  Qed.

  (** Final verification: Dilworth's Theorem holds for S(3,1).
      
      The [Dilworth] lemma extracts the numerical equality from the Width and
      ChainCoverNumber proofs. Since both are 3, we get 3 = 3.
      
      This completes the concrete verification that for S(3,1):
        width = 3 = minimum chain cover number
      
      as predicted by Dilworth's Theorem. *)
  Lemma Element_Size_6 : cardinal Element (Full_set Element) 6.
  Proof.
    assert (Heq : Full_set Element =
      Add Element (Add Element (Add Element (Add Element
        (Add Element (Add Element (Empty_set Element)
          (AA I0)) (AA I1)) (AA I2))
          (BB I0)) (BB I1)) (BB I2)).
    { apply Extensionality_Ensembles; intro e; split.
      - intros _; destruct e as [i|i]; destruct i;
        repeat first [apply Union_intror; apply In_singleton | apply Union_introl].
      - intros _; apply Full_intro. }
    rewrite Heq.
    apply card_add; [apply card_add; [apply card_add; [apply card_add;
      [apply card_add; [apply card_add |] |] |] |] |].
    - apply card_empty.
    - solve_not_in_empty.
    - intros H; inversion H; subst; inversion H0.
    - intros H; inversion H; subst; inversion H0; subst; inversion H1.
    - intros H; inversion H; subst; inversion H0; subst; inversion H1; subst;
        inversion H2.
    - intros H; inversion H; subst; inversion H0; subst; inversion H1; subst;
        inversion H2; subst; inversion H3.
    - intros H; inversion H; subst; inversion H0; subst; inversion H1; subst;
        inversion H2; subst; inversion H3; subst; inversion H4.
  Qed.

  Theorem S31_Dilworth_verification : 3 = 3.
  Proof.
    eapply (Dilworth S31Rel 6).
    - apply Element_Size_6.
    - apply S31_Width_3.
    - apply S31_ChainCoverNumber_3.
  Qed.

End ConcreteExample.

(** Summary
    ========
    
    We have formally verified Dilworth's Theorem for the Standard Example S(3,1):
    
    1. Defined S(3,1) as a poset with 6 elements and proved the poset axioms
    
    2. Constructed a maximum antichain {AA I0, AA I1, AA I2} of size 3
       - Proved it's an antichain (pairwise incomparable)
       - Proved its cardinality is exactly 3
    
    3. Constructed a minimum chain cover {{AA I0, BB I0}, {AA I1, BB I1}, {AA I2, BB I2}}
       - Proved each component is a chain (totally ordered)
       - Proved it covers all elements
       - Proved its cardinality is exactly 3
    
    4. Applied DilworthA lemma bidirectionally to establish:
       - No antichain can be larger than 3 (upper bounded by cover size)
       - No chain cover can be smaller than 3 (lower bounded by antichain size)
    
    5. Concluded: width(S(3,1)) = chain_cover_number(S(3,1)) = 3 ✓
*)
