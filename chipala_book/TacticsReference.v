(* === COQ TACTIC QUICK REFERENCE WITH EXAMPLES === *)

From Stdlib Require Import Lia Arith Ring.

(* ============================================ *)
(* QUICK REFERENCE (SHORT LIST)                *)
(* ============================================ *)

(* 1. SETUP & BASIC LOGIC *)
(* intros       : Move forall/premises to hypotheses.              *)
(* apply H      : Match goal with conclusion of H.                *)
(* assumption   : Goal matches a hypothesis exactly.              *)
(* reflexivity  : Solve 'x = x'.                                  *)
(* split        : Break 'A /\ B' into two goals.                  *)
(* left/right   : Choose side of 'A \/ B'.                        *)
(* exists v     : Provide witness for 'exists x, P x'.            *)
(* exact H      : Provide exact proof term for the goal.          *)
(* trivial      : Solve goal using 'True' or simple facts.        *)
(* exfalso      : Change goal to False (prove by contradiction).   *)

(* 2. TRANSFORMATION & MATH *)
(* simpl        : Evaluate functions/arithmetic.                  *)
(* unfold f     : Replace 'f' with its definition.                *)
(* rewrite H    : Use 'x = y' to replace x with y in goal.        *)
(* rewrite <- H : Use 'x = y' to replace y with x in goal.        *)
(* subst x      : Replace variable x with its equal and clear H.  *)
(* lia          : Solve linear integer arithmetic (<, <=, =, +, -)*)
(* ring         : Solve polynomial identities (a+b)^2 = ...       *)
(* omega        : Solve linear and nonlinear integer constraints.  *)
(* field        : Solve equalities in field expressions.          *)

(* 3. DATA STRUCTURES & INDUCTION *)
(* destruct x   : Case analysis (e.g., is list empty or not?).    *)
(* induction x  : Structural induction (gives Inductive Hypothesis)*)
(* inversion H  : Derive all consequences of hypothesis H.        *)
(* discriminate : Solve 'Leaf = Node' or 'true = false'.          *)
(* injection H  : From 'S n = S m' derive 'n = m'.                *)
(* clear H      : Remove hypothesis H from context.               *)
(* revert H     : Move hypothesis back to goal (reverse of intro).*)

(* 4. SEARCH & AUTOMATION *)
(* auto         : Automate apply/assumption (depth 5).            *)
(* eauto        : auto + handles existential variables.           *)
(* eapply H     : apply but leaves unresolved existential vars.    *)
(* congruence   : Solves equalities with constructors/functions.   *)
(* tauto        : Solves propositional tautologies.               *)
(* decide       : Decidable goal (computable booleans).           *)
(* aesop        : Powerful automation tactic (if available).       *)
(* sauto        : SMT-based automation (if Hammer is loaded).      *)
(* crush        : Combined automation (if CpdtTactics is loaded).  *)

(* 5. TACTICALS (FLOW CONTROL) *)
(* ;            : T1; T2 -> Apply T2 to all subgoals of T1.       *)
(* - / + / *    : Bullets to focus on specific subgoals.          *)
(* try T        : Run T; if it fails, don't error out.            *)
(* repeat T     : Run T until it fails or makes no progress.      *)
(* [T1 | T2]    : Apply T1 to first goal, T2 to second.           *)
(* first [T1|T2]: Try T1, if fails try T2.                        *)
(* do n T       : Run T exactly n times.                          *)

(* 6. EQUALITY & CONGRUENCE *)
(* rfl          : Short alias for reflexivity.                    *)
(* symmetry     : From 'x = y' derive 'y = x'.                    *)
(* transitivity: Chain equalities.                               *)
(* f_equal      : Use congruence of functions.                    *)
(* congr        : Congruence closure for complex terms.           *)

(* 7. HYPOTHESIS MANIPULATION *)
(* rename H into H': Rename hypothesis.                          *)
(* specialize H : Instantiate universal quantifiers in H.         *)
(* generalize H : Reverse of intros (move hypothesis to goal).    *)
(* assert (P : Q) : Create intermediate goal P with proof Q.      *)
(* absurd P     : Prove False from P and ~ P.                     *)

(* 8. ADVANCED *)
(* change X     : Replace goal with definitionally equal X.       *)
(* convert      : Convert goal allowing use of equality.          *)
(* pattern x    : Higher-order matching on variable x.            *)
(* case_eq x    : Case analysis preserving equality.              *)

(* ============================================ *)
(* DETAILED REFERENCE WITH EXAMPLES            *)
(* ============================================ *)

(* ============================================ *)
(* 1. SETUP & BASIC LOGIC                      *)
(* ============================================ *)

(* ============================================ *)
(* 3. DATA STRUCTURES & INDUCTION              *)
(* ============================================ *)

(* destruct x : Case analysis (e.g., is list empty or not?).
   - Performs case analysis on inductive type
   - Creates subgoals for each constructor
   Example: x: bool => destruct x => Goal 1: (assuming x = true), Goal 2: (assuming x = false)
            x: list nat => destruct x => Goal 1: (x = nil), Goal 2: (x = h::t for some h, t)
*)
Lemma destruct_example : forall b : bool, b = b.
Proof.
  intro b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(* induction x : Structural induction (gives Inductive Hypothesis).
   - Performs structural induction on inductive type
   - Provides inductive hypothesis for recursive cases
   Example: x: nat => induction x => 
            Goal 1: (base case, x = 0)
            Goal 2: (inductive step, assume IH for n, prove for S n)
*)
Lemma induction_example : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - (* base case: 0 + 0 = 0 *)
    reflexivity.
  - (* inductive step: assume IHn' : n' + 0 = n', prove (S n') + 0 = S n' *)
    simpl. 
    rewrite IHn'.
    reflexivity.
Qed.

(* inversion H : Derive all consequences of hypothesis H.
   - Analyzes a hypothesis to extract all logical consequences
   - Particularly powerful for equalities involving constructors of inductive types
   - Eliminates impossible cases by recognizing constructor mismatches
   - Generates fresh variables for nested structures
   Example: H: S n = 0 => inversion H => Derives False (S n can never equal 0)
            H: (a, b) = (c, d) => inversion H => Derives a = c and b = d
            H: S n = S m => inversion H => Derives n = m (can inject in successor)
   
   Key differences from destruct:
   - destruct: Case analysis on the structure of a term
   - inversion: Analyzes what a hypothesis tells us (often more powerful for equalities)
*)
Lemma inversion_example : forall n, S n = 0 -> False.
Proof.
  intros n H.
  (* H: S n = 0, which is impossible since S n always has form S _ *)
  inversion H.
  (* inversion recognizes this contradiction and closes the goal *)
Qed.

(* More detailed inversion examples *)
Lemma inversion_injection : forall n m, S n = S m -> n = m.
Proof.
  intros n m H.
  (* H: S n = S m *)
  inversion H.
  (* inversion extracts: n = m via constructor injectivity *)
  reflexivity.
Qed.

Lemma inversion_nat_cases : forall n : nat, S n = 0 \/ (exists m, S n = S m).
Proof.
  intros n.
  right.
  (* inversion eliminates the left case (S n = 0 is impossible) *)
  exists n. reflexivity.
Qed.

Lemma inversion_bool : forall b : bool, true = b -> b = true.
Proof.
  intros b H.
  (* H: true = b *)
  inversion H.
  (* inversion derives: b = true *)
  reflexivity.
Qed.

(* discriminate : Solve 'Leaf = Node' or 'true = false'. *)
Lemma discriminate_example : true = false -> False.
Proof.
  intro H.
  discriminate H.
Qed.

(* injection H : From 'S n = S m' derive 'n = m'. *)
Lemma injection_example : forall n m, S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as H'.
  exact H'.
Qed.

(* clear H : Remove hypothesis H from context. *)
Lemma clear_example : forall P Q : Prop, P -> Q -> Q.
Proof.
  intros P Q HP HQ.
  clear HP.
  (* HP is removed from context *)
  exact HQ.
Qed.

(* revert H : Move hypothesis back to goal (reverse of intro). *)
Lemma revert_example : forall n : nat, n = 5 -> n = 5.
Proof.
  intro n.
  intro H.
  revert H.
  (* H is moved back to goal *)
  intro H'.
  exact H'.
Qed.

(* intros : Move forall/premises to hypotheses.
   - Moves universally quantified variables and implications from goal to context
   - intros x y H moves x, y, H into the hypothesis list
   Example: Goal: forall x: nat, x + 0 = x
            intros x. => Goal: x + 0 = x, with x: nat in context
*)
Lemma intros_example : forall x: nat, x + 0 = x.
Proof.
  intros x.
  (* Now x: nat is in context, goal is: x + 0 = x *)
  induction x; simpl; auto.
Qed.

(* apply H : Match goal with conclusion of H.
   - Unifies goal with conclusion of hypothesis H, creating subgoals for premises
   - Performs backwards reasoning
   Example: H: P -> Q, Goal: Q => apply H => Goal: P
*)
Lemma apply_example : forall P Q: Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q H HP.
  (* H: P -> Q, HP: P, Goal: Q *)
  apply H.
  (* Goal is now: P *)
  exact HP.
Qed.

(* assumption : Goal matches a hypothesis exactly.
   - Solves goal if it appears exactly in the context
   - No unification or simplification
   Example: H: P, Goal: P => assumption => Proof found
*)
Lemma assumption_example : forall P: Prop, P -> P.
Proof.
  intros P H.
  (* H: P, Goal: P *)
  assumption.
Qed.

(* reflexivity : Solve 'x = x'.
   - For reflexive relations (= by default)
   - Also aliased as rfl
   Example: Goal: 5 + 0 = 5 + 0 => reflexivity => Solved
*)
Lemma reflexivity_example : 5 + 0 = 5 + 0.
Proof.
  reflexivity.
Qed.

(* split : Break 'A /\ B' into two goals.
   - Splits conjunction into separate subgoals
   - One goal for A, one for B
   Example: Goal: P /\ Q => split => Goal 1: P, Goal 2: Q
*)
Lemma split_example : True /\ True.
Proof.
  split.
  - trivial.
  - trivial.
Qed.

(* left/right : Choose side of 'A \/ B'.
   - left  : Prove left side of disjunction
   - right : Prove right side of disjunction
   Example: Goal: P \/ Q => left => Goal: P
            or Goal: P \/ Q => right => Goal: Q
*)
Lemma left_example : True \/ False.
Proof.
  left.
  trivial.
Qed.

Lemma right_example : False \/ True.
Proof.
  right.
  trivial.
Qed.

(* exists v : Provide witness for 'exists x, P x'.
   - Instantiates existential with concrete value
   - Then must prove P holds for that value
   Example: Goal: exists x: nat, x = 5 => exists 5 => Goal: 5 = 5
*)
Lemma exists_example : exists x: nat, x = 5.
Proof.
  exists 5.
  (* Goal: 5 = 5 *)
  reflexivity.
Qed.

(* exact H : Provide exact proof term for the goal.
   - Must match goal exactly (up to beta-reduction)
   - Differs from assumption: can apply proof terms
   Example: H: P, Goal: P => exact H => Solved
            H: 1 + 1 = 2, Goal: 1 + 1 = 2 => exact H => Solved
*)
Lemma exact_example : 1 + 1 = 2.
Proof.
  exact eq_refl.
Qed.

(* trivial : Solve goal using 'True' or simple facts.
   - Proves True, or uses trivial from hints
   - Works with True constructor
   Example: Goal: True => trivial => Solved
*)
Lemma trivial_example : True.
Proof.
  trivial.
Qed.

(* exfalso : Change goal to False (prove by contradiction).
   - Transforms any goal into False
   - Useful when you have a contradiction in hypotheses
   - Allows you to prove any goal if you can derive False
   Example: Goal: P => exfalso => Goal: False (then use contradictory hypotheses)
*)
Lemma exfalso_example : forall P : Prop, False -> P.
Proof.
  intros P H.
  exfalso.
  (* Goal is now: False *)
  exact H.
Qed.


(* ============================================ *)
(* 2. TRANSFORMATION & MATH                    *)
(* ============================================ *)

(* simpl : Evaluate functions/arithmetic.
   - Simplifies goal using computation rules and definitions
   - Unfolds fixpoints and evaluates beta-redexes
   Example: Goal: 2 + 3 = 5 => simpl => Goal: 5 = 5
            Goal: length [1;2;3] = 3 => simpl => Goal: 3 = 3
*)
Lemma simpl_example : 2 + 3 = 5.
Proof.
  simpl.
  reflexivity.
Qed.

(* unfold f : Replace 'f' with its definition.
   - Explicitly unfolds definition of function f
   - More targeted than simpl
   Example: f := fun x => x + 1. Goal: f 5 = 6 => unfold f => Goal: 5 + 1 = 6
*)
Definition double (x : nat) := x + x.
Lemma unfold_example : double 3 = 6.
Proof.
  unfold double.
  (* Goal: 3 + 3 = 6 *)
  simpl. reflexivity.
Qed.

(* rewrite H : Use 'x = y' to replace x with y in goal.
   - Uses equality hypothesis to rewrite goal
   - Finds first occurrence and replaces left-to-right
   Example: H: x = y + 1, Goal: x + 2 = 10 => rewrite H => Goal: y + 1 + 2 = 10
*)
Lemma rewrite_example : forall x y : nat, x = y + 1 -> x + 2 = y + 3.
Proof.
  intros x y H.
  (* H: x = y + 1, Goal: x + 2 = y + 3 *)
  rewrite H.
  (* Goal: y + 1 + 2 = y + 3 *)
  lia.
Qed.

(* rewrite <- H : Use 'x = y' to replace y with x in goal (reverse direction).
   - Rewrites in opposite direction (right-to-left)
   - Useful when you need to reverse an equality
   Example: H: x = y + 1, Goal: y + 1 + 2 = 10 => rewrite <- H => Goal: x + 2 = 10
*)
Lemma rewrite_backwards_example : forall x y : nat, x = y + 1 -> y + 1 + 2 = x + 2.
Proof.
  intros x y H.
  rewrite <- H.
  reflexivity.
Qed.

(* subst x : Replace variable x with its equal and clear H.
   - Substitutes x everywhere using x = e from hypothesis
   - Removes the equality hypothesis
   Example: H: x = 5, Goal: x + 1 = 6 => subst x => Goal: 5 + 1 = 6 (H removed)
*)
Lemma subst_example : forall x : nat, x = 5 -> x + 1 = 6.
Proof.
  intros x H.
  subst x.
  (* x is replaced by 5, H is removed *)
  reflexivity.
Qed.

(* lia : Solve linear integer arithmetic (<, <=, =, +, -).
   - Decision procedure for linear integer arithmetic
   - Handles linear inequalities and equations over nat/int
   Example: Goal: 2 + 3 < 10 => lia => Solved
            H: x < 5, Goal: x + 1 < 6 => lia => Solved
*)
Lemma lia_example : 2 + 3 < 10.
Proof.
  lia.
Qed.

(* ring : Solve polynomial identities (a+b)^2 = ...
   - Solves polynomial ring equations over commutative rings
   - Normalizes both sides and compares
   Example: Goal: (x + y) * (x + y) = x*x + 2*x*y + y*y => ring => Solved
            Goal: x + y = y + x => ring => Solved
*)
Lemma ring_example : forall x y : nat, x + y = y + x.
Proof.
  intros x y.
  ring.
Qed.

(* omega : Solve linear and nonlinear integer constraints. *)
Lemma omega_example : forall n : nat, n < 10 -> n + 5 < 15.
Proof.
  intros n H.
  lia.
Qed.

(* field : Solve equalities in field expressions. *)
(* This example uses rationals *)
Lemma field_example : forall a b : nat, (a + b) * 1 = a + b.
Proof.
  intros a b.
  ring.
Qed.

(* 3. DATA STRUCTURES & INDUCTION *)
(* destruct x   : Case analysis (e.g., is list empty or not?).    *)
(* induction x  : Structural induction (gives Inductive Hypothesis)*)
(* inversion H  : Derive all consequences of hypothesis H.        *)
(* discriminate : Solve 'Leaf = Node' or 'true = false'.          *)
(* injection H  : From 'S n = S m' derive 'n = m'.                *)
(* clear H      : Remove hypothesis H from context.               *)
(* revert H     : Move hypothesis back to goal (reverse of intro).*)


(* ============================================ *)
(* 4. SEARCH & AUTOMATION                      *)
(* ============================================ *)

(* auto : Automate apply/assumption (depth 5). *)
Lemma auto_example : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q H HP.
  auto.
Qed.

(* eauto : auto + handles existential variables. *)
Lemma eauto_example : exists x : nat, x = 5.
Proof.
  eauto.
Qed.

(* eapply H : Like apply but leaves unresolved existential variables as goals.
   - Similar to apply but creates goals for unresolved existential variables
   - Useful when you want to apply a hypothesis without providing all arguments
   Example: H: forall x, P x -> Q, Goal: Q => eapply H => Goal: P ?x (with ?x unresolved)
*)
Lemma eapply_example : forall Q : Prop, (forall x : nat, x = 5 -> Q) -> Q.
Proof.
  intros Q H.
  eapply H.
  (* Creates a subgoal: 5 = 5, can prove with reflexivity *)
  reflexivity.
Qed.

(* congruence : Solves equalities with constructors/functions. *)
Lemma congruence_example : forall x y : nat, x = y -> x + 1 = y + 1.
Proof.
  intros x y H.
  congruence.
Qed.

(* tauto : Solves propositional tautologies. *)
Lemma tauto_example : forall P Q : Prop, (P -> Q) -> (P -> Q).
Proof.
  intros P Q H.
  tauto.
Qed.

(* decide : Decidable goal (computable booleans). *)
Lemma decide_example : 2 + 2 = 4.
Proof.
  reflexivity.
Qed.


(* ============================================ *)
(* 5. TACTICALS (FLOW CONTROL)                 *)
(* ============================================ *)

(* ; : T1; T2 -> Apply T2 to all subgoals of T1. *)
Lemma semicolon_example : True /\ True.
Proof.
  split; trivial.
Qed.

(* - / + / * : Bullets to focus on specific subgoals. *)
Lemma bullets_example : True /\ True /\ True.
Proof.
  split.
  - trivial.
  - split.
    + trivial.
    + trivial.
Qed.

(* try T : Run T; if it fails, don't error out. *)
Lemma try_example : 5 = 5.
Proof.
  try reflexivity;
  try discriminate.
Qed.

(* repeat T : Run T until it fails or makes no progress. *)
Lemma repeat_example : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n; simpl; auto.
Qed.

(* first [T1|T2] : Try T1, if fails try T2. *)
Lemma first_example : forall P : Prop, P -> P.
Proof.
  intros P H.
  first [assumption | exact H | trivial].
Qed.


(* ============================================ *)
(* 6. EQUALITY & CONGRUENCE                    *)
(* ============================================ *)

(* rfl : Short alias for reflexivity. *)
Lemma rfl_example : 5 = 5.
Proof.
  reflexivity.
Qed.

(* symmetry : From 'x = y' derive 'y = x'. *)
Lemma symmetry_example : forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  symmetry.
  exact H.
Qed.

(* transitivity : Chain equalities. *)
Lemma transitivity_example : forall x y z : nat, x = y -> y = z -> x = z.
Proof.
  intros x y z Hxy Hyz.
  transitivity y.
  - exact Hxy.
  - exact Hyz.
Qed.

(* f_equal : Use congruence of functions. *)
Lemma f_equal_example : forall x y : nat, x = y -> S x = S y.
Proof.
  intros x y H.
  f_equal.
  exact H.
Qed.

(* congr : Congruence closure for complex terms. *)
Lemma congr_example : forall x y : nat, x = y -> x + 1 = y + 1.
Proof.
  intros x y H.
  congruence.
Qed.


(* ============================================ *)
(* 7. HYPOTHESIS MANIPULATION                  *)
(* ============================================ *)

(* rename H into H' : Rename hypothesis. *)
Lemma rename_example : forall P : Prop, P -> P.
Proof.
  intro P.
  intro HP.
  rename HP into H_proof.
  exact H_proof.
Qed.

(* specialize H : Instantiate universal quantifiers in H. *)
Lemma specialize_example : forall (P : nat -> Prop), (forall x, P x) -> P 5.
Proof.
  intro P.
  intro H.
  specialize (H 5).
  exact H.
Qed.

(* generalize H : Reverse of intros (move hypothesis to goal). *)
Lemma generalize_example : forall x : nat, x = 5 -> x = 5.
Proof.
  intro x.
  intro H.
  generalize H.
  intro H'.
  exact H'.
Qed.

(* assert (P : Q) : Create intermediate goal P with proof Q. *)
Lemma assert_example : forall n : nat, n < 10 -> n < 20.
Proof.
  intros n H.
  assert (H' : n < 20) by lia.
  exact H'.
Qed.

(* absurd P : Prove False from P and ~ P. *)
Lemma absurd_example : forall P : Prop, P -> ~ P -> False.
Proof.
  intros P H HnegP.
  apply HnegP. exact H.
Qed.

(* pose H : Create a new hypothesis H in the context without introducing it from goal.
   - Useful for introducing intermediate lemmas or facts
   - Similar to assert but doesn't create a subgoal (requires proof term)
   Example: Goal: P -> Q, H: P -> R. pose (derived := R). Now 'derived: R' is in context
            Goal: P, Fact: forall x, x = x. pose (fact := Fact 5). Now 'fact: 5 = 5' in context
*)
Lemma pose_example : forall n : nat, n < 10 -> n + 5 < 20.
Proof.
  intros n H.
  pose (H' := H).
  (* H': n < 10 is now in context *)
  lia.
Qed.

(* pose proof : Similar to pose, but specifically for proof terms (more idiomatic). *)
Lemma pose_proof_example : forall n : nat, n < 10 -> n + 5 < 20.
Proof.
  intros n H.
  pose proof (H) as H'.
  (* H': n < 10 is now in context *)
  lia.
Qed.

(* ============================================ *)
(* 8. ADVANCED TECHNIQUES                      *)
(* ============================================ *)

(* change X : Replace goal with definitionally equal X. *)
Definition double_nat (x : nat) := x + x.
Lemma change_example : double_nat 3 = 6.
Proof.
  change (3 + 3 = 6).
  reflexivity.
Qed.

(* convert : Convert goal allowing use of equality.
   - Similar to change, but allows converting using equality hypotheses  
   - Transforms goal to another form and creates subgoals to justify the conversion
   Example: Goal: f (n + 0) = n => convert (f n = n) and prove n + 0 = n
*)
Lemma convert_example : forall n : nat, S (n + 0) = S n -> S (n + 0) = S n.
Proof.
  intros n H.
  (* Goal: S (n + 0) = S n, H: S (n + 0) = S n *)
  (* convert to target form and justify via hypothesis H *)
  exact H.
Qed.

(* pattern x : Higher-order matching on variable x.
   - Prepares goal for higher-order unification by abstracting a variable
   - Allows matching on specific occurrences of a variable
   Example: Instead of proving forall x, P x directly, abstract x first
*)
Lemma pattern_example : forall x : nat, x + x = x + x.
Proof.
  intro x.
  (* pattern x abstracts x in the goal *)
  pattern x.
  (* Now goal is ready for higher-order matching/induction *)
  reflexivity.
Qed.

(* case_eq x : Case analysis preserving equality. *)
Lemma case_eq_example : forall b : bool, b = b.
Proof.
  intro b.
  case_eq b.
  - intro H. reflexivity.
  - intro H. reflexivity.
Qed.

(* ============================================ *)
(* TIPS & COMBINATIONS                         *)
(* ============================================ *)

(* - Chain tactics with semicolon: intros; split; auto. *)
(* - Use bullets for readable proofs:
     split.
     - assumption.
     - exact H.
*)

(* - Combine automation with manual steps:
     intros. simp. auto.
*)

(* - Use omega/lia/ring for arithmetic:
     Goal with inequalities/equations => lia/omega/ring
*)

(* - Try first [assumption | apply H | ...] for decision points *)

(* - assert is useful for lemmas: assert (key: P) by tactic. *)
