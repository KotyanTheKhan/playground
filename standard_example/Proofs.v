From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Classes.RelationClasses.
From Posets Require Import PosetClasses.
Require Import Structure.

(* 
  Standard Example Proofs
  Refactored to use smaller lemmas and standard automation.
*)

Lemma standard_refl (n k : nat) : Reflexive (StandardExampleRel n k).
Proof.
  intro x. apply SER_Refl.
Qed.

Lemma standard_antisym (n k : nat) : Antisymmetric Element eq (StandardExampleRel n k).
Proof.
  intros x y Hxy Hyx.
  destruct Hxy.
  - (* x = y *) reflexivity.
  - (* x = A i, y = B j *)
    (* Hyx : StandardExampleRel n k (B j) (A i) *)
    inversion Hyx.
Qed.

Lemma standard_trans (n k : nat) : Transitive (StandardExampleRel n k).
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy.
  - (* x = y *) assumption.
  - (* x = A i, y = B j *)
    (* Hyz : StandardExampleRel n k (B j) z *)
    inversion Hyz; subst.
    (* z = B j case solved by subst and assumption? No, subst replaces z with B j. *)
    (* Wait, if z = B j, then we need to apply SER_Le. *)
    (* If inversion solved it, then SER_Le must be applied automatically? No. *)
    (* Let's check the previous code. *)
    (* inversion Hyz; subst. *)
    (* + apply SER_Le. assumption. *)
    (* + discriminate. *)
    (* If inversion solved it, then I don't need to apply SER_Le? *)
    (* Maybe inversion Hyz found that B j <= z is only possible if z is B j (Refl) or z is B j' (Le). *)
    (* If z is B j (Refl), then Hyz is Refl. subst replaces z with B j. *)
    (* Then we need to prove StandardExampleRel n k (A i) (B j). *)
    (* This is exactly Hxy (A i <= B j). *)
    (* So assumption should solve it. *)
    (* If z is B j' (Le), then B j <= B j' is impossible. *)
    (* So inversion solves the second case. *)
    (* So only the first case remains: StandardExampleRel n k (A i) (B j). *)
    (* And assumption solves it. *)
    (* So `inversion Hyz; subst; assumption.` might work? *)
    (* Or `inversion Hyz; subst; try assumption.` *)
    (* Let's try to just remove bullets and see if `apply SER_Le; assumption` is needed. *)
    (* If `inversion` solved everything, then I don't need anything. *)
    (* But the error says "No more goals" at `+`. *)
    (* This means `inversion Hyz; subst` solved EVERYTHING? *)
    (* If `inversion` solved everything, then `apply SER_Le` was not needed? *)
    (* Wait, `inversion` on `StandardExampleRel` (Refl or Le). *)
    (* Case 1: Refl. z = B j. Goal: A i <= B j. *)
    (* Case 2: Le. B j <= z. Implies B j = A i' (impossible). *)
    (* So Case 2 is solved. *)
    (* Case 1 remains. *)
    (* Why did it say "No more goals"? *)
    (* Maybe `subst` solved it? *)
    (* If z = B j, goal is A i <= B j. *)
    (* Hxy is A i <= B j. *)
    (* So `assumption` solves it. *)
    (* But I didn't write `assumption` yet in the replacement? *)
    (* Ah, I wrote `inversion Hyz; subst. apply SER_Le. assumption.` in the previous step? *)
    (* No, I wrote: *)
    (* inversion Hyz; subst. *)
    (* + apply SER_Le. assumption. *)
    (* + discriminate. *)
    (* If I remove bullets, I should check if `apply SER_Le` is needed. *)
    (* If Hxy is `A i <= B j` (which is `StandardExampleRel ...`), and goal is `StandardExampleRel ...`. *)
    (* Then `assumption` works. *)
    (* `apply SER_Le` constructs a `Le` proof. *)
    (* Hxy is already a proof. *)
    (* So `assumption` is better. *)
    (* But why did `inversion` solve it? *)
    (* Maybe `inversion` does `subst` and `assumption` implicitly? No. *)
    (* The error `Wrong bullet +: No more goals` means that BEFORE `+`, the goal was solved. *)
    (* The code before `+` was `inversion Hyz; subst.` *)
    (* So `inversion Hyz; subst` solved the goal. *)
    (* This is strange because `A i <= B j` is not trivial. *)
    (* Unless `Hxy` was used by `inversion`? No. *)
    (* Let's look at the context. *)
    (* `destruct Hxy`. Case `x = A i, y = B j`. *)
    (* `Hxy` is gone? No, `destruct` keeps it if we named it? No, `destruct Hxy` consumes it. *)
    (* But we have `exists d, ...` from `destruct`. *)
    (* Wait, `destruct Hxy` gives: *)
    (* 1. `x = y`. Solved. *)
    (* 2. `x = A i`, `y = B j`, and argument `exists d...`. *)
    (* Let's call the argument `Hle`. *)
    (* So we have `Hle : exists d...`. *)
    (* Goal: `StandardExampleRel n k (A i) z`. *)
    (* `Hyz : StandardExampleRel n k (B j) z`. *)
    (* `inversion Hyz`. *)
    (* Case 1: `z = B j`. Goal: `StandardExampleRel n k (A i) (B j)`. *)
    (* We have `Hle`. We can apply `SER_Le`. *)
    (* So it is NOT solved automatically. *)
    (* Why did it say "No more goals"? *)
    (* Maybe `inversion` failed to generate subgoals? *)
    (* Or maybe I am misinterpreting the line number. *)
    (* Line 35 is `+ (* z = B j *) ...`. *)
    (* The code before it is `inversion Hyz; subst.` *)
    (* If `inversion` generated 0 subgoals, then `Hyz` was contradictory. *)
    (* `Hyz : B j <= z`. *)
    (* Is it possible that `B j` is maximal? *)
    (* `StandardExampleRel` allows `A <= B` and `Refl`. *)
    (* `B` can be on the right (in `Le`). *)
    (* But `B` cannot be on the left in `Le` (only `A` is on left). *)
    (* `SER_Le : forall i j, ... -> A i <= B j`. *)
    (* So `B j <= z` implies `Refl` (z = B j). *)
    (* It cannot be `Le` because `B j` is not `A i`. *)
    (* So `inversion Hyz` should give ONLY `z = B j`. *)
    (* And `subst` makes `z` into `B j`. *)
    (* So we have 1 subgoal: `StandardExampleRel n k (A i) (B j)`. *)
    (* So why "No more goals" at `+`? *)
    (* Ah, maybe because I used `; subst` which applies to ALL subgoals. *)
    (* And then I tried to use bullets `+`. *)
    (* If there is only 1 subgoal, I cannot use bullets? *)
    (* Yes! Coq bullets `+` are for multiple subgoals. *)
    (* If there is only 1 subgoal, I should not use bullets. *)
    (* So I should just write the proof for the single subgoal. *)
    
    (* So the plan is: remove bullets. *)
    (* And provide the proof for the single case. *)
    (* `apply SER_Le. assumption.` (if `Hle` is available). *)
    (* Wait, `destruct Hxy` gave `Hle`? *)
    (* `destruct Hxy` produces variables for arguments. *)
    (* `StandardExampleRel` has arguments `i j` and `exists d...`. *)
    (* So `destruct` gives `i j Hle`. *)
    (* So `apply SER_Le. apply Hle.` *)
    
    (* Let's verify `standard_trans` code in `Proofs.v`. *)
    (* `intros x y z Hxy Hyz. destruct Hxy.` *)
    (* Case 2: `destruct Hxy` might not name the hypothesis `Hle`. *)
    (* It might be unnamed. *)
    (* `destruct Hxy` usually introduces names if we use `as [...]`. *)
    (* If not, it puts them in context. *)
    (* Let's check `Proofs.v` content again. *)
    (* It just says `destruct Hxy.` *)
    (* So we might have `H : exists d...`. *)
    (* `assumption` should find it. *)
    
    (* So `apply SER_Le. assumption.` should work. *)
    
    apply SER_Le. assumption.
Qed.

(* Proof that StandardExampleRel is a Poset *)
Instance StandardExample_IsPoset (n k : nat) : IsPoset Element (StandardExampleRel n k).
Proof.
  constructor.
  - apply standard_refl.
  - apply standard_antisym.
  - apply standard_trans.
Qed.

(* Proof that CrownPoset is a Poset *)
Instance CrownPoset_IsPoset (n : nat) : IsPoset Element (CrownPoset n).
Proof.
  apply StandardExample_IsPoset.
Qed.
