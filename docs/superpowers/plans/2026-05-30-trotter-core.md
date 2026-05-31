# Plan: close `trotter_path_family_impossible` (last dimension admit)

Goal: prove the boundary-CP coverage core of Trotter Thm 6.1. Build sound Qed
lemmas step by step; commit each; do not fabricate.

Already Qed (this session): greedy→path reduction (`greedy_reject_path`), path
decomposition (`aug_path_step3_or_via_acc`), `aug_no_backward_S'`, mono helpers.

Steps:
1. **Structural CP facts.** Two CPs sharing the top (`(x',y')`,`(z,y')`) ⟹ `z`
   incomparable to `x'`; dually for shared bottom. So a boundary CP's S'-endpoint
   is incomparable to the relevant `{x',y'}` element. (Qed; pure `critical_down/up`.)
2. **Path-into-special decomposition.** A path ending at `y'` (∉S') exits S' at a
   last S'-vertex via `R w y'`, `x'→y'`, or a reversed boundary edge into `y'`;
   dually for `x'`. (Qed; structural.)
3. **Refining-CP extraction.** From a boundary path (for the chosen `L'`) extract
   a critical pair `(p',q')` with `R p' x'` and `R y' q'`. (The deep step.)
4. **Extremality elimination.** Step 3's CP refines `(x',y')`; `IsExtremalCP`
   forces it `= (x',y')`, contradicting the path's nontriviality. (Qed.)
5. **Assemble** `trotter_path_family_impossible` from 1–4 (choose `L'` via the
   realizer reversing the S'-incomparability from step 1).

Risk: step 3 is the genuine Trotter content; may need several sub-lemmas or prove
intractable in one pass. Steps 1–2 are sound regardless and reusable.
