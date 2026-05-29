# Step-by-step plan: find the proof of the n=5 base case (counts 5-8)

> **For agentic workers:** use superpowers:executing-plans. Steps are checkboxes; each is one small, verifiable action. Every build via `bash .claude/scripts/timed-build.sh <secs> <target> [jobs] [mem_mb]`, and ALWAYS `pkill -9 -f dune` before a fresh reflection/`vm_compute` build.

**Goal:** close `EdgeCount{5,6,7,8}.v` (admit count 5 -> 1), then Track B (Trotter).

**Why this shape:** the n=5 base is ALREADY mostly built non-reflectively — 105
`n5_*_two_realizer` explicit handlers + ~60 `N5Dispatcher` microcases. Counts
1-4 and 9 are closed. The only blocker for 5-8 was proving EXHAUSTIVENESS
(every count-K poset matches one of the handled patterns) — which we tried by
`native_compute` over C(25,K) and it is infeasible for K>=5. So this plan
FIRST measures the real gap, then closes it by the cheapest route, with two
fallbacks.

---

## Phase 0 — Map the exact gap (cheap; investigation only)

- [ ] **0.1** List the 105 handler signatures: `grep -nE 'Lemma n5_.*_two_realizer' posets/dimension/N5Realizers.v`. Note which structural shapes they cover (claw, chain, fence, diamond, bowtie, N, V, Y, pendant, ...).
- [ ] **0.2** Read `EdgeCount4.v` end-to-end as the TEMPLATE: it does `destruct (classic (exists <pattern>))` -> per-class handler for 10 patterns, then the residual "no pattern" branch via `exhaustive_4edge` (reflection over C(25,4)=12650, feasible). Confirm the exact shape of the per-pattern dispatch and the residual contradiction.
- [ ] **0.3** For each K in {8,7,6,5}: enumerate (on paper / OEIS) the iso-classes of 5-element posets with K comparabilities (the patterns). Cross-reference against the 105 handlers (0.1) to list, PER K, which patterns already have a handler and which need a new one. Output: a per-K table {pattern -> handler-name | NEW}.
- [ ] **0.4** Decide per K whether exhaustiveness can avoid reflection (Phase 2) or needs it. Record the gap precisely in the status doc; commit.

## Phase 0 FINDINGS (2026-05-30)

`N5Realizers.v` has **105** `n5_*_two_realizer` handlers spanning essentially
every 5-element iso-class (claws, chains, fences, diamonds, bowties, K_2_3 +
minus-edge/matching variants, kite, pentagon, X/T/N/inv_N/V/inv_V/Y shapes,
class31/38/40, ...). So **realizer construction is DONE**; Phase 1 is likely
empty or tiny.

=> The realizer-compute / orientation / bridge detour (Sessions S1-S3) was
unnecessary. The ONLY gap for 5-8 is EXHAUSTIVENESS + classic dispatch, exactly
like `EdgeCount4.v`. Crucially, the EdgeCount4 reflection checks is_poset_b +
PATTERN booleans (`any_pattern_b`), NOT a realizer search — cheap per item.
The earlier "infeasible" was `sublists K all_pairs` = C(25,K)=1.08M for K=8;
the CONSTRAINED enumeration (Phase 2a) is ~8-15k = EdgeCount4 scale (12650,
which compiled in ~120 s / 5 chunks). So Phase 2a is the primary, feasible path.

## Phase 1 — Per-class handlers (mechanical, FAST compile, no reflection)

For each NEW pattern from 0.3 (none if all covered):

- [ ] **1.k** Create `EdgeCount{K}_<pattern>.v` mirroring an existing `EdgeCount4_<pattern>.v`: a `Lemma n5_edge_count_{K}_<pattern>` that, given the pattern witnesses, builds the 2-realizer by calling the matching `N5Realizers` handler (or `n5_two_realizer_framework` with explicit ranks). Build via `timed-build.sh 600 <file>.vo 1`; commit per file. (These are linear, ~120 lines each, fast to compile — like the EdgeCount4 helpers.)

## Phase 1.5 — COUNT-8 special case: structural dispatch, NO reflection (do first)

Count-8 has EXACTLY two incomparable pairs (provable: `incomp_carrier_exists`
gives one, `second_incomp_of_8` a distinct second, `two_incomp_le_8` forbids a
third — all Qed in `EdgeCountIncomp.v`). So EdgeCount8 needs NO `exhaustive_8edge`
reflection; it dispatches structurally:
  - [ ] extract incomparable pairs {p,q},{r,s} (the two extractors);
  - [ ] `destruct (classic (shares a vertex))`: disjoint ({p,q},{r,s} all 4
        distinct, 5th comparable to all) vs shared ({u,v},{u,w});
  - [ ] in each config the 8 comparabilities' orientation is constrained; case
        on the remaining structure and route to the matching `N5Realizers`
        handler (candidates: K_3_2_minus_matching / diamond_pendant_* /
        3_layer_diamond / bowtie_*_cap for disjoint; the inv/_minus_two_edges
        variants for shared). Provide the handler its witnesses.
This is the cleanest count to close first (reuses Qed extractors; fast compile).
Counts 7,6,5 (>=3 incomparable pairs, no clean extraction) fall back to Phase 2
reflection (constrained enum).

## Phase 2 — Exhaustiveness for each count K (the crux)

The residual "no pattern matched -> contradiction" needs: every is_poset matrix
with edge_count = K matches one of the Phase-1 patterns. Three options, in
preference order; pick per K based on 0.4:

- [ ] **2a (preferred if feasible): constrained reflection.** Enumerate by the
  K comparable UNORDERED pairs + orientation, NOT C(25,K) ordered subsets:
  ~C(10,10-K)*2^K (8064/13440/15360/11520 for K=5/6/7/8) ~ EdgeCount4 scale.
  Build the generator `enum_count K`, prove `exhaustive_{K}edge : forall M,
  is_poset_b M = true -> edge_count_b M = K -> any_pattern_b M = true` by
  `native_cast_no_check (eq_refl true)`, CHUNKED (~3-5 chunks, like
  N5Reflect_Exhaustive). Probe the chunk size/time FIRST (pkill dune; vm or
  native). If a chunk compiles < 5 min, proceed; else 2b/2c.
- [ ] **2b: hand exhaustiveness via the dispatcher case-split.** Prove
  `exhaustive_{K}edge` by the same classic structural case analysis the
  `N5Dispatcher` microcases use (destruct comparabilities of the strict edges,
  classify) — no `native_compute`. More manual but no perf wall.
- [ ] **2c: removable-point reduction (sidesteps exhaustiveness entirely).**
  Prove `dim_remove_max : x maximal in P -> exists r, IsRealizer (P) r /\
  card r = card(realizer of P-x)` (place x last in both extensions), and the
  dual for a minimal x. Then `n5_edge_count_K_two_realizer` (or all of 5-8 at
  once): a count-K non-chain 5-poset has a maximal or minimal element whose
  removal yields a 4-element poset (dim<=2, already Qed); lift via dim_remove.
  Coverage sub-claim: every non-chain 5-poset has a removable max/min reducing
  to a dim<=2 subposet — verify on the (few) count-K shapes from 0.3.

## Phase 3 — Wire + verify

- [ ] **3.1** For each K: assemble `n5_edge_count_{K}_two_realizer` = per-pattern
  classic dispatch (Phase 1) + residual via `exhaustive_{K}edge` (Phase 2),
  exactly like the committed `EdgeCount4.v`. Build `timed-build.sh 600
  EdgeCount{K}.vo 1`; commit. Admit count drops one per K.
- [ ] **3.2** After all four: `timed-build.sh 1800 posets/dimension 2` green;
  confirm admit count = 1 (only Trotter). Update status doc; commit.

## Phase 4 — Track B (Trotter, admit #2)

- [ ] **4.1** Decompose `trotter_coverage_via_extremality` (RemovablePairs.v:1834)
  into focused sub-lemmas (cycle->refining-CP; extremality kills chains; greedy
  bookkeeping). Run `proof-skeptic`. Commit refactor.
- [ ] **4.2..** Close sub-lemmas one per session; `proof-skeptic` at each.

## Decision gates / risk

- After 0.3: if the gap is just exhaustiveness (all patterns have handlers), go
  straight to Phase 2. If 2a's chunk probe is infeasible, use 2c
  (removable-point) — it avoids the perf wall established over the last 3
  sessions.
- 2c is the recommended primary if Phase 0 shows many uncovered patterns:
  it closes counts 5-8 with ONE dim-reduction lemma + coverage, reusing the
  Qed n=4 base, no per-pattern handlers or reflection.

## Success criteria

`grep -rnE '^[[:space:]]*(Admitted|admit)\.' posets/dimension` empty;
`timed-build.sh 1800 posets/dimension 2` green.
