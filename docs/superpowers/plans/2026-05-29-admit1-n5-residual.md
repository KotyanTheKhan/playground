# Plan: Close admit #1 — `n5_residual_classes_two_realizer`

Track: n=5 base case of `hiraguchi_bound`. Status doc:
`docs/superpowers/specs/2026-05-28-dimension-replan-status.md`.

## Target

`N5DispatcherShapes.v:38`:
```
n5_residual_classes_two_realizer :
  cardinal B (Full_set B) 5 ->
  ~ (forall a b, R2 a b -> a = b) ->            (* not antichain *)
  (exists a b, Incomparable R2 a b) ->          (* not a chain *)
  (exists p q x y, p<>q /\ R2 p q /\ x<>y /\ R2 x y /\ ~(x=p/\y=q)) ->  (* >=2 edges *)
  exists r, IsRealizer R2 r /\ cardinal _ r 2.
```
True by Hiraguchi (every poset on <=5 elements has dim <=2; the smallest
3-dimensional poset, the standard example S_3, has 6 elements).

## Scoping findings (2026-05-29)

- `n5_edge_count_{1,2,3,4}_two_realizer` (in `N5Exhaustive/EdgeCount{1..4}.v`)
  are all Qed but **orphaned** — nothing dispatches to them. `EdgeCount4` was
  closed this session (reflection); 1/2/3 predate it.
- No master "case on `edge_count_5`, route to handler" lemma exists.
- `EdgeCount5..9` do not exist.
- No poset-duality lemma; edge count is dual-invariant anyway, so duality does
  NOT reduce high counts to low.
- **Reflection enumeration does not scale.** `EdgeCount4` enumerated
  C(25,4)=12650 edge-sets. Counts 5..9 are C(25,K) = 53130 / 177100 / 480700 /
  1081575 / 2042975. native_compute over the larger ones is infeasible
  (time + the very OOM class we just fixed). The `EdgeCount4` template is NOT
  reusable as-is for K>=6.

## Decomposition

### Category 1 — mechanical (this session)

**M1. Master edge-count dispatch** in a new file
`N5Exhaustive/EdgeCountDispatch.v` (or inside `N5DispatcherShapes.v`):
```
edge_count residual hyps -> get p,q (a strict edge) from the >=2-edges hyp
  -> carrier_5_destructure p q  => r s t + Hcov over {p,q,r,s,t}
  -> let k := edge_count_5 R2 p q r s t
  -> prove 2 <= k <= 9
  -> case k:
       2 => n5_edge_count_2_two_realizer
       3 => n5_edge_count_3_two_realizer
       4 => n5_edge_count_4_two_realizer
       5..9 => n5_edge_count_K_two_realizer  (FOCUSED ADMITS, new)
```
Supporting small lemmas:
- `edge_count_ge_2_of_two_edges`: two distinct comparable unordered pairs => k>=2.
  (Handle the (x,y)=(q,p) subtlety via antisymmetry.)
- `edge_count_le_9_of_incomparable`: an incomparable pair => k<=9.
- Both build on `EdgeCount.v` (`edge_count_5_le_10`, `strict_indicator_*`).

After M1: residual is closed *modulo* 5 focused admits
`n5_edge_count_{5,6,7,8,9}_two_realizer`. EdgeCount2/3/4 now contribute.
Admit-count bookkeeping: residual(1) -> 5 focused (net +4), but counts 2-4
genuinely closed. This is progressive refinement (D4), not regression.

### Category 2 — iterable, but technique TBD (later sessions, one per count)

**I5..I9. Close `n5_edge_count_K_two_realizer` for K=5,6,7,8,9.**
The `EdgeCount4` reflection template likely won't scale (see findings).
Candidate techniques to evaluate per count (decision needed — see Risk):
  (a) Constrained reflection: enumerate only *poset* edge-sets of count K, not
      all C(25,K) subsets (needs a smarter generator than `sublists`).
  (b) High-count cases (K=8,9) have <=2 incomparable pairs => few iso classes,
      possibly direct realizer construction.
  (c) A uniform argument (Dushnik-Miller / standard-example obstruction) that
      sidesteps per-count enumeration entirely.

### Category 3 — deep claim

If (c) pans out, the single deep input is "the smallest poset of dimension 3
has >5 elements" (or the n=5 instance of Hiraguchi). Otherwise the deep content
is distributed across the per-count iso-class realizer constructions.

## Session breakdown

- **S1 (now):** M1 master dispatch + the two bound lemmas. Commit. Verify
  `posets/dimension` green. Residual replaced by 5 focused admits.
- **S2:** Spike one of K=9 (smallest, <=1 incomparable pair) to decide the
  technique for 5-9. This de-risks before committing to 5 more builds.
- **S3-S6:** close K=8,7,6,5 with the chosen technique.

## Risk register

- R1: reflection won't scale to K>=6 (HIGH, established). Mitigation: S2 spike
  picks technique (b)/(c) before investing.
- R2: master dispatch bound lemmas (k>=2, k<=9) fiddlier than expected (LOW).
- R3: admit count temporarily rises 2 -> 6 after S1 (expected; D4).
