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

## S2 spike result (2026-05-29) — technique validated

**Do NOT use reflection for counts 5-9.** The vehicle is
`n5_two_realizer_framework` (N5Realizers.v:285), the same lemma all 30+
per-class handlers use. It takes two rank functions `rk1 rk2 : B -> nat` and
discharges all realizer machinery from:
  - pairwise-distinct ranks (2 x 10 goals),
  - R2-monotone: `R2 x y -> rk_i x <= rk_i y` (2 goals),
  - intersection: `rk1 x<=rk1 y -> rk2 x<=rk2 y -> R2 x y` (1 goal),
  - a distinguishing pair `exists x y, rk1 x<=rk1 y /\ rk2 y<rk2 x` (1 goal).

So each count K=5..9 is an explicit rank construction, NOT enumeration.

Count-9 structure: edge_count=9 => exactly one incomparable pair {u,v}; by
transitivity u,v are TWINS (identical order relations to the other three
elements, which are totally ordered). `rk1`/`rk2` = the down-count ranking with
the u/v tie broken oppositely. Estimated ~1 session (~120-300 lines, cf.
`n5_one_edge_two_realizer`); identify the pair, ~4 structural sub-cases for
where the twin block sits, discharge the framework goals by `lia`.

Counts 8,7,6,5 have 2,3,4,5 incomparable pairs respectively (harder rank
constructions; count-5 needs the incomparability graph to be 2-colorable into
the two extensions, which holds for n=5 but is the most involved).

## Count-9 concrete construction (designed 2026-05-29) — NO case-split

Define on the carrier {a,b,c,d,e} (B arbitrary, use `excluded_middle_informative`):
- `lab x` := 0/1/2/3/4 by which of a..e x is (injective on carrier by Hcov + distinctness).
- `rk x`  := down-count = sum over z in {a,b,c,d,e} of `[R2 z x]` (reflexive-inclusive).
- `rk1 x := 6 * rk x + lab x`,  `rk2 x := 6 * rk x + (4 - lab x)`.

Invoke `n5_two_realizer_framework R2 a b c d e ... rk1 rk2`. Supporting lemmas
(all GENERIC — no enumeration, no structural sub-cases):
1. `lab` injective on carrier (casework on Hcov x, Hcov y + the 10 distinctness hyps).
2. `rk` monotone: `R2 x y -> rk x <= rk y` (down-set inclusion via transitivity).
3. `rk` strict:   `R2 x y -> x<>y -> rk x < rk y` (y is in down(y)\down(x)).
   => rk1, rk2 monotone (R2 x y gives x=y or rk x < rk y; the +lab/+(4-lab)
   slack is < 6 <= 6*(rk y - rk x), so lia closes).
4. rk1, rk2 injective: `6*rk x + lab x = 6*rk y + lab y` with lab in [0,4] forces
   rk x = rk y and lab x = lab y => x = y. Gives all 20 pairwise-distinct goals.
5. Extract THE incomparable pair: `edge_count_5 = 9` => exactly one pair has
   indicator-sum 0 => incomparable; all others comparable. (10 classic splits;
   the all-comparable branch forces edge_count = 10 via "distinct comparable
   pair has indicator-sum 1", contradiction with = 9.) Yields u,v incomparable
   and "every other carrier element is comparable to both u and v".
6. Twin/equal-rk: incomparable u,v with all z comparable to both => for each z,
   R2 z u <-> R2 z u and (by transitivity) z is on the same side of u and v, so
   down(u) and down(v) have the same common part; with u not in down(v) and v
   not in down(u), rk u = rk v.
   INTERSECTION (`rk1 x<=rk1 y -> rk2 x<=rk2 y -> R2 x y`): adding the two gives
   rk x <= rk y; if rk x = rk y then x = y (rk1 inj-style) and R2 x x; if
   rk x < rk y then x,y are NOT the (equal-rk) incomparable pair, so comparable,
   and R2 y x would give rk y < rk x — so R2 x y. (Uses lemma 6: the only
   incomparable pair has equal rk, so rk x < rk y rules out incomparable.)
   DISTINGUISHING pair: take the extracted u,v; WLOG lab u < lab v (else swap),
   rk u = rk v, so rk1 u <= rk1 v and rk2 v < rk2 u.

Estimated ~200-250 lines, ~6 small lemmas, fast compile (no native_compute).

## Risk register

- R1: reflection won't scale to K>=6 (HIGH, established). Mitigation: S2 spike
  picks technique (b)/(c) before investing.
- R2: master dispatch bound lemmas (k>=2, k<=9) fiddlier than expected (LOW).
- R3: admit count temporarily rises 2 -> 6 after S1 (expected; D4).
