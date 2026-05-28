---
name: searching-existing-formalizations
description: Use before starting hard Coq formalization work or admitting a complex lemma — check whether the theorem (or a close variant) is already proven in Coq, MathComp, or community libraries. Triggers: starting a new formalization track, about to write a non-trivial Lemma, considering admitting a deep claim, stuck on a proof technique, reaching for a tactic pattern you suspect already exists.
---

# Searching Existing Formalizations

Before reinventing a proof, check if it (or a close variant) already exists. A 5-minute search can save days of formalization work.

## When to invoke

Trigger this skill when about to:
- **Start a new formalization track** (e.g., before "Track B: Trotter Ch.6").
- **Admit a complex lemma** — first verify nobody has formalized it.
- **Write a multi-page Qed** — there may be a library tactic.
- **Implement a structural recursion** — likely covered by existing infrastructure.
- **Define a typeclass / record** — existing libraries may have the same shape.

## What to search for

Search in priority order:

### Tier 1: Coq-direct sources (proofs you can import/adapt)

1. **[Coq Package Index](https://coq.inria.fr/opam/www/)** — `mise exec -- opam search <topic>` or browse the web index. Look for packages with names matching your domain (e.g., `coq-dimension`, `coq-poset`, `coq-order`).

2. **[coq-community on GitHub](https://github.com/coq-community)** — curated community projects. Search the org for your theorem. This is where Dilworth's theorem and many combinatorial results live.

3. **[MathComp library](https://math-comp.github.io/htmldoc_2_3_0/index.html)** — Bourbaki-style ssreflect mathematics. Has `fintype`, `finset`, `order`, `poset` modules. Even if you're not using ssreflect, the proof STRUCTURE is informative.

4. **[Coq Standard Library](https://coq.inria.fr/library/)** — basic structures + `Relations.*`. Useful for: order relations, well-foundedness, finite enumerations.

5. **[Stdpp](https://gitlab.mpi-sws.org/iris/stdpp)** — Iris's std library extension. Strong on finite sets, multisets, lists.

### Tier 2: Intuition sources (read for ideas, not direct import)

6. **Google Scholar** — search the theorem name + "Coq" or "formal proof". May reveal informal write-ups or papers describing formalization attempts.

7. **[nLab](https://ncatlab.org/)** — category-theoretic encyclopedia. Useful for spotting equivalent formulations of your problem (e.g., "this is just an adjunction").

8. **[OEIS](https://oeis.org/)** — for combinatorial sequences/objects. We used A000112 (unlabeled posets count) for the n=5 enumeration.

### Tier 3: Discussion/community

9. **[Coq Zulip](https://coq.zulipchat.com/)** — search the chat history for tactic patterns or "how do I prove X". Active community.

10. **[Coq Discourse](https://coq.discourse.group/)** — Q&A site. Long-form discussions.

11. **[Proof General Mailing List archives](https://lists.gforge.inria.fr/pipermail/coq-club/)** — historical Coq community.

### Tier 4: Cross-system (informational only)

12. **[Mizar Mathematical Library](http://mizar.org/library/)** — formal mathematics in Mizar. Different logic; useful for *seeing how a theorem decomposes*, not for direct import.

13. **[Isabelle AFP](https://www.isa-afp.org/)** — Archive of Formal Proofs. Has many order-theoretic results. Again, intuition only.

14. **[Lean Mathlib](https://leanprover-community.github.io/mathlib4_docs/)** — fast-growing mathematical library in Lean. Often the most up-to-date formalization of advanced math.

## Search protocol

When you decide to search:

1. **Identify the precise statement** you'd be proving. The more specific, the better the search.
2. **Extract keywords**: `poset dimension`, `Hiraguchi bound`, `Trotter removable pair`, etc.
3. **Run 2-3 targeted searches** across Tier 1 sources first. Use `WebFetch` to read promising pages.
4. **If Tier 1 misses**, escalate to Tier 2 for intuition; Tier 3 for community wisdom.
5. **Document what you found** (or didn't) in a comment near the lemma you're about to write or admit. Future agents will thank you.

## What to do with results

### Found a matching Coq formalization
- **In an opam package**: add it as a dependency (via `mise.toml`).
- **In a GitHub repo not on opam**: vendor it (`vendor/<name>/`), like we did with `ZornsLemma`.
- **In MathComp**: import the relevant module; you may need to translate types between MathComp and the project's typeclasses.

### Found a close-but-not-identical formalization
- **Adapt the proof structure** — reuse the strategy, retype the statement to fit your context.
- **Cite the source** in a comment so future readers know where the approach came from.

### Found only literature references (no formal proof)
- Read the paper(s) to understand the standard proof technique.
- Decompose into smaller lemmas as the paper does.
- This is where Trotter Ch.6 fell for us: clear paper proof, no formalization, so we built it ourselves.

### Found nothing
- Document the search itself in a comment.
- Proceed with original formalization, knowing you're on the frontier.

## Anti-patterns

- **Searching during proof crisis**: search BEFORE starting hard work, not after you're stuck for hours.
- **Treating Mizar/Isabelle/Lean as "just copy-paste"**: different logics, different libraries. Translation is non-trivial.
- **Endless searching**: 30 min max per search session. If nothing surfaces, proceed with original work.
- **Ignoring near-matches**: a slightly different theorem statement often has a useful proof structure.

## Quick triggers

| You're about to... | Search first for... |
|---|---|
| Define a new typeclass for an algebraic structure | "<structure name> typeclass site:github.com" |
| Prove a lemma about finite enumeration | MathComp `finset` / `fintype` modules |
| Admit a result with a known classical proof | The paper title + "Coq" or "formal" |
| Reach for `well_founded` recursion | Stdlib `Wellfounded.*`, MathComp `Wf` |
| Implement a fixed-point combinator | Stdlib `Wf` or MathComp `recurrence` patterns |
| Prove dimension/cardinality bounds | OEIS sequence + paper references |

## Worked example: what we should have done for Trotter

Before starting Track B (~15 hours of work), we should have:

1. Searched coq-community for "trotter" / "dimension" / "poset" → likely no direct hit.
2. Searched MathComp's `order` module → see if dimension is defined.
3. Searched Lean's Mathlib for `Order.Dimension` → would have shown the formal approach (if any).
4. Searched Google Scholar for "Coq formalization order dimension" → may have found related work.
5. Read Trotter's Ch.6 directly to identify exact intermediate lemmas needed.

If we had found nothing (likely the case for n ≥ 6), we'd still benefit from steps 1-4 by knowing the formalization is genuinely novel. The 30-minute search would have been a good investment.
