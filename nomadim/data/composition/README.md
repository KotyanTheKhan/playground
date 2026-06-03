# Frontier composition examples

Connecting two concurrent groups of events by a **frontier** (which group-1 event
sends a message to which group-2 event), and what it does to the order **dimension**.
Each file is a `poset:` doc on 6 vertices — group-1 events `a0,a1,a2` = vertices
`0,1,2`, group-2 events `b0,b1,b2` = vertices `3,4,5`, edges = the frontier messages
`a_i -> b_j`. Open in the nomadim editor and press *Compute dimension* to verify.

Both groups are dim-2 antichains on their own; the question is whether the
connection **preserves** dim 2.

| File | Scenario | Frontier `F a_i b_j` | dim | Coq |
|------|----------|----------------------|-----|-----|
| `01_broadcast_barrier_dim2.yaml` | broadcast / full barrier | always (every a→every b) | **2** | `threshold_dim_le2` (φ=ψ=0) |
| `02_cascade_staircase_dim2.yaml` | cascade / staircase pipeline | `i ≤ j` (nested rows) | **2** | `threshold_dim_le2` = `Fstair` |
| `03_gather_funnel_dim2.yaml` | gather / funnel | `j = 0` (one column) | **2** | `threshold_dim_le2` |
| `04_scatter_fanout_dim2.yaml` | scatter / fan-out | `i = 0` (one row) | **2** | `threshold_dim_le2` |
| `05_parallel_handoff_dim2.yaml` | parallel hand-off | `i = j` (diagonal matching) | **2** | `disjoint_chains_dim_le2` (not Ferrers) |
| `06_crown_roundrobin_dim3.yaml` | round-robin avoidance (crown / S₃) | `i ≠ j` (maximal crossing) | **3** | `crown3_dim_ge_3` |

**Rule of thumb:** a frontier **composes** (keeps dim 2) when its messages, drawn
between a linearly-ordered send side and receive side, form a **staircase with no
crossings** (a Ferrers / threshold relation): 01–04 above. A simple disjoint
matching (05) also stays dim 2. Only a **genuinely crossing** frontier — the
round-robin crown (06), the standard example S₃ — raises the dimension to 3.

Formalized in `execution/FrontierCompose.v` (the `threshold_dim_le2` /
`crown3_dim_ge_3` dichotomy); `06` is identical to `../poset_s3.yaml`.
