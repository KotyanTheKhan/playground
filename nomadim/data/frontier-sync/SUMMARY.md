# Minimum-synchronization fully frontier-synchronized executions

An *execution* is `N` processes plus an ordered list of pairwise synchronizations. It is **fully frontier synchronized** when every process' start event is causally below every process' last event (`is_full_synchronized`): the whole opening frontier is seen by the whole closing frontier.

Grouped by **order dimension** (dimensions are bounded by `N`). For each `N` and each dimension `d` that a fully-synchronized execution of `N` processes can have, `S` is the **minimum** number of synchronizations achieving dimension `d`; the rows are the distinct (non-isomorphic) executions at that `(d, S)`. Found with `nomadim enumerate --all-dims --with-dim -j 4`; realizer counts from `nomadim dimension --all` (capped at 1000).

**Headline:** a higher dimension is *cheaper* in syncs. The minimum full synchronization of N processes is the highest-dimensional one; spending extra syncs lowers the dimension. Within `N <= 5` only dimensions 2 and 3 occur.

| N | dimension | min S | # shapes | shape | # realizers | syncs | file |
|---|-----------|-------|----------|-------|-------------|-------|------|
| 2 | 2 | 1 | 1 | 1 | 2 | (0,1) | `N2_S1_dim2_real2_01.yaml` |
| 3 | 2 | 3 | 2 | 1 | 4 | (0,1) (0,2) (0,1) | `N3_S3_dim2_real4_01.yaml` |
| 3 | 2 | 3 | 2 | 2 | 4 | (0,1) (0,2) (1,2) | `N3_S3_dim2_real4_02.yaml` |
| 4 | 2 | 5 | 10 | 1 | 4 | (0,1) (0,2) (0,3) (0,2) (0,1) | `N4_S5_dim2_real4_01.yaml` |
| 4 | 2 | 5 | 10 | 2 | 4 | (0,1) (0,2) (0,3) (0,2) (1,2) | `N4_S5_dim2_real4_02.yaml` |
| 4 | 2 | 5 | 10 | 3 | 4 | (0,1) (0,2) (0,3) (2,3) (1,2) | `N4_S5_dim2_real4_03.yaml` |
| 4 | 2 | 5 | 10 | 4 | 4 | (0,1) (0,2) (0,3) (2,3) (1,3) | `N4_S5_dim2_real4_04.yaml` |
| 4 | 2 | 5 | 10 | 5 | 4 | (0,1) (0,2) (2,3) (0,2) (0,1) | `N4_S5_dim2_real4_05.yaml` |
| 4 | 2 | 5 | 10 | 6 | 4 | (0,1) (0,2) (2,3) (0,2) (1,2) | `N4_S5_dim2_real4_06.yaml` |
| 4 | 2 | 5 | 10 | 7 | 4 | (0,1) (0,2) (2,3) (0,3) (0,1) | `N4_S5_dim2_real4_07.yaml` |
| 4 | 2 | 5 | 10 | 8 | 4 | (0,1) (0,2) (2,3) (0,3) (1,3) | `N4_S5_dim2_real4_08.yaml` |
| 4 | 2 | 5 | 10 | 9 | 16 | (0,1) (2,3) (0,2) (0,1) (2,3) | `N4_S5_dim2_real16_09.yaml` |
| 4 | 2 | 5 | 10 | 10 | 16 | (0,1) (2,3) (0,2) (0,3) (1,2) | `N4_S5_dim2_real16_10.yaml` |
| 4 | 3 | 4 | 1 | 1 | >=1000 (cap) | (0,1) (2,3) (0,2) (1,3) | `N4_S4_dim3_real1000cap_01.yaml` |
| 5 | 2 | 7 | 40 | 1 | 4 | (0,1) (0,2) (0,3) (0,4) (0,3) (0,2) (0,1) | `N5_S7_dim2_real4_01.yaml` |
| 5 | 2 | 7 | 40 | 2 | 4 | (0,1) (0,2) (0,3) (0,4) (0,3) (0,2) (1,2) | `N5_S7_dim2_real4_02.yaml` |
| 5 | 2 | 7 | 40 | 3 | 4 | (0,1) (0,2) (0,3) (0,4) (0,3) (2,3) (1,2) | `N5_S7_dim2_real4_03.yaml` |
| 5 | 2 | 7 | 40 | 4 | 4 | (0,1) (0,2) (0,3) (0,4) (0,3) (2,3) (1,3) | `N5_S7_dim2_real4_04.yaml` |
| 5 | 2 | 7 | 40 | 5 | 4 | (0,1) (0,2) (0,3) (0,4) (3,4) (2,3) (1,2) | `N5_S7_dim2_real4_05.yaml` |
| 5 | 2 | 7 | 40 | 6 | 4 | (0,1) (0,2) (0,3) (0,4) (3,4) (2,3) (1,3) | `N5_S7_dim2_real4_06.yaml` |
| 5 | 2 | 7 | 40 | 7 | 4 | (0,1) (0,2) (0,3) (0,4) (3,4) (2,4) (1,2) | `N5_S7_dim2_real4_07.yaml` |
| 5 | 2 | 7 | 40 | 8 | 4 | (0,1) (0,2) (0,3) (0,4) (3,4) (2,4) (1,4) | `N5_S7_dim2_real4_08.yaml` |
| 5 | 2 | 7 | 40 | 9 | 4 | (0,1) (0,2) (0,3) (3,4) (0,3) (0,2) (0,1) | `N5_S7_dim2_real4_09.yaml` |
| 5 | 2 | 7 | 40 | 10 | 4 | (0,1) (0,2) (0,3) (3,4) (0,3) (0,2) (1,2) | `N5_S7_dim2_real4_10.yaml` |
| 5 | 2 | 7 | 40 | 11 | 4 | (0,1) (0,2) (0,3) (3,4) (0,3) (2,3) (1,2) | `N5_S7_dim2_real4_11.yaml` |
| 5 | 2 | 7 | 40 | 12 | 4 | (0,1) (0,2) (0,3) (3,4) (0,3) (2,3) (1,3) | `N5_S7_dim2_real4_12.yaml` |
| 5 | 2 | 7 | 40 | 13 | 4 | (0,1) (0,2) (0,3) (3,4) (0,4) (0,2) (0,1) | `N5_S7_dim2_real4_13.yaml` |
| 5 | 2 | 7 | 40 | 14 | 4 | (0,1) (0,2) (0,3) (3,4) (0,4) (0,2) (1,2) | `N5_S7_dim2_real4_14.yaml` |
| 5 | 2 | 7 | 40 | 15 | 4 | (0,1) (0,2) (0,3) (3,4) (0,4) (2,4) (1,2) | `N5_S7_dim2_real4_15.yaml` |
| 5 | 2 | 7 | 40 | 16 | 4 | (0,1) (0,2) (0,3) (3,4) (0,4) (2,4) (1,4) | `N5_S7_dim2_real4_16.yaml` |
| 5 | 2 | 7 | 40 | 17 | 4 | (0,1) (0,2) (2,3) (2,4) (2,3) (0,2) (0,1) | `N5_S7_dim2_real4_17.yaml` |
| 5 | 2 | 7 | 40 | 18 | 4 | (0,1) (0,2) (2,3) (2,4) (2,3) (0,2) (1,2) | `N5_S7_dim2_real4_18.yaml` |
| 5 | 2 | 7 | 40 | 19 | 4 | (0,1) (0,2) (2,3) (2,4) (2,3) (0,3) (0,1) | `N5_S7_dim2_real4_19.yaml` |
| 5 | 2 | 7 | 40 | 20 | 4 | (0,1) (0,2) (2,3) (2,4) (2,3) (0,3) (1,3) | `N5_S7_dim2_real4_20.yaml` |
| 5 | 2 | 7 | 40 | 21 | 4 | (0,1) (0,2) (2,3) (2,4) (3,4) (0,3) (0,1) | `N5_S7_dim2_real4_21.yaml` |
| 5 | 2 | 7 | 40 | 22 | 4 | (0,1) (0,2) (2,3) (2,4) (3,4) (0,3) (1,3) | `N5_S7_dim2_real4_22.yaml` |
| 5 | 2 | 7 | 40 | 23 | 4 | (0,1) (0,2) (2,3) (2,4) (3,4) (0,4) (0,1) | `N5_S7_dim2_real4_23.yaml` |
| 5 | 2 | 7 | 40 | 24 | 4 | (0,1) (0,2) (2,3) (2,4) (3,4) (0,4) (1,4) | `N5_S7_dim2_real4_24.yaml` |
| 5 | 2 | 7 | 40 | 25 | 4 | (0,1) (0,2) (2,3) (3,4) (2,3) (0,2) (0,1) | `N5_S7_dim2_real4_25.yaml` |
| 5 | 2 | 7 | 40 | 26 | 4 | (0,1) (0,2) (2,3) (3,4) (2,3) (0,2) (1,2) | `N5_S7_dim2_real4_26.yaml` |
| 5 | 2 | 7 | 40 | 27 | 4 | (0,1) (0,2) (2,3) (3,4) (2,3) (0,3) (0,1) | `N5_S7_dim2_real4_27.yaml` |
| 5 | 2 | 7 | 40 | 28 | 4 | (0,1) (0,2) (2,3) (3,4) (2,3) (0,3) (1,3) | `N5_S7_dim2_real4_28.yaml` |
| 5 | 2 | 7 | 40 | 29 | 4 | (0,1) (0,2) (2,3) (3,4) (2,4) (0,2) (0,1) | `N5_S7_dim2_real4_29.yaml` |
| 5 | 2 | 7 | 40 | 30 | 4 | (0,1) (0,2) (2,3) (3,4) (2,4) (0,2) (1,2) | `N5_S7_dim2_real4_30.yaml` |
| 5 | 2 | 7 | 40 | 31 | 4 | (0,1) (0,2) (2,3) (3,4) (2,4) (0,4) (0,1) | `N5_S7_dim2_real4_31.yaml` |
| 5 | 2 | 7 | 40 | 32 | 4 | (0,1) (0,2) (2,3) (3,4) (2,4) (0,4) (1,4) | `N5_S7_dim2_real4_32.yaml` |
| 5 | 2 | 7 | 40 | 33 | 16 | (0,1) (0,2) (3,4) (0,3) (0,2) (0,1) (3,4) | `N5_S7_dim2_real16_33.yaml` |
| 5 | 2 | 7 | 40 | 34 | 16 | (0,1) (0,2) (3,4) (0,3) (0,2) (1,2) (3,4) | `N5_S7_dim2_real16_34.yaml` |
| 5 | 2 | 7 | 40 | 35 | 16 | (0,1) (0,2) (3,4) (0,3) (0,4) (2,3) (1,2) | `N5_S7_dim2_real16_35.yaml` |
| 5 | 2 | 7 | 40 | 36 | 16 | (0,1) (0,2) (3,4) (0,3) (0,4) (2,3) (1,3) | `N5_S7_dim2_real16_36.yaml` |
| 5 | 2 | 7 | 40 | 37 | 16 | (0,1) (0,2) (3,4) (2,3) (0,2) (0,1) (3,4) | `N5_S7_dim2_real16_37.yaml` |
| 5 | 2 | 7 | 40 | 38 | 16 | (0,1) (0,2) (3,4) (2,3) (0,2) (1,2) (3,4) | `N5_S7_dim2_real16_38.yaml` |
| 5 | 2 | 7 | 40 | 39 | 16 | (0,1) (0,2) (3,4) (2,3) (0,3) (0,1) (2,4) | `N5_S7_dim2_real16_39.yaml` |
| 5 | 2 | 7 | 40 | 40 | 16 | (0,1) (0,2) (3,4) (2,3) (0,3) (1,3) (2,4) | `N5_S7_dim2_real16_40.yaml` |
| 5 | 3 | 6 | 4 | 1 | >=1000 (cap) | (0,1) (0,2) (3,4) (0,3) (0,1) (2,4) | `N5_S6_dim3_real1000cap_01.yaml` |
| 5 | 3 | 6 | 4 | 2 | >=1000 (cap) | (0,1) (0,2) (3,4) (0,3) (2,4) (1,2) | `N5_S6_dim3_real1000cap_02.yaml` |
| 5 | 3 | 6 | 4 | 3 | >=1000 (cap) | (0,1) (0,2) (3,4) (0,3) (2,4) (1,3) | `N5_S6_dim3_real1000cap_03.yaml` |
| 5 | 3 | 6 | 4 | 4 | >=1000 (cap) | (0,1) (0,2) (3,4) (0,3) (2,4) (1,4) | `N5_S6_dim3_real1000cap_04.yaml` |

Notes:

- Within `N <= 5` the only dimensions that occur are **2** and **3** (verified for every shape up to S=8 for N=4 and N=5); `N=2` and `N=3` are always dimension 2, and dimension 3 first appears at `N=4`. See `FINDINGS.md` for the full dimension histograms.
- A higher dimension needs *fewer* syncs: dim 3 fully synchronizes N=4 in 4 syncs / N=5 in 6 syncs, but dim 2 needs 5 / 7 respectively.
- The default enumerator keeps only dimension <= 2, so it never sees the dimension-3 minimum shapes and over-reports the minimum S.
- '# realizers' counts minimum colorings of the critical-pair hypergraph; `>=1000 (cap)` means the count reached the tool's 1000 cap.
