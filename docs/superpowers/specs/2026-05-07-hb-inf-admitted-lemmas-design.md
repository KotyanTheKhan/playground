# Design: Prove admitted lemmas in ExtendedHistory.v via `hb_inf`

## Problem

`happenedBefore/examples/pingpong/ExtendedHistory.v` contains four admitted lemmas:

```coq
ax_ping : forall n i, happened_before (pp_history_ext n) (map_ping_send i) (map_ping_recv i)
ax_turn : forall n i, happened_before (pp_history_ext n) (map_ping_recv i) (map_pong_send i)
ax_pong : forall n i, happened_before (pp_history_ext n) (map_pong_send i) (map_pong_recv i)
ax_next : forall n i, happened_before (pp_history_ext n) (map_pong_recv i) (map_ping_send (S i))
```

These are **false as stated**: for small `n` (e.g., `n = 0`) the history is empty and
`happened_before nil e1 e2` reduces to `e1 = e2`. Since ping-send and ping-recv live on
different processes, the statement fails. No finite `n` can satisfy `forall i` because
for any fixed `n`, cycles with `i * msgs_per_cycle_ext >= n` are not in the history.

The in-range sub-cases are already proved (`ping_causes_recv_ext`, `turn_causes_pong_ext`,
`pong_causes_recv_ext`, `inter_causes_next_ext`). The `Admitted`s cover the impossible
out-of-range case.

## Solution: Colimit relation `hb_inf`

### New definition

Inside `Section PingPongParameters` in `ExtendedHistory.v`, add:

```coq
Definition hb_inf (e1 e2 : Event) : Prop :=
  exists n, happened_before (pp_history_ext n) e1 e2.
```

`hb_inf` is the causal relation over unbounded execution: `e1` causally precedes `e2`
iff they are related in some finite prefix. It is the Prop-level colimit of the
`pp_history_ext` chain.

### Replace the four admitted lemmas

Change statement from `forall n i, happened_before (pp_history_ext n) ...` to
`forall i, hb_inf ...`. Each proof picks the minimal `n` that puts the relevant
message in the history, then applies the existing in-range lemma:

```coq
Lemma ax_ping : forall i,
  hb_inf (map_ping_send GAP_0 GAP_1 i) (map_ping_recv GAP_0 GAP_1 i).
Proof.
  intro i. unfold hb_inf.
  exists (i * msgs_per_cycle_ext + 1). apply ping_causes_recv_ext. lia.
Qed.

Lemma ax_turn : forall i,
  hb_inf (map_ping_recv GAP_0 GAP_1 i) (map_pong_send GAP_0 GAP_1 i).
Proof.
  intro i. unfold hb_inf.
  exists (i * msgs_per_cycle_ext + 2). apply turn_causes_pong_ext. lia.
Qed.

Lemma ax_pong : forall i,
  hb_inf (map_pong_send GAP_0 GAP_1 i) (map_pong_recv GAP_0 GAP_1 i).
Proof.
  intro i. unfold hb_inf.
  exists (i * msgs_per_cycle_ext + 3). apply pong_causes_recv_ext. lia.
Qed.

Lemma ax_next : forall i,
  hb_inf (map_pong_recv GAP_0 GAP_1 i) (map_ping_send GAP_0 GAP_1 (S i)).
Proof.
  intro i. unfold hb_inf.
  exists (i * msgs_per_cycle_ext + 4). apply inter_causes_next_ext. lia.
Qed.
```

### Updated instance

The `n` parameter is dropped; the instance is over `hb_inf`:

```coq
Instance ex_is_ping_pong : IsPairAlternatingSymPingPong hb_inf.
Proof.
  exact {|
    map_cycle_ping_send := map_ping_send GAP_0 GAP_1;
    map_cycle_ping_recv := map_ping_recv GAP_0 GAP_1;
    map_cycle_pong_send := map_pong_send GAP_0 GAP_1;
    map_cycle_pong_recv := map_pong_recv GAP_0 GAP_1;
    ax_even_init := map_ping_send_even_process GAP_0 GAP_1;
    ax_even_resp := map_ping_recv_even_process GAP_0 GAP_1;
    ax_odd_init  := map_ping_send_odd_process  GAP_0 GAP_1;
    ax_odd_resp  := map_ping_recv_odd_process  GAP_0 GAP_1;
    ax_ping_rel  := ax_ping;
    ax_turn_rel  := ax_turn;
    ax_pong_rel  := ax_pong;
    ax_next_rel  := ax_next
  |}.
Defined.
```

## Migration note

Any downstream site that wrote `ex_is_ping_pong n` (passing an explicit `n`) must drop
that argument and use `hb_inf` as the relation instead of
`happened_before (pp_history_ext n)`.

## Files changed

- `happenedBefore/examples/pingpong/ExtendedHistory.v` — only file modified
