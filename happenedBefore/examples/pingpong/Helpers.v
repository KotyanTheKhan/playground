From Stdlib Require Import Arith Lia.

(** Arithmetic helpers for ping-pong cycle index / offset calculations. *)

Section PingPongHelpers.

  Lemma div_mul_add_small : forall a b n,
    n > 0 -> b < n -> (a * n + b) / n = a.
  Proof.
    intros. rewrite Nat.div_add_l by lia. rewrite Nat.div_small by lia. lia.
  Qed.

  Lemma mod_mul_add_small : forall a b n,
    n > 0 -> b < n -> (a * n + b) mod n = b.
  Proof.
    intros a b n Hn Hb.
    rewrite Nat.add_comm, Nat.Div0.mod_add. apply Nat.mod_small; assumption.
  Qed.

  (** Cycle index of the (1+k)-th internal event when events_per_cycle = 2 + gap. *)
  Lemma int_event_same_cycle : forall i k gap,
    k < gap -> (i * (2 + gap) + 1 + k) / (2 + gap) = i.
  Proof.
    intros i k gap Hk.
    replace (i * (2 + gap) + 1 + k) with (i * (2 + gap) + (1 + k)) by lia.
    apply div_mul_add_small; lia.
  Qed.

  (** Intra-cycle offset of the (1+k)-th internal event when events_per_cycle = 2 + gap. *)
  Lemma int_event_offset : forall i k gap,
    k < gap -> (i * (2 + gap) + 1 + k) mod (2 + gap) = 1 + k.
  Proof.
    intros i k gap Hk.
    replace (i * (2 + gap) + 1 + k) with (i * (2 + gap) + (1 + k)) by lia.
    apply mod_mul_add_small; lia.
  Qed.

End PingPongHelpers.
