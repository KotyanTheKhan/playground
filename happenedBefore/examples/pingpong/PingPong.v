(**
  Infinite Ping-Pong: alternating symmetric two-process protocol.

  This file re-exports all modules for convenience.
  See individual files for details:
    - Helpers.v        : arithmetic helpers (div/mod lemmas)
    - Definitions.v    : event layout, messages, transactions, cycle maps
    - FixedHistory.v   : fixed history, rank function, acyclicity
    - ExtendedHistory.v: protocol typeclass, extended history, instance
*)

From HappenedBeforePingPong Require Export
  Helpers
  Definitions
  FixedHistory
  ExtendedHistory.
