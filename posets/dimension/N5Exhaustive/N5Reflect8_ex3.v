(* Count-8 exhaustiveness chunk 3: native_cast over 1/5 of count8_assigns. *)
From Stdlib Require Import List.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8.

Lemma cov_c3 : forallb chk8 (firstn 2304 (skipn 6912 count8_assigns)) = true.
Proof. native_cast_no_check (eq_refl true). Qed.
