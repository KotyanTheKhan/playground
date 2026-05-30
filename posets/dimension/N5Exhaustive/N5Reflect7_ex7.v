(** Count-7 coverage chunk 7/7 (native_cast). *)
From Stdlib Require Import List Bool.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8 N5Reflect7.
Lemma cov7_c7 : forallb chk7 (firstn 1920 (skipn 13440 count7_assigns)) = true.
Proof. native_cast_no_check (eq_refl true). Qed.
