From Stdlib Require Import List Bool.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8 N5Reflect5.
Lemma cov5_c0 : forallb chk5 (firstn 1008 (skipn 0 count5_assigns)) = true.
Proof. native_cast_no_check (eq_refl true). Qed.
