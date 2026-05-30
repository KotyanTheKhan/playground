From Stdlib Require Import List Bool.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8 N5Reflect6.
Lemma cov6_c0 : forallb chk6 (firstn 1680 (skipn 0 count6_assigns)) = true.
Proof. native_cast_no_check (eq_refl true). Qed.
