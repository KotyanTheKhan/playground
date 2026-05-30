From Stdlib Require Import List Bool.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8 N5Reflect6.
Lemma cov6_c7 : forallb chk6 (firstn 1680 (skipn 11760 count6_assigns)) = true.
Proof. native_cast_no_check (eq_refl true). Qed.
