(** Combine the 8 count-6 coverage chunks into the full coverage fact. *)
From Stdlib Require Import List Arith Lia.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8 N5Reflect6
  N5Reflect6_ex0 N5Reflect6_ex1 N5Reflect6_ex2 N5Reflect6_ex3
  N5Reflect6_ex4 N5Reflect6_ex5 N5Reflect6_ex6 N5Reflect6_ex7.
Import ListNotations.

Lemma skipn_skipn6 : forall (A:Type) m n (l:list A),
  skipn n (skipn m l) = skipn (m+n) l.
Proof.
  induction m as [|m IH]; intros n l.
  - reflexivity.
  - destruct l as [|x t]. + rewrite !skipn_nil. reflexivity. + simpl. apply IH.
Qed.

Lemma len6 : length count6_assigns = 13440.
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_app6 : forall (A:Type) (f:A->bool) (a b:list A),
  forallb f (a ++ b) = andb (forallb f a) (forallb f b).
Proof. induction a as [|x a IH]; intro b; simpl; [reflexivity | rewrite IH; now destruct (f x)]. Qed.

Lemma cov6_0 : forallb chk6 (firstn 1680 count6_assigns) = true.
Proof. exact cov6_c0. Qed.

Lemma t1 : skipn 1680 (skipn 1680 count6_assigns) = skipn 3360 count6_assigns.
Proof. now rewrite skipn_skipn6. Qed.
Lemma t2 : skipn 1680 (skipn 3360 count6_assigns) = skipn 5040 count6_assigns.
Proof. now rewrite skipn_skipn6. Qed.
Lemma t3 : skipn 1680 (skipn 5040 count6_assigns) = skipn 6720 count6_assigns.
Proof. now rewrite skipn_skipn6. Qed.
Lemma t4 : skipn 1680 (skipn 6720 count6_assigns) = skipn 8400 count6_assigns.
Proof. now rewrite skipn_skipn6. Qed.
Lemma t5 : skipn 1680 (skipn 8400 count6_assigns) = skipn 10080 count6_assigns.
Proof. now rewrite skipn_skipn6. Qed.
Lemma t6 : skipn 1680 (skipn 10080 count6_assigns) = skipn 11760 count6_assigns.
Proof. now rewrite skipn_skipn6. Qed.

Lemma coverage_6 : forallb chk6 count6_assigns = true.
Proof.
  assert (E : count6_assigns =
    firstn 1680 count6_assigns ++
    firstn 1680 (skipn 1680 count6_assigns) ++
    firstn 1680 (skipn 3360 count6_assigns) ++
    firstn 1680 (skipn 5040 count6_assigns) ++
    firstn 1680 (skipn 6720 count6_assigns) ++
    firstn 1680 (skipn 8400 count6_assigns) ++
    firstn 1680 (skipn 10080 count6_assigns) ++
    firstn 1680 (skipn 11760 count6_assigns)).
  { rewrite <- (firstn_skipn 1680 count6_assigns) at 1; f_equal;
    rewrite <- (firstn_skipn 1680 (skipn 1680 count6_assigns)) at 1; f_equal;
    rewrite t1;
    rewrite <- (firstn_skipn 1680 (skipn 3360 count6_assigns)) at 1; f_equal;
    rewrite t2;
    rewrite <- (firstn_skipn 1680 (skipn 5040 count6_assigns)) at 1; f_equal;
    rewrite t3;
    rewrite <- (firstn_skipn 1680 (skipn 6720 count6_assigns)) at 1; f_equal;
    rewrite t4;
    rewrite <- (firstn_skipn 1680 (skipn 8400 count6_assigns)) at 1; f_equal;
    rewrite t5;
    rewrite <- (firstn_skipn 1680 (skipn 10080 count6_assigns)) at 1; f_equal;
    rewrite t6;
    symmetry; apply firstn_all2; rewrite length_skipn, len6; lia. }
  rewrite E. rewrite !forallb_app6.
  rewrite cov6_0, cov6_c1, cov6_c2, cov6_c3, cov6_c4, cov6_c5, cov6_c6, cov6_c7.
  reflexivity.
Qed.
