(** Combine the 8 count-5 coverage chunks. *)
From Stdlib Require Import List Arith Lia.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8 N5Reflect5
  N5Reflect5_ex0 N5Reflect5_ex1 N5Reflect5_ex2 N5Reflect5_ex3
  N5Reflect5_ex4 N5Reflect5_ex5 N5Reflect5_ex6 N5Reflect5_ex7.
Import ListNotations.
Lemma skipn_skipn5 : forall (A:Type) m n (l:list A),
  skipn n (skipn m l) = skipn (m+n) l.
Proof. induction m as [|m IH]; intros n l. - reflexivity.
  - destruct l as [|x t]. + rewrite !skipn_nil. reflexivity. + simpl. apply IH. Qed.
Lemma len5 : length count5_assigns = 8064.
Proof. vm_compute. reflexivity. Qed.
Lemma forallb_app5 : forall (A:Type) (f:A->bool) (a b:list A),
  forallb f (a ++ b) = andb (forallb f a) (forallb f b).
Proof. induction a as [|x a IH]; intro b; simpl; [reflexivity | rewrite IH; now destruct (f x)]. Qed.
Lemma cov5_0 : forallb chk5 (firstn 1008 count5_assigns) = true.
Proof. exact cov5_c0. Qed.
Lemma u1 : skipn 1008 (skipn 1008 count5_assigns) = skipn 2016 count5_assigns.
Proof. now rewrite skipn_skipn5. Qed.
Lemma u2 : skipn 1008 (skipn 2016 count5_assigns) = skipn 3024 count5_assigns.
Proof. now rewrite skipn_skipn5. Qed.
Lemma u3 : skipn 1008 (skipn 3024 count5_assigns) = skipn 4032 count5_assigns.
Proof. now rewrite skipn_skipn5. Qed.
Lemma u4 : skipn 1008 (skipn 4032 count5_assigns) = skipn 5040 count5_assigns.
Proof. now rewrite skipn_skipn5. Qed.
Lemma u5 : skipn 1008 (skipn 5040 count5_assigns) = skipn 6048 count5_assigns.
Proof. now rewrite skipn_skipn5. Qed.
Lemma u6 : skipn 1008 (skipn 6048 count5_assigns) = skipn 7056 count5_assigns.
Proof. now rewrite skipn_skipn5. Qed.
Lemma coverage_5 : forallb chk5 count5_assigns = true.
Proof.
  assert (E : count5_assigns =
    firstn 1008 count5_assigns ++
    firstn 1008 (skipn 1008 count5_assigns) ++
    firstn 1008 (skipn 2016 count5_assigns) ++
    firstn 1008 (skipn 3024 count5_assigns) ++
    firstn 1008 (skipn 4032 count5_assigns) ++
    firstn 1008 (skipn 5040 count5_assigns) ++
    firstn 1008 (skipn 6048 count5_assigns) ++
    firstn 1008 (skipn 7056 count5_assigns)).
  { rewrite <- (firstn_skipn 1008 count5_assigns) at 1; f_equal;
    rewrite <- (firstn_skipn 1008 (skipn 1008 count5_assigns)) at 1; f_equal;
    rewrite u1;
    rewrite <- (firstn_skipn 1008 (skipn 2016 count5_assigns)) at 1; f_equal;
    rewrite u2;
    rewrite <- (firstn_skipn 1008 (skipn 3024 count5_assigns)) at 1; f_equal;
    rewrite u3;
    rewrite <- (firstn_skipn 1008 (skipn 4032 count5_assigns)) at 1; f_equal;
    rewrite u4;
    rewrite <- (firstn_skipn 1008 (skipn 5040 count5_assigns)) at 1; f_equal;
    rewrite u5;
    rewrite <- (firstn_skipn 1008 (skipn 6048 count5_assigns)) at 1; f_equal;
    rewrite u6;
    symmetry; apply firstn_all2; rewrite length_skipn, len5; lia. }
  rewrite E. rewrite !forallb_app5.
  rewrite cov5_0, cov5_c1, cov5_c2, cov5_c3, cov5_c4, cov5_c5, cov5_c6, cov5_c7.
  reflexivity.
Qed.
