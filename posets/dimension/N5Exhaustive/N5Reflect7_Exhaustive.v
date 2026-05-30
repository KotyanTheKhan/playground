(** Combine the 8 count-7 coverage chunks into the full coverage fact. *)
From Stdlib Require Import List Arith Lia.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8 N5Reflect7
  N5Reflect7_ex0 N5Reflect7_ex1 N5Reflect7_ex2 N5Reflect7_ex3
  N5Reflect7_ex4 N5Reflect7_ex5 N5Reflect7_ex6 N5Reflect7_ex7.
Import ListNotations.

Lemma skipn_skipn7 : forall (A:Type) m n (l:list A),
  skipn n (skipn m l) = skipn (m+n) l.
Proof.
  induction m as [|m IH]; intros n l.
  - reflexivity.
  - destruct l as [|x t].
    + rewrite !skipn_nil. reflexivity.
    + simpl. apply IH.
Qed.

Lemma len7 : length count7_assigns = 15360.
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_app7 : forall (A:Type) (f:A->bool) (a b:list A),
  forallb f (a ++ b) = andb (forallb f a) (forallb f b).
Proof. induction a as [|x a IH]; intro b; simpl; [reflexivity | rewrite IH; now destruct (f x)]. Qed.

Lemma cov7_0 : forallb chk7 (firstn 1920 count7_assigns) = true.
Proof. exact cov7_c0. Qed.

Lemma s1 : skipn 1920 (skipn 1920 count7_assigns) = skipn 3840 count7_assigns.
Proof. now rewrite skipn_skipn7. Qed.
Lemma s2 : skipn 1920 (skipn 3840 count7_assigns) = skipn 5760 count7_assigns.
Proof. now rewrite skipn_skipn7. Qed.
Lemma s3 : skipn 1920 (skipn 5760 count7_assigns) = skipn 7680 count7_assigns.
Proof. now rewrite skipn_skipn7. Qed.
Lemma s4 : skipn 1920 (skipn 7680 count7_assigns) = skipn 9600 count7_assigns.
Proof. now rewrite skipn_skipn7. Qed.
Lemma s5 : skipn 1920 (skipn 9600 count7_assigns) = skipn 11520 count7_assigns.
Proof. now rewrite skipn_skipn7. Qed.
Lemma s6 : skipn 1920 (skipn 11520 count7_assigns) = skipn 13440 count7_assigns.
Proof. now rewrite skipn_skipn7. Qed.

Lemma coverage_7 : forallb chk7 count7_assigns = true.
Proof.
  assert (E : count7_assigns =
    firstn 1920 count7_assigns ++
    firstn 1920 (skipn 1920 count7_assigns) ++
    firstn 1920 (skipn 3840 count7_assigns) ++
    firstn 1920 (skipn 5760 count7_assigns) ++
    firstn 1920 (skipn 7680 count7_assigns) ++
    firstn 1920 (skipn 9600 count7_assigns) ++
    firstn 1920 (skipn 11520 count7_assigns) ++
    firstn 1920 (skipn 13440 count7_assigns)).
  { rewrite <- (firstn_skipn 1920 count7_assigns) at 1; f_equal;
    rewrite <- (firstn_skipn 1920 (skipn 1920 count7_assigns)) at 1; f_equal;
    rewrite s1;
    rewrite <- (firstn_skipn 1920 (skipn 3840 count7_assigns)) at 1; f_equal;
    rewrite s2;
    rewrite <- (firstn_skipn 1920 (skipn 5760 count7_assigns)) at 1; f_equal;
    rewrite s3;
    rewrite <- (firstn_skipn 1920 (skipn 7680 count7_assigns)) at 1; f_equal;
    rewrite s4;
    rewrite <- (firstn_skipn 1920 (skipn 9600 count7_assigns)) at 1; f_equal;
    rewrite s5;
    rewrite <- (firstn_skipn 1920 (skipn 11520 count7_assigns)) at 1; f_equal;
    rewrite s6;
    symmetry; apply firstn_all2; rewrite length_skipn, len7; lia. }
  rewrite E. rewrite !forallb_app7.
  rewrite cov7_0, cov7_c1, cov7_c2, cov7_c3, cov7_c4, cov7_c5, cov7_c6, cov7_c7.
  reflexivity.
Qed.
