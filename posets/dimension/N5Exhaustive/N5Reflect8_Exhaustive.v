(** Combine the 5 count-8 exhaustiveness chunks into the full coverage fact. *)
From Stdlib Require Import List Arith Lia.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8
  N5Reflect8_ex0 N5Reflect8_ex1 N5Reflect8_ex2 N5Reflect8_ex3 N5Reflect8_ex4.
Import ListNotations.

Lemma skipn_skipn' : forall (A:Type) m n (l:list A),
  skipn n (skipn m l) = skipn (m+n) l.
Proof.
  induction m as [|m IH]; intros n l.
  - reflexivity.
  - destruct l as [|x t].
    + rewrite !skipn_nil. reflexivity.
    + simpl. apply IH.
Qed.

Lemma len8 : length count8_assigns = 11520.
Proof. vm_compute. reflexivity. Qed.

Lemma cov0 : forallb chk8 (firstn 2304 count8_assigns) = true.
Proof. exact cov_c0. Qed.

Lemma forallb_app' : forall (A:Type) (f:A->bool) (a b:list A),
  forallb f (a ++ b) = andb (forallb f a) (forallb f b).
Proof. induction a as [|x a IH]; intro b; simpl; [reflexivity | rewrite IH; now destruct (f x)]. Qed.

Lemma forallb_5app : forall (A:Type) (f:A->bool) (l0 l1 l2 l3 l4:list A),
  forallb f l0 = true -> forallb f l1 = true -> forallb f l2 = true ->
  forallb f l3 = true -> forallb f l4 = true ->
  forallb f (l0 ++ l1 ++ l2 ++ l3 ++ l4) = true.
Proof. intros A f l0 l1 l2 l3 l4 H0 H1 H2 H3 H4.
  rewrite !forallb_app', H0, H1, H2, H3, H4. reflexivity. Qed.

Lemma sk2 : skipn 2304 (skipn 2304 count8_assigns) = skipn 4608 count8_assigns.
Proof. now rewrite skipn_skipn'. Qed.
Lemma sk3 : skipn 2304 (skipn 4608 count8_assigns) = skipn 6912 count8_assigns.
Proof. now rewrite skipn_skipn'. Qed.
Lemma sk4 : skipn 2304 (skipn 6912 count8_assigns) = skipn 9216 count8_assigns.
Proof. now rewrite skipn_skipn'. Qed.

Lemma coverage_8 : forallb chk8 count8_assigns = true.
Proof.
  assert (E : count8_assigns =
    firstn 2304 count8_assigns ++
    firstn 2304 (skipn 2304 count8_assigns) ++
    firstn 2304 (skipn 4608 count8_assigns) ++
    firstn 2304 (skipn 6912 count8_assigns) ++
    firstn 2304 (skipn 9216 count8_assigns)).
  { rewrite <- (firstn_skipn 2304 count8_assigns) at 1; f_equal;
    rewrite <- (firstn_skipn 2304 (skipn 2304 count8_assigns)) at 1; f_equal;
    rewrite sk2;
    rewrite <- (firstn_skipn 2304 (skipn 4608 count8_assigns)) at 1; f_equal;
    rewrite sk3;
    rewrite <- (firstn_skipn 2304 (skipn 6912 count8_assigns)) at 1; f_equal;
    rewrite sk4;
    symmetry; apply firstn_all2; rewrite skipn_length, len8; lia. }
  rewrite E.
  apply forallb_5app.
  - exact cov0.
  - exact cov_c1.
  - exact cov_c2.
  - exact cov_c3.
  - exact cov_c4.
Qed.

(* ---- bridge piece: enum_k_none enumerates every exactly-k-None list ---- *)
Definition num_none (a : list (option bool)) : nat :=
  length (filter (fun o => match o with None => true | _ => false end) a).

Lemma enum_k_none_complete : forall a n k,
  length a = n -> num_none a = k -> In a (enum_k_none n k).
Proof.
  induction a as [|x a IH]; intros n k Hlen Hk.
  - simpl in Hlen, Hk. subst. simpl. left. reflexivity.
  - destruct x as [b|].
    + simpl in Hlen. unfold num_none in Hk; simpl in Hk. fold (num_none a) in Hk.
      subst n k. simpl. apply in_or_app. right. destruct b.
      * apply in_or_app. left.
        apply (in_map (cons (Some true))). apply IH; reflexivity.
      * apply in_or_app. right. apply in_or_app. left.
        apply (in_map (cons (Some false))). apply IH; reflexivity.
    + simpl in Hlen. unfold num_none in Hk; simpl in Hk. fold (num_none a) in Hk.
      subst n k. simpl. apply in_or_app. left.
      apply (in_map (cons None)). apply IH; reflexivity.
Qed.
