(* Agreement.v — universal equivalence of the frontier "schedule" denotation
   and the explicit "edge-set" denotation of a program.

   The earlier files proved this only by example (Examples.v) and abstractly
   (hb_prog_eq: equal programs => equal hb).  Here we close the gap with a
   UNIVERSAL theorem: every schedule translates to an edge-spec denoting the
   SAME program, hence the same happened-before poset. *)

From Stdlib Require Import List Arith Lia.
From Execution Require Import Op Event Edges Rank Poset Schedule FromEdges.
Import ListNotations.

(* Translate a schedule into the equivalent explicit edge-spec:
   every process has length = #frontiers; for each frontier k and pair (p,q)
   in it, emit the message tuple (p,k,q,k,k). *)
Definition translate (s : Schedule) : EdgeSpec :=
  {| es_nprocs := sch_nprocs s;
     es_lens   := repeat (length (sch_frontiers s)) (sch_nprocs s);
     es_msgs   := flat_map
        (fun k => map (fun pq => (fst pq, k, snd pq, k, k))
                      (nth k (sch_frontiers s) []))
        (seq 0 (length (sch_frontiers s))) |}.

(* ------------------------------------------------------------------ *)
(* Small list facts about [find] not present in Stdlib.                *)
(* ------------------------------------------------------------------ *)

Lemma find_app {A} (f : A -> bool) (l1 l2 : list A) :
  find f (l1 ++ l2) =
    match find f l1 with Some x => Some x | None => find f l2 end.
Proof.
  induction l1 as [|x l1 IH]; simpl; [reflexivity|].
  destruct (f x); [reflexivity|exact IH].
Qed.

Lemma find_none_of_all {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = false) -> find f l = None.
Proof.
  induction l as [|x l IH]; intro Hall; simpl; [reflexivity|].
  rewrite (Hall x (or_introl eq_refl)).
  apply IH. intros y Hy. apply Hall. right; exact Hy.
Qed.

Lemma find_map {A B} (g : A -> B) (f : B -> bool) (l : list A) :
  find f (map g l) = option_map g (find (fun x => f (g x)) l).
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  destruct (f (g x)); [reflexivity|exact IH].
Qed.

Lemma find_ext {A} (f g : A -> bool) (l : list A) :
  (forall x, f x = g x) -> find f l = find g l.
Proof.
  intro Hfg. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite Hfg. destruct (g x); [reflexivity|exact IH].
Qed.

(* ------------------------------------------------------------------ *)
(* Generic "block" lemma: a [find] over the translated message list,    *)
(* with a predicate that pins the block index k (keyed on the 2nd       *)
(* component), collapses to a [find] over frontier k alone.             *)
(* ------------------------------------------------------------------ *)

Lemma find_translate_block :
  forall s k (pred : (nat * nat) -> bool)
         (mpred : (nat * nat * nat * nat * nat) -> bool),
    k < length (sch_frontiers s) ->
    (forall pq, mpred (fst pq, k, snd pq, k, k) = pred pq) ->
    (forall sp si rq rj t, si <> k -> mpred (sp, si, rq, rj, t) = false) ->
    find mpred (es_msgs (translate s))
    = option_map (fun pq => (fst pq, k, snd pq, k, k))
                 (find pred (nth k (sch_frontiers s) [])).
Proof.
  intros s k pred mpred Hk Hhit Hmiss.
  simpl es_msgs.
  set (N := length (sch_frontiers s)) in *.
  set (F := fun j => map (fun pq => (fst pq, j, snd pq, j, j))
                         (nth j (sch_frontiers s) [])).
  (* split seq 0 N = seq 0 k ++ (k :: seq (S k) (N - k - 1)) *)
  assert (Hsplit : seq 0 N = seq 0 k ++ k :: seq (S k) (N - k - 1)).
  { replace N with (k + (N - k)) at 1 by lia.
    rewrite seq_app. f_equal. simpl plus.
    destruct (N - k) as [|m] eqn:Em; [lia|].
    simpl seq. f_equal. f_equal. lia. }
  rewrite Hsplit, flat_map_app. simpl flat_map.
  rewrite find_app.
  (* prefix: all blocks j < k, so 2nd component = j <> k => mpred = false *)
  assert (Hpre : find mpred (flat_map F (seq 0 k)) = None).
  { apply find_none_of_all. intros x Hx.
    apply in_flat_map in Hx. destruct Hx as [j [Hj Hxin]].
    apply in_seq in Hj. unfold F in Hxin.
    apply in_map_iff in Hxin. destruct Hxin as [pq [Heq _]].
    subst x. apply Hmiss. lia. }
  rewrite Hpre.
  (* block k ++ suffix: handle via find_app *)
  rewrite find_app.
  (* block k: find mpred (map ...) = option_map ... (find pred (frontier k)) *)
  unfold F at 1.
  rewrite find_map.
  rewrite (find_ext (fun pq => mpred (fst pq, k, snd pq, k, k)) pred)
    by (intro pq; apply Hhit).
  (* suffix: all blocks j > k, 2nd component = j <> k => mpred = false *)
  assert (Hsuf : find mpred (flat_map F (seq (S k) (N - k - 1))) = None).
  { apply find_none_of_all. intros x Hx.
    apply in_flat_map in Hx. destruct Hx as [j [Hj Hxin]].
    apply in_seq in Hj. unfold F in Hxin.
    apply in_map_iff in Hxin. destruct Hxin as [pq [Heq _]].
    subst x. apply Hmiss. lia. }
  destruct (find pred (nth k (sch_frontiers s) [])) as [pq|]; simpl.
  - reflexivity.
  - rewrite Hsuf. reflexivity.
Qed.

(* Receiver variant: predicate pins the block via the 4th component rj.
   Same proof; in block j the 4th component is also j. *)
Lemma find_translate_block_recv :
  forall s k (pred : (nat * nat) -> bool)
         (mpred : (nat * nat * nat * nat * nat) -> bool),
    k < length (sch_frontiers s) ->
    (forall pq, mpred (fst pq, k, snd pq, k, k) = pred pq) ->
    (forall sp si rq rj t, rj <> k -> mpred (sp, si, rq, rj, t) = false) ->
    find mpred (es_msgs (translate s))
    = option_map (fun pq => (fst pq, k, snd pq, k, k))
                 (find pred (nth k (sch_frontiers s) [])).
Proof.
  intros s k pred mpred Hk Hhit Hmiss.
  simpl es_msgs.
  set (N := length (sch_frontiers s)) in *.
  set (F := fun j => map (fun pq => (fst pq, j, snd pq, j, j))
                         (nth j (sch_frontiers s) [])).
  assert (Hsplit : seq 0 N = seq 0 k ++ k :: seq (S k) (N - k - 1)).
  { replace N with (k + (N - k)) at 1 by lia.
    rewrite seq_app. f_equal. simpl plus.
    destruct (N - k) as [|m] eqn:Em; [lia|].
    simpl seq. f_equal. f_equal. lia. }
  rewrite Hsplit, flat_map_app. simpl flat_map.
  rewrite find_app.
  assert (Hpre : find mpred (flat_map F (seq 0 k)) = None).
  { apply find_none_of_all. intros x Hx.
    apply in_flat_map in Hx. destruct Hx as [j [Hj Hxin]].
    apply in_seq in Hj. unfold F in Hxin.
    apply in_map_iff in Hxin. destruct Hxin as [pq [Heq _]].
    subst x. apply Hmiss. lia. }
  rewrite Hpre.
  rewrite find_app.
  unfold F at 1.
  rewrite find_map.
  rewrite (find_ext (fun pq => mpred (fst pq, k, snd pq, k, k)) pred)
    by (intro pq; apply Hhit).
  assert (Hsuf : find mpred (flat_map F (seq (S k) (N - k - 1))) = None).
  { apply find_none_of_all. intros x Hx.
    apply in_flat_map in Hx. destruct Hx as [j [Hj Hxin]].
    apply in_seq in Hj. unfold F in Hxin.
    apply in_map_iff in Hxin. destruct Hxin as [pq [Heq _]].
    subst x. apply Hmiss. lia. }
  destruct (find pred (nth k (sch_frontiers s) [])) as [pq|]; simpl.
  - reflexivity.
  - rewrite Hsuf. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Pointwise op equality at one (process, index) position.             *)
(* ------------------------------------------------------------------ *)

Lemma translate_op_eq :
  forall s p k, k < length (sch_frontiers s) ->
    op_at_es (translate s) p k = op_for (nth k (sch_frontiers s) []) p k.
Proof.
  intros s p k Hk.
  unfold op_at_es.
  (* SENDER find collapses to a find over frontier k. *)
  assert (Hsnd :
    find (fun m => let '(sp, si, _, _, _) := m in
                   andb (Nat.eqb sp p) (Nat.eqb si k)) (es_msgs (translate s))
    = option_map (fun pq => (fst pq, k, snd pq, k, k))
                 (find (fun pq => Nat.eqb (fst pq) p)
                       (nth k (sch_frontiers s) []))).
  { apply find_translate_block; [exact Hk| |].
    - intro pq. simpl. rewrite Nat.eqb_refl, Bool.andb_true_r. reflexivity.
    - intros sp si rq rj t Hsi.
      assert (Nat.eqb si k = false) by (apply Nat.eqb_neq; exact Hsi).
      rewrite H, Bool.andb_false_r. reflexivity. }
  assert (Hrcv :
    find (fun m => let '(_, _, rq, rj, _) := m in
                   andb (Nat.eqb rq p) (Nat.eqb rj k)) (es_msgs (translate s))
    = option_map (fun pq => (fst pq, k, snd pq, k, k))
                 (find (fun pq => Nat.eqb (snd pq) p)
                       (nth k (sch_frontiers s) []))).
  { apply find_translate_block_recv; [exact Hk| |].
    - intro pq. simpl. rewrite Nat.eqb_refl, Bool.andb_true_r. reflexivity.
    - intros sp si rq rj t Hrj.
      assert (Nat.eqb rj k = false) by (apply Nat.eqb_neq; exact Hrj).
      rewrite H, Bool.andb_false_r. reflexivity. }
  rewrite Hsnd, Hrcv.
  unfold op_for.
  destruct (find (fun pq => Nat.eqb (fst pq) p) (nth k (sch_frontiers s) []))
    as [[a b]|]; simpl.
  - reflexivity.
  - destruct (find (fun pq => Nat.eqb (snd pq) p) (nth k (sch_frontiers s) []))
      as [[a b]|]; simpl; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* THE universal agreement.                                            *)
(* ------------------------------------------------------------------ *)

Theorem schedule_edges_agree :
  forall s, desugar_prog s = prog_of_edgespec (translate s).
Proof.
  intro s.
  unfold desugar_prog, prog_of_edgespec.
  f_equal.
  (* es_nprocs (translate s) = sch_nprocs s definitionally *)
  simpl es_nprocs.
  apply map_ext_in. intros p Hp. apply in_seq in Hp. destruct Hp as [_ Hp].
  simpl in Hp. (* p < 0 + sch_nprocs s *)
  (* the inner map ranges over seq 0 (nth p (es_lens (translate s)) 0) *)
  assert (Hlen : nth p (es_lens (translate s)) 0 = length (sch_frontiers s)).
  { simpl es_lens. apply nth_repeat_lt. lia. }
  rewrite Hlen.
  apply map_ext_in. intros k Hk. apply in_seq in Hk. destruct Hk as [_ Hk].
  simpl in Hk.
  symmetry. apply translate_op_eq. lia.
Qed.

(* Same underlying program => identical happened-before order (transported). *)
Corollary schedule_edges_hb_agree :
  forall s (a b : Event (desugar_prog s)),
    hb (desugar_prog s) a b <->
    hb (prog_of_edgespec (translate s))
       (eq_rect _ (fun X => Event X) a _ (schedule_edges_agree s))
       (eq_rect _ (fun X => Event X) b _ (schedule_edges_agree s)).
Proof. intros s a b. apply hb_prog_eq. Qed.
