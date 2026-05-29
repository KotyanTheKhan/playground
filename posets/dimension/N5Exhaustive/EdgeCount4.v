(** edge_count_5 = 4 case for n=5 dispatcher.

    When [edge_count_5 R2 a b c d e = 4] over 5 pairwise distinct
    elements covering the carrier, there are exactly four strict
    edges.  By transitive-closure and structural classification, the
    iso class falls into one of 10 patterns (classes 11-20 of the
    enumeration).  Dispatch to the per-class helper. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import
  EdgeCount EdgeCount4_extract
  EdgeCount4_4claw_up EdgeCount4_4claw_down
  EdgeCount4_bowtie EdgeCount4_disjoint
  EdgeCount4_chain3_below EdgeCount4_chain3_above
  EdgeCount4_M_shape EdgeCount4_K32mm
  EdgeCount4_3claw_up_xp EdgeCount4_3claw_down_xl
  N5Reflect N5Reflect_Exhaustive N5Transport N5Iff.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount4.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  (** Main lemma: edge_count = 4 yields a 2-realizer. *)
  Lemma n5_edge_count_4_two_realizer :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      exists r : Ensemble (B -> B -> Prop),
        IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    (* Classical existence checks for each of the 10 iso-class patterns.
       Each [classic] either gives us a witness (apply per-class lemma)
       or refutes that pattern.  If all 10 are refuted, derive False. *)

    (* Class 11: 4-claw up.  Exists root with 4 leaves below. *)
    destruct (classic
      (exists r l1 l2 l3 l4 : B,
         r <> l1 /\ r <> l2 /\ r <> l3 /\ r <> l4 /\
         l1 <> l2 /\ l1 <> l3 /\ l1 <> l4 /\
         l2 <> l3 /\ l2 <> l4 /\ l3 <> l4 /\
         R2 r l1 /\ R2 r l2 /\ R2 r l3 /\ R2 r l4))
      as [H11 | Hn11].
    { destruct H11 as
        [r [l1 [l2 [l3 [l4
        [Hrl1 [Hrl2 [Hrl3 [Hrl4
        [Hl12 [Hl13 [Hl14
        [Hl23 [Hl24 [Hl34
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]]]]]]].
      apply (n5_edge_count_4_4claw_up R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               r l1 l2 l3 l4 Hrl1 Hrl2 Hrl3 Hrl4
               Hl12 Hl13 Hl14 Hl23 Hl24 Hl34 HR1 HR2' HR3 HR4). }

    (* Class 20: 4-claw down.  Exists root with 4 parents. *)
    destruct (classic
      (exists r l1 l2 l3 l4 : B,
         r <> l1 /\ r <> l2 /\ r <> l3 /\ r <> l4 /\
         l1 <> l2 /\ l1 <> l3 /\ l1 <> l4 /\
         l2 <> l3 /\ l2 <> l4 /\ l3 <> l4 /\
         R2 l1 r /\ R2 l2 r /\ R2 l3 r /\ R2 l4 r))
      as [H20 | Hn20].
    { destruct H20 as
        [r [l1 [l2 [l3 [l4
        [Hrl1 [Hrl2 [Hrl3 [Hrl4
        [Hl12 [Hl13 [Hl14
        [Hl23 [Hl24 [Hl34
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]]]]]]].
      apply (n5_edge_count_4_4claw_down R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               r l1 l2 l3 l4 Hrl1 Hrl2 Hrl3 Hrl4
               Hl12 Hl13 Hl14 Hl23 Hl24 Hl34 HR1 HR2' HR3 HR4). }

    (* Class 16: Bowtie K_{2,2} + isolated. *)
    destruct (classic
      (exists p1 p2 q1 q2 : B,
         p1 <> p2 /\ p1 <> q1 /\ p1 <> q2 /\
         p2 <> q1 /\ p2 <> q2 /\ q1 <> q2 /\
         R2 p1 q1 /\ R2 p1 q2 /\ R2 p2 q1 /\ R2 p2 q2))
      as [H16 | Hn16].
    { destruct H16 as
        [p1 [p2 [q1 [q2
        [Hp1p2 [Hp1q1 [Hp1q2 [Hp2q1 [Hp2q2 [Hq1q2
        [HR11 [HR12 [HR21 HR22]]]]]]]]]]]]].
      apply (n5_edge_count_4_bowtie R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               p1 p2 q1 q2 Hp1p2 Hp1q1 Hp1q2 Hp2q1 Hp2q2 Hq1q2
               HR11 HR12 HR21 HR22). }

    (* Class 15: Disjoint chain3 + chain2. *)
    destruct (classic
      (exists alpha beta gamma delta eps : B,
         alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
         beta <> gamma /\ beta <> delta /\ beta <> eps /\
         gamma <> delta /\ gamma <> eps /\ delta <> eps /\
         R2 alpha beta /\ R2 beta gamma /\ R2 alpha gamma /\ R2 delta eps))
      as [H15 | Hn15].
    { destruct H15 as
        [alpha [beta [gamma [delta [eps
        [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]]]]]]].
      apply (n5_edge_count_4_disjoint R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               alpha beta gamma delta eps H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
               HR1 HR2' HR3 HR4). }

    (* Class 12: Chain3 + below pendant. *)
    destruct (classic
      (exists alpha beta gamma delta : B,
         alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\
         beta <> gamma /\ beta <> delta /\ gamma <> delta /\
         R2 alpha beta /\ R2 beta gamma /\ R2 alpha gamma /\ R2 alpha delta))
      as [H12 | Hn12].
    { destruct H12 as
        [alpha [beta [gamma [delta
        [H1 [H2 [H3 [H4 [H5 [H6
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]].
      apply (n5_edge_count_4_chain3_below R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               alpha beta gamma delta H1 H2 H3 H4 H5 H6 HR1 HR2' HR3 HR4). }

    (* Class 14: Chain3 + above pendant. *)
    destruct (classic
      (exists alpha beta gamma delta : B,
         alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\
         beta <> gamma /\ beta <> delta /\ gamma <> delta /\
         R2 alpha beta /\ R2 beta gamma /\ R2 delta gamma /\ R2 alpha gamma))
      as [H14 | Hn14].
    { destruct H14 as
        [alpha [beta [gamma [delta
        [H1 [H2 [H3 [H4 [H5 [H6
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]].
      apply (n5_edge_count_4_chain3_above R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               alpha beta gamma delta H1 H2 H3 H4 H5 H6 HR1 HR2' HR3 HR4). }

    (* Class 13: 3-claw up with extra parent. *)
    destruct (classic
      (exists alpha beta gamma delta eps : B,
         alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
         beta <> gamma /\ beta <> delta /\ beta <> eps /\
         gamma <> delta /\ gamma <> eps /\ delta <> eps /\
         R2 beta alpha /\ R2 beta gamma /\ R2 beta eps /\ R2 delta gamma))
      as [H13 | Hn13].
    { destruct H13 as
        [alpha [beta [gamma [delta [eps
        [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]]]]]]].
      apply (n5_edge_count_4_3claw_up_xp R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               alpha beta gamma delta eps H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
               HR1 HR2' HR3 HR4). }

    (* Class 18: 3-claw down with extra leaf. *)
    destruct (classic
      (exists alpha beta gamma delta eps : B,
         alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
         beta <> gamma /\ beta <> delta /\ beta <> eps /\
         gamma <> delta /\ gamma <> eps /\ delta <> eps /\
         R2 alpha beta /\ R2 gamma beta /\ R2 eps beta /\ R2 gamma delta))
      as [H18 | Hn18].
    { destruct H18 as
        [alpha [beta [gamma [delta [eps
        [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]]]]]]].
      apply (n5_edge_count_4_3claw_down_xl R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               alpha beta gamma delta eps H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
               HR1 HR2' HR3 HR4). }

    (* Class 17: M-shape. *)
    destruct (classic
      (exists alpha beta gamma delta eps : B,
         alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
         beta <> gamma /\ beta <> delta /\ beta <> eps /\
         gamma <> delta /\ gamma <> eps /\ delta <> eps /\
         R2 beta alpha /\ R2 beta gamma /\ R2 delta gamma /\ R2 delta eps))
      as [H17 | Hn17].
    { destruct H17 as
        [alpha [beta [gamma [delta [eps
        [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]]]]]]].
      apply (n5_edge_count_4_M_shape R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               alpha beta gamma delta eps H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
               HR1 HR2' HR3 HR4). }

    (* Class 19: K_{3,2} minus a matching. *)
    destruct (classic
      (exists alpha beta gamma delta eps : B,
         alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
         beta <> gamma /\ beta <> delta /\ beta <> eps /\
         gamma <> delta /\ gamma <> eps /\ delta <> eps /\
         R2 alpha eps /\ R2 beta delta /\ R2 gamma delta /\ R2 gamma eps))
      as [H19 | Hn19].
    { destruct H19 as
        [alpha [beta [gamma [delta [eps
        [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10
        [HR1 [HR2' [HR3 HR4]]]]]]]]]]]]]]]]]].
      apply (n5_edge_count_4_K32mm R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               alpha beta gamma delta eps H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
               HR1 HR2' HR3 HR4). }

    (* Reflection: build the boolean matrix, invoke exhaustive_4edge to
       get one of 10 boolean patterns true, lift via the iff lemma to
       the abstract exists shape, contradiction with the corresponding
       Hn11..Hn20 hypothesis. *)
    pose proof (R2_matrix_is_poset R2 a b c d e
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) as Hp_b.
    pose proof (R2_matrix_edge_count_eq R2 a b c d e
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) as Hec_b.
    rewrite Hec in Hec_b.
    destruct (exhaustive_4edge _ Hp_b Hec_b) as
      [Hb | [Hb | [Hb | [Hb | [Hb | [Hb | [Hb | [Hb | [Hb | Hb]]]]]]]]];
    [ apply (is_4claw_up_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn11 Hb)
    | apply (is_4claw_down_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn20 Hb)
    | apply (is_bowtie_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn16 Hb)
    | apply (is_disjoint_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn15 Hb)
    | apply (is_chain3_below_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn12 Hb)
    | apply (is_chain3_above_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn14 Hb)
    | apply (is_M_shape_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn17 Hb)
    | apply (is_K32mm_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn19 Hb)
    | apply (is_3claw_up_xp_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn13 Hb)
    | apply (is_3claw_down_xl_b_to_exists R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb;
      contradiction (Hn18 Hb) ].
  Qed.

End EdgeCount4.
