(** edge_count_5 = 5 case for the n=5 dispatcher.  Generated (mirror EdgeCount7). *)

From Stdlib Require Import List Classical Arith Lia Bool.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import
  EdgeCount N5Reflect N5Reflect8 N5Reflect5 N5Reflect5_Count N5Transport N5Iff
  EdgeCount5_c1  EdgeCount5_c2  EdgeCount5_c3  EdgeCount5_c4  EdgeCount5_c5  EdgeCount5_c6  EdgeCount5_c7  EdgeCount5_c8  EdgeCount5_c9  EdgeCount5_c10.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount5.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma n5_edge_count_5_two_realizer :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 5 ->
      exists r : Ensemble (B -> B -> Prop),
        IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    (* Pattern 1 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 t q /\ R2 t r))
      as [H1 | Hn1].
    { destruct H1 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c1 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 2 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 q r /\ R2 t s))
      as [H2 | Hn2].
    { destruct H2 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c2 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 3 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 p t /\ R2 q r))
      as [H3 | Hn3].
    { destruct H3 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c3 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 4 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 q r /\ R2 q s))
      as [H4 | Hn4].
    { destruct H4 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c4 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 5 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 s q /\ R2 s r /\ R2 t q))
      as [H5 | Hn5].
    { destruct H5 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c5 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 6 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 q r /\ R2 s r /\ R2 s t))
      as [H6 | Hn6].
    { destruct H6 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c6 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 7 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 q r /\ R2 t r))
      as [H7 | Hn7].
    { destruct H7 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c7 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 8 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 q r /\ R2 s r))
      as [H8 | Hn8].
    { destruct H8 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c8 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 9 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 q r /\ R2 s q /\ R2 s r))
      as [H9 | Hn9].
    { destruct H9 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c9 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* Pattern 10 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 q r /\ R2 s r /\ R2 t r))
      as [H10 | Hn10].
    { destruct H10 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & E1 & E2 & E3 & E4 & E5).
      exact (n5_edge_count_5_c10 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst E1 E2 E3 E4 E5). }
    (* All ten patterns refuted: reflection contradiction. *)
    pose proof (R2_matrix_is_poset R2 a b c d e
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) as Hp_b.
    pose proof (R2_matrix_edge_count_eq R2 a b c d e
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) as Hec_b.
    rewrite Hec in Hec_b.
    pose proof (exhaustive_5edge (R2_matrix R2 a b c d e) Hp_b Hec_b) as Hany.
    unfold any_pattern_5_b in Hany. rewrite !orb_true_iff in Hany.
    destruct Hany as [[[[[[[[[Hb|Hb]|Hb]|Hb]|Hb]|Hb]|Hb]|Hb]|Hb]|Hb].
    - apply (is_c5_1_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn1 Hb).
    - apply (is_c5_2_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn2 Hb).
    - apply (is_c5_3_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn3 Hb).
    - apply (is_c5_4_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn4 Hb).
    - apply (is_c5_5_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn5 Hb).
    - apply (is_c5_6_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn6 Hb).
    - apply (is_c5_7_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn7 Hb).
    - apply (is_c5_8_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn8 Hb).
    - apply (is_c5_9_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn9 Hb).
    - apply (is_c5_10_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn10 Hb).
  Qed.

End EdgeCount5.
