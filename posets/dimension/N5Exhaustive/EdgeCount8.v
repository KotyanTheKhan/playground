(** edge_count_5 = 8 case for the n=5 dispatcher.

    Every 5-element poset with exactly 8 comparable pairs has a 2-realizer.
    Dispatch on the 6 count-8 iso-class patterns (handlers EdgeCount8_c1..c6):
    classically test each pattern's shape; if present, apply its handler.  If
    all six are absent, the reflection fact [exhaustive_8edge] on [R2_matrix]
    (with [edge_count_b = 8] transported from [edge_count_5 = 8]) forces one
    of the six [is_c8_k_b] booleans true, which lifts (via [N5Iff]) to the
    shape just refuted — contradiction. *)

From Stdlib Require Import List Classical Arith Lia Bool.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import
  EdgeCount N5Reflect N5Reflect8 N5Reflect8_Count N5Transport N5Iff
  EdgeCount8_c1 EdgeCount8_c2 EdgeCount8_c3 EdgeCount8_c4 EdgeCount8_c5 EdgeCount8_c6.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount8.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma n5_edge_count_8_two_realizer :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 8 ->
      exists r : Ensemble (B -> B -> Prop),
        IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    (* Pattern 1 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 p t /\ R2 q r /\ R2 q s /\ R2 t r /\ R2 t s))
      as [H1 | Hn1].
    { destruct H1 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & HRpq & HRpr & HRps & HRpt & HRqr & HRqs & HRtr & HRts).
      exact (n5_edge_count_8_c1 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst
               HRpq HRpr HRps HRpt HRqr HRqs HRtr HRts). }
    (* Pattern 2 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 q r /\ R2 q s /\ R2 t q /\ R2 t r /\ R2 t s))
      as [H2 | Hn2].
    { destruct H2 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & HRpq & HRpr & HRps & HRqr & HRqs & HRtq & HRtr & HRts).
      exact (n5_edge_count_8_c2 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst
               HRpq HRpr HRps HRqr HRqs HRtq HRtr HRts). }
    (* Pattern 3 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 q r /\ R2 s r /\ R2 t q /\ R2 t r /\ R2 t s))
      as [H3 | Hn3].
    { destruct H3 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & HRpq & HRpr & HRps & HRqr & HRsr & HRtq & HRtr & HRts).
      exact (n5_edge_count_8_c3 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst
               HRpq HRpr HRps HRqr HRsr HRtq HRtr HRts). }
    (* Pattern 4 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 p t /\ R2 q r /\ R2 q s /\ R2 q t /\ R2 r s))
      as [H4 | Hn4].
    { destruct H4 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & HRpq & HRpr & HRps & HRpt & HRqr & HRqs & HRqt & HRrs).
      exact (n5_edge_count_8_c4 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst
               HRpq HRpr HRps HRpt HRqr HRqs HRqt HRrs). }
    (* Pattern 5 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 p t /\ R2 q r /\ R2 q s /\ R2 r s /\ R2 t s))
      as [H5 | Hn5].
    { destruct H5 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & HRpq & HRpr & HRps & HRpt & HRqr & HRqs & HRrs & HRts).
      exact (n5_edge_count_8_c5 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst
               HRpq HRpr HRps HRpt HRqr HRqs HRrs HRts). }
    (* Pattern 6 *)
    destruct (classic (exists p q r s t : B,
        p <> q /\ p <> r /\ p <> s /\ p <> t /\ q <> r /\ q <> s /\ q <> t /\
        r <> s /\ r <> t /\ s <> t /\
        R2 p q /\ R2 p r /\ R2 p s /\ R2 q r /\ R2 q s /\ R2 r s /\ R2 t r /\ R2 t s))
      as [H6 | Hn6].
    { destruct H6 as (p & q & r & s & t & Hpq & Hpr & Hps & Hpt & Hqr & Hqs & Hqt &
        Hrs & Hrt & Hst & HRpq & HRpr & HRps & HRqr & HRqs & HRrs & HRtr & HRts).
      exact (n5_edge_count_8_c6 R2 Hcard a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde
               Hcov Hec p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst
               HRpq HRpr HRps HRqr HRqs HRrs HRtr HRts). }
    (* All six patterns refuted: reflection contradiction. *)
    pose proof (R2_matrix_is_poset R2 a b c d e
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) as Hp_b.
    pose proof (R2_matrix_edge_count_eq R2 a b c d e
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) as Hec_b.
    rewrite Hec in Hec_b.
    pose proof (exhaustive_8edge (R2_matrix R2 a b c d e) Hp_b Hec_b) as Hany.
    unfold any_pattern_8_b in Hany. rewrite !orb_true_iff in Hany.
    destruct Hany as [[[[[Hb|Hb]|Hb]|Hb]|Hb]|Hb].
    - apply (is_c8_1_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn1 Hb).
    - apply (is_c8_2_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn2 Hb).
    - apply (is_c8_3_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn3 Hb).
    - apply (is_c8_4_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn4 Hb).
    - apply (is_c8_5_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn5 Hb).
    - apply (is_c8_6_b_to_exists R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde) in Hb.
      contradiction (Hn6 Hb).
  Qed.

End EdgeCount8.
