(* Online clock locality: worked instances (test-only). *)
From Stdlib Require Import List Arith Lia.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Poset Schedule ScheduleWf
                             BarrierExecDim.
From ExecClock Require Import OnlineClock OnlineClockExamples OnlineClockLocal.
Import ListNotations.

(* the local observations of s_msg3's three events *)
Example obs_e00 : local_obs s_msg3 0 0 = Send 1 0.
Proof. vm_compute. reflexivity. Qed.
Example obs_e10 : local_obs s_msg3 1 0 = Recv 0 0.
Proof. vm_compute. reflexivity. Qed.
Example obs_e20 : local_obs s_msg3 2 0 = Local.
Proof. vm_compute. reflexivity. Qed.

(* local_stamp computes the same literal timestamps as the offline stamp *)
Example lstamp_e00 : local_stamp 3 0 0 (local_obs s_msg3 0 0) = ((0,0,0),(0,2,0)).
Proof. vm_compute. reflexivity. Qed.
Example lstamp_e10 : local_stamp 3 1 0 (local_obs s_msg3 1 0) = ((0,0,1),(0,2,1)).
Proof. vm_compute. reflexivity. Qed.
Example lstamp_e20 : local_stamp 3 2 0 (local_obs s_msg3 2 0) = ((0,2,0),(0,0,0)).
Proof. vm_compute. reflexivity. Qed.

(* a concrete instance of the locality theorem *)
Example lstamp_correct_e00 :
  local_stamp (sch_nprocs s_msg3) (fst (proj1_sig e00)) (snd (proj1_sig e00))
              (local_obs s_msg3 (fst (proj1_sig e00)) (snd (proj1_sig e00)))
  = stamp s_msg3 e00.
Proof. apply local_stamp_correct. Qed.

(* causality through the schedule-blind clock: the ordered (true) case *)
Example msg3_local_e00_le_e10 :
  stamp_le
    (local_stamp (sch_nprocs s_msg3) (fst (proj1_sig e00)) (snd (proj1_sig e00))
                 (local_obs s_msg3 (fst (proj1_sig e00)) (snd (proj1_sig e00))))
    (local_stamp (sch_nprocs s_msg3) (fst (proj1_sig e10)) (snd (proj1_sig e10))
                 (local_obs s_msg3 (fst (proj1_sig e10)) (snd (proj1_sig e10)))).
Proof. apply (blo_iff_local_stamp s_msg3 wf_s_msg3 msg3_pos e00 e10). exact msg3_blo_e00_e10. Qed.

(* the isolated event e20 and the sender e00 are stamp_le-incomparable (false case) *)
Example msg3_local_e00_e20_incomp :
  ~ stamp_le (local_stamp 3 0 0 (local_obs s_msg3 0 0))
             (local_stamp 3 2 0 (local_obs s_msg3 2 0))
  /\ ~ stamp_le (local_stamp 3 2 0 (local_obs s_msg3 2 0))
                (local_stamp 3 0 0 (local_obs s_msg3 0 0)).
Proof. unfold stamp_le, local_stamp, local_obs, le_lex3. vm_compute. intuition lia. Qed.
