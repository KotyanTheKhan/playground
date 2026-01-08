(* Join semilattice instance for lists *)
Require Import Posets.PosetClasses.
Require Import Structure.
Require Import Operations.
Require Import Helpers.
From Hammer Require Import Hammer.

Instance list_join_semilattice : IsJoinSemilattice List list_join.
Proof.
  constructor.
  - (* join_assoc *)
    intros x y z. unfold list_join.
    destruct (list_leb x y) eqn:Exy;
    destruct (list_leb y z) eqn:Eyz;
    destruct (list_leb x z) eqn:Exz.
    + (* T T T *) hauto lq:on.
    + (* T T F *) exfalso. apply (list_leb_trans x y z) in Exy; auto. rewrite Exy in Exz. discriminate.
    + (* T F T *) hauto lq:on.
    + (* T F F *) hauto lq:on.
    + (* F T T *) hauto lq:on.
    + (* F T F *) hauto lq:on.
    + (* F F T *) 
      (* This is the tricky case: x > y, y > z, but x <= z *)
      (* z <= y <= x implies z <= x. We have x <= z. So x = z. *)
      destruct (list_leb z y) eqn:Ezy.
      * destruct (list_leb y x) eqn:Eyx.
        -- destruct (list_leb z x) eqn:Ezx.
           ++ (* z <= y, y <= x, z <= x *)
              assert (Hzx: z = x) by (apply list_leb_antisym; auto).
              rewrite Hzx. simpl. rewrite Exy. reflexivity.
           ++ exfalso. apply (list_leb_trans z y x) in Ezy; auto. rewrite Ezy in Ezx. discriminate.
        -- exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
      * destruct (list_leb y x) eqn:Eyx.
        -- exfalso. destruct (list_leb_total y z) as [H | H]; rewrite H in *; discriminate.
        -- exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
    + (* F F F *) hauto lq:on.
  - (* join_comm *)
    intros x y. unfold list_join.
    destruct (list_leb x y) eqn:Exy.
    + destruct (list_leb y x) eqn:Eyx.
      * symmetry. apply (list_leb_antisym x y Exy Eyx).
      * reflexivity.
    + destruct (list_leb y x) eqn:Eyx.
      * reflexivity.
      * exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
  - (* join_idem *)
    intro x. unfold list_join.
    rewrite list_leb_refl. reflexivity.
Qed.
