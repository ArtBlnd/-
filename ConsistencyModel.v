(* ================================================  *)
(*  ConsistencyModel.v                               *)
(*  Concrete model for ExistenceIsDifference v7      *)
(*                                                   *)
(*  MODEL:                                           *)
(*    Dimension = nat                                *)
(*    Entity = nat × nat (dimension, index)          *)
(*    dim_le = <=? on nat                            *)
(*    native_dim (d, i) = d                          *)
(*    reify n = (n+1, 0)                             *)
(*    project (d,i) d' _ =                           *)
(*      if d = d' then (d,i) else (d', 0)            *)
(*                                                   *)
(*  tower d n = d + n (strictly increasing, acyclic) *)
(*  projection collapses all entities to index 0     *)
(*  red_apple=(0,0) and green_apple=(0,1) witness    *)
(*  the non-theorems (proj= but native≠)             *)
(* ================================================  *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Eqdep_dec.

(* ================================================ *)
(*  MODEL DEFINITION                                *)
(* ================================================ *)

Definition CDim := nat.
Definition CEnt := (nat * nat)%type.

(* dim_le via boolean <=? for proof irrelevance *)
Definition cdim_le (d1 d2 : CDim) : Prop :=
  (d1 <=? d2) = true.

Definition cnative_dim (e : CEnt) : CDim := fst e.

Definition creify (d : CDim) : CEnt := (S d, 0).

Definition creify_dim (d : CDim) : CDim :=
  cnative_dim (creify d).

Definition cproject (a : CEnt) (d : CDim)
  (H : cdim_le (cnative_dim a) d) : CEnt :=
  if Nat.eq_dec (fst a) d then a else (d, 0).

(* ================================================ *)
(*  HELPER                                          *)
(* ================================================ *)

Lemma cdim_le_iff : forall d1 d2,
  cdim_le d1 d2 <-> d1 <= d2.
Proof.
  intros. unfold cdim_le.
  rewrite Nat.leb_le. tauto.
Qed.

(* ================================================ *)
(*  AXIOM VERIFICATION                              *)
(* ================================================ *)

(* 1. dim_le_refl *)
Theorem v_dim_le_refl : forall d, cdim_le d d.
Proof.
  intro. apply cdim_le_iff. lia.
Qed.

(* 2. dim_le_trans *)
Theorem v_dim_le_trans : forall d1 d2 d3,
  cdim_le d1 d2 -> cdim_le d2 d3 -> cdim_le d1 d3.
Proof.
  intros d1 d2 d3 H1 H2.
  apply cdim_le_iff in H1.
  apply cdim_le_iff in H2.
  apply cdim_le_iff. lia.
Qed.

(* 3. dim_le_irrel *)
Theorem v_dim_le_irrel : forall d1 d2
  (H1 H2 : cdim_le d1 d2), H1 = H2.
Proof.
  intros. unfold cdim_le in *.
  apply UIP_dec. exact Bool.bool_dec.
Qed.

(* 4. project_dim *)
Theorem v_project_dim : forall a d
  (H : cdim_le (cnative_dim a) d),
  cnative_dim (cproject a d H) = d.
Proof.
  intros. unfold cproject, cnative_dim.
  destruct (Nat.eq_dec (fst a) d) as [Heq | Hneq].
  - exact Heq.
  - reflexivity.
Qed.

(* 5. project_self *)
Theorem v_project_self : forall a
  (H : cdim_le (cnative_dim a) (cnative_dim a)),
  cproject a (cnative_dim a) H = a.
Proof.
  intros. unfold cproject, cnative_dim.
  destruct (Nat.eq_dec (fst a) (fst a)) as [Heq | Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

(* 6. existence_is_difference *)
Theorem v_existence_is_difference : forall a b : CEnt,
  cnative_dim a = cnative_dim b ->
  {a = b} + {a <> b}.
Proof.
  intros [a1 a2] [b1 b2] H. simpl in *.
  destruct (Nat.eq_dec a1 b1) as [H1 | H1],
           (Nat.eq_dec a2 b2) as [H2 | H2].
  - left. subst. reflexivity.
  - right. intro Heq. inversion Heq. contradiction.
  - right. intro Heq. inversion Heq. contradiction.
  - right. intro Heq. inversion Heq. contradiction.
Qed.

(* 7. reify_injective *)
Theorem v_reify_injective : forall d1 d2,
  creify d1 = creify d2 -> d1 = d2.
Proof.
  intros d1 d2 H. unfold creify in H.
  inversion H. reflexivity.
Qed.

(* 8. tower_acyclic *)

Fixpoint ctower (d : CDim) (n : nat) : CDim :=
  match n with
  | O   => d
  | S m => creify_dim (ctower d m)
  end.

Lemma ctower_plus : forall d n,
  ctower d n = d + n.
Proof.
  intros d n. induction n as [| n' IH].
  - simpl. lia.
  - simpl. unfold creify_dim, cnative_dim, creify.
    simpl. rewrite IH. lia.
Qed.

Theorem v_tower_acyclic : forall d n m,
  ctower d n = ctower d m -> n = m.
Proof.
  intros d n m H.
  rewrite ctower_plus in H.
  rewrite ctower_plus in H.
  lia.
Qed.

(* ================================================ *)
(*  DERIVED: reify_dim_neq (sanity check)           *)
(* ================================================ *)

Theorem v_reify_dim_neq : forall d,
  creify_dim d <> d.
Proof.
  intros d H. unfold creify_dim, cnative_dim, creify in H.
  simpl in H. lia.
Qed.

(* ================================================ *)
(*  NON-THEOREM WITNESSES                           *)
(*                                                  *)
(*  red_apple and green_apple are different entities*)
(*  in dimension 0. Their projections to dimension 1*)
(*  are equal. This witnesses:                      *)
(*                                                  *)
(*  1. proj= does NOT imply native=                 *)
(*     (projections equal, entities different)      *)
(*                                                  *)
(*  2. native≠ does NOT imply proj≠                 *)
(*     (entities different, projections equal)      *)
(* ================================================ *)

Definition red_apple   : CEnt := (0, 0).
Definition green_apple : CEnt := (0, 1).

Theorem w_apples_differ :
  red_apple <> green_apple.
Proof. discriminate. Qed.

Theorem w_apples_same_dim :
  cnative_dim red_apple = cnative_dim green_apple.
Proof. reflexivity. Qed.

Theorem w_projections_collapse :
  forall (Hr : cdim_le (cnative_dim red_apple) 1)
         (Hg : cdim_le (cnative_dim green_apple) 1),
    cproject red_apple 1 Hr = cproject green_apple 1 Hg.
Proof.
  intros. unfold cproject, red_apple, green_apple,
    cnative_dim. simpl. reflexivity.
Qed.

(* ================================================  *)
(*  MODEL PROPERTIES                                 *)
(*                                                   *)
(*  - Dimension = nat: infinite, as required by      *)
(*    tower_acyclic (finite sets would cycle by      *)
(*    pigeonhole)                                    *)
(*                                                   *)
(*  - reify_dim d = S d: tower goes 0,1,2,3,...      *)
(*    trivially acyclic                              *)
(*                                                   *)
(*  - projection collapses index to 0:               *)
(*    all information besides "which dimension"      *)
(*    is lost. This is maximally lossy, making       *)
(*    the non-theorem witnesses easy to construct.   *)
(*                                                   *)
(*  - dim_le defined via <=? (boolean) rather than   *)
(*    le (inductive) for clean proof irrelevance     *)
(*    via UIP on bool.                               *)
(* ================================================  *)