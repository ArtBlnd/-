(* ================================================  *)
(*  ConsistencyModelPD.v                             *)
(*  Path-dependent model for ExistenceIsDifference v7*)
(*                                                   *)
(*  MODEL:                                           *)
(*    Dimension = nat                                *)
(*    Entity = nat × nat (dimension, index)          *)
(*    dim_le = <=? on nat                            *)
(*    native_dim (d, i) = d                          *)
(*    reify n = (n+1, 0)                             *)
(*    project (d,v) d' _ =                           *)
(*      if d = d' then (d,v)                         *)
(*      else (d', v mod (d'-d+1))                    *)
(*                                                   *)
(*  Different intermediate dimensions apply          *)
(*  different mod divisors, stripping different      *)
(*  information. This causes path dependence:        *)
(*                                                   *)
(*    project(project((0,5), 1), 2) = (2, 1)         *)
(*    project((0,5), 2)             = (2, 2)         *)
(*                                                   *)
(*  Together with ConsistencyModel.v (no path dep),  *)
(*  this proves: path dependence is neither          *)
(*  required nor forbidden by the axioms.            *)
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

Definition cdim_le (d1 d2 : CDim) : Prop :=
  (d1 <=? d2) = true.

Definition cnative_dim (e : CEnt) : CDim := fst e.

Definition creify (d : CDim) : CEnt := (S d, 0).

Definition creify_dim (d : CDim) : CDim :=
  cnative_dim (creify d).

(* The key difference from ConsistencyModel.v:
   projection uses mod (d' - d + 1) instead of
   collapsing everything to 0. Different jumps
   strip different information. *)
Definition cproject (a : CEnt) (d : CDim)
  (H : cdim_le (cnative_dim a) d) : CEnt :=
  if Nat.eqb (fst a) d then a
  else (d, Nat.modulo (snd a) (S (d - fst a))).

(* ================================================ *)
(*  HELPERS                                         *)
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
  destruct (Nat.eqb (fst a) d) eqn:E.
  - apply Nat.eqb_eq in E. simpl. exact E.
  - simpl. reflexivity.
Qed.

(* 5. project_self *)
Theorem v_project_self : forall a
  (H : cdim_le (cnative_dim a) (cnative_dim a)),
  cproject a (cnative_dim a) H = a.
Proof.
  intros. unfold cproject, cnative_dim.
  rewrite Nat.eqb_refl. reflexivity.
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
(*  PATH DEPENDENCE WITNESS                         *)
(*                                                  *)
(*  Entity (0, 5) projected two ways to dimension 2:*)
(*                                                  *)
(*  Path A: 0 → 1 → 2                               *)
(*    project (0,5) 1 = (1, 5 mod 2) = (1, 1)       *)
(*    project (1,1) 2 = (2, 1 mod 2) = (2, 1)       *)
(*                                                  *)
(*  Path B: 0 → 2                                   *)
(*    project (0,5) 2 = (2, 5 mod 3) = (2, 2)       *)
(*                                                  *)
(*  (2, 1) ≠ (2, 2). Path dependence.               *)
(*                                                  *)
(*  Interpretation: going through dimension 1 first *)
(*  applies mod 2 (losing some info), then mod 2    *)
(*  again. Going directly applies mod 3 (losing     *)
(*  different info). The intermediate window        *)
(*  determines what survives.                       *)
(* ================================================ *)

Theorem v_path_dependence :
  forall (H1 : cdim_le 0 1) (H2 : cdim_le 1 2) (H3 : cdim_le 0 2),
    cproject (cproject (0, 5) 1 H1) 2 H2 <>
    cproject (0, 5) 2 H3.
Proof.
  intros H1 H2 H3 Heq.
  apply (f_equal snd) in Heq.
  vm_compute in Heq.
  discriminate Heq.
Qed.

(* ================================================ *)
(*  NON-THEOREM WITNESSES                           *)
(*  (same as ConsistencyModel.v — also holds here)  *)
(* ================================================ *)

Definition red_apple   : CEnt := (0, 0).
Definition green_apple : CEnt := (0, 2).

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
  intros. vm_compute. reflexivity.
Qed.

(* ================================================  *)
(*  SUMMARY                                          *)
(*                                                   *)
(*  This model satisfies all 8 axioms and            *)
(*  additionally witnesses path dependence:          *)
(*    project(project(a, d1), d2) ≠ project(a, d2)   *)
(*  for a=(0,5), d1=1, d2=2.                         *)
(*                                                   *)
(*  Combined with ConsistencyModel.v (which has no   *)
(*  path dependence), this establishes:              *)
(*  - Path dependence is CONSISTENT with the axioms  *)
(*  - Path independence is CONSISTENT with the axioms*)
(*  - Therefore the axioms neither require nor       *)
(*    forbid path dependence.                        *)
(*                                                   *)
(*  This is the formal version of the v7 design      *)
(*  note: "No axiom equates them. This is            *)
(*  intentional."                                    *)
(* ================================================ *)