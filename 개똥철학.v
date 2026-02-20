(* ========================================== *)
(*  Existence Is Difference — v7              *)
(*                                            *)
(*  Insight: where does dimension d live as   *)
(*  an entity? is just native_dim (reify d).  *)
(*  This is not a new concept — it is         *)
(*  projection viewed from the other side.    *)
(*  projection: entity → coarser view         *)
(*  reify:      dimension → entity view       *)
(*  Both are looking through a window.        *)
(*  native_dim (reify d) is simply where      *)
(*  that entity-view lands.                   *)
(*                                            *)
(*  native_dim (reify d) is NOT above or      *)
(*  below d. It has no directional            *)
(*  relationship to d. It is simply           *)
(*  DIFFERENT from d (assuming no             *)
(*  self-containment).                        *)
(*                                            *)
(*  Primitives:                               *)
(*  - Entity: what exists                     *)
(*  - Dimension: a domain = an operation      *)
(*  - reify: a dimension, viewed as entity    *)
(*  - The axiom: same dim → decidable ==|!=   *)
(* ========================================== *)

(* === Primitives === *)

Parameter Entity : Type.
Parameter Dimension : Type.

(* ================================================ *)
(*  DIMENSION HIERARCHY — PREORDER                  *)
(* ================================================ *)

Parameter dim_le : Dimension -> Dimension -> Prop.
Notation "d1 <= d2" := (dim_le d1 d2).

Axiom dim_le_refl  : forall d, d <= d.
Axiom dim_le_trans : forall d1 d2 d3,
  d1 <= d2 -> d2 <= d3 -> d1 <= d3.
(* No antisymmetry — preorder *)

Axiom dim_le_irrel : forall d1 d2 (H1 H2 : d1 <= d2),
  H1 = H2.

(* ================================================ *)
(*  DIMENSIONAL EQUIVALENCE                         *)
(* ================================================ *)

Definition dim_equiv (d1 d2 : Dimension) : Prop :=
  d1 <= d2 /\ d2 <= d1.
Notation "d1 ≈ d2" := (dim_equiv d1 d2) (at level 70).

Theorem dim_equiv_refl : forall d, d ≈ d.
Proof. intro d. split; apply dim_le_refl. Qed.

Theorem dim_equiv_sym : forall d1 d2, d1 ≈ d2 -> d2 ≈ d1.
Proof. intros d1 d2 [H1 H2]. split; assumption. Qed.

Theorem dim_equiv_trans : forall d1 d2 d3,
  d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof.
  intros d1 d2 d3 [H12 H21] [H23 H32]. split.
  - exact (dim_le_trans _ _ _ H12 H23).
  - exact (dim_le_trans _ _ _ H32 H21).
Qed.

(* ================================================ *)
(*  NATIVE DIMENSION                                *)
(* ================================================ *)

Parameter native_dim : Entity -> Dimension.

(* ================================================ *)
(*  PROJECTION                                      *)
(* ================================================ *)

Parameter project : forall (a : Entity) (d : Dimension),
  native_dim a <= d -> Entity.

Axiom project_dim : forall a d (H : native_dim a <= d),
  native_dim (project a d H) = d.

Axiom project_self : forall a (H : native_dim a <= native_dim a),
  project a (native_dim a) H = a.

Lemma project_irrel :
  forall a d (H1 H2 : native_dim a <= d),
    project a d H1 = project a d H2.
Proof.
  intros. rewrite (dim_le_irrel _ _ H1 H2). reflexivity.
Qed.

(* NOTE ON PATH DEPENDENCE:
   If native_dim a <= d1 <= d2, then:
     project (project a d1 H1) d2 H2
   vs
     project a d2 H3
   may differ. No axiom equates them.

   This is intentional. Information loss depends on
   the path taken. Projecting "orange" to "fruit"
   then to "living thing" may lose different info
   than projecting "orange" directly to "living thing."

   This is NOT a bug — it reflects the fact that
   different intermediate domains have different
   ==|!= operators, and each operator determines
   what survives. *)

(* NOTE ON IRREVERSIBILITY:
   project goes from fine to coarse only (dim_le).
   There is no "un-project." Once information is
   lost through projection, it cannot be recovered.
   This is not a limitation but a feature:
   projection changes the domain (= operator),
   and the old operator's distinctions simply
   do not exist in the new domain. *)

(* ================================================ *)
(*  THE CORE AXIOM: Existence Is Difference         *)
(* ================================================ *)

Axiom existence_is_difference :
  forall a b : Entity,
    native_dim a = native_dim b ->
    {a = b} + {a <> b}.

(* ================================================ *)
(*  DEFINITIONS                                     *)
(* ================================================ *)

Definition natively_comparable (a b : Entity) : Prop :=
  native_dim a = native_dim b.

Definition comparable_at (a b : Entity) (d : Dimension) : Prop :=
  native_dim a <= d /\ native_dim b <= d.

Definition distinguish_at
  (a b : Entity) (d : Dimension)
  (Ha : native_dim a <= d) (Hb : native_dim b <= d)
  : {project a d Ha = project b d Hb} +
    {project a d Ha <> project b d Hb}.
Proof.
  apply existence_is_difference.
  rewrite project_dim, project_dim. reflexivity.
Defined.

(* ================================================ *)
(*  REIFICATION                                     *)
(*                                                  *)
(*  reify d: dimension d, viewed as an entity.      *)
(*                                                  *)
(*  native_dim (reify d): the dimension where       *)
(*  that entity-view lives. This is not above       *)
(*  or below d — just somewhere else.               *)
(* ================================================ *)

Parameter reify : Dimension -> Entity.

(* Different dimensions are different entities. *)
Axiom reify_injective :
  forall d1 d2, reify d1 = reify d2 -> d1 = d2.

(* Shorthand for readability *)
Definition reify_dim (d : Dimension) : Dimension :=
  native_dim (reify d).

(* ================================================ *)
(*  ENTITY → DOMAIN + OPERATOR                      *)
(* ================================================ *)

Theorem entity_has_domain :
  forall a : Entity,
    exists d : Dimension, native_dim a = d.
Proof.
  intro a. exists (native_dim a). reflexivity.
Qed.

Theorem entity_has_operator :
  forall a b : Entity,
    native_dim a = native_dim b ->
    {a = b} + {a <> b}.
Proof.
  exact existence_is_difference.
Qed.

(* ================================================ *)
(*  DIMENSION → DOMAIN + OPERATOR (via reify)       *)
(* ================================================ *)

Theorem dimension_has_domain :
  forall d : Dimension,
    exists md : Dimension, native_dim (reify d) = md.
Proof.
  intro d. exists (reify_dim d). reflexivity.
Qed.

Theorem dimension_has_operator :
  forall d1 d2 : Dimension,
    reify_dim d1 = reify_dim d2 ->
    {reify d1 = reify d2} + {reify d1 <> reify d2}.
Proof.
  intros d1 d2 Hmeta.
  apply existence_is_difference.
  exact Hmeta.
Qed.

Theorem dim_identity_decidable_at :
  forall d1 d2 : Dimension,
    reify_dim d1 = reify_dim d2 ->
    {d1 = d2} + {d1 <> d2}.
Proof.
  intros d1 d2 Hmeta.
  destruct (dimension_has_operator d1 d2 Hmeta) as [Heq | Hneq].
  - left. exact (reify_injective d1 d2 Heq).
  - right. intro H. apply Hneq. rewrite H. reflexivity.
Qed.

(* ================================================ *)
(*  REIFY TOWER                                     *)
(* ================================================ *)

Theorem reify_dim_has_domain :
  forall d : Dimension,
    exists mmd : Dimension,
      native_dim (reify (reify_dim d)) = mmd.
Proof.
  intro d. exists (reify_dim (reify_dim d)). reflexivity.
Qed.

Fixpoint tower (d : Dimension) (n : nat) : Dimension :=
  match n with
  | O   => d
  | S m => reify_dim (tower d m)
  end.

Theorem every_level_has_domain :
  forall d : Dimension, forall n : nat,
    exists md : Dimension,
      native_dim (reify (tower d n)) = md.
Proof.
  intros d n.
  exists (reify_dim (tower d n)). reflexivity.
Qed.

Theorem every_level_has_operator :
  forall d : Dimension, forall n : nat,
  forall a b : Entity,
    native_dim a = tower d n ->
    native_dim b = tower d n ->
    {a = b} + {a <> b}.
Proof.
  intros d n a b Ha Hb.
  apply existence_is_difference.
  rewrite Ha, Hb. reflexivity.
Qed.

(* ================================================ *)
(*  NO SELF-CONTAINMENT — TOWER ACYCLICITY          *)
(*                                                  *)
(*  The reify tower never cycles back.              *)
(*                                                  *)
(*  This cannot be derived from other axioms:       *)
(*  reify produces something different, but         *)
(*  "different" has no direction — it could gain,   *)
(*  lose, or simply change information. Without     *)
(*  monotonicity, cycle-freedom is not provable.    *)
(*                                                  *)
(*  Therefore we axiomatize it directly.            *)
(* ================================================ *)

(* Same principle as existence_is_difference
   applied at the dimension level:
   a round-trip with no information loss
   means no difference, therefore one. *)

Axiom tower_acyclic : forall d : Dimension, forall n m : nat,
  tower d n = tower d m -> n = m.

Theorem reify_dim_neq : forall d : Dimension, reify_dim d <> d.
Proof.
  intros d H.
  assert (Ht : tower d 1 = tower d 0).
  { simpl. exact H. }
  apply (tower_acyclic d 1 0) in Ht.
  discriminate Ht.
Qed.

Theorem no_self_containment :
  forall d : Dimension,
    native_dim (reify d) <> d.
Proof.
  intro d. exact (reify_dim_neq d).
Qed.

Theorem level_separation :
  forall d : Dimension, forall n : nat,
    tower d (S n) <> tower d n.
Proof.
  intros d n H.
  apply (tower_acyclic d (S n) n) in H.
  induction n.
  - discriminate H.
  - injection H. exact IHn.
Qed.

(* NOTE ON TOWER CYCLES:
   level_separation forbids consecutive repeats:
     tower d (S n) ≠ tower d n.

   tower_acyclic forbids ALL cycles of any length:
     tower d n = tower d m → n = m.

   This means:
     reify_dim d1 = d2  and  reify_dim d2 = d1
   is impossible. If it held:
     tower d1 0 = d1
     tower d1 1 = reify_dim d1 = d2
     tower d1 2 = reify_dim d2 = d1 = tower d1 0
   so tower d1 2 = tower d1 0, giving 2 = 0.
   Contradiction. *)

(* ================================================ *)
(*  DIMENSION COMPARISON IS CONTEXTUAL              *)
(* ================================================ *)

Definition dims_comparable (d1 d2 : Dimension) : Prop :=
  exists c : Dimension,
    reify_dim d1 <= c /\ reify_dim d2 <= c.

Theorem dims_comparable_at :
  forall d1 d2 : Dimension,
  forall c : Dimension,
    reify_dim d1 <= c ->
    reify_dim d2 <= c ->
    comparable_at (reify d1) (reify d2) c.
Proof.
  intros d1 d2 c H1 H2. split; assumption.
Qed.

Theorem dims_have_op_at :
  forall d1 d2 : Dimension,
  forall c : Dimension,
  forall (H1 : native_dim (reify d1) <= c)
         (H2 : native_dim (reify d2) <= c),
    {project (reify d1) c H1 =
     project (reify d2) c H2} +
    {project (reify d1) c H1 <>
     project (reify d2) c H2}.
Proof.
  intros. apply existence_is_difference.
  rewrite project_dim, project_dim. reflexivity.
Qed.

(* ================================================ *)
(*  COMPARISON-INFORMATION TRADEOFF                 *)
(* ================================================ *)

Theorem coarsening_widens :
  forall a b d1 d2,
    d1 <= d2 ->
    comparable_at a b d1 ->
    comparable_at a b d2.
Proof.
  intros a b d1 d2 Hle [Ha Hb].
  split.
  - exact (dim_le_trans _ _ _ Ha Hle).
  - exact (dim_le_trans _ _ _ Hb Hle).
Qed.

Theorem projection_reflects_diff :
  forall a b d
    (Ha : native_dim a <= d) (Hb : native_dim b <= d),
    project a d Ha <> project b d Hb ->
    a <> b.
Proof.
  intros a b d Ha Hb Hproj Heq.
  apply Hproj. subst b. apply project_irrel.
Qed.

(* NOT provable (information loss):
   a <> b does NOT imply projections differ. *)

Theorem native_identity_is_absolute :
  forall a b : Entity,
    native_dim a = native_dim b ->
    forall (Ha : native_dim a <= native_dim a)
           (Hb : native_dim b <= native_dim a),
      project a (native_dim a) Ha =
      project b (native_dim a) Hb ->
      a = b.
Proof.
  intros a b Hnd Ha Hb Heq.
  rewrite project_self in Heq.
  revert Heq. revert Hb.
  rewrite Hnd.
  intros Hb Heq.
  rewrite project_self in Heq.
  exact Heq.
Qed.

(* ================================================ *)
(*  UNIVERSAL DIMENSION                             *)
(*                                                  *)
(*  The framework does not assert or deny its       *)
(*  existence. dim_le is a preorder, not a lattice: *)
(*  Top is not required.                            *)
(*                                                  *)
(*  The definition below shows that IF such a       *)
(*  dimension existed, everything would be          *)
(*  comparable.                                     *)
(* ================================================ *)

Definition universal_dim (d : Dimension) : Prop :=
  forall a : Entity, native_dim a <= d.

Theorem universal_makes_comparable :
  forall d : Dimension,
    universal_dim d ->
    forall a b : Entity, comparable_at a b d.
Proof.
  intros d Huniv a b. split; apply Huniv.
Qed.

(* ================================================ *)
(*  COMPARABILITY: equivalence relation             *)
(* ================================================ *)

Theorem comp_at_refl : forall a d,
  native_dim a <= d -> comparable_at a a d.
Proof. intros. split; assumption. Qed.

Theorem comp_at_sym : forall a b d,
  comparable_at a b d -> comparable_at b a d.
Proof. intros a b d [Ha Hb]. split; assumption. Qed.

Theorem comp_at_trans : forall a b c d,
  comparable_at a b d -> comparable_at b c d -> comparable_at a c d.
Proof. intros a b c d [Ha _] [_ Hc]. split; assumption. Qed.

(* ================================================ *)
(*  SELF-REFERENCE                                  *)
(* ================================================ *)

Theorem self_reference_via_coarsening :
  forall d c : Dimension,
    reify_dim d <= c ->
    d <= c ->
    forall a : Entity,
      native_dim a = d ->
      comparable_at (reify d) a c.
Proof.
  intros d c Hmeta Hd a Ha. split.
  - exact Hmeta.
  - rewrite Ha. exact Hd.
Qed.

Theorem self_reference_impossible :
  forall d : Dimension,
    (forall c, ~ (reify_dim d <= c /\ d <= c)) ->
    forall a : Entity,
      native_dim a = d ->
      forall c, ~ comparable_at (reify d) a c.
Proof.
  intros d Hno a Ha c [Hm Hd].
  apply (Hno c). split.
  - exact Hm.
  - rewrite Ha in Hd. exact Hd.
Qed.

(* ================================================ *)
(*  DICHOTOMY                                       *)
(* ================================================ *)

Theorem dichotomy :
  forall a b : Entity,
    a <> b ->
    forall d : Dimension,
    forall (Ha : native_dim a <= d) (Hb : native_dim b <= d),
      (project a d Ha <> project b d Hb)
      \/
      (project a d Ha = project b d Hb).
Proof.
  intros a b Hneq d Ha Hb.
  destruct (existence_is_difference
    (project a d Ha) (project b d Hb)
    (eq_trans (project_dim a d Ha)
              (eq_sym (project_dim b d Hb))))
    as [Heq | Hneq_proj].
  - right. exact Heq.
  - left. exact Hneq_proj.
Qed.

(* ================================================ *)
(*  NON-THEOREMS                                    *)
(*                                                  *)
(*  NOT provable:                                   *)
(*    project a d Ha = project b d Hb -> a = b      *)
(*    a <> b -> project a d Ha <> project b d Hb    *)
(*                                                  *)
(*  Projection is not invertible. Distinct entities  *)
(*  can collapse under projection.                  *)
(*  Witnessed by ConsistencyModel.v.                *)
(* ================================================ *)

(* ================================================ *)
(*  DESIGN DECISIONS                                *)
(* ================================================ *)

(* NOTE ON EMPTY DOMAINS:
   No axiom guarantees that any entity or dimension
   exists. Entity and Dimension could be empty types.
   If empty, all forall-theorems are vacuously true.
   The framework describes what follows IF something
   exists. It does not claim anything must exist. *)

(* NOTE ON SINGLETONS:
   If only one entity exists in a dimension,
   existence_is_difference gives {a = a} + {a <> a},
   which is trivially left (reflexivity). *)

(* NOTE ON reify_injective:
   This is the one axiom whose necessity is debatable.
   It says: different dimensions produce different
   entities under reify.

   What breaks without it:
   Only dim_identity_decidable_at (the ability to
   decide whether two dimensions are the same when
   their reify_dims match). All other theorems
   survive. *)

(* NOTE ON tower_acyclic:
   Previously, no-self-containment was axiomatized
   directly as reify_dim_neq (reify_dim d ≠ d),
   which only forbade 1-cycles. tower_acyclic
   forbids all cycles of any length.

   This argument is sound but not formally derivable
   from other axioms. reify has no monotonic
   direction — it can gain, lose, or simply change
   information. Without monotonicity, the round-trip
   argument has no formal anchor.

   Therefore tower_acyclic is axiomatized directly.
   It strictly generalizes reify_dim_neq, which is
   now derived as a theorem. Net change: one axiom
   replaced by a strictly stronger one. *)

(* NOTE ON DIRECTIONALITY:
   native_dim (reify d) has no directional
   relationship to d. It is not "above" or "below."
   It is simply different from d.

   Three cases are all consistent:
   - d <= native_dim (reify d)
   - native_dim (reify d) <= d
   - incomparable
   The framework does not choose between them. *)

(* NOTE ON PREORDER (NOT PARTIAL ORDER):
   dim_le is reflexive and transitive but NOT
   antisymmetric. This is deliberate.

   d1 <= d2 and d2 <= d1 does NOT imply d1 = d2.
   Instead it means d1 ≈ d2: dimensionally
   equivalent. Bidirectional projection with no
   information loss.

   Antisymmetry would collapse dim_equiv with
   propositional equality. The preorder keeps
   them separate. *)

(* ================================================ *)
(*  INVENTORY                                       *)
(*                                                  *)
(*  Types (2):                                      *)
(*    Entity, Dimension                             *)
(*                                                  *)
(*  Parameters (4):                                 *)
(*    dim_le, native_dim, project, reify            *)
(*                                                  *)
(*  Axioms (8):                                     *)
(*    dim_le_refl          (preorder)               *)
(*    dim_le_trans         (preorder)               *)
(*    dim_le_irrel         (proof irrelevance)      *)
(*    project_dim          (projection lands right) *)
(*    project_self         (identity projection)    *)
(*    existence_is_difference  (the core axiom)     *)
(*    reify_injective      (distinct dims ≠ entities)*)
(*    tower_acyclic        (reify tower never cycles)*)
(*                                                  *)
(*  Derived:                                        *)
(*    - dim_equiv is equivalence relation           *)
(*    - entity → domain + operator                  *)
(*    - dimension → domain + operator               *)
(*    - every tower level → domain + operator       *)
(*    - reify_dim_neq (from tower_acyclic)          *)
(*    - no self-containment (from reify_dim_neq)    *)
(*    - level separation (from tower_acyclic)       *)
(*    - dimension comparison is contextual          *)
(*    - projection reflects difference              *)
(*    - projection does NOT preserve difference     *)
(*    - coarsening widens comparability             *)
(*    - native identity is absolute                 *)
(*    - comparability is equivalence relation       *)
(*    - self-reference: coarsening or impossible    *)
(*    - dichotomy                                   *)
(*    - NON-THEOREMS (witnessed by models):         *)
(*      proj= does NOT imply native=               *)
(*      native≠ does NOT imply proj≠               *)
(* ================================================ *)

(* ================================================ *)
(*  COMPANION FILES                                 *)
(*                                                  *)
(*  ConsistencyModel.v                              *)
(*    Concrete model satisfying all axioms.          *)
(*    Witnesses the non-theorems.                   *)
(*                                                  *)
(*  ConsistencyModelPD.v                            *)
(*    Path-dependent model satisfying all axioms.   *)
(*    Together with ConsistencyModel.v, proves      *)
(*    path dependence is independent of the axioms. *)
(* ================================================ *)

(* ================================================ *)
(*  VERSION HISTORY                                 *)
(*                                                  *)
(*  v1: Initial formalization. Overclaimed —        *)
(*      tried to prove "sameness implies not        *)
(*      attributable" as a theorem. Actually        *)
(*      just equality substitution (x=y → Px↔Py).   *)
(*                                                  *)
(*  v2-v3: Restructuring. Added dim_equiv,          *)
(*      separated preorder from partial order.      *)
(*                                                  *)
(*  v4: Added entropy-style examples in comments.   *)
(*                                                  *)
(*  v5: dim_entity and operator as separate params. *)
(*      Too many moving parts.                      *)
(*                                                  *)
(*  v6: DOMAIN = OPERATOR unification.              *)
(*      Merged dim_entity + reify into one.         *)
(*      Removed theorems that were just equality    *)
(*      properties.                                 *)
(*                                                  *)
(*  v7 (current): Removed meta_dimension parameter  *)
(*      and reify_placement axiom. native_dim(reify *)
(*      d) replaces both. Renamed meta_level to     *)
(*      tower. Replaced reify_dim_neq axiom with    *)
(*      tower_acyclic (strictly stronger).           *)
(*      reify_dim_neq and level_separation now      *)
(*      derived as theorems.                        *)
(* ================================================ *)