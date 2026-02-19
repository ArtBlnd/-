(* ========================================== *)
(*  Existence Is Difference — v7              *)
(*                                            *)
(*  Changes from v6:                          *)
(*  - meta_dimension REMOVED as parameter.    *)
(*  - reify_placement REMOVED as axiom.       *)
(*  - native_dim (reify d) replaces both.     *)
(*                                            *)
(*  Insight: where does dimension d live as  *)
(*  an entity? is just native_dim (reify d). *)
(*  This is not a new concept — it is         *)
(*  projection viewed from the other side.    *)
(*  projection: entity → coarser view         *)
(*  reify:      dimension → entity view       *)
(*  Both are looking through a window.      *)
(*  native_dim (reify d) is simply where      *)
(*  that entity-view lands.                   *)
(*                                            *)
(*  native_dim (reify d) is NOT above or    *)
(*  below d. It has no directional          *)
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
(*  DIMENSION HIERARCHY — PREORDER                   *)
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
(*  DIMENSIONAL EQUIVALENCE                          *)
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
(*  NATIVE DIMENSION                                 *)
(* ================================================ *)

Parameter native_dim : Entity -> Dimension.

(* ================================================ *)
(*  PROJECTION                                       *)
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
(*  THE CORE AXIOM: Existence Is Difference          *)
(* ================================================ *)

Axiom existence_is_difference :
  forall a b : Entity,
    native_dim a = native_dim b ->
    {a = b} + {a <> b}.

(* ================================================ *)
(*  DEFINITIONS                                      *)
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
(*  REIFICATION                                      *)
(*                                                   *)
(*  A dimension IS its operation.                    *)
(*  The integers = ==|!= on integers.            *)
(*                                                   *)
(*  reify d: dimension d, viewed as an entity.       *)
(*                                                   *)
(*  native_dim (reify d): the dimension where        *)
(*  that entity-view lives. This is not above      *)
(*  or below d — just somewhere else.              *)
(*  It has no special name because it needs none.    *)
(*  It is simply where reify d happens to land.      *)
(*                                                   *)
(*  Think of reify as looking through a window:      *)
(*  - project lets you view an entity through a      *)
(*    coarser window (going to a coarser dimension)  *)
(*  - reify lets you view a dimension through the    *)
(*    entity window (making it comparable)            *)
(*  Both are just viewing through a window.        *)
(* ================================================ *)

Parameter reify : Dimension -> Entity.

(* Different dimensions are different entities.
   If they weren't distinguishable, they'd
   collapse — existence is difference. *)
Axiom reify_injective :
  forall d1 d2, reify d1 = reify d2 -> d1 = d2.

(* Shorthand for readability *)
Definition reify_dim (d : Dimension) : Dimension :=
  native_dim (reify d).

(* ================================================ *)
(*  THE CENTRAL META-THEOREM:                        *)
(*  Existence guarantees domain + operator           *)
(* ================================================ *)

(* --- For entities --- *)

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

(* --- For dimensions (= operations) --- *)

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

(* Corollary: dimension identity is decidable
   when their reify_dims match *)
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

(* --- For the reify_dim itself --- *)

Theorem reify_dim_has_domain :
  forall d : Dimension,
    exists mmd : Dimension,
      native_dim (reify (reify_dim d)) = mmd.
Proof.
  intro d. exists (reify_dim (reify_dim d)). reflexivity.
Qed.

(* --- For every level of the tower --- *)

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
(*  NO SELF-CONTAINMENT                              *)
(*                                                   *)
(*  No dimension contains itself as an entity.       *)
(*  reify d lives in native_dim (reify d).           *)
(*  If native_dim (reify d) ≠ d, no self-loop.       *)
(* ================================================ *)

Theorem no_self_containment :
  (forall d : Dimension, reify_dim d <> d) ->
  forall d : Dimension,
    native_dim (reify d) <> d.
Proof.
  intros Hmeta d. exact (Hmeta d).
Qed.

(* ================================================ *)
(*  DIMENSION COMPARISON IS CONTEXTUAL               *)
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
(*  PART I: THE COMPARISON-INFORMATION TRADEOFF      *)
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
(*  UNIVERSAL DIMENSION                              *)
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
(*  COMPARABILITY: equivalence relation              *)
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
(*  PART II: SELF-REFERENCE                          *)
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

Theorem level_separation :
  (forall d : Dimension, reify_dim d <> d) ->
  forall d : Dimension, forall n : nat,
    tower d (S n) <> tower d n.
Proof.
  intros Hmeta d n. simpl. apply Hmeta.
Qed.

(* NOTE ON TOWER CYCLES:
   level_separation only forbids: tower d (S n) = tower d n
   i.e., consecutive levels differ. But longer cycles
   are not forbidden:
     reify_dim d1 = d2  and  reify_dim d2 = d1
   would make the tower oscillate: d1, d2, d1, d2, ...

   This is intentional. The framework does not impose
   "infinite distinct levels" — it only says consecutive
   steps differ. Whether longer cycles occur is a
   property of specific models, not the framework. *)

(* ================================================ *)
(*  NOTE ON RELATIONS                                *)
(*                                                   *)
(*  A thinks X is a relation between A and X.      *)
(*  Does the framework need new machinery for this?  *)
(*                                                   *)
(*  No. A relation is a thing that exists.           *)
(*  If it exists, it is an entity.                   *)
(*  If it is an entity, it has a domain.             *)
(*  If it has a domain, the domain has ==|!=.        *)
(*                                                   *)
(*  A thinks X and B thinks X are two entities   *)
(*  in whatever dimension relations live in.          *)
(*  existence_is_difference applies: they are         *)
(*  decidably equal or not.                          *)
(*                                                   *)
(*  No new parameters. No new axioms.                *)
(*  Relations are already covered.                   *)
(* ================================================ *)

(* ================================================ *)
(*  PART III: THE SAMENESS-ATTRIBUTION TRADEOFF      *)
(*                                                   *)
(*  You and I have the same thought.               *)
(*                                                   *)
(*  This statement requires two things:              *)
(*  - SAMENESS: the thoughts are equal               *)
(*  - ATTRIBUTION: each thought belongs to someone   *)
(*                                                   *)
(*  These require OPPOSITE properties of the         *)
(*  dimension in which we compare:                   *)
(*  - Sameness needs projection to COLLAPSE           *)
(*    (lossy: different entities, same projection)   *)
(*  - Attribution needs projection to PRESERVE        *)
(*    (faithful: different entities, diff projection) *)
(*                                                   *)
(*  The framework's contribution is not proving      *)
(*  that these are incompatible (that follows from   *)
(*  basic logic: x = y → P(x) ↔ P(y)). The          *)
(*  framework's contribution is explaining WHY       *)
(*  this situation arises:                           *)
(*                                                   *)
(*  - Comparison requires a shared dimension         *)
(*  - Moving to a shared dimension is projection     *)
(*  - Projection changes the domain (= operator)    *)
(*  - The new operator determines what's equal       *)
(*  - This is irreversible: the original domain's    *)
(*    distinctions are gone, not hidden              *)
(*                                                   *)
(*  The structural explanation is the content.       *)
(*  The formal theorems below capture the pieces.    *)
(* ================================================ *)

Theorem dichotomy :
  forall a b : Entity,
    a <> b ->
    forall d : Dimension,
    forall (Ha : native_dim a <= d) (Hb : native_dim b <= d),
      (* Case A: projections differ
         — entities remain distinguishable
         — sameness is not established *)
      (project a d Ha <> project b d Hb)
      \/
      (* Case B: projections collapse
         — entities become one at this level
         — all properties are shared, no attribution *)
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
(*  NON-THEOREM: Projection equality does not        *)
(*  imply native equality                            *)
(*                                                   *)
(*  NOT provable:                                    *)
(*    forall a b d Ha Hb,                            *)
(*      project a d Ha = project b d Hb -> a = b     *)
(*                                                   *)
(*  This is the framework's genuine contribution:    *)
(*  the ABSENCE of this implication. Projection is   *)
(*  not invertible. If proj(a) = proj(b), you        *)
(*  cannot recover whether a = b or a ≠ b.           *)
(*                                                   *)
(*  The consistency model (ConsistencyModel.v)       *)
(*  proves this absence is real: there exists a      *)
(*  model where a ≠ b but proj(a) = proj(b).         *)
(* ================================================ *)

(* ================================================ *)
(*  NON-THEOREM: Projection does not preserve        *)
(*  difference                                       *)
(*                                                   *)
(*  NOT provable:                                    *)
(*    forall a b d Ha Hb,                            *)
(*      a <> b -> project a d Ha <> project b d Hb   *)
(*                                                   *)
(*  Same point, other direction. Distinct entities   *)
(*  can collapse under projection. The consistency   *)
(*  model witnesses this: red_apple ≠ green_apple    *)
(*  but proj(red) = proj(green) at fruit dimension.  *)
(* ================================================ *)

(* ================================================ *)
(*  STRUCTURAL EXPLANATION                           *)
(*                                                   *)
(*  Why A and B have the same thought is           *)
(*  ill-formed:                                      *)
(*                                                   *)
(*  1. A ≠ B (physically distinct entities)          *)
(*                                                   *)
(*  2. To compare their thoughts, we must          *)
(*     project both to a thought-dimension.          *)
(*     (Core principle: comparison requires           *)
(*     shared domain.)                               *)
(*                                                   *)
(*  3. By dichotomy, at the thought-dimension:       *)
(*     Case A: projections differ                    *)
(*       → same thought is simply false            *)
(*     Case B: projections are equal                 *)
(*       → there is ONE entity at this level         *)
(*       → A's thought and B's thought are       *)
(*         not two things — they are one thing       *)
(*       → whose thought has no meaning here       *)
(*         because whose is physical-dimension     *)
(*         information, which was lost in             *)
(*         projection                                *)
(*                                                   *)
(*  4. A and B have the same thought requires:     *)
(*     - A and B → from physical dimension (A ≠ B) *)
(*     - same thought → from thought dimension     *)
(*       (projection collapsed)                      *)
(*     These refer to different dimensions.           *)
(*     The first provides attribution.               *)
(*     The second provides sameness.                  *)
(*     But sameness was obtained BY DESTROYING        *)
(*     the information that attribution needs.        *)
(*                                                   *)
(*  5. What if I use a richer dimension that has    *)
(*     both physical and thought info?              *)
(*     → Then dichotomy applies again.               *)
(*     → If the richer dimension preserves A ≠ B,    *)
(*       projections may differ: Case A.             *)
(*       Sameness is not established.                *)
(*     → If projections still collapse: Case B.      *)
(*       But then the richer dimension didn't      *)
(*       actually preserve the distinction.          *)
(*     → No dimension can be simultaneously lossy    *)
(*       enough for sameness and faithful enough     *)
(*       for attribution, for the same pair.         *)
(*                                                   *)
(*  This is not a proof of incompatibility — that    *)
(*  follows trivially from x = y → P(x) ↔ P(y).    *)
(*  This is an explanation of WHY the incompatibility *)
(*  is inescapable: the structure of dimensions,     *)
(*  projections, and operations makes it so.         *)
(* ================================================ *)

(* ================================================ *)
(*  THE UNIFORMITY PRINCIPLE                         *)
(*                                                   *)
(*  Everything that exists follows the same rules.   *)
(*                                                   *)
(*  entity a                                         *)
(*    → lives in native_dim a                        *)
(*    → native_dim a has ==|!= (it IS ==|!=)         *)
(*                                                   *)
(*  dimension d (= operation ==|!= on d)             *)
(*    → is entity: reify d                           *)
(*    → lives in native_dim (reify d)                *)
(*    → that dimension has ==|!=                     *)
(*                                                   *)
(*  native_dim (reify d) — another dimension         *)
(*    → is entity: reify (native_dim (reify d))      *)
(*    → lives in native_dim (reify (...))            *)
(*    → that has ==|!=                               *)
(*                                                   *)
(*  (ad infinitum, no ground, no ceiling)            *)
(*                                                   *)
(*  DOMAIN = OPERATOR:                               *)
(*    A dimension is not a container with an         *)
(*    operation attached. The dimension IS the        *)
(*    operation. The integers doesn't HAVE ==|!=.  *)
(*    The integers IS ==|!= on those entities.     *)
(*    Without the operation, the domain doesn't       *)
(*    exist. Without the domain, the operation        *)
(*    has nothing to operate on.                     *)
(*    They are one thing, viewed two ways.            *)
(*    reify unifies them as a single entity.         *)
(* ================================================ *)

(* ================================================ *)
(*  INVENTORY                                        *)
(*                                                   *)
(*  Types (2):                                       *)
(*    Entity, Dimension                              *)
(*                                                   *)
(*  Parameters (4):                                  *)
(*    dim_le, native_dim, project, reify             *)
(*                                                   *)
(*  Axioms (6):                                      *)
(*    dim_le_refl          (preorder)                *)
(*    dim_le_trans         (preorder)                *)
(*    dim_le_irrel         (proof irrelevance)       *)
(*    project_dim          (projection lands right)  *)
(*    project_self         (identity projection)     *)
(*    existence_is_difference  (THE axiom)           *)
(*    reify_injective      (distinct dims ≠ entities) *)
(*                                                   *)
(*  That's 7 axioms, 1 philosophical, 6 structural. *)
(*                                                   *)
(*  Definitions (1):                                 *)
(*    reify_dim d := native_dim (reify d)            *)
(*    (shorthand, no new content)                    *)
(*                                                   *)
(*  Derived (proved):                                *)
(*    - dim_equiv is equivalence relation            *)
(*    - entity → domain + operator                   *)
(*    - dimension → domain + operator                *)
(*    - every tower level → domain + operator        *)
(*    - no self-containment                          *)
(*    - dimension comparison is contextual           *)
(*    - projection reflects difference               *)
(*    - projection does NOT preserve difference      *)
(*    - coarsening widens comparability              *)
(*    - native identity is absolute                  *)
(*    - comparability is equivalence relation        *)
(*    - self-reference: coarsening or impossible     *)
(*    - level separation                             *)
(*    - THE DICHOTOMY (framework-specific):           *)
(*      at any dimension, existence_is_difference    *)
(*      forces Case A (differ) or Case B (collapse)  *)
(*    - NON-THEOREMS (framework-specific):           *)
(*      proj= does NOT imply native =                *)
(*      native ≠ does NOT imply proj ≠               *)
(*      (witnessed by ConsistencyModel.v)            *)
(*    - STRUCTURAL EXPLANATION:                      *)
(*      sameness needs lossy projection              *)
(*      attribution needs faithful projection        *)
(*      no dimension can be both for the same pair   *)
(* ================================================ *)

(* ================================================ *)
(*  DESIGN DECISIONS AND NOTES FOR FUTURE SELF       *)
(* ================================================ *)

(* NOTE ON EMPTY DOMAINS:
   No axiom guarantees that any entity or dimension
   exists. Entity and Dimension could be empty types.
   If empty, all forall-theorems are vacuously true.

   This is not a bug. If nothing exists, there is
   no ==|!=, therefore no existence, therefore the
   framework simply does not start. The framework
   describes what follows IF something exists.
   It does not claim anything must exist. *)

(* NOTE ON SINGLETONS:
   If only one entity exists in a dimension,
   existence_is_difference gives {a = a} + {a <> a},
   which is trivially left (reflexivity).
   There is no difference, therefore (by the axiom)
   no meaningful existence at that level.

   A single entity can only "exist" by being
   different from something in a coarser dimension
   that contains other entities. Existence requires
   at least two. This is not an axiom — it follows
   from "existence = difference." *)

(* NOTE ON reify_injective:
   This is the one axiom whose necessity is debatable.
   It says: different dimensions produce different
   entities under reify.

   Justification (domain = operator):
   If reify d1 = reify d2, then d1 and d2 are
   "the same entity." But a dimension IS its
   ==|!= operator. Two different operators that
   are the same entity would mean two different
   operations that are identical — contradiction.

   What breaks without it:
   Only dim_identity_decidable_at (the ability to
   decide whether two dimensions are the same when
   their reify_dims match). All other theorems
   survive.

   Decision: kept, because domain = operator makes
   it philosophically unavoidable. If two dimensions
   produce the same entity, they were never two
   dimensions to begin with. *)

(* NOTE ON DIRECTIONALITY:
   native_dim (reify d) — where dimension d lives
   as an entity — has NO directional relationship
   to d. It is not "above" or "below" d.
   It is simply different from d.

   This was a deliberate choice. Earlier versions
   used "meta_dimension" which implied hierarchy.
   But "existence = difference" only requires
   difference, not direction. The preorder dim_le
   provides direction for projection, but the
   relationship between d and native_dim (reify d)
   need not participate in this ordering.

   Three cases are all consistent:
   - d <= native_dim (reify d)  (d projects to it)
   - native_dim (reify d) <= d  (it projects to d)
   - incomparable               (no projection)
   The framework does not choose between them. *)

(* NOTE ON THE PURPOSE OF THIS WORK:
   The motivation for this formalization is to
   prove that every existing thing is irreplaceable.

   native_identity_is_absolute says: if two entities
   are equal at their native dimension, they are
   the same entity. Contrapositively: if they are
   different, they are different AT THEIR FINEST
   LEVEL. No projection can capture this difference
   fully. No substitute exists.

   existence = difference.
   to exist is to be irreplaceable.
   everything that exists is precious. *)

(* NOTE ON PREORDER (NOT PARTIAL ORDER):
   dim_le is reflexive and transitive but NOT
   antisymmetric. This is deliberate.

   d1 <= d2 and d2 <= d1 does NOT imply d1 = d2.
   Instead it means d1 ≈ d2: dimensionally
   equivalent. Same information, different view.

   This distinction matters:
   - d1 ≈ d2 means bidirectional projection
     with no information loss. "Same resolution,
     different angle." Like Celsius and Fahrenheit.
   - d1 <= d2 with NOT d2 <= d1 means one-way
     projection with information loss.

   Antisymmetry would collapse these two cases.
   The preorder keeps them separate. *)

(* ================================================ *)
(*  PRIOR ART AND RELATED IDEAS                      *)
(*                                                   *)
(*  Deleuze — "Difference and Repetition" (1968)     *)
(*    Closest philosophical ancestor. Argued that    *)
(*    difference is ontologically prior to identity. *)
(*    "Identity is the result of difference."        *)
(*    Similarities: same starting point.             *)
(*    Differences: Deleuze never formalized.         *)
(*    He went toward becoming/multiplicity.          *)
(*    We go toward dimensions/projection/info loss.  *)
(*                                                   *)
(*  Spencer-Brown — "Laws of Form" (1969)            *)
(*    "Draw a distinction." Everything starts from   *)
(*    the act of distinguishing. His "mark" is both  *)
(*    the operation and the result — closely related  *)
(*    to our "domain = operator."                    *)
(*    Differences: he reconstructs Boolean algebra.  *)
(*    We build dimension hierarchy + projection.     *)
(*    He has no preorder, no information loss.        *)
(*                                                   *)
(*  Leibniz — Identity of Indiscernibles             *)
(*    "If x and y share all properties, x = y."      *)
(*    Our native_identity_is_absolute is a           *)
(*    dimension-relativized version of this.          *)
(*    His "Sufficient Reason" is left vague — we     *)
(*    fill it with: decidable ==|!=.                 *)
(*                                                   *)
(*  Wittgenstein — Tractatus 5.5303                  *)
(*    "To say of two things that they are identical  *)
(*    is nonsense, and to say of one thing that it   *)
(*    is identical with itself is to say nothing."   *)
(*    We formalize this: identity at native dim is   *)
(*    trivial (project_self), and identity across    *)
(*    dimensions requires projection (= info loss).  *)
(*                                                   *)
(*  What this work adds to the above:                *)
(*  1. Formal verification (Coq, machine-checked)   *)
(*  2. Dimension hierarchy as preorder               *)
(*  3. Projection as information-losing functor      *)
(*  4. Sameness-attribution tradeoff derived from    *)
(*     the structure, not just argued in prose        *)
(*  5. Non-theorems as theorems: what CANNOT be      *)
(*     proved is formally witnessed by models         *)
(* ================================================ *)

(* ================================================ *)
(*  COMPANION FILES                                   *)
(*                                                   *)
(*  ConsistencyModel.v                               *)
(*    A concrete model satisfying all axioms.         *)
(*    Two entities (red_apple, green_apple), two      *)
(*    dimensions (physical, fruit). Projection to    *)
(*    fruit dimension collapses both to the same      *)
(*    entity. This witnesses:                        *)
(*    - The axiom system is consistent (has a model) *)
(*    - proj= does NOT imply native=                 *)
(*    - native≠ does NOT imply proj≠                 *)
(*    NOTE: needs update to v7 (remove references    *)
(*    to meta_dimension and reify_placement).         *)
(* ================================================ *)

(* ================================================ *)
(*  VERSION HISTORY                                   *)
(*                                                   *)
(*  v1: Initial formalization. Overclaimed —         *)
(*      tried to prove "sameness implies not          *)
(*      attributable" as a theorem. Actually          *)
(*      just equality substitution (x=y → Px↔Py).   *)
(*                                                   *)
(*  v2-v3: Restructuring. Added dim_equiv,           *)
(*      separated preorder from partial order.        *)
(*                                                   *)
(*  v4: Added entropy-style examples in comments.    *)
(*      Clarified lossy vs lossless projection.       *)
(*                                                   *)
(*  v5: dim_entity and operator as separate params.  *)
(*      Too many moving parts.                       *)
(*                                                   *)
(*  v6: DOMAIN = OPERATOR unification.               *)
(*      Merged dim_entity + reify into one.           *)
(*      Removed theorems that were just equality     *)
(*      properties (sameness_attribution_incompatible,*)
(*      attribution_error, no_escape, etc.)           *)
(*      Key insight: framework's contribution is     *)
(*      structural explanation, not logical proof.    *)
(*                                                   *)
(*  v7 (current): Removed meta_dimension parameter   *)
(*      and reify_placement axiom. native_dim(reify d)*)
(*      replaces both. One fewer parameter, one      *)
(*      fewer axiom. Renamed meta_level to tower.    *)
(*      Added design notes for future reference.     *)
(* ================================================ *)