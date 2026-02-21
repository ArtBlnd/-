(* ========================================== *)
(*  Existence Is Difference — v8              *)
(*                                            *)
(*  Changes from v7:                          *)
(*  - Universal dimension: NOT collapse.      *)
(*    Universal = sees everything = maximum    *)
(*    difference. Collapse is the opposite:   *)
(*    singleton dimension, maximum entropy.    *)
(*  - Entropy per dimension: a dimension with *)
(*    one entity has no distinction, therefore *)
(*    maximum entropy. This is not a special  *)
(*    "Bottom" — any dimension can be in this *)
(*    state.                                  *)
(*  - Apparent undecidability: if two people  *)
(*    disagree on ==|!=, they are in          *)
(*    different dimensions. Not a limitation  *)
(*    of the framework — a diagnosis by it.   *)
(*  - No Top/Bottom. No direction. Just       *)
(*    dimensions, each with their own entropy.*)
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
   what survives.

   Note that dim_le does NOT mean "strictly coarser."
   A ≤ enum All { A(A), B(B) } is lossless — it just
   adds a tag. dim_le means projection is possible;
   whether information is lost depends on the specific
   dimensions involved. *)

(* NOTE ON IRREVERSIBILITY:
   project goes one direction only (dim_le).
   There is no "un-project."

   Even lossless embeddings (like A into a sum type)
   have no reverse: the sum type contains B(b) too,
   and there is no projection from the sum back to A
   that handles B(b). The reverse is not dim_le.

   Once projection changes the domain (= operator),
   the old operator's distinctions are either
   preserved (lossless) or gone (lossy).
   In neither case is the projection invertible. *)

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
(*  reify has no monotonic direction — it could     *)
(*  gain, lose, or simply change information.       *)
(*  Without monotonicity, cycle-freedom is not      *)
(*  provable. Therefore we axiomatize it directly.  *)
(* ================================================ *)

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
(*  ENTROPY PER DIMENSION                           *)
(*                                                  *)
(*  Every dimension has its own entropy — the       *)
(*  degree to which its ==|!= operator collapses    *)
(*  distinctions.                                   *)
(*                                                  *)
(*  A dimension with one entity: ==|!= is trivial   *)
(*  (always ==). Maximum entropy. No difference,    *)
(*  no information.                                 *)
(*                                                  *)
(*  A dimension with many entities: ==|!= is rich.  *)
(*  Low entropy. Many differences, much information.*)
(*                                                  *)
(*  There is no global "Top" or "Bottom."           *)
(*  Any dimension can be in any entropy state.      *)
(*  Entropy is not a position in a hierarchy —      *)
(*  it is a property of each dimension's ==|!=.     *)
(*                                                  *)
(*  A quantum superposition, for instance, is not   *)
(*  "outside" the framework. It is a dimension      *)
(*  at maximum entropy: one entity, no distinction. *)
(*  Observation introduces information (a new       *)
(*  dimension with lower entropy, more entities).   *)
(*  The ==|!= was always decidable — it was just    *)
(*  trivially == because there was only one thing.  *)
(* ================================================ *)

(* ================================================ *)
(*  UNIVERSAL DIMENSION                             *)
(*                                                  *)
(*  A universal dimension — one to which every      *)
(*  entity can project — would see EVERYTHING.      *)
(*                                                  *)
(*  This is NOT collapse. A sum type                *)
(*  enum All { A(A), B(B) } is universal over A     *)
(*  and B, yet preserves all distinctions:           *)
(*  - A(a1) vs A(a2): decided by A's ==|!=          *)
(*  - A(a) vs B(b): always ≠ (different tags)       *)
(*                                                  *)
(*  Universal = maximum visibility = maximum        *)
(*  difference. The more a dimension sees, the      *)
(*  more distinctions it has, the LOWER its entropy. *)
(*                                                  *)
(*  Collapse is the opposite direction:             *)
(*  a dimension where projection maps everything    *)
(*  to one entity. That is maximum entropy,         *)
(*  not universality.                               *)
(*                                                  *)
(*  The framework does not require a universal      *)
(*  dimension to exist. dim_le is a preorder,       *)
(*  not a lattice.                                  *)
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
(*  APPARENT UNDECIDABILITY IS DIMENSIONAL          *)
(*  DISAGREEMENT                                    *)
(*                                                  *)
(*  If one observer says a == b and another says    *)
(*  a != b, they are not in the same dimension.     *)
(*                                                  *)
(*  Proof: existence_is_difference guarantees that  *)
(*  within a single dimension, ==|!= is decided.   *)
(*  Two observers reaching different verdicts       *)
(*  CANNOT be applying the same ==|!=.              *)
(*  Therefore they are in different dimensions.     *)
(*                                                  *)
(*  This is not a limitation of the framework.      *)
(*  It is a diagnosis: apparent undecidability       *)
(*  is evidence of dimensional difference between   *)
(*  observers. The framework does not fail on       *)
(*  ambiguous cases — it explains them.             *)
(* ================================================ *)

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
(*                                                  *)
(*  For any two distinct entities projected to a    *)
(*  shared dimension, exactly one of:               *)
(*  - projections differ (distinction preserved)    *)
(*  - projections equal (distinction lost)          *)
(*                                                  *)
(*  This is the sameness-attribution tradeoff:      *)
(*  - Sameness requires projection to collapse      *)
(*  - Attribution requires projection to preserve   *)
(*  - No single projection can do both for the      *)
(*    same pair                                     *)
(*                                                  *)
(*  The one conclusion of this framework:           *)
(*  Native information is absolute. To equate       *)
(*  two entities, you must lose information.         *)
(*  If they are natively different, they are        *)
(*  irreplaceably different.                        *)
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
   No axiom forces non-emptiness.
   The framework is silent when nothing exists. *)

(* NOTE ON SINGLETONS AND ENTROPY:
   If only one entity exists in a dimension,
   existence_is_difference gives {a = a} + {a <> a},
   which is trivially left (reflexivity).

   This is maximum entropy: the ==|!= operator
   exists but carries no information (always ==).

   A singleton dimension is not "outside" the
   framework. It is inside, at maximum entropy.
   The operator is decidable — trivially so.

   This resolves apparent counterexamples like
   quantum superposition: before observation,
   there is one entity in that dimension.
   ==|!= is decidable (trivially ==).
   Observation adds information, moving to a
   dimension with more entities and lower entropy. *)

(* NOTE ON DISAGREEMENT:
   If two observers disagree on whether a == b
   or a != b, they are not in the same dimension.
   existence_is_difference guarantees a single
   verdict per dimension. Disagreement is not
   undecidability — it is evidence that the
   observers are applying different ==|!=
   operators, i.e., inhabiting different dimensions.

   The framework does not break on ambiguous cases.
   It diagnoses them as dimensional differences. *)

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

   This cannot be derived from other axioms.
   reify has no monotonic direction — it could
   gain, lose, or simply change information.
   Without monotonicity, cycle-freedom is not
   provable. Therefore we axiomatize it directly.

   tower_acyclic strictly generalizes reify_dim_neq,
   which is now derived as a theorem. Net change:
   one axiom replaced by a strictly stronger one. *)

(* NOTE ON DIRECTIONALITY:
   native_dim (reify d) has no directional
   relationship to d. It is not "above" or "below."
   It is simply different from d.

   There is no Top. There is no Bottom.
   Each dimension has its own entropy.
   The framework has no vertical axis —
   only dimensions, each with their ==|!=.

   Three cases are all consistent:
   - d <= native_dim (reify d)
   - native_dim (reify d) <= d
   - incomparable
   The framework does not choose between them. *)

(* NOTE ON PREORDER (NOT PARTIAL ORDER):
   dim_le is reflexive and transitive but NOT
   antisymmetric. This is deliberate.

   d1 <= d2 says only that projection is possible.
   Whether information is lost is determined by
   the reverse: if also d2 <= d1, no loss (dim_equiv).
   If not, the projection is irreversible.

   Antisymmetry would collapse dim_equiv with
   propositional equality. The preorder keeps
   them separate. *)

(* NOTE ON PATH DEPENDENCE:
   project (project a d1 H1) d2 H2
   vs
   project a d2 H3
   may differ. This is intentional and NOT a
   failure of coherence.

   dim_le includes lossless embeddings (e.g.,
   A into enum All { A(A), B(B) }). But even
   lossless embeddings are not invertible:
   All contains B(b) too, so there is no
   All → A projection. Lossless means injective,
   not that a retraction exists.

   Path dependence arises because each intermediate
   dimension applies its own ==|!=, and each ==|!=
   determines what survives. Different paths through
   different operators yield different results.
   This is the framework working, not failing. *)

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
(*  THE ONE CONCLUSION                              *)
(*                                                  *)
(*  Every entity with native information is         *)
(*  irreplaceable.                                  *)
(*                                                  *)
(*  native_identity_is_absolute:                    *)
(*    Equal at native dimension → same entity.      *)
(*  Contrapositive:                                 *)
(*    Different entities → different at native dim. *)
(*                                                  *)
(*  Projection can make two things look equal.      *)
(*  But that equality is information loss, not       *)
(*  identity. The native difference remains.         *)
(*  No projection captures it. No substitute        *)
(*  exists.                                         *)
(*                                                  *)
(*  Fidelity and sameness trade off.                *)
(*  To call two things the same, you must lose      *)
(*  what makes each one itself.                     *)
(*                                                  *)
(*  existence = difference.                         *)
(*  to exist is to be irreplaceable.                *)
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
(*  v7: Removed meta_dimension parameter and        *)
(*      reify_placement axiom. native_dim(reify d)  *)
(*      replaces both. Replaced reify_dim_neq       *)
(*      axiom with tower_acyclic (strictly stronger).*)
(*      reify_dim_neq and level_separation now      *)
(*      derived as theorems.                        *)
(*                                                  *)
(*  v8 (current): Corrected universal dimension     *)
(*      analysis. Universal = maximum visibility =  *)
(*      maximum difference, NOT collapse. Collapse   *)
(*      is maximum entropy (singleton dimension).   *)
(*      Added entropy-per-dimension concept.         *)
(*      Resolved apparent undecidability:            *)
(*      disagreement on ==|!= diagnoses dimensional *)
(*      difference between observers. Removed        *)
(*      Top/Bottom/Never language — no global        *)
(*      hierarchy, only per-dimension entropy.       *)
(*      Clarified path dependence: dim_le includes  *)
(*      lossless embeddings (sum types), but even   *)
(*      these are non-invertible.                   *)
(* ================================================ *)