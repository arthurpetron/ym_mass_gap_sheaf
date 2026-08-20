/-
M4ab -- pin the Yang--Mills-specific content to the same selected continuum
theory and to one classified compact-simple group.

`FourDExistence.ContinuumYMExistence` predates the project's same-object
discipline.  Its four Yang--Mills-specific carrier predicates existentially
choose their own observable algebra, functional, running-coupling data, and
spectral model; their `ContinuumMeasure` argument is not used by the carrier
definitions.  In particular, identity actions and unrelated toy models inhabit
those carriers.

This module records the stronger pins needed after
`ContinuumSelectedExactMassDecayTarget`:

* a nontrivial group action on the exact OS algebra, with the exact OS
  functional invariant under every supplied action;
* a nonidentity idempotent gauge projection on that same algebra, fixing the
  selected gap insertions and through which the same functional factors;
* a Cartan-type / genuine-simple-rank tag whose exact adjoint Casimir drives an
  inverse-coupling trajectory evaluated on the selected projective measure
  thread; and
* a non-Gaussianity witness for the exact same continuum gap correlator already
  carrying the positive exact mass.

The structure is deliberately uninhabited.  It is also not a new frontier
scorecard: `FrontierDAGBridges` records the named completion map from the
canonical `FrontierDAG` into this selected pinned package.

Two limits are explicit.  First, the action-label group below has not yet been
identified with a constructive presentation of the full real group `O(4)`.
Second, a `CartanType` plus exact Casimirs classifies the compact-simple Lie type
but does not yet carry the root/global-form/Haar algorithms required by the
constructive input law.  Both are later analytic/algebraic pins, not conclusions
of this file.
-/

import YMGap.Continuum.ContinuumSelectedExactMassDecayTarget
import YMGap.MassGap.AllSimpleTypes

namespace YMGap.Continuum.ContinuumSelectedTheoryPins

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ContinuumSelectedExactMassDecayTarget
open YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.OSAxioms
open YMGap.MassGap.AllSimpleTypes
open YMGap.RepTheory
open YMGap.RG

/-! ## 1. A nontrivial action on the selected OS observable algebra -/

/-- A group of observable-algebra symmetries acting on the exact OS algebra of
`T`.  Every action preserves the exact OS functional, and a carried witness
rules out the identity-only action.

This is the same-object rotation-action interface.  Its label group must still
be identified with a constructive presentation of full `O(4)` before it can be
called O(4) restoration. -/
structure SelectedRotationActionPins
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) : Type 2 where
  label : Type
  identity : label
  compose : label -> label -> label
  inverse : label -> label
  compose_assoc : forall g h k,
    compose (compose g h) k = compose g (compose h k)
  identity_left : forall g, compose identity g = g
  identity_right : forall g, compose g identity = g
  inverse_left : forall g, compose (inverse g) g = identity
  inverse_right : forall g, compose g (inverse g) = identity
  action : label -> ObsHom T.existence.os_axioms.A T.existence.os_axioms.A
  action_identity : forall a,
    (action identity).map a = a
  action_compose : forall g h a,
    (action (compose g h)).map a = (action g).map ((action h).map a)
  functional_equivariant : forall g,
    FunctionalEquivariant T.existence.os_axioms.E (action g)
  movedLabel : label
  movedObservable : T.existence.os_axioms.A.carrier
  moved : Not ((action movedLabel).map movedObservable = movedObservable)

/-! ## 2. Gauge projection on the same OS algebra and selected gap channel -/

/-- A nonidentity gauge projection on the exact OS algebra of `T`.  The same
functional factors through it, and every selected connected-gap insertion is
fixed by it.  The moved observable prevents the identity projection on a
trivial algebra from satisfying this stronger pin. -/
structure SelectedGaugeProjectionPins
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) : Type 1 where
  projection : ObsHom T.existence.os_axioms.A T.existence.os_axioms.A
  idempotent : forall a,
    projection.map (projection.map a) = projection.map a
  functional_factors : forall a,
    T.existence.os_axioms.E.E (projection.map a) =
      T.existence.os_axioms.E.E a
  gapInsertion_fixed : forall t,
    projection.map
        (T.corrected.exact.projective.continuumInsertion
          T.corrected.exact.projective.gapObservable t) =
      T.corrected.exact.projective.continuumInsertion
        T.corrected.exact.projective.gapObservable t
  movedObservable : T.existence.os_axioms.A.carrier
  moved : Not (projection.map movedObservable = movedObservable)

/-! ## 3. The classified group drives the selected projective UV trajectory -/

/-- The one-loop inverse-coupling trajectory, with its group Casimir fixed by a
classified compact-simple Cartan type and evaluated on the exact selected
measure thread `mu.pick j`.

The evaluator is supplied data because the stage carriers `M j` currently have
no intrinsic coupling projection.  `selectedTrajectoryPinned` is the explicit
same-thread seam; no stage coupling or projective measure is manufactured. -/
structure SelectedGroupUVPins
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu)
    (groupType : CartanType) : Type 1 where
  initialInverseCoupling : Q'
  stageInverseCoupling : (j : Nat) -> M j -> Q'
  selectedTrajectoryPinned : forall j,
    stageInverseCoupling j (mu.pick j) =
      invRunningCoupling initialInverseCoupling
        (repDataOf groupType).C2_adj j

/-! ## 4. Non-Gaussianity of the exact same continuum gap correlator -/

/-- A Wick-product violation on the exact continuum gap correlator selected by
`T`.  Unlike `FourDExistence.NontrivialityContent`, this cannot choose an
unrelated finite spectral model. -/
structure SelectedCorrelationNonGaussianPin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) : Type 1 where
  separation : Nat
  wickViolation :
    Not (CReal.Equiv
      (T.corrected.exact.projective.continuumCorr
        T.corrected.exact.projective.gapObservable separation)
      (CReal.mul
        (T.corrected.exact.projective.continuumCorr
          T.corrected.exact.projective.gapObservable 0)
        (T.corrected.exact.projective.continuumCorr
          T.corrected.exact.projective.gapObservable 0)))

/-! ## 5. Combined same-theory pins -/

/-- The Yang--Mills-specific pins for one selected exact-mass continuum target.
This record strengthens the old phantom carrier fields without changing their
high-dependency legacy definitions.  No inhabitant is supplied. -/
structure SelectedTheoryPins
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) : Type 3 where
  groupType : CartanType
  simpleRank : IsSimpleRank groupType
  rotations : SelectedRotationActionPins T
  gauge : SelectedGaugeProjectionPins T
  uv : SelectedGroupUVPins T groupType
  nonGaussian : SelectedCorrelationNonGaussianPin T

namespace SelectedTheoryPins

/-- The classified Cartan type supplies the repository's exact admissible
representation data.  This is a classification/Casimir result, not a continuum
existence theorem for that group. -/
def groupAdmissible
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumSelectedExactMassDecayTarget mu}
    (P : SelectedTheoryPins T) :
    AdmissibleSimpleGroup (repDataOf P.groupType) :=
  admissible_of_cartanType P.groupType P.simpleRank

/-- The exact one-loop coefficient selected by the pinned group is positive. -/
theorem uvBetaPositive
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumSelectedExactMassDecayTarget mu}
    (P : SelectedTheoryPins T) :
    (0 : Q') < betaZero (repDataOf P.groupType).C2_adj :=
  betaZero_pos P.groupAdmissible.hvee_lb

/-- The inverse coupling evaluated on consecutive measures of the exact
selected projective thread is strictly increasing. -/
theorem selectedInverseCouplingStrictMono
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumSelectedExactMassDecayTarget mu}
    (P : SelectedTheoryPins T) (j : Nat) :
    P.uv.stageInverseCoupling j (mu.pick j) <
      P.uv.stageInverseCoupling (j + 1) (mu.pick (j + 1)) := by
  rw [P.uv.selectedTrajectoryPinned j,
    P.uv.selectedTrajectoryPinned (j + 1)]
  exact invRunningCoupling_strictMono P.uvBetaPositive j

/-- Repackage one carried nontrivial rotation as the legacy carrier, now using
the exact same OS algebra and functional.  This does not identify the label
group with full `O(4)`. -/
def sameOSRotationCarrierContent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumSelectedExactMassDecayTarget mu}
    (P : SelectedTheoryPins T) : O4RestorationContent mu :=
  Exists.intro T.existence.os_axioms.A
    (Exists.intro T.existence.os_axioms.E
      (Exists.intro (P.rotations.action P.rotations.movedLabel)
        (P.rotations.functional_equivariant P.rotations.movedLabel)))

/-- Repackage the same-algebra nonidentity projection as the legacy gauge
carrier.  The stronger moved-observable and selected-gap fixedness data remain
available in `P.gauge`. -/
def sameOSGaugeCarrierContent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumSelectedExactMassDecayTarget mu}
    (P : SelectedTheoryPins T) : GaugeGeneratedContent mu :=
  Exists.intro T.existence.os_axioms.A
    (Exists.intro T.existence.os_axioms.E
      (Exists.intro P.gauge.projection
        (And.intro P.gauge.idempotent P.gauge.functional_factors)))

/-- Repackage the group-Casimir trajectory as the legacy UV carrier.  Its
witnesses are constructed from Type-level data before entering the legacy
propositional wrapper. -/
def sameThreadUVCarrierContent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumSelectedExactMassDecayTarget mu}
    (P : SelectedTheoryPins T) : UVAsymptoticFreedomContent mu :=
  Exists.intro P.uv.initialInverseCoupling
    (Exists.intro (repDataOf P.groupType).C2_adj
      (And.intro P.groupAdmissible.hvee_lb
        (And.intro P.uvBetaPositive
          (fun j => invRunningCoupling_strictMono P.uvBetaPositive j))))

/-- The selected gap insertion is fixed by the same nonidentity gauge
projection at every integer separation. -/
theorem selectedGapInsertionGaugeFixed
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumSelectedExactMassDecayTarget mu}
    (P : SelectedTheoryPins T) (t : Nat) :
    P.gauge.projection.map
        (T.corrected.exact.projective.continuumInsertion
          T.corrected.exact.projective.gapObservable t) =
      T.corrected.exact.projective.continuumInsertion
        T.corrected.exact.projective.gapObservable t :=
  P.gauge.gapInsertion_fixed t

/-- The non-Gaussianity witness is about the exact same continuum correlator
that carries `T`'s positive exact mass and decay bound. -/
theorem selectedContinuumCorrelationWickViolation
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumSelectedExactMassDecayTarget mu}
    (P : SelectedTheoryPins T) :
    Not (CReal.Equiv
      (T.corrected.exact.projective.continuumCorr
        T.corrected.exact.projective.gapObservable P.nonGaussian.separation)
      (CReal.mul
        (T.corrected.exact.projective.continuumCorr
          T.corrected.exact.projective.gapObservable 0)
        (T.corrected.exact.projective.continuumCorr
          T.corrected.exact.projective.gapObservable 0))) :=
  P.nonGaussian.wickViolation

end SelectedTheoryPins

end YMGap.Continuum.ContinuumSelectedTheoryPins

#print axioms YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins.groupAdmissible
#print axioms YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins.uvBetaPositive
#print axioms YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins.selectedInverseCouplingStrictMono
#print axioms YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins.sameOSRotationCarrierContent
#print axioms YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins.sameOSGaugeCarrierContent
#print axioms YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins.sameThreadUVCarrierContent
#print axioms YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins.selectedGapInsertionGaugeFixed
#print axioms YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins.selectedContinuumCorrelationWickViolation
