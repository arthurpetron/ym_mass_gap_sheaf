/-
M4x -- the corrected exact-physical-mass target.

The legacy Clay scorecard uses the transfer margin `1 - q` and a weak O(4)
compatibility slot.  The selected continuum endpoint developed in M4 instead
has the physically normalized mass `-log(q)`, a nontrivial continuum
clustering channel, and a full `IsO4Restoration` field through its explicit
`ContinuumYMExistence` datum.

One important continuum obligation is still logically independent: the exact
mass must be a spacing-uniform decay rate for a genuine physical correlator
family.  `UniformPhysicalCorrelationDecay` is the repository's strongest
existing formulation of that obligation.  This module adds the missing
same-mass pin, using constructive-real equivalence because equality of raw
approximation sequences is not representation invariant.

No inhabitant is supplied.  In particular, neither a
`ContinuumExactMassClusteringTarget` nor a
`UniformPhysicalCorrelationDecay` is constructed here.  The result is a
corrected target interface and a precise residual boundary, not a solution of
four-dimensional Yang--Mills.
-/

import YMGap.Continuum.ContinuumExactMassClusteringTarget
import YMGap.Continuum.UniformCorrelationDecay

namespace YMGap.Continuum.ContinuumCorrectedExactMassTarget

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ContinuumExactMassClusteringTarget
open YMGap.Continuum.ContinuumExactMassClusteringTarget.ContinuumExactMassClusteringTarget
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ContinuumSquaredClusteringHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.UniformCorrelationDecay
open YMGap.Rubric.ClayScorecard

/-- The spacing-uniform physical decay obligation, with its mass identified
representation-invariantly with the target's canonical exact logarithmic
mass.  This structure is deliberately uninhabited. -/
structure ExactMassUniformDecayExtension
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu) : Type 2 where
  uniformDecay : UniformPhysicalCorrelationDecay
  massPinned : CReal.Equiv uniformDecay.m T.canonicalPositiveMass.1
  /-- The physical correlator returned at a target spacing carries that same
  spacing internally.  `fam a` alone does not enforce this because
  `PhysicalCorrelator.a` is an independent field. -/
  familySpacingPinned : forall j : Nat,
    Q'.eqv
      (uniformDecay.fam
        (T.physicalSpacing.spacing j)
        (T.physicalSpacing.spacing_pos j)).a
      (T.physicalSpacing.spacing j)
  /-- At every target spacing and sampled physical separation, the uniform
  family is the same finite-stage gap correlator selected by the projective
  measure thread.  This is the same-object seam; a mass equality alone would
  not identify the two correlation theories. -/
  sampledCorrelationPinned : forall (j t : Nat),
    (uniformDecay.fam
      (T.physicalSpacing.spacing j)
      (T.physicalSpacing.spacing_pos j)).corr
        (T.sampling.latticeSteps j t) =
      T.projective.stageCorrelators.corrFromStage j (mu.pick j)
        T.projective.gapObservable (T.sampling.latticeSteps j t)

/-- The exact-mass selected continuum endpoint together with the correctly
mass-pinned spacing-uniform physical correlation decay.  Full O(4) is the
strong field of `exact.existence`, not the legacy rubric surrogate. -/
structure ContinuumCorrectedExactMassTarget
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 3 where
  exact : ContinuumExactMassClusteringTarget mu
  uniform : ExactMassUniformDecayExtension exact

namespace ContinuumCorrectedExactMassTarget

/-- The canonical positive representative of the exact physical mass. -/
def canonicalPositiveMass
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) :
    Σ' mass : CReal, CReal.IsPositive mass :=
  T.exact.canonicalPositiveMass

/-- The positive exact physical mass in the completed-real quotient. -/
def positiveMassRC
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : PositiveRC :=
  T.exact.positiveMassRC

/-- Nontrivial squared clustering on the selected continuum channel. -/
def nontrivialClustering
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) :
    NontrivialRCSquaredGeometricClustering
      T.exact.endpoint.correlationPin.continuumGapCorrRC :=
  T.exact.nontrivialClustering

/-- Full continuum O(4) restoration comes from the same explicit continuum
existence datum as the selected reconstruction and clustering channel. -/
def fullO4Restoration
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) :
    IsO4Restoration mu :=
  T.exact.existence.os1_o4_restoration

/-- The uniform correlation-decay mass is the exact logarithmic endpoint mass
in the representation-invariant completed-real currency. -/
theorem uniformMassRC_eq_positiveMassRC
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) :
    Quotient.mk crealSetoid T.uniform.uniformDecay.m =
      T.positiveMassRC.value := by
  calc
    Quotient.mk crealSetoid T.uniform.uniformDecay.m =
        Quotient.mk crealSetoid T.canonicalPositiveMass.1 :=
      Quotient.sound T.uniform.massPinned
    _ = T.positiveMassRC.value :=
      T.exact.massRC_eq_canonicalPositiveMassRC.symm

/-- The uniformly decaying physical family converges, along the target's own
spacing and separation sampling, to the same projective continuum gap
correlator.  This is derived from the finite-stage same-object pin and the
projective cutoff-removal theorem already carried by `exact`. -/
theorem uniformSampledGapCorrelationConverges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t : Nat) :
    CReal.ConvergesTo
      (fun j => CReal.ofQ'
        ((T.uniform.uniformDecay.fam
          (T.exact.physicalSpacing.spacing j)
          (T.exact.physicalSpacing.spacing_pos j)).corr
            (T.exact.sampling.latticeSteps j t)))
      (T.exact.projective.continuumCorr
        T.exact.projective.gapObservable t) := by
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun j => CReal.ofQ'
      (T.exact.projective.stageCorrelators.corrFromStage j (mu.pick j)
        T.exact.projective.gapObservable
        (T.exact.sampling.latticeSteps j t)))
  · intro j
    rw [T.uniform.sampledCorrelationPinned j t]
    exact CReal.Equiv.refl _
  · exact
      T.exact.projective.continuumCorrelators.rescaledStageConverges
        T.exact.projective.gapObservable t

/-- The corrected target therefore yields the repository's constructive
uniform-decay mass-gap package, with the quotient identity above recording
that its mass is the selected exact physical rate. -/
def uniformMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : MassGap :=
  uniformPhysicalCorrelationDecay_imp_massGap T.uniform.uniformDecay

/-- The corrected uniform physical decay implies the old scorecard's
uniform-in-coupling clause, only as a downstream legacy projection. -/
def legacyUniformInCoupling
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) :
    RubricUniformInCoupling :=
  correlationDecay_imp_rubricUniformInCoupling T.uniform.uniformDecay

end ContinuumCorrectedExactMassTarget

end YMGap.Continuum.ContinuumCorrectedExactMassTarget

#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget.canonicalPositiveMass
#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget.positiveMassRC
#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget.nontrivialClustering
#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget.fullO4Restoration
#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget.uniformMassRC_eq_positiveMassRC
#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ExactMassUniformDecayExtension.familySpacingPinned
#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget.uniformSampledGapCorrelationConverges
#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget.uniformMassGap
#print axioms YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget.legacyUniformInCoupling
