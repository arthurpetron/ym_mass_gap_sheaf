/-
# Projective/OS handoff for the raw moving-cube continuum channel

The dynamic raw moving-cube compiler constructs an `RC`-valued continuum
correlation from explicit completed-real representatives.  The older
`ProjectiveOSCorrelationHandoff` is keyed to rational `PhysicalSeparator`
stage correlations, so routing the dynamic channel through it would lose the
literal representative lineage.

This module supplies the narrow completed-real adapter.  It records that each
raw representative is the expectation of one cutoff-independent OS insertion
on the selected projective measure thread.  Constructive uniqueness of limits
then identifies the raw continuum limit with the selected OS functional.  A
second fixed equality identifies that insertion with one connected OS
two-point channel.  The quotient-real equality and zero-time nontriviality
transport follow without choosing new representatives.

No projective measure, continuum Yang--Mills existence datum, raw variation,
stage-expectation equality, OS connected insertion, or GNS reconstruction is
inhabited here.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
import YMGap.Continuum.MeasureLinkedOSReconstruction
import YMGap.Continuum.PhysicalSeparatorContinuumRealization
import YMGap.Continuum.ProjectiveOSCorrelationHandoff

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.RCStrictPositivity

/-! ## 1. The one projective-thread same-object bridge -/

/-- The literal raw moving-cube representatives are expectations of fixed OS
insertions on the same projective thread used by the measure-linked
reconstruction data.

The two equality fields are deliberately separate.  The first is the
cutoff-to-projective-measure identification; the second is the connected OS
semantics.  Neither can silently select a different observable family. -/
structure RawMovingCubeProjectiveOSCorrelationHandoff
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (D : MeasureLinkedOSGNSData H) : Type 2 where
  /-- A fixed OS-algebra insertion for every integer physical time. -/
  continuumInsertion : Nat -> H.os_axioms.A.carrier
  /-- Each literal raw representative is the expectation of that fixed
  insertion on the selected stage measure. -/
  rawRepresentative_eq_stageExpectation : forall (time scale : Nat),
    CReal.Equiv
      (raw.representative time scale)
      (D.stageFunctional.expectationFromStage scale (mu.pick scale)
        (continuumInsertion time))
  /-- One connected two-point semantics in the same OS algebra. -/
  osConnected : OSConnectedTwoPointSemantics H
  /-- The fixed continuum insertion and connected gap insertion have the same
  value under the selected OS functional. -/
  continuumInsertion_eq_connectedFunctional : forall time : Nat,
    CReal.Equiv
      (CReal.ofQ' (H.os_axioms.E.E (continuumInsertion time)))
      (CReal.ofQ' (H.os_axioms.E.E
        (osConnected.connectedInsertion osConnected.gapInsertion time)))

/-! ## 2. Reuse the existing projective OS path through one exact adapter -/

/-- The one remaining same-object equality needed to connect a dynamic raw
moving-cube representative to an existing rational
`ProjectiveOSCorrelationHandoff`.  It fixes that handoff's own gap observable
and physical sampling schedule, so neither can drift during the adapter. -/
structure RawMovingCubeSampledGapCorrelationIdentification
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (projective : ProjectiveOSCorrelationHandoff P H D sampling) : Type 2 where
  rawRepresentative_eq_sampledGap : forall (time scale : Nat),
    CReal.Equiv
      (raw.representative time scale)
      (CReal.ofQ'
        (projective.stageCorrelators.corrFromStage scale (mu.pick scale)
          projective.gapObservable (sampling.latticeSteps scale time)))

namespace RawMovingCubeProjectiveOSCorrelationHandoff

/-- Compile the dynamic completed-real projective handoff from the existing
rational projective OS route plus the single literal-representative adapter.
All projective-measure and connected-OS semantics are reused unchanged. -/
def ofProjectiveOSCorrelationHandoff
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (projective : ProjectiveOSCorrelationHandoff P H D sampling)
    (sameObject : RawMovingCubeSampledGapCorrelationIdentification
      family raw projective) :
    RawMovingCubeProjectiveOSCorrelationHandoff family raw H D where
  continuumInsertion := fun time =>
    projective.continuumInsertion projective.gapObservable time
  rawRepresentative_eq_stageExpectation := by
    intro time scale
    exact CReal.Equiv.trans
      (sameObject.rawRepresentative_eq_sampledGap time scale)
      (projective.sampledCorr_eq_stageExpectation
        scale projective.gapObservable time)
  osConnected := projective.osConnectedTwoPoint
  continuumInsertion_eq_connectedFunctional := fun time =>
    CReal.Equiv.symm (projective.gapFunctional_eq time)

/-! ## 3. Contract the projective diagram by limit uniqueness -/

/-- The complete limit already selected by the raw variation is the OS
functional value of the fixed insertion on the selected projective thread. -/
theorem rawLimitRepresentative_eq_osFunctional
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    (B : RawMovingCubeProjectiveOSCorrelationHandoff family raw H D)
    (time : Nat) :
    CReal.Equiv
      ((rawMovingCubeContinuumLimitOfVariation family raw).limitRepresentative
        time)
      (CReal.ofQ' (H.os_axioms.E.E (B.continuumInsertion time))) := by
  apply CReal.Equiv_of_limit_of_equal
    (fun scale => B.rawRepresentative_eq_stageExpectation time scale)
    ((rawMovingCubeContinuumLimitOfVariation family raw).converges time)
  exact D.projectiveFunctional.stageExpectationConverges
    (B.continuumInsertion time)

/-- The same raw limit is the selected connected OS two-point function. -/
theorem rawLimitRepresentative_eq_osConnected
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    (B : RawMovingCubeProjectiveOSCorrelationHandoff family raw H D)
    (time : Nat) :
    CReal.Equiv
      ((rawMovingCubeContinuumLimitOfVariation family raw).limitRepresentative
        time)
      (CReal.ofQ' (H.os_axioms.E.E
        (B.osConnected.connectedInsertion B.osConnected.gapInsertion time))) :=
  CReal.Equiv.trans
    (B.rawLimitRepresentative_eq_osFunctional time)
    (B.continuumInsertion_eq_connectedFunctional time)

/-- Quotient descent preserves the exact same-object identification between
the raw continuum correlation and the connected OS channel. -/
theorem rawContinuumConnectedAutocorrelation_eq_osConnected
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    (B : RawMovingCubeProjectiveOSCorrelationHandoff family raw H D)
    (time : Nat) :
    (rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
        time =
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (H.os_axioms.E.E
          (B.osConnected.connectedInsertion B.osConnected.gapInsertion time))) :
        CReal.RC) := by
  apply Quotient.sound
  exact B.rawLimitRepresentative_eq_osConnected time

/-! ## 4. Nontriviality survives the same-object handoff -/

/-- Positivity of the raw zero-time limit transfers to the definitionally
connected OS channel; no independent OS nonzero observable is selected. -/
theorem osConnected_zero_isPositive
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    (B : RawMovingCubeProjectiveOSCorrelationHandoff family raw H D)
    (nontrivial : MovingCubeRawContinuumNontriviality family raw) :
    RCIsPositive
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (H.os_axioms.E.E
          (B.osConnected.connectedInsertion B.osConnected.gapInsertion 0)))) := by
  rw [← B.rawContinuumConnectedAutocorrelation_eq_osConnected 0]
  exact nontrivial.zero_isPositive

end RawMovingCubeProjectiveOSCorrelationHandoff

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff.RawMovingCubeProjectiveOSCorrelationHandoff.ofProjectiveOSCorrelationHandoff
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff.RawMovingCubeProjectiveOSCorrelationHandoff.rawLimitRepresentative_eq_osFunctional
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff.RawMovingCubeProjectiveOSCorrelationHandoff.rawLimitRepresentative_eq_osConnected
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff.RawMovingCubeProjectiveOSCorrelationHandoff.rawContinuumConnectedAutocorrelation_eq_osConnected
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff.RawMovingCubeProjectiveOSCorrelationHandoff.osConnected_zero_isPositive
