/-
# Dynamic BF4 physical rate to the selected Wilson exact logarithmic gap

The all-vector graph-norm compiler reaches the selected Wilson transfer with
the correct scheduled power for one unit of physical time.  Its remaining
scalar companion is the exact identification of the dynamic physical-gap
limit with the logarithmic Hamiltonian gap of that same transfer separator.

This module records that companion in convergence form.  The actual rational
cutoff stream `family.physicalGap` must converge to the exact logarithmic gap
computed from the selected Wilson reconstruction.  Its independently supplied
summable variation already makes the same stream converge to a constructive
limit.  Constructive uniqueness of limits therefore produces the exact rate
equality; the physical rate band supplies positivity rather than postulating
it again.

Finally, the exact-rate handoff and the graph-norm limit compiler contract to
the existing `WilsonMinimalBoundedMassGap`.  Both inputs are indexed by the
same dynamic family and selected Wilson datum.  The observable channel remains
a downstream consequence and is not used to infer the all-vector gap.

No dynamic family, variation bound, reconstruction convergence, graph-norm
approximation, projective measure, continuum Yang--Mills theory, or Clay
conclusion is inhabited here.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler
import YMGap.Continuum.EffMassConvergence

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler
open YMGap.Continuum.EffMassConvergence
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. Same-stream exact-rate reconstruction handoff -/

/-- The actual dynamic physical-gap stream converges to the exact logarithmic
gap of the reconstruction selected by the same Wilson datum.

The handoff is stated as convergence rather than as a free equality of two
completed values.  This retains the cutoff stream that generated the physical
rate and lets constructive uniqueness perform the contraction. -/
structure DynamicVacuumSectorWilsonExactRateHandoff
    (family : DynamicVacuumSectorCompletedFamily 0)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  /-- Strict positivity of the selected rational Wilson separator, required
  for its finite exact logarithm. -/
  positiveGapBound : PositiveTransferGapBound D.reconstruction
  /-- The definitionally same rational physical-gap stream converges to the
  exact logarithmic gap of the selected Wilson reconstruction. -/
  physicalGapConverges : CReal.ConvergesTo
    (fun scale => CReal.ofQ' (family.physicalGap scale))
    (exactLogGap D.reconstruction positiveGapBound)

namespace DynamicVacuumSectorWilsonExactRateHandoff

/-! ## 1a. Reverse construction from an exact logarithmic witness -/

/-- Repackage a positive exact-logarithmic gap witness as the same-stream
physical-rate handoff, provided the variation-selected limit is explicitly
identified with the witness rate.

The equality is deliberately an input `CReal.Equiv`: the constructor does not
infer that a physical variation limit is the Wilson rate.  It only transports
the existing constructive convergence along that supplied identification and
keeps the positive transfer-gap bound from the exact-log witness. -/
def ofPositiveExactLogGapWitness
    {family : DynamicVacuumSectorCompletedFamily 0}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (witness : PositiveExactLogGapWitness D.reconstruction)
    (rate_equiv : CReal.Equiv gapVariation.limit witness.rate) :
    DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D where
  positiveGapBound := witness.exactGap.positiveGapBound
  physicalGapConverges := by
    have hlim : CReal.Equiv gapVariation.limit
        (exactLogGap D.reconstruction witness.exactGap.positiveGapBound) :=
      CReal.Equiv.trans rate_equiv witness.exactGap.rate_equiv
    exact convergesTo_retarget gapVariation.converges hlim

/-- Constructive uniqueness identifies the variation-selected physical rate
with the exact logarithm of the selected Wilson separator. -/
theorem physicalGapLimit_equiv_exactLog
    {family : DynamicVacuumSectorCompletedFamily 0}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D) :
    CReal.Equiv gapVariation.limit
      (exactLogGap D.reconstruction data.positiveGapBound) :=
  CReal.Equiv_of_limit_of_equal
    (fun scale => CReal.Equiv.refl
      (CReal.ofQ' (family.physicalGap scale)))
    gapVariation.converges data.physicalGapConverges

/-- Exact-log reconstruction data at the physical rate selected by the
summable dynamic variation. -/
def toExactLogGapAt
    {family : DynamicVacuumSectorCompletedFamily 0}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D) :
    ExactLogGapAt D.reconstruction gapVariation.limit where
  positiveGapBound := data.positiveGapBound
  rate_equiv := data.physicalGapLimit_equiv_exactLog

/-- The rate band supplies a positive rational floor for the same limit, so
the exact-log equality upgrades to the endpoint's positive-rate witness. -/
def toPositiveExactLogGapWitness
    {family : DynamicVacuumSectorCompletedFamily 0}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D) :
    PositiveExactLogGapWitness D.reconstruction where
  rate := gapVariation.limit
  rate_posEv := physicalGapVariationLimit_posEv family band gapVariation
  exactGap := data.toExactLogGapAt

/-! ## 2. Contract with the all-vector graph-norm compiler -/

/-- Assemble the minimal bounded Wilson mass-gap endpoint from two independent
compiler branches on the same dynamic family and selected Wilson datum:

* convergence of the physical-gap stream to the reconstruction logarithm; and
* graph-norm convergence of every scheduled finite vacuum vector.

The first supplies the positive exact rate.  The second supplies the direct
operator-norm gap. -/
def compileWilsonMinimalBoundedMassGap
    {family : DynamicVacuumSectorCompletedFamily 0}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D)
    (graphNorm : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family ratePower D) :
    WilsonMinimalBoundedMassGap D where
  exactRate := exactRate.toPositiveExactLogGapWitness band
  operatorGap := graphNorm.toWilsonOperatorNormGapPin

/-- The assembled endpoint retains definitionally the physical rate selected
by the dynamic gap variation. -/
@[simp] theorem compileWilsonMinimalBoundedMassGap_rate
    {family : DynamicVacuumSectorCompletedFamily 0}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D)
    (graphNorm : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family ratePower D) :
    (compileWilsonMinimalBoundedMassGap band exactRate graphNorm).rate =
      gapVariation.limit := rfl

end DynamicVacuumSectorWilsonExactRateHandoff

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff.DynamicVacuumSectorWilsonExactRateHandoff.physicalGapLimit_equiv_exactLog
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff.DynamicVacuumSectorWilsonExactRateHandoff.ofPositiveExactLogGapWitness
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff.DynamicVacuumSectorWilsonExactRateHandoff.toExactLogGapAt
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff.DynamicVacuumSectorWilsonExactRateHandoff.toPositiveExactLogGapWitness
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff.DynamicVacuumSectorWilsonExactRateHandoff.compileWilsonMinimalBoundedMassGap
