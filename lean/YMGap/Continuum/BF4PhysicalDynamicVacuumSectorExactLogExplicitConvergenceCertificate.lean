/-
# Explicit certificate for the exact physical logarithmic rate

The exact-log variation compiler constructs an eventual-outer `CReal.ModCauchyEv`
for the full-range rate of the same completed physical family.  This module
exports that witness through the Type-level explicit convergence interface,
retaining the compiler's sequence, diagonal limit, and all supplied inputs.

This is only a representation upgrade.  It does not construct a physical-gap
variation witness, an inverse-square spacing tail, a cofinal capacity check, a
continuum measure, an OS/GNS reconstruction, or the Clay mass gap.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Constructive.CRealModCauchyExplicitConvergenceCertificate
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogExplicitConvergenceCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.SummableRationalStepVariation

namespace DynamicVacuumSectorObservablePin

/-! ## The same-object exact-log certificate -/

/-- The exact full-log rate of the pinned observable has an explicit
term-stage and approximation-stage modulus whenever the existing same-family
variation and spacing inputs are supplied.  The limit is definitionally the
same `completeLimitCauchy` value selected by `exactLogRateLimit`. -/
def exactLogRateExplicitCertificate
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ExplicitConvergenceCertificate
      (fullRangeRateFamily pin).rate
      (exactLogRateLimit pin band gapVariation spacingTail) :=
  CReal.ModCauchyEv.toExplicitConvergenceCertificate
    (exactLogRateCauchy pin band gapVariation spacingTail)

end DynamicVacuumSectorObservablePin

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogExplicitConvergenceCertificate

/-! ## Dependency gate -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogExplicitConvergenceCertificate.DynamicVacuumSectorObservablePin.exactLogRateExplicitCertificate
