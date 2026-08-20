/-
M4f -- identify the cutoff exact-rate limit with the reconstruction by
constructive uniqueness of limits.

The endpoint previously requested an `ExactLogGapAt` equality directly.  The
more informative analytic statement is that the same finite-cutoff exact-rate
sequence converges to the reconstruction's computed value
`-log(rec.gapBound)`.  Once the rate sequence has its constructive Cauchy
modulus, uniqueness of limits derives the equality.

This module performs only that formal reduction.  It does not prove the
convergence field of `ExactRateReconstructionHandoff`.
-/

import YMGap.Constructive.CRealCompleteCauchy
import YMGap.Continuum.OSExactLogGap
import YMGap.Continuum.PhysicalSeparatorFullLogComparison

namespace YMGap.Continuum.ExactRateReconstructionHandoff

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

/-- The finite exact physical-rate sequence converges to the logarithmic gap
computed from one fixed OS reconstruction.

This is the remaining same-object generator identification in convergence
form.  It is stronger in provenance than a free equality between two completed
values because it names the actual cutoff sequence on the left. -/
structure ExactRateReconstructionHandoff
    (C : FullRangeExactPhysicalSeparatorCertificate)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) : Type 1 where
  /-- Strict positivity of the rational transfer separator, needed for its
  finite logarithm. -/
  positiveGapBound : PositiveTransferGapBound rec
  /-- The exact cutoff rates converge to the reconstruction's computed
  logarithmic gap. -/
  exactRateConverges : CReal.ConvergesTo C.rateFamily.rate
    (exactLogGap rec positiveGapBound)

namespace ExactRateReconstructionHandoff

/-- Construct the exact logarithmic gap equality from the supplied cutoff
Cauchy modulus and uniqueness of the limit of the same sequence. -/
def exactLogGapAt
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {rec : OSReconstruction mu}
    (H : ExactRateReconstructionHandoff C rec)
    (rateCauchy : CReal.ModCauchyEv C.rateFamily.rate) :
    ExactLogGapAt rec
      (CReal.completeLimitCauchy C.rateFamily.rate rateCauchy) where
  positiveGapBound := H.positiveGapBound
  rate_equiv := CReal.Equiv_of_limit_of_equal
    (fun k => CReal.Equiv.refl (C.rateFamily.rate k))
    (CReal.convergesTo_completeLimitCauchy C.rateFamily.rate rateCauchy)
    H.exactRateConverges

end ExactRateReconstructionHandoff

end YMGap.Continuum.ExactRateReconstructionHandoff

#print axioms YMGap.Continuum.ExactRateReconstructionHandoff.ExactRateReconstructionHandoff.exactLogGapAt
