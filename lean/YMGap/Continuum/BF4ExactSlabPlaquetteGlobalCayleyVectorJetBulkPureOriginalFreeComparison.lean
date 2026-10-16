/-
# Pure ORIGINAL vector-jet to finite FREE comparison capstone

The exact centered north-weight deficit is joined to the existing four-error
cleared-response comparison.  The identity-scaled pure ORIGINAL vector-jet
response is thereby written as the finite FREE covariance plus five explicit
errors, with the new `1 - P^14` contribution kept separate.

No error is proved small here.  In particular, no southern-tail estimate,
multi-chart partition, strict-margin payment, cutoff-uniform comparison,
continuum theory, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkPureOriginalFreeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Complete named remainder for the identity-scaled pure ORIGINAL response.
The first summand is the preceding comparison's ORIGINAL-to-FREE, inner,
outer and Cayley total; the second is the exact centered north-weight loss. -/
def globalCayleyVectorJetBulkCenteredIdentityScaledPureFreeTotalRemainder
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) : CReal :=
  CReal.add
    (globalCayleyVectorJetBulkCenteredFreeComparisonTotalRemainder
      w hw0 hw1 half s hs stage leftTime rightTime)
    (globalCayleyVectorJetBulkCenteredNorthWeightDeficit
      w hw0 hw1 half s hs leftTime rightTime)

private theorem cadd_assoc (left middle right : CReal) :
    CReal.Equiv
      (CReal.add (CReal.add left middle) right)
      (CReal.add left (CReal.add middle right)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_assoc_eqv
      (left.approx n) (middle.approx n) (right.approx n))

/-- Exact five-error capstone.  The identity-scaled pure ORIGINAL response
equals the finite FREE covariance plus the previously named four errors and
the separate centered `1 - P^14` north-weight deficit. -/
theorem globalCayleyVectorJetBulkCenteredIdentityScaledPure_freeComparison_total_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
          half s hs stage leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredIdentityScaledPureFreeTotalRemainder
          w hw0 hw1 half s hs stage leftTime rightTime)) := by
  let pure := globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
    w hw0 hw1 half s hs leftTime rightTime
  let cleared := globalCayleyVectorJetBulkCenteredClearedResponse
    w hw0 hw1 half s hs leftTime rightTime
  let free := globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
    half s hs stage leftTime rightTime
  let previous := globalCayleyVectorJetBulkCenteredFreeComparisonTotalRemainder
    w hw0 hw1 half s hs stage leftTime rightTime
  let north := globalCayleyVectorJetBulkCenteredNorthWeightDeficit
    w hw0 hw1 half s hs leftTime rightTime
  have hpure :=
    globalCayleyVectorJetBulkCenteredIdentityScaledPure_cleared_deficit
      w hw0 hw1 half s hs leftTime rightTime
  change CReal.Equiv pure (CReal.add cleared north) at hpure
  have hcleared := globalCayleyVectorJetBulkCentered_freeComparison_total_split
    w hw0 hw1 half s hs stage leftTime rightTime
    hwidth hleftTime hrightTime
  change CReal.Equiv cleared (CReal.add free previous) at hcleared
  change CReal.Equiv pure (CReal.add free (CReal.add previous north))
  exact hpure.trans
    ((Pivot2.add_congr hcleared (CReal.Equiv.refl north)).trans
      (cadd_assoc free previous north))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkPureOriginalFreeComparison

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkPureOriginalFreeComparison.globalCayleyVectorJetBulkCenteredIdentityScaledPureFreeTotalRemainder
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkPureOriginalFreeComparison.globalCayleyVectorJetBulkCenteredIdentityScaledPure_freeComparison_total_split
