/-
# Conditional tree-gauge bridge to the exact five-cycle Haar marginal

This module composes the literal 139-shear BF4 tree-gauge ledger with the
exact integration of the 25 tree blocks and 18 unused cycle blocks.  For any
supported polynomial whose finite translation scan succeeds, the original
48-fold raw adapted Haar value is therefore an exact fivefold Haar value.

The five surviving blocks occur in the geometric based-cycle order
`[0,4,5,6,10]`.  The finite scan hypothesis remains explicit here; removing
it for the cutoff-one slab polynomials is a separate certificate theorem.

## Axiom gate

Finite polynomial recursion and the two previously checked bridge halves
only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationSemantics
import YMGap.Continuum.BF4ExactSpatialTreeCycleFiveHaarMarginal

namespace YMGap.Continuum.BF4ExactSpatialTreeGaugeFiveHaarBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSpatialTreeCycleFiveHaarMarginal
open YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-- Apply the literal tree-gauge shear ledger, move based cycles
`[0,4,5,6,10]` to the tail, and integrate the other 43 adapted blocks. -/
def exactTreeGaugeBasedCycleFiveHaarMarginal
    (polynomial : RatPoly) : RatPoly :=
  exactBasedCycleFiveHaarMarginal
    (applyBF4TreeGaugeTranslationLedger polynomial)

theorem exactTreeGaugeBasedCycleFiveHaarMarginal_supported_five
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks 5
      (exactTreeGaugeBasedCycleFiveHaarMarginal polynomial) := by
  exact exactBasedCycleFiveHaarMarginal_supported_five _

/-- **Exact conditional BF4 tree-gauge-to-fivefold bridge.**  The left side
uses all 48 adapted raw coordinates.  The right side first replaces every
chord by its rooted tree-gauge word and then retains exactly five cycle
coordinates. -/
theorem quaternionHaar_48_eq_treeGaugeBasedCycleFiveHaarMarginal
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 48 polynomial)
    (hcheck : bf4TreeGaugeTranslationLedgerCheck polynomial = true) :
    quaternionHaar 48 polynomial ≈
      quaternionHaar 5
        (exactTreeGaugeBasedCycleFiveHaarMarginal polynomial) := by
  have htranslatedSupport :
      SupportedQuaternionBlocks 48
        (applyBF4TreeGaugeTranslationLedger polynomial) :=
    applyBF4TreeGaugeTranslationLedger_supported polynomial hsupport
  exact Q'.eqv_trans _
    (quaternionHaar 48
      (applyBF4TreeGaugeTranslationLedger polynomial)) _
    (Q'.eqv_symm
      (applyBF4TreeGaugeTranslationLedger_haar_sound
        polynomial hsupport hcheck))
    (by
      simpa [exactTreeGaugeBasedCycleFiveHaarMarginal] using
        quaternionHaar_48_eq_basedCycleFiveHaarMarginal
          (applyBF4TreeGaugeTranslationLedger polynomial)
          htranslatedSupport)

/-- The output coordinates in the bridge theorem are ordered by the five
rooted based cycles `[0,4,5,6,10]`. -/
theorem exactTreeGaugeBasedCycleFiveHaarMarginal_cycle_order :
    bf4AdaptedTransmittedBlocks.map
        (fun block => block - bf4AdaptedTreeBlockCount) =
      [0, 4, 5, 6, 10] :=
  exactBasedCycleFiveHaarMarginal_cycle_order

end YMGap.Continuum.BF4ExactSpatialTreeGaugeFiveHaarBridge

#print axioms YMGap.Continuum.BF4ExactSpatialTreeGaugeFiveHaarBridge.quaternionHaar_48_eq_treeGaugeBasedCycleFiveHaarMarginal
