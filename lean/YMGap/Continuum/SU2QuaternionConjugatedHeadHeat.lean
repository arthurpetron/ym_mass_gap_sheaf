/-
# Conjugated finite head heat estimate

The literal head conditional update already has a checked angular defect
bound.  An explicit involution of the quaternion blocks transports that
bound to the corresponding recoded carrier.  The transported map is defined
by conjugation; identifying it with an independently defined interacting
selected-link kernel remains a separate obligation.

This is a finite polynomial/Haar statement only.  It does not assert an OS
transfer gap, a thermodynamic limit, or a continuum Yang--Mills theory.
-/

import YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.SU2QuaternionConjugatedHeadHeat

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

local infix:50 " ≈ " => Q'.eqv

/-! ## The conjugated update -/

/-- Conjugate the literal head conditional update by a block involution.
The involution is its own inverse, so this is the finite-coordinate analogue
of transporting the head update to another quaternion block. -/
def conjugatedHeadMap
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (w : Q') (K : Nat) (polynomial : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial s
    (headMap w K (reindexQuaternionPolynomial s polynomial))

theorem conjugatedHeadMap_supported
    {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (tail : Nat) (hblocks : blocks = tail + 1)
    (w : Q') (K : Nat) {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks
      (conjugatedHeadMap s w K polynomial) := by
  subst blocks
  exact reindex_supported s
    (headMap w K (reindexQuaternionPolynomial s polynomial))

/-! ## Transport of the defect bound -/

/-- The checked local head-map angular defect survives conjugation by an
explicit block involution.  The right-hand energy is deliberately written for
the recoded polynomial: no unproved derivative/reindex commutation is hidden
inside this theorem. -/
theorem conjugatedHeadMap_defect_le_angular
    (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K)
    (s : QuaternionBlockInvolution (tail + 1)) (polynomial : RatPoly)
    (hpolynomial : SupportedQuaternionBlocks (tail + 1) polynomial) :
    quaternionHaar (tail + 1) (polyMul polynomial polynomial) -
        quaternionHaar (tail + 1)
          (polyMul polynomial (conjugatedHeadMap s w K polynomial)) ≤
      ((1 : Q') - w) *
        quaternionHaar (tail + 1)
          (angularSquare (reindexQuaternionPolynomial s polynomial)) := by
  let recoded := reindexQuaternionPolynomial s polynomial
  have hrecoded : SupportedQuaternionBlocks (tail + 1) recoded :=
    reindex_supported s polynomial
  have hnorm :
      quaternionHaar (tail + 1) (polyMul polynomial polynomial) ≈
        quaternionHaar (tail + 1) (polyMul recoded recoded) := by
    have hchange := quaternionHaar_reindex s
      (polyMul polynomial polynomial)
      (supported_polyMul hpolynomial hpolynomial)
    rw [reindexQuaternionPolynomial_mul] at hchange
    exact Q'.eqv_symm hchange
  have hcross :
      quaternionHaar (tail + 1)
          (polyMul polynomial
            (reindexQuaternionPolynomial s
              (headMap w K recoded))) ≈
        quaternionHaar (tail + 1)
          (polyMul recoded (headMap w K recoded)) := by
    exact reindex_pair s polynomial (headMap w K recoded)
      hpolynomial (headMap_supported tail w K hrecoded)
  have hleft :
      quaternionHaar (tail + 1) (polyMul polynomial polynomial) -
          quaternionHaar (tail + 1)
            (polyMul polynomial (conjugatedHeadMap s w K polynomial)) ≈
        quaternionHaar (tail + 1) (polyMul recoded recoded) -
          quaternionHaar (tail + 1)
            (polyMul recoded (headMap w K recoded)) := by
    exact Q'.add_eqv_congr' hnorm
      (Q'.neg_eqv_congr _ _ (by simpa [conjugatedHeadMap, recoded] using hcross))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleft)
    (headMap_defect_le_angular tail hw0 hw1 K hK recoded hrecoded)

end YMGap.Continuum.SU2QuaternionConjugatedHeadHeat

#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeat.conjugatedHeadMap
#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeat.conjugatedHeadMap_supported
#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeat.conjugatedHeadMap_defect_le_angular
