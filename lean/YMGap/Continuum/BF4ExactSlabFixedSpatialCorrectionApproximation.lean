/-
# Finite correction errors for the actual family tests

The family uses corrected_i=(d_i*G_k)*q_i on active coordinates and
corrected_i=q_i on the kinetic fringe. At one common correction degree k,
the literal difference corrected_i-q_i has square cap
  chi^k*chi^k*polynomialCap(q_i)^2,
where chi is the existing finite erased-message reciprocal rate. The
fringe difference is coefficient-zero, not merely small in Haar norm.

The consumer is FamilyCost.correctedSum. These estimates do not assume
an aggregate decomposition budget, bound the signed determinant cost,
or assert uniformity as any physical regulator varies. The degree k
is a polynomial correction degree, not physical time.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage (conditionalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse
  (radius radius_nonnegative reciprocal multiplierErrorInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost (correctedTest correctedTest_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost (corrected)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks activeBlocks

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem subtract_self (p : RatPoly) : RatPolyCoeffEqv (polyAdd p (polyNeg p)) polyZero :=
  (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
    (by decide) (fun _ => p)).trans (RatPolyCoeffEqv.zero_smul polyOne)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- Difference for the SAME corrected family, at a common finite degree. -/
def correctionDefect (qs : Nat → RatPoly) (k i : Nat) : RatPoly :=
  polyAdd (corrected hw0 hw1 K width hK n qs (fun _ => k) i) (polyNeg (qs i))

theorem correctionDefect_supported (qs : Nat → RatPoly) (k i : Nat)
    (hq : SupportedQuaternionBlocks (N width) (qs i)) :
    SupportedQuaternionBlocks (N width) (correctionDefect hw0 hw1 K width hK n qs k i) := by
  unfold correctionDefect corrected
  by_cases hi : i ∈ activeBlocks width
  · rw [if_pos hi]
    exact supported_add (correctedTest_supported hw0 hw1 K width hK n i hq k) (support_neg hq)
  · rw [if_neg hi]
    exact supported_add hq (support_neg hq)

theorem correctionDefect_fringe (qs : Nat → RatPoly) (k i : Nat)
    (hi : i ∉ activeBlocks width) :
    RatPolyCoeffEqv (correctionDefect hw0 hw1 K width hK n qs k i) polyZero := by
  unfold correctionDefect corrected
  rw [if_neg hi]
  exact subtract_self (qs i)

/-- An actual error interval on every supported component. Even indices
outside the retained range cause no assertion about a heat factor: they
are inactive and their displayed correction is exactly the identity. -/
def correctionDefectInterval (qs : Nat → RatPoly) (k i : Nat)
    (hq : SupportedQuaternionBlocks (N width) (qs i)) :
    Interval (N width) (correctionDefect hw0 hw1 K width hK n qs k i)
      ((radius hw0 hw1 K width hK n)^k * polynomialCap (qs i)) := by
  have hs := correctionDefect_supported hw0 hw1 K width hK n qs k i hq
  by_cases hi : i ∈ activeBlocks width
  · apply Interval.ofCoeff hs
      (q := polyMul (polyAdd (polyMul (conditionalMessage w K width n i)
        (reciprocal hw0 hw1 K width hK n i k)) (polyNeg polyOne)) (qs i))
    · unfold correctionDefect corrected
      rw [if_pos hi]
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.var 1)))
        (.mul (.add (.var 0) (.neg (.const 1))) (.var 1)) (by decide)
        (fun
          | 0 => polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i k)
          | _ => qs i)
    · exact (multiplierErrorInterval hw0 hw1 K width hK n i hi k).mul
        (polynomialInterval (N width) (qs i) hq)
  · exact Interval.ofCoeff hs (correctionDefect_fringe hw0 hw1 K width hK n qs k i hi)
      ((Interval.zero (N width)).weaken (Q'.mul_nonneg _ _
        (Q'.pow_nonneg _ (radius_nonnegative hw0 hw1 K width hK n) k)
        (polynomialCap_nonnegative (qs i))))

/-- The bound is a computed square certificate, ready for finite-family
square summation. No per-component quantitative budget is supplied. -/
def correctionDefectSquareBound (qs : Nat → RatPoly) (k i : Nat)
    (hq : SupportedQuaternionBlocks (N width) (qs i)) :
    SquareBound (N width) (correctionDefect hw0 hw1 K width hK n qs k i)
      (((radius hw0 hw1 K width hK n)^k * (radius hw0 hw1 K width hK n)^k) *
        (polynomialCap (qs i) * polynomialCap (qs i))) := by
  let P := correctionDefectInterval hw0 hw1 K width hK n qs k i hq
  let Q : SquareBound (N width) (correctionDefect hw0 hw1 K width hK n qs k i)
      (((radius hw0 hw1 K width hK n)^k * polynomialCap (qs i)) *
        ((radius hw0 hw1 K width hK n)^k * polynomialCap (qs i))) :=
    ⟨P.support, Q'.mul_nonneg _ _ P.nonnegative P.nonnegative, (P.mul P).upper⟩
  exact SquareBound.changeCap
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => (radius hw0 hw1 K width hK n)^k | _ => polynomialCap (qs i))) Q

end YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation.correctionDefect
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation.correctionDefect_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation.correctionDefect_fringe
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation.correctionDefectInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionApproximation.correctionDefectSquareBound
