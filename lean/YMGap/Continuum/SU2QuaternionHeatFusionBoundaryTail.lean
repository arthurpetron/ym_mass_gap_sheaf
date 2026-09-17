/-
# Quantitative cutoff-boundary error for the original heat fusion identity

Both signed boundary terms are retained. Sharp character certificates bound
their sum by two adjacent squared-dimension majorants, and the existing
all-nome geometric tail supplies an explicit cutoff for any tolerance.
The cutoff depends on the rational nome and tolerance, not the Haar carrier
size or the chosen supported unit-bounded scalar polynomial.

This controls only the cutoff boundary of the exact fusion residual. It
does not bound the signed bulk response or change an original partition.
-/

import YMGap.Continuum.SU2QuaternionHeatFusionResidual
import YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
import YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse

namespace YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (dimQ dimQ_nonneg)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_nonneg)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (negInterval)
open YMGap.Continuum.SU2QuaternionHeatFusionResidual (boundaryResidual)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatMajorant)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval

local infix:50 " ≈ " => Q'.eqv

/-- Sum of the two literal boundary character caps. -/
def boundaryCap (w : Q') (K : Nat) : Q' :=
  coeffW w K * dimQ (K+1) + coeffW w (K+1) * dimQ K

theorem boundaryCap_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') ≤ boundaryCap w K :=
  Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (coeffW_nonneg hw K) (dimQ_nonneg (K+1)))
    (Q'.mul_nonneg _ _ (coeffW_nonneg hw (K+1)) (dimQ_nonneg K))

/-- Original-carrier interval certificates for the signed boundary residual. -/
def boundaryInterval {w : Q'} {blocks : Nat} {x : RatPoly}
    (hw : (0 : Q') ≤ w) (P : SquareBound blocks x 1) (K : Nat) :
    Interval blocks (boundaryResidual w K x) (boundaryCap w K) :=
  ((sharpCharacterInterval P (K+1)).smul (coeffW w K) (coeffW_nonneg hw K)).add
    (negInterval ((sharpCharacterInterval P K).smul
      (coeffW w (K+1)) (coeffW_nonneg hw (K+1))))

private theorem dim_next_le_twice (K : Nat) : dimQ (K+1) ≤ 2 * dimQ K :=
  Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat (show K+2 ≤ 2*(K+1) by omega))
    (Q'.le_of_eqv (SU3CharFactor.ofNat_mul_eqv 2 (K+1)))

private theorem dim_le_twice_next (K : Nat) : dimQ K ≤ 2 * dimQ (K+1) :=
  Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat (show K+1 ≤ 2*(K+2) by omega))
    (Q'.le_of_eqv (SU3CharFactor.ofNat_mul_eqv 2 (K+2)))

private theorem crossed_cap_le {a b d e : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (he : e ≤ 2*d) (hd : d ≤ 2*e) :
    a*e + b*d ≤ 2*(a*d + b*e) := by
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ he ha)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hd hb))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.const 2) (.var 2)))
        (.mul (.var 1) (.mul (.const 2) (.var 3))))
      (.mul (.const 2)
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
      (by decide) (fun | 0 => a | 1 => b | 2 => d | _ => e)))

/-- A length-two existing tail controls both boundary terms. -/
theorem boundaryCap_le_tail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (M : Nat) : boundaryCap w (spacingLabelCutoff w + M) ≤
      2 * spacingClosedTail w M := by
  let K := spacingLabelCutoff w + M
  have hcross : boundaryCap w K ≤
      2 * (coeffW w K * dimQ K + coeffW w (K+1) * dimQ (K+1)) :=
    crossed_cap_le (coeffW_nonneg (Q'.le_of_lt hw0) K)
      (coeffW_nonneg (Q'.le_of_lt hw0) (K+1))
      (dim_next_le_twice K) (dim_le_twice_next K)
  have hmajorant :
      2 * (coeffW w K * dimQ K + coeffW w (K+1) * dimQ (K+1)) ≈
        2 * (pointwiseHeatMajorant w K + pointwiseHeatMajorant w (K+1)) :=
    Q'.mul_eqv_congr_left 2 _ _
      (Q'.add_eqv_congr' (heat_dimension_majorant w K) (heat_dimension_majorant w (K+1)))
  have hblock : pointwiseHeatMajorant w K + pointwiseHeatMajorant w (K+1) ≤
      spacingClosedTail w M := by
    simpa only [K, finSum, Nat.add_zero, Nat.add_assoc, Q'.zero_add'] using
      shiftedMajorant_block hw0 hw1 M 2
  exact Q'.le_trans' _ _ _ hcross
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmajorant)
      (Q'.mul_le_mul_of_nonneg_left _ _ 2 hblock (by decide)))

/-- Explicit cutoff data, using half the requested tolerance in the old modulus. -/
def boundaryCutoff (w epsilon : Q') : Nat :=
  spacingLabelCutoff w + spacingTailCauchyCutoff w (HalfPow.half * epsilon)

/-- Every later cutoff has the requested boundary cap, at fixed rational nome. -/
theorem boundaryCap_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat)
    (hK : boundaryCutoff w epsilon ≤ K) : boundaryCap w K ≤ epsilon := by
  have hN : spacingLabelCutoff w ≤ K := by
    unfold boundaryCutoff at hK
    omega
  have hM : spacingTailCauchyCutoff w (HalfPow.half * epsilon) ≤
      K - spacingLabelCutoff w := by
    unfold boundaryCutoff at hK
    omega
  have htail := boundaryCap_le_tail hw0 hw1 (K - spacingLabelCutoff w)
  rw [Nat.add_sub_of_le hN] at htail
  have hsmall := closedTail_small hw0 hw1 (HalfPow.half * epsilon)
    (ExpNeg.half_mul_pos epsilon he) (K - spacingLabelCutoff w) hM
  have hhalf : 2 * (HalfPow.half * epsilon) ≈ epsilon :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0))
      (by decide) (fun _ => HalfPow.half * epsilon)) (ExpNeg.two_halves epsilon)
  exact Q'.le_trans' _ _ _ htail
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 hsmall (by decide))
      (Q'.le_of_eqv hhalf))

/-- The same explicit cutoff produces a boundary certificate on any carrier. -/
def boundarySmallInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat)
    (hK : boundaryCutoff w epsilon ≤ K) :
    Interval blocks (boundaryResidual w K x) epsilon :=
  (boundaryInterval (Q'.le_of_lt hw0) P K).weaken
    (boundaryCap_small hw0 hw1 epsilon he K hK)

end YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail

#print axioms YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail.boundaryCap
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail.boundaryCap_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail.boundaryInterval
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail.boundaryCap_le_tail
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail.boundaryCutoff
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail.boundaryCap_small
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail.boundarySmallInterval
