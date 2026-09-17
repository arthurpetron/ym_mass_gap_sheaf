/-
# Finite-degree diagonal cost in the actual marginal

For the explicit polynomial reciprocal G of the one-erasure message d,
the dual test is t*q*G and its corrected actual-marginal test is d*G*q.
The erased diagonal equals h times the corrected norm plus the positive
cost H[nu*d*(t-h*d)*(q*G)^2]. Both lower and upper cost certificates retain
the full original nu=(V*T^n1)*T^(n+1)1. No inverse limit is taken.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse
open YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet (erasedPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left cap_add)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks activeBlocks

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n i : Nat)

/-- Corrected test in the actual nu inner product, at explicit finite degree. -/
def correctedTest (q : RatPoly) (k : Nat) : RatPoly :=
  polyMul (polyMul (conditionalMessage w K width n i)
    (reciprocal hw0 hw1 K width hK n i k)) q

theorem correctedTest_supported {q : RatPoly} (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    SupportedQuaternionBlocks (N width) (correctedTest hw0 hw1 K width hK n i q k) :=
  supported_polyMul
    (supported_polyMul (conditionalMessage_supported w K width n i)
      (reciprocal_supported hw0 hw1 K width hK n i k)) hq

/-- The residual diagonal polynomial, before inserting the actual marginal. -/
def diagonalPolynomial (q : RatPoly) (k : Nat) : RatPoly :=
  let d := conditionalMessage w K width n i
  let t := terminalMessage w K width (n+1)
  let qG := polyMul q (reciprocal hw0 hw1 K width hK n i k)
  polyMul (polyMul d (polyAdd t (polyNeg (polyMul (cap (headFloor w)) d)))) (polyMul qG qG)

def diagonalCost (q : RatPoly) (k : Nat) : Q' :=
  quaternionHaar (N width) (polyMul (marginalWeight w K width n)
    (diagonalPolynomial hw0 hw1 K width hK n i q k))

private def erasedCertificate (hi : i ∈ activeBlocks width) :
    Certificate (N width) (conditionalMessage w K width n i) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => conditionalMessage w K width n i | _ => cap (lower hw0 hw1 K width n)))
    ((lowerCertificate hw0 hw1 K width hK n i hi).add
      (Certificate.constant (N width) _ (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n))))

private theorem haar_neg (b : Nat) : ∀ p : RatPoly,
    quaternionHaar b (polyNeg p) ≈ -(quaternionHaar b p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv _ _) (haar_neg b p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_sub (b : Nat) (p q : RatPoly) :
    quaternionHaar b (polyAdd p (polyNeg q)) ≈ quaternionHaar b p + -(quaternionHaar b q) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append b p (polyNeg q))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg b q))

/-- The actual erased diagonal splits exactly; no conditional centering is needed. -/
theorem diagonal_pin (q : RatPoly) (k : Nat) :
    erasedPair w K width n i (dualTest hw0 hw1 K width hK n i q k)
      (dualTest hw0 hw1 K width hK n i q k) ≈
    headFloor w * marginalPair w K width n
      (correctedTest hw0 hw1 K width hK n i q k) (correctedTest hw0 hw1 K width hK n i q k) +
      diagonalCost hw0 hw1 K width hK n i q k := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let d := conditionalMessage w K width n i
  let t := terminalMessage w K width (n+1)
  let G := reciprocal hw0 hw1 K width hK n i k
  let v := correctedTest hw0 hw1 K width hK n i q k
  have hp : RatPolyCoeffEqv
      (polyMul (polyMul a d)
        (polyMul (dualTest hw0 hw1 K width hK n i q k) (dualTest hw0 hw1 K width hK n i q k)))
      (polyAdd (polySmul (headFloor w) (polyMul (marginalWeight w K width n) (polyMul v v)))
        (polyMul (marginalWeight w K width n) (diagonalPolynomial hw0 hw1 K width hK n i q k))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1))
        (.mul (.mul (.mul (.var 2) (.var 3)) (.var 4)) (.mul (.mul (.var 2) (.var 3)) (.var 4))))
      (.add (.mul (.var 5) (.mul (.mul (.var 0) (.var 2))
        (.mul (.mul (.mul (.var 1) (.var 4)) (.var 3)) (.mul (.mul (.var 1) (.var 4)) (.var 3)))))
        (.mul (.mul (.var 0) (.var 2))
          (.mul (.mul (.var 1) (.add (.var 2) (.neg (.mul (.var 5) (.var 1)))))
            (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))))
      (by decide) (fun | 0 => a | 1 => d | 2 => t | 3 => q | 4 => G | _ => cap (headFloor w))).trans
        ((cap_mul_left (headFloor w) _).add (.refl _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (quaternionHaar_polySmul _ _ _) (Q'.eqv_refl _)))

/-- Concrete positive certificate for the diagonal remainder, in the SAME nu. -/
def diagonalCertificate (hi : i ∈ activeBlocks width) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    Certificate (N width) (polyMul (marginalWeight w K width n)
      (diagonalPolynomial hw0 hw1 K width hK n i q k)) :=
  (marginalCertificate hw0 hw1 K width hK n).mul
    (((erasedCertificate hw0 hw1 K width hK n i hi).mul
      (.ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left (headFloor w) _)))
        (conditionalMessage_lowerCertificate hw0 hw1 K width hK n i hi))).mul
      (.square (polyMul q (reciprocal hw0 hw1 K width hK n i k))
        (supported_polyMul hq (reciprocal_supported hw0 hw1 K width hK n i k))))

theorem diagonalCost_nonnegative (hi : i ∈ activeBlocks width) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    (0 : Q') ≤ diagonalCost hw0 hw1 K width hK n i q k :=
  (diagonalCertificate hw0 hw1 K width hK n i hi hq k).haar_nonnegative

/-- The upper cost defect factors as nu*d*(U*d-t)*(q*G)^2. -/
def diagonalUpperCertificate (hi : i ∈ activeBlocks width) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    Certificate (N width) (polyAdd
      (polySmul (prefixCap w + -(headFloor w)) (polyMul (marginalWeight w K width n)
        (polyMul (correctedTest hw0 hw1 K width hK n i q k)
          (correctedTest hw0 hw1 K width hK n i q k))))
      (polyNeg (polyMul (marginalWeight w K width n)
        (diagonalPolynomial hw0 hw1 K width hK n i q k)))) := by
  let nu := marginalWeight w K width n
  let d := conditionalMessage w K width n i
  let t := terminalMessage w K width (n+1)
  let G := reciprocal hw0 hw1 K width hK n i k
  let U := prefixCap w
  let h := headFloor w
  have B : Certificate (N width) (polyAdd (polyMul (cap U) d) (polyNeg t)) :=
    .ofCoeff ((cap_mul_left U d).add (.refl _)) (conditionalMessage_capCertificate hw0 hw1 K width hK n i hi)
  have C := ((marginalCertificate hw0 hw1 K width hK n).mul
    ((erasedCertificate hw0 hw1 K width hK n i hi).mul B)).mul
      (Certificate.square (polyMul q G) (supported_polyMul hq (reciprocal_supported hw0 hw1 K width hK n i k)))
  have hcap : RatPolyCoeffEqv (cap (U + -h)) (polyAdd (cap U) (polyNeg (cap h))) := by
    have hn : RatPolyCoeffEqv (polyNeg (cap h)) (cap (-h)) := by
      intro weight
      change (-(h*1))*weight []+0 ≈ ((-h)*1)*weight []+0
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv h 1))) (Q'.eqv_refl _)
    exact (cap_add U (-h)).symm.trans ((RatPolyCoeffEqv.refl _).add hn.symm)
  refine .ofCoeff (((cap_mul_left (U + -h) _).symm.trans (hcap.mul_right _)).add (.refl _) |>.trans ?_) C
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.add (.var 5) (.neg (.var 6))) (.mul (.var 0)
      (.mul (.mul (.mul (.var 1) (.var 4)) (.var 3)) (.mul (.mul (.var 1) (.var 4)) (.var 3)))))
      (.neg (.mul (.var 0) (.mul (.mul (.var 1) (.add (.var 2) (.neg (.mul (.var 6) (.var 1)))))
        (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4)))))))
    (.mul (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 5) (.var 1)) (.neg (.var 2)))))
      (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))
    (by decide) (fun | 0 => nu | 1 => d | 2 => t | 3 => q | 4 => G | 5 => cap U | _ => cap h)

/-- Diagonal control with explicit nome-dependent coefficient U-h, not a
uniform bound of the sum by the norm of a sum of tests. -/
theorem diagonalCost_upper (hi : i ∈ activeBlocks width) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (N width) q) (k : Nat) :
    diagonalCost hw0 hw1 K width hK n i q k ≤
      (prefixCap w + -(headFloor w))*marginalPair w K width n
        (correctedTest hw0 hw1 K width hK n i q k) (correctedTest hw0 hw1 K width hK n i q k) := by
  have h := (diagonalUpperCertificate hw0 hw1 K width hK n i hi hq k).haar_nonnegative
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (haar_sub (N width) _ _)
      (Q'.add_eqv_congr' (quaternionHaar_polySmul _ _ _) (Q'.eqv_refl _)))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.correctedTest
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.correctedTest_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.diagonalPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.diagonalCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.diagonal_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.diagonalCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.diagonalCost_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.diagonalUpperCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost.diagonalCost_upper
