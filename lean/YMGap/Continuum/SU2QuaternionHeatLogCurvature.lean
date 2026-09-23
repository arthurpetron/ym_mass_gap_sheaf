/-
# Constructed local log-Hessian numerator bounds for the ORIGINAL heat

For the actual relative heat h and any two supported block rotations A,B,
the certificates below prove

  -C(w) h^2 <= h A(Bh) - (Ah)(Bh) <= C(w) h^2.

No logarithm or reciprocal density is postulated: these are denominator-
cleared polynomial certificates. The constant and cutoff onset are computed
from the nome; neither is asserted uniform as w approaches one. Turning
these local certificates and the whole-kernel Hessian sign into a normalized
joint score bound still requires the actual reciprocal/limit join. Multiplying
by another kernel factor does NOT supply that join.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound
import YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage

namespace YMGap.Continuum.SU2QuaternionHeatLogCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage
open YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)

local infix:50 " ≈ " => Q'.eqv

private def floorScaledLower {blocks : Nat} {h p : RatPoly} {b delta c : Q'}
    (hb : (0 : Q') ≤ b) (hcancel : b*delta ≈ c)
    (H : Certificate blocks (polyAdd h (polyNeg (cap delta))))
    (P : Certificate blocks (polyAdd (cap c) p)) :
    Certificate blocks (polyAdd (polyMul (cap b) h) p) := by
  have hc : RatPolyCoeffEqv (polyMul (cap b) (cap delta)) (cap c) :=
    (cap_mul b delta).trans (RatPolyCoeffEqv.smul_coefficient hcancel polyOne)
  have PP := Certificate.ofCoeff (hc.add (RatPolyCoeffEqv.refl p)) P
  have HH := (Certificate.constant blocks b hb).mul H
  exact Certificate.ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1)) (.var 3))
    (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 2)) (.var 3))) (by decide)
    (fun | 0 => cap b | 1 => h | 2 => cap delta | _ => p)) (HH.add PP)

private def productLower {blocks : Nat} {u x y : RatPoly}
    (XP : Certificate blocks (polyAdd u x))
    (XM : Certificate blocks (polyAdd u (polyNeg x)))
    (YP : Certificate blocks (polyAdd u y))
    (YM : Certificate blocks (polyAdd u (polyNeg y))) :
    Certificate blocks (polyAdd (polyMul u u) (polyNeg (polyMul x y))) := by
  let p := polyAdd (polyMul u u) (polyNeg (polyMul x y))
  have twice : Certificate blocks (polySmul 2 p) :=
    Certificate.ofCoeff ((cap_mul_left 2 p).symm.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.const 2) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 2)))))
        (.add (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.neg (.var 2))))
          (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 2))))
        (by decide) (fun | 0 => u | 1 => x | _ => y)))
      ((XP.mul YM).add (XM.mul YP))
  exact Certificate.ofCoeff
    (((RatPolyCoeffEqv.smul_assoc HalfPow.half 2 p).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide : HalfPow.half*2 ≈ 1) p)).trans
      (RatPolyCoeffEqv.one_smul p)).symm
    (twice.smul HalfPow.half HalfPow.half_nonneg)

private def productUpper {blocks : Nat} {u x y : RatPoly}
    (XP : Certificate blocks (polyAdd u x))
    (XM : Certificate blocks (polyAdd u (polyNeg x)))
    (YP : Certificate blocks (polyAdd u y))
    (YM : Certificate blocks (polyAdd u (polyNeg y))) :
    Certificate blocks (polyAdd (polyMul u u) (polyMul x y)) := by
  let p := polyAdd (polyMul u u) (polyMul x y)
  have twice : Certificate blocks (polySmul 2 p) :=
    Certificate.ofCoeff ((cap_mul_left 2 p).symm.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.const 2) (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))))
        (.add (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 2)))
          (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 2)))))
        (by decide) (fun | 0 => u | 1 => x | _ => y)))
      ((XP.mul YP).add (XM.mul YM))
  exact Certificate.ofCoeff
    (((RatPolyCoeffEqv.smul_assoc HalfPow.half 2 p).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide : HalfPow.half*2 ≈ 1) p)).trans
      (RatPolyCoeffEqv.one_smul p)).symm
    (twice.smul HalfPow.half HalfPow.half_nonneg)

/-- The actual denominator-cleared mixed log-Hessian numerator. -/
def logHessianNumerator (h : RatPoly) (i j k l : Nat) : RatPoly :=
  polyAdd (polyMul h (angularDerivative i j (angularDerivative k l h)))
    (polyNeg (polyMul (angularDerivative i j h) (angularDerivative k l h)))

private def assembleBounds {blocks : Nat} {h x y z : RatPoly} {b r : Q'}
    (H : Certificate blocks h)
    (ZP : Certificate blocks (polyAdd (polyMul (cap b) h) z))
    (ZM : Certificate blocks (polyAdd (polyMul (cap b) h) (polyNeg z)))
    (XP : Certificate blocks (polyAdd (polyMul (cap r) h) x))
    (XM : Certificate blocks (polyAdd (polyMul (cap r) h) (polyNeg x)))
    (YP : Certificate blocks (polyAdd (polyMul (cap r) h) y))
    (YM : Certificate blocks (polyAdd (polyMul (cap r) h) (polyNeg y))) :
    Certificate blocks (polyAdd (polyMul (cap (b+r*r)) (polyMul h h))
      (polyAdd (polyMul h z) (polyNeg (polyMul x y)))) ×
    Certificate blocks (polyAdd (polyMul (cap (b+r*r)) (polyMul h h))
      (polyNeg (polyAdd (polyMul h z) (polyNeg (polyMul x y))))) := by
  have hc : RatPolyCoeffEqv (cap (b+r*r))
      (polyAdd (cap b) (polyMul (cap r) (cap r))) :=
    (cap_add b (r*r)).symm.trans ((RatPolyCoeffEqv.refl _).add (cap_mul r r).symm)
  let env : Nat → RatPoly
    | 0 => h | 1 => x | 2 => y | 3 => z | 4 => cap b | _ => cap r
  constructor
  · exact Certificate.ofCoeff (((hc.mul_right _).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 4) (.mul (.var 5) (.var 5))) (.mul (.var 0) (.var 0)))
          (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2)))))
        (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 0)) (.var 3)))
          (.add (.mul (.mul (.var 5) (.var 0)) (.mul (.var 5) (.var 0)))
            (.neg (.mul (.var 1) (.var 2))))) (by decide) env))
      ((H.mul ZP).add (productLower XP XM YP YM))
  · exact Certificate.ofCoeff (((hc.mul_right _).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 4) (.mul (.var 5) (.var 5))) (.mul (.var 0) (.var 0)))
          (.neg (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2))))))
        (.add (.mul (.var 0) (.add (.mul (.var 4) (.var 0)) (.neg (.var 3))))
          (.add (.mul (.mul (.var 5) (.var 0)) (.mul (.var 5) (.var 0)))
            (.mul (.var 1) (.var 2)))) (by decide) env))
      ((H.mul ZM).add (productUpper XP XM YP YM))

/-- Explicit local relative second-derivative cost; nome dependence is retained. -/
def secondRelativeCap (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Q' :=
  heatSecondDerivativeCap w 32 32 64 *
    Q'.recipPos (headFloor w) (headFloor_positive hw0 hw1)

/-- Computed entrywise log-Hessian cap, independent of ambient size and cutoff. -/
def logCurvatureCap (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Q' :=
  secondRelativeCap w hw0 hw1 + relativeCap w 32 * relativeCap w 32

/-- Both signs of every actual mixed entry, on the original Haar carrier.
The late-cutoff guard is the existing relative first-derivative onset. -/
def heatLogHessianBounds
    {blocks a b s t i j k l : Nat}
    (ha : a < blocks) (hb : b < blocks) (hs : s < blocks) (ht : t < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) :
    Certificate blocks
      (polyAdd (polyMul (cap (logCurvatureCap w hw0 hw1))
        (polyMul (heatAt a b w K) (heatAt a b w K)))
        (logHessianNumerator (heatAt a b w K) (4*s+i) (4*s+j) (4*t+k) (4*t+l))) ×
    Certificate blocks
      (polyAdd (polyMul (cap (logCurvatureCap w hw0 hw1))
        (polyMul (heatAt a b w K) (heatAt a b w K)))
        (polyNeg (logHessianNumerator (heatAt a b w K) (4*s+i) (4*s+j) (4*t+k) (4*t+l)))) := by
  let D := heatSecondAngularInterval ha hb hs ht hi hj hk hl hw0 hw1 K
  let P := heatRelativeBound ha hb (show 4*s+i < 4*blocks by omega)
    (show 4*s+j < 4*blocks by omega) hw0 hw1 K hK
  let Q := heatRelativeBound ha hb (show 4*t+k < 4*blocks by omega)
    (show 4*t+l < 4*blocks by omega) hw0 hw1 K hK
  let F := heatAt_floorCertificate ha hb hw0 hw1 K
    (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK)
  have hnonneg : (0 : Q') ≤ secondRelativeCap w hw0 hw1 :=
    Q'.mul_nonneg _ _ D.nonnegative (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hcancel : secondRelativeCap w hw0 hw1 * headFloor w ≈
      heatSecondDerivativeCap w 32 32 64 := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)))
      (Q'.mul_one_eqv _)
  exact assembleBounds P.positive
    (floorScaledLower hnonneg hcancel F D.lower)
    (floorScaledLower hnonneg hcancel F D.upper) P.lower P.upper Q.lower Q.upper

end YMGap.Continuum.SU2QuaternionHeatLogCurvature

#print axioms YMGap.Continuum.SU2QuaternionHeatLogCurvature.secondRelativeCap
#print axioms YMGap.Continuum.SU2QuaternionHeatLogCurvature.logCurvatureCap
#print axioms YMGap.Continuum.SU2QuaternionHeatLogCurvature.heatLogHessianBounds
