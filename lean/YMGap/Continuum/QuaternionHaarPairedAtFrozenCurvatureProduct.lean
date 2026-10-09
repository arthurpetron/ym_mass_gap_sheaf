/-
Actual selected-block frozen curvature tensorization.
The derivative coefficients are frozen only AFTER all ordered jets are taken.
The opposite squares give the exact product identity even for dependent factors.
This leaf supplies no reciprocal passage, weighted Bochner or continuum bound.
-/

import YMGap.Continuum.QPolyHaarPairedAtFrozenZero
import YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation

namespace YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul_left)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (frozenFirstAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.QPolyHaarPairedAtFrozenProduct
open YMGap.Continuum.QPolyHaarPairedAtFrozenZero

local infix:50 " ≈ " => Q'.eqv

/-- Literal first/all-nine second jets on the original selected block. -/
def frozenCurvatureAt (s : Nat) (C : Q') (p : RatPoly) (u : Fin 3 → RatPoly) : RatPoly :=
  QuaternionHaarFrozenCurvatureApproximation.jetCurvature C p
    (fun i => pairedDerivativeAt s i p)
    (fun i j => pairedDerivativeAt s i (pairedDerivativeAt s j p)) u

/-- Raw polynomial congruence also transports every actual ordered jet. -/
theorem frozenCurvatureAt_congr (s : Nat) (C : Q') (u : Fin 3 → RatPoly)
    {p q : RatPoly} (hpq : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (frozenCurvatureAt s C p u) (frozenCurvatureAt s C q u) :=
  ((hpq.mul hpq).mul_left (threeSquare u) |>.mul_left (cap C)).add
    ((hpq.mul (frozenSecondAt_congr s u hpq)).add
      (RatPolyCoeffEqv.neg ((frozenFirstAt_congr s u hpq).mul
        (frozenFirstAt_congr s u hpq))))

theorem frozenCurvatureAt_cost_congr (s : Nat) (p : RatPoly) (u : Fin 3 → RatPoly)
    {C D : Q'} (hCD : C ≈ D) :
    RatPolyCoeffEqv (frozenCurvatureAt s C p u) (frozenCurvatureAt s D p u) :=
  ((RatPolyCoeffEqv.smul_coefficient hCD polyOne).mul_right
    (polyMul (threeSquare u) (polyMul p p))).add (RatPolyCoeffEqv.refl _)

private def sq (p : PolyExpr) : PolyExpr := .mul p p
private def curvature (C U p dp ddp : PolyExpr) : PolyExpr :=
  .add (.mul C (.mul U (sq p))) (.add (.mul p ddp) (.neg (sq dp)))

/-- Exact product formula, not an inference from positivity. -/
theorem frozenCurvatureAt_product_pin (s : Nat) (C D : Q') (p q : RatPoly)
    (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (frozenCurvatureAt s (C+D) (polyMul p q) u)
      (polyAdd (polyMul (polyMul q q) (frozenCurvatureAt s C p u))
        (polyMul (polyMul p p) (frozenCurvatureAt s D q u))) := by
  let dp := frozenFirstAt s u p
  let dq := frozenFirstAt s u q
  let ddp := frozenSecondAt s u p
  let ddq := frozenSecondAt s u q
  have hfirst := frozenFirstAt_mul s u p q
  have hsecond := (frozenSecondAt_mul s u p q).trans
    (((RatPolyCoeffEqv.refl _).add (cap_mul_left 2 (polyMul dp dq)).symm).add
      (RatPolyCoeffEqv.refl _))
  have hstart : RatPolyCoeffEqv (frozenCurvatureAt s (C+D) (polyMul p q) u)
      (polyAdd
        (polyMul (polyAdd (cap C) (cap D))
          (polyMul (threeSquare u) (polyMul (polyMul p q) (polyMul p q))))
        (polyAdd
          (polyMul (polyMul p q)
            (polyAdd (polyAdd (polyMul ddp q) (polyMul (cap 2) (polyMul dp dq)))
              (polyMul p ddq)))
          (polyNeg (polyMul
            (polyAdd (polyMul dp q) (polyMul p dq))
            (polyAdd (polyMul dp q) (polyMul p dq)))))) :=
    ((cap_add C D).symm.mul_right _).add
      ((hsecond.mul_left (polyMul p q)).add (RatPolyCoeffEqv.neg (hfirst.mul hfirst)))
  exact hstart.trans (coeffEvalExpr_eqv_of_normalize_eq
    (curvature (.add (.var 0) (.var 1)) (.var 2) (.mul (.var 3) (.var 6))
      (.add (.mul (.var 4) (.var 6)) (.mul (.var 3) (.var 7)))
      (.add (.add (.mul (.var 5) (.var 6))
        (.mul (.const 2) (.mul (.var 4) (.var 7)))) (.mul (.var 3) (.var 8))))
    (.add (.mul (sq (.var 6)) (curvature (.var 0) (.var 2) (.var 3) (.var 4) (.var 5)))
      (.mul (sq (.var 3)) (curvature (.var 1) (.var 2) (.var 6) (.var 7) (.var 8))))
    (by decide) (fun
      | 0 => cap C | 1 => cap D | 2 => threeSquare u | 3 => p | 4 => dp
      | 5 => ddp | 6 => q | 7 => dq | _ => ddq))

/-- Actual frozen curvature certificates tensorize with additive costs. -/
def frozen_product_curvature_certificate {blocks : Nat} (s : Nat) (C D : Q')
    (p q : RatPoly) (u : Fin 3 → RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (P : Certificate blocks (frozenCurvatureAt s C p u))
    (Q : Certificate blocks (frozenCurvatureAt s D q u)) :
    Certificate blocks (frozenCurvatureAt s (C+D) (polyMul p q) u) :=
  Certificate.ofCoeff (frozenCurvatureAt_product_pin s C D p q u)
    ((Certificate.multiplySquare q hq P).add (Certificate.multiplySquare p hp Q))

/-- An independent factor has exact zero curvature at cost zero. -/
def frozen_independent_curvature_zero_certificate {blocks : Nat} (s : Nat)
    (p : RatPoly) (u : Fin 3 → RatPoly) (hind : QuaternionBlockIndependent s p) :
    Certificate blocks (frozenCurvatureAt s 0 p u) := by
  have hfirst := frozenFirstAt_independent_zero s u hind
  have hsecond := frozenSecondAt_independent_zero s u hind
  have hp : RatPolyCoeffEqv (frozenCurvatureAt s 0 p u)
      (polyAdd (polyMul (cap 0) (polyMul (threeSquare u) (polyMul p p)))
        (polyAdd (polyMul p polyZero) (polyNeg (polyMul polyZero polyZero)))) :=
    (RatPolyCoeffEqv.refl _).add
      ((hsecond.mul_left p).add (RatPolyCoeffEqv.neg (hfirst.mul hfirst)))
  have htail : RatPolyCoeffEqv
      (polyAdd (polyMul p polyZero) (polyNeg (polyMul polyZero polyZero))) polyZero :=
    ((RatPolyCoeffEqv.mul_zero_right p).add
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_left polyZero))).trans
      (RatPolyCoeffEqv.zero_add polyZero)
  have hzero : RatPolyCoeffEqv
      (polyAdd (polyMul (cap 0) (polyMul (threeSquare u) (polyMul p p)))
        (polyAdd (polyMul p polyZero) (polyNeg (polyMul polyZero polyZero)))) (cap 0) :=
    ((((cap_mul_left 0 _).trans (RatPolyCoeffEqv.zero_smul _)).add htail).trans
      (RatPolyCoeffEqv.zero_add polyZero)).trans
      (RatPolyCoeffEqv.zero_smul polyOne).symm
  exact Certificate.ofCoeff (hp.trans hzero) (Certificate.constant blocks 0 (Q'.le_refl' 0))

/-- Raising a cost pays only a nonnegative supported direction square. -/
def frozenCurvatureAt_raise_cost_certificate {blocks : Nat} (s : Nat)
    {C D : Q'} (p : RatPoly) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i))
    (hp : SupportedQuaternionBlocks blocks p) (hCD : C ≤ D)
    (P : Certificate blocks (frozenCurvatureAt s C p u)) :
    Certificate blocks (frozenCurvatureAt s D p u) := by
  let U : Certificate blocks (threeSquare u) :=
    (Certificate.square (u 0) (hu 0)).add
      ((Certificate.square (u 1) (hu 1)).add (Certificate.square (u 2) (hu 2)))
  let S := Certificate.ofCoeff (cap_mul_left (D + -C)
      (polyMul (threeSquare u) (polyMul p p)))
    (Certificate.smul (D + -C) (Q'.sub_nonneg_of_le hCD)
      (U.mul (Certificate.square p hp)))
  have hcap : RatPolyCoeffEqv (cap D) (polyAdd (cap C) (cap (D + -C))) :=
    (RatPolyCoeffEqv.smul_coefficient (poly_identity_of_normal_eq
      (.var 1) (.add (.var 0) (.add (.var 1) (.neg (.var 0))))
      (by decide) (fun | 0 => C | _ => D)) polyOne).trans (cap_add C (D + -C)).symm
  have hsplit : RatPolyCoeffEqv (frozenCurvatureAt s D p u)
      (polyAdd (frozenCurvatureAt s C p u)
        (polyMul (cap (D + -C)) (polyMul (threeSquare u) (polyMul p p)))) :=
    ((hcap.mul_right _).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.add (.add (.mul (.var 0) (.var 2)) (.var 3)) (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => cap C | 1 => cap (D + -C)
          | 2 => polyMul (threeSquare u) (polyMul p p)
          | _ => polyAdd (polyMul p (frozenSecondAt s u p))
            (polyNeg (polyMul (frozenFirstAt s u p) (frozenFirstAt s u p)))))
  exact Certificate.ofCoeff hsplit (P.add S)

end YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct

#print axioms YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct.frozenCurvatureAt_congr
#print axioms YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct.frozenCurvatureAt_cost_congr
#print axioms YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct.frozenCurvatureAt_product_pin
#print axioms YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct.frozen_product_curvature_certificate
#print axioms YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct.frozen_independent_curvature_zero_certificate
#print axioms YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct.frozenCurvatureAt_raise_cost_certificate
