/-
Raw basis pins for the actual selected-block paired curvature and its Haar
integration-by-parts cancellation. No mixed jets are symmetrized.
-/

import YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt

namespace YMGap.Continuum.QPolyHaarPairedAtFrozenBasis

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt (quaternionHaar_angularDerivative_at)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QPolyHaarFrozenChain (threeSum_congr threeSum_mul_left)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (frozenFirstAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct (frozenCurvatureAt)

local infix:50 " ≈ " => Q'.eqv

/-- One literal polynomial direction, with zeros in the other two slots. -/
def basisDirection (i : Fin 3) : Fin 3 → RatPoly :=
  fun j => if j = i then polyOne else polyZero

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

/-- Three-slot basis contraction, coefficientwise for arbitrary entries. -/
theorem threeSum_basis (f : Fin 3 → RatPoly) (i : Fin 3) :
    RatPolyCoeffEqv
      (threeSum (fun j => polyMul (basisDirection i j) (f j))) (f i) := by
  rcases direction_cases i with rfl | rfl | rfl
  · change RatPolyCoeffEqv
      (polyAdd (polyMul polyOne (f 0))
        (polyAdd (polyMul polyZero (f 1)) (polyMul polyZero (f 2)))) (f 0)
    exact (((RatPolyCoeffEqv.one_mul _).add
      ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.mul_zero_left _))).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.zero_add polyZero))).trans
      (RatPolyCoeffEqv.add_zero _)
  · change RatPolyCoeffEqv
      (polyAdd (polyMul polyZero (f 0))
        (polyAdd (polyMul polyOne (f 1)) (polyMul polyZero (f 2)))) (f 1)
    exact (((RatPolyCoeffEqv.mul_zero_left _).add
      ((RatPolyCoeffEqv.one_mul _).add (RatPolyCoeffEqv.mul_zero_left _))).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _))).trans
      (RatPolyCoeffEqv.zero_add _)
  · change RatPolyCoeffEqv
      (polyAdd (polyMul polyZero (f 0))
        (polyAdd (polyMul polyZero (f 1)) (polyMul polyOne (f 2)))) (f 2)
    exact (((RatPolyCoeffEqv.mul_zero_left _).add
      ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.one_mul _))).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.zero_add _))).trans
      (RatPolyCoeffEqv.zero_add _)

theorem threeSquare_basis (i : Fin 3) :
    RatPolyCoeffEqv (threeSquare (basisDirection i)) polyOne := by
  have h (j : Fin 3) : RatPolyCoeffEqv
      (polyMul (basisDirection i j) (basisDirection i j))
      (polyMul (basisDirection i j) polyOne) := by
    by_cases hj : j = i
    · simp only [basisDirection, if_pos hj]
      exact RatPolyCoeffEqv.refl _
    · simp only [basisDirection, if_neg hj]
      exact RatPolyCoeffEqv.refl _
  exact (threeSum_congr h).trans (threeSum_basis (fun _ => polyOne) i)

theorem quadraticForm_basis (M : Fin 3 → Fin 3 → RatPoly) (i : Fin 3) :
    RatPolyCoeffEqv (quadraticForm (basisDirection i) M) (M i i) := by
  let u := basisDirection i
  have hinner (r : Fin 3) : RatPolyCoeffEqv
      (threeSum (fun j => polyMul (polyMul (u r) (u j)) (M r j)))
      (polyMul (u r) (M r i)) :=
    (threeSum_congr (fun j => RatPolyCoeffEqv.mul_assoc (u r) (u j) (M r j))).trans
      ((threeSum_mul_left (u r) (fun j => polyMul (u j) (M r j))).trans
        ((threeSum_basis (fun j => M r j) i).mul_left (u r)))
  exact (threeSum_congr hinner).trans (threeSum_basis (fun r => M r i) i)

theorem frozenFirstAt_basis (s : Nat) (p : RatPoly) (i : Fin 3) :
    RatPolyCoeffEqv (frozenFirstAt s (basisDirection i) p)
      (pairedDerivativeAt s i p) :=
  threeSum_basis (fun j => pairedDerivativeAt s j p) i

theorem frozenSecondAt_basis (s : Nat) (p : RatPoly) (i : Fin 3) :
    RatPolyCoeffEqv (frozenSecondAt s (basisDirection i) p)
      (pairedDerivativeAt s i (pairedDerivativeAt s i p)) :=
  quadraticForm_basis (fun j k => pairedDerivativeAt s j (pairedDerivativeAt s k p)) i

/-- The actual basis specialization of selected-block frozen curvature. -/
theorem frozenCurvatureAt_basis_pin (s : Nat) (C : Q') (p : RatPoly) (i : Fin 3) :
    RatPolyCoeffEqv (frozenCurvatureAt s C p (basisDirection i))
      (polyAdd (polyMul (cap C) (polyMul p p))
        (polyAdd (polyMul p (pairedDerivativeAt s i (pairedDerivativeAt s i p)))
          (polyNeg (polyMul (pairedDerivativeAt s i p) (pairedDerivativeAt s i p))))) := by
  have hcost : RatPolyCoeffEqv
      (polyMul (threeSquare (basisDirection i)) (polyMul p p)) (polyMul p p) :=
    ((threeSquare_basis i).mul_right (polyMul p p)).trans
      (RatPolyCoeffEqv.one_mul (polyMul p p))
  exact (hcost.mul_left (cap C)).add
    (((frozenSecondAt_basis s p i).mul_left p).add
      (RatPolyCoeffEqv.neg ((frozenFirstAt_basis s p i).mul
        (frozenFirstAt_basis s p i))))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -quaternionHaar blocks p
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Every paired generator, including its signed middle plane, has zero
integral in the original in-range product Haar carrier. -/
theorem paired_haar_zero {blocks s : Nat} (hs : s < blocks) (i : Fin 3)
    (p : RatPoly) : quaternionHaar blocks (pairedDerivativeAt s i p) ≈ 0 := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (quaternionHaar_angularDerivative_at hs (by decide) (by decide) p)
          (quaternionHaar_angularDerivative_at hs (by decide) (by decide) p))
        (by decide))
  · have hz := quaternionHaar_angularDerivative_at hs (by decide : 1 < 4)
      (by decide : 3 < 4) p
    have hn : quaternionHaar blocks (polyNeg (blockAngularDerivative s 1 3 p)) ≈ 0 :=
      Q'.eqv_trans _ _ _ (haar_neg blocks _)
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hz) (by decide))
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (quaternionHaar_angularDerivative_at hs (by decide) (by decide) p) hn)
        (by decide))
  · exact Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (quaternionHaar_angularDerivative_at hs (by decide) (by decide) p)
          (quaternionHaar_angularDerivative_at hs (by decide) (by decide) p))
        (by decide))

theorem paired_square_haar_zero {blocks s : Nat} (hs : s < blocks)
    (i : Fin 3) (p : RatPoly) :
    quaternionHaar blocks (pairedDerivativeAt s i (pairedDerivativeAt s i p)) ≈ 0 :=
  paired_haar_zero hs i (pairedDerivativeAt s i p)

end YMGap.Continuum.QPolyHaarPairedAtFrozenBasis

#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.basisDirection
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.threeSum_basis
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.threeSquare_basis
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.quadraticForm_basis
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.frozenFirstAt_basis
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.frozenSecondAt_basis
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.frozenCurvatureAt_basis_pin
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.paired_haar_zero
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenBasis.paired_square_haar_zero
