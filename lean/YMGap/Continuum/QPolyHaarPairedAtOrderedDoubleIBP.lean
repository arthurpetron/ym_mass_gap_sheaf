/-
Ordered double integration by parts for the actual selected-block paired frame.
The first integration moves the outer i derivative, and the second moves j;
neither the ordered jets nor the polynomial directions are symmetrized.
-/

import YMGap.Continuum.QPolyHaarPairedAtFrozenBasis
import YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP

namespace YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum pairedDerivative)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt pairedDerivativeAt_zero)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QPolyHaarFrozenChain (threeSum_congr threeSum_mul_left)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (pairedAt_mul)
open YMGap.Continuum.QPolyHaarPairedAtFrozenProduct (pairedAt_add)
open YMGap.Continuum.QPolyHaarPairedAtFrozenBasis (paired_haar_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP
  (gradient sourceInner doubleIBPSource)

local infix:50 " ≈ " => Q'.eqv

private theorem neg_of_sum_zero (a b : Q') (h : a + b ≈ 0) : b ≈ -a := by
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
      (.add (.var 1) (.var 0)) (by decide) (fun n => if n = 0 then b else a)) h

/-- Skew-adjointness of each literal paired direction for arbitrary polynomial
insertions in the original finite product Haar integral. -/
theorem pairedAt_haar_pair {blocks s : Nat} (hs : s < blocks)
    (i : Fin 3) (a b : RatPoly) :
    quaternionHaar blocks (polyMul a (pairedDerivativeAt s i b)) ≈
      -(quaternionHaar blocks (polyMul (pairedDerivativeAt s i a) b)) := by
  apply neg_of_sum_zero
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_append blocks _ _))
    (Q'.eqv_trans _ _ _
      (haar_of_coeff (pairedAt_mul s i a b).symm)
      (paired_haar_zero hs i (polyMul a b)))

/-- The second integration reverses the order of the two differentiations on
the coefficient product. No commutator identity is used. -/
theorem pairedAt_haar_ordered_pair {blocks s : Nat} (hs : s < blocks)
    (i j : Fin 3) (a W : RatPoly) :
    quaternionHaar blocks
      (polyMul a (pairedDerivativeAt s i (pairedDerivativeAt s j W))) ≈
    quaternionHaar blocks
      (polyMul W (pairedDerivativeAt s j (pairedDerivativeAt s i a))) := by
  have hfirst := pairedAt_haar_pair hs i a (pairedDerivativeAt s j W)
  have hsecond := pairedAt_haar_pair hs j (pairedDerivativeAt s i a) W
  exact Q'.eqv_trans _ _ _ hfirst
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hsecond)
      (Q'.eqv_trans _ _ _
        (Q'.neg_neg_eqv _)
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

private theorem haar_three_congr (blocks : Nat) {f g : Fin 3 → RatPoly}
    (h : ∀ i, quaternionHaar blocks (f i) ≈ quaternionHaar blocks (g i)) :
    quaternionHaar blocks (threeSum f) ≈ quaternionHaar blocks (threeSum g) := by
  have ha (v : Fin 3 → RatPoly) :
      quaternionHaar blocks (threeSum v) ≈
        quaternionHaar blocks (v 0) +
          (quaternionHaar blocks (v 1) + quaternionHaar blocks (v 2)) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (quaternionHaar_append blocks _ _))
  exact Q'.eqv_trans _ _ _ (ha f)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (h 0) (Q'.add_eqv_congr' (h 1) (h 2)))
      (Q'.eqv_symm (ha g)))

private theorem pairedAt_threeSum (s : Nat) (j : Fin 3) (f : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (pairedDerivativeAt s j (threeSum f))
      (threeSum (fun i => pairedDerivativeAt s j (f i))) :=
  (pairedAt_add s j (f 0) (polyAdd (f 1) (f 2))).trans
    ((RatPolyCoeffEqv.refl _).add (pairedAt_add s j (f 1) (f 2)))

private theorem threeSum_swap (f : Fin 3 → Fin 3 → RatPoly) :
    RatPolyCoeffEqv (threeSum (fun i => threeSum (fun j => f i j)))
      (threeSum (fun j => threeSum (fun i => f i j))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.add (.var 1) (.var 2)))
      (.add (.add (.var 3) (.add (.var 4) (.var 5)))
        (.add (.var 6) (.add (.var 7) (.var 8)))))
    (.add (.add (.var 0) (.add (.var 3) (.var 6)))
      (.add (.add (.var 1) (.add (.var 4) (.var 7)))
        (.add (.var 2) (.add (.var 5) (.var 8)))))
    (by decide) (fun
      | 0 => f 0 0 | 1 => f 0 1 | 2 => f 0 2
      | 3 => f 1 0 | 4 => f 1 1 | 5 => f 1 2
      | 6 => f 2 0 | 7 => f 2 1 | _ => f 2 2)

/-- The coefficient source preserves its ordered outer-j, inner-i derivative.
The polynomial directions are differentiated only here, after both integrations. -/
def orderedSourceAt (s : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  threeSum (fun j => pairedDerivativeAt s j
    (threeSum (fun i => pairedDerivativeAt s i (polyMul (u i) (u j)))))

/-- Each literal entry of the frozen Hessian moves its two ordered derivatives
onto the coefficient product under the same original Haar functional. -/
theorem frozenSecondAt_haar_ordered_pair {blocks s : Nat} (hs : s < blocks)
    (W : RatPoly) (u : Fin 3 → RatPoly) (i j : Fin 3) :
    quaternionHaar blocks
      (polyMul (polyMul (u i) (u j))
        (pairedDerivativeAt s i (pairedDerivativeAt s j W))) ≈
    quaternionHaar blocks
      (polyMul W (pairedDerivativeAt s j
        (pairedDerivativeAt s i (polyMul (u i) (u j))))) :=
  pairedAt_haar_ordered_pair hs i j (polyMul (u i) (u j)) W

/-- All nine frozen ordered jets integrate to the genuine ordered source.
No support, positivity, or commutation premise is needed. -/
theorem frozenSecondAt_haar_ordered_source {blocks s : Nat} (hs : s < blocks)
    (W : RatPoly) (u : Fin 3 → RatPoly) :
    quaternionHaar blocks (frozenSecondAt s u W) ≈
      quaternionHaar blocks (polyMul W (orderedSourceAt s u)) := by
  let B := fun i j => pairedDerivativeAt s j
    (pairedDerivativeAt s i (polyMul (u i) (u j)))
  have hpair : quaternionHaar blocks (frozenSecondAt s u W) ≈
      quaternionHaar blocks
        (threeSum (fun i => threeSum (fun j => polyMul W (B i j)))) := by
    change quaternionHaar blocks
      (threeSum (fun i => threeSum (fun j =>
        polyMul (polyMul (u i) (u j))
          (pairedDerivativeAt s i (pairedDerivativeAt s j W))))) ≈ _
    exact haar_three_congr blocks (fun i =>
      haar_three_congr blocks (fun j =>
        frozenSecondAt_haar_ordered_pair hs W u i j))
  have hsource : RatPolyCoeffEqv
      (threeSum (fun i => threeSum (fun j => polyMul W (B i j))))
      (polyMul W (orderedSourceAt s u)) := by
    refine (threeSum_swap (fun i j => polyMul W (B i j))).trans ?_
    have hinner (j : Fin 3) : RatPolyCoeffEqv
        (threeSum (fun i => polyMul W (B i j)))
        (polyMul W (pairedDerivativeAt s j
          (threeSum (fun i => pairedDerivativeAt s i (polyMul (u i) (u j)))))) :=
      (threeSum_mul_left W (fun i => B i j)).trans
        ((pairedAt_threeSum s j
          (fun i => pairedDerivativeAt s i (polyMul (u i) (u j)))).symm.mul_left W)
    exact (threeSum_congr hinner).trans
      (threeSum_mul_left W (fun j => pairedDerivativeAt s j
        (threeSum (fun i => pairedDerivativeAt s i (polyMul (u i) (u j))))))
  exact Q'.eqv_trans _ _ _ hpair (haar_of_coeff hsource)

/-- At the head, the selected-block source is the established paired-linear
source, literally with the same ordered derivatives. -/
theorem orderedSourceAt_head (f : RatPoly) :
    orderedSourceAt 0 (fun i => pairedDerivative i f) = doubleIBPSource f := by
  simp only [orderedSourceAt, doubleIBPSource, sourceInner, gradient,
    pairedDerivativeAt_zero]

end YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP

#print axioms YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP.pairedAt_haar_pair
#print axioms YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP.pairedAt_haar_ordered_pair
#print axioms YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP.orderedSourceAt
#print axioms YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP.frozenSecondAt_haar_ordered_pair
#print axioms YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP.frozenSecondAt_haar_ordered_source
#print axioms YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP.orderedSourceAt_head
