/-
# Linear order comparison of original conditional variance determinants

The conditional masses are pinned to one under every surviving Haar insertion,
not by a false free-coefficient equality. One common upper-valued center gives
a square certificate for c*Var_R-Var_P from the actual certificate c*R-P.
No conditional mass, source norm, or variance is inverted. Arbitrary certified
upper weights survive. This does not construct a kernel comparison, an angular
Poincare constant, or a changing-family estimate.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.SU2QuaternionConditionalVarianceOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- The center is a polynomial on the shared surviving variables. -/
def centeredSquare (heads : Nat) (P Q m : RatPoly) : RatPoly :=
  let z := polyAdd Q (polyNeg (liftBoundary heads m))
  partialHaarHeads heads (polyMul P (polyMul z z))

private theorem centered_expand (heads : Nat) (P Q m : RatPoly) :
    RatPolyCoeffEqv (centeredSquare heads P Q m)
      (polyAdd
        (polyAdd
          (polyAdd (partialHaarHeads heads (polyMul P (polyMul Q Q)))
            (polyNeg (polyMul (partialHaarHeads heads (polyMul P Q)) m)))
          (polyNeg (polyMul (partialHaarHeads heads (polyMul P Q)) m)))
        (polyMul (partialHaarHeads heads P) (polyMul m m))) := by
  have he : RatPolyCoeffEqv
      (polyMul P (polyMul (polyAdd Q (polyNeg (liftBoundary heads m)))
        (polyAdd Q (polyNeg (liftBoundary heads m)))))
      (polyAdd
        (polyAdd
          (polyAdd (polyMul P (polyMul Q Q))
            (polyNeg (polyMul (polyMul P Q) (liftBoundary heads m))))
          (polyNeg (polyMul (polyMul P Q) (liftBoundary heads m))))
        (polyMul P (liftBoundary heads (polyMul m m)))) := by
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2)))
        (.add (.var 1) (.neg (.var 2)))))
      (.add (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
        (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
        (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => P | 1 => Q | _ => liftBoundary heads m)
  unfold centeredSquare
  refine (partialHaarHeads_congr heads he).trans ?_
  rw [partialHaarHeads_add, partialHaarHeads_add, partialHaarHeads_add]
  have hc := (partialHaarHeads_neg heads _).trans
    (RatPolyCoeffEqv.neg (partialHaarHeads_mul_lift heads (polyMul P Q) m))
  exact (((RatPolyCoeffEqv.refl _).add hc).add hc).add
    (partialHaarHeads_mul_lift heads P (polyMul m m))

private theorem determinant_unit_pin (tail heads : Nat) (P Q : RatPoly)
    (hunit : HaarCarrierEqv tail (partialHaarHeads heads P) polyOne) :
    HaarCarrierEqv tail (determinant heads P Q)
      (polyAdd (partialHaarHeads heads (polyMul P (polyMul Q Q)))
        (polyNeg (polyMul (partialHaarHeads heads (polyMul P Q))
          (partialHaarHeads heads (polyMul P Q))))) := by
  unfold determinant
  exact HaarCarrierEqv.add
    ((HaarCarrierEqv.mul_right _ hunit).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul _)))
    (HaarCarrierEqv.refl tail _)

/-- Conditional mean minimization, retaining every shared-tail insertion. -/
theorem centered_square_minimization_pin (tail heads : Nat) (P Q m : RatPoly)
    (hunit : HaarCarrierEqv tail (partialHaarHeads heads P) polyOne) :
    HaarCarrierEqv tail (centeredSquare heads P Q m)
      (polyAdd (determinant heads P Q)
        (polyMul (polyAdd (partialHaarHeads heads (polyMul P Q)) (polyNeg m))
          (polyAdd (partialHaarHeads heads (polyMul P Q)) (polyNeg m)))) := by
  let a := partialHaarHeads heads (polyMul P (polyMul Q Q))
  let b := partialHaarHeads heads (polyMul P Q)
  have hm := (HaarCarrierEqv.mul_right (polyMul m m) hunit).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul _))
  have hraw : HaarCarrierEqv tail (centeredSquare heads P Q m)
      (polyAdd (polyAdd (polyAdd a (polyNeg (polyMul b m)))
        (polyNeg (polyMul b m))) (polyMul m m)) :=
    (RatPolyCoeffEqv.haarCarrier (centered_expand heads P Q m)).trans
      (HaarCarrierEqv.add (HaarCarrierEqv.refl tail _) hm)
  have hr := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
      (.neg (.mul (.var 1) (.var 2)))) (.mul (.var 2) (.var 2)))
    (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
      (.mul (.add (.var 1) (.neg (.var 2)))
        (.add (.var 1) (.neg (.var 2)))))
    (by decide) (fun | 0 => a | 1 => b | _ => m)
  exact (hraw.trans (RatPolyCoeffEqv.haarCarrier hr)).trans
    (HaarCarrierEqv.add (determinant_unit_pin tail heads P Q hunit).symm
      (HaarCarrierEqv.refl tail _))

private theorem center_at_mean (tail heads : Nat) (R Q : RatPoly)
    (hunit : HaarCarrierEqv tail (partialHaarHeads heads R) polyOne) :
    HaarCarrierEqv tail
      (centeredSquare heads R Q (partialHaarHeads heads (polyMul R Q)))
      (determinant heads R Q) :=
  (centered_square_minimization_pin tail heads R Q _ hunit).trans
    (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.mul (.add (.var 1) (.neg (.var 1)))
        (.add (.var 1) (.neg (.var 1))))) (.var 0) (by decide)
      (fun | 0 => determinant heads R Q | _ => partialHaarHeads heads (polyMul R Q))))

/-- Actual kernel order gives a LINEAR variance factor. The only positive
input is c*R-P; no source sign or conditional normalizer inverse is used. -/
def conditional_variance_order_certificate (tail heads : Nat) (P R Q : RatPoly)
    (c : Q')
    (hP : SupportedQuaternionBlocks (tail+heads) P)
    (hR : SupportedQuaternionBlocks (tail+heads) R)
    (hQ : SupportedQuaternionBlocks (tail+heads) Q)
    (unitP : HaarCarrierEqv tail (partialHaarHeads heads P) polyOne)
    (unitR : HaarCarrierEqv tail (partialHaarHeads heads R) polyOne)
    (Order : Certificate (tail+heads) (polyAdd (polySmul c R) (polyNeg P))) :
    Certificate tail (polyAdd (polySmul c (determinant heads R Q))
      (polyNeg (determinant heads P Q))) := by
  let m := partialHaarHeads heads (polyMul R Q)
  let v := partialHaarHeads heads (polyMul P Q)
  let z := polyAdd Q (polyNeg (liftBoundary heads m))
  let e := polyAdd v (polyNeg m)
  have hm := partialHaarHeads_supported tail heads _ (supported_polyMul hR hQ)
  have hv := partialHaarHeads_supported tail heads _ (supported_polyMul hP hQ)
  have hz : SupportedQuaternionBlocks (tail+heads) z :=
    supported_add hQ (supported_neg (lift_supported hm heads))
  have he : SupportedQuaternionBlocks tail e := supported_add hv (supported_neg hm)
  have Pos := partialHaarHeads_certificate tail heads (Order.mul (.square z hz))
  have hex : RatPolyCoeffEqv
      (polyMul (polyAdd (polySmul c R) (polyNeg P)) (polyMul z z))
      (polyAdd (polySmul c (polyMul R (polyMul z z)))
        (polyNeg (polyMul P (polyMul z z)))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => polySmul c R | 1 => polyNeg P | _ => polyMul z z)).trans
      ((RatPolyCoeffEqv.polyMul_smul_left c R (polyMul z z)).add
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
          (by decide) (fun | 0 => P | _ => polyMul z z)))
  have hlin := (partialHaarHeads_congr heads hex).trans (by
    rw [partialHaarHeads_add]
    exact (partialHaarHeads_smul heads c _).add (partialHaarHeads_neg heads _))
  have hr := center_at_mean tail heads R Q unitR
  have hp := centered_square_minimization_pin tail heads P Q m unitP
  have hsum : HaarCarrierEqv tail
      (polyAdd (partialHaarHeads heads
        (polyMul (polyAdd (polySmul c R) (polyNeg P)) (polyMul z z)))
        (polyMul e e))
      (polyAdd (polySmul c (determinant heads R Q))
        (polyNeg (determinant heads P Q))) := by
    refine (HaarCarrierEqv.add
      ((RatPolyCoeffEqv.haarCarrier hlin).trans
        (HaarCarrierEqv.add (HaarCarrierEqv.smul c hr) (HaarCarrierEqv.neg hp)))
      (HaarCarrierEqv.refl tail _)).trans ?_
    exact RatPolyCoeffEqv.haarCarrier
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.neg (.add (.var 1) (.var 2)))) (.var 2))
        (.add (.var 0) (.neg (.var 1))) (by decide)
        (fun | 0 => polySmul c (determinant heads R Q)
             | 1 => determinant heads P Q | _ => polyMul e e)))
  exact .transport hsum.symm (Pos.add (.square e he))

/-- Every certified output weight is retained in the variance comparison. -/
theorem conditional_variance_order_weighted (tail heads : Nat) (P R Q W : RatPoly)
    (c : Q')
    (hP : SupportedQuaternionBlocks (tail+heads) P)
    (hR : SupportedQuaternionBlocks (tail+heads) R)
    (hQ : SupportedQuaternionBlocks (tail+heads) Q)
    (unitP : HaarCarrierEqv tail (partialHaarHeads heads P) polyOne)
    (unitR : HaarCarrierEqv tail (partialHaarHeads heads R) polyOne)
    (Order : Certificate (tail+heads) (polyAdd (polySmul c R) (polyNeg P)))
    (PW : Certificate tail W) :
    quaternionHaar tail (polyMul W (determinant heads P Q)) ≤
      c*quaternionHaar tail (polyMul W (determinant heads R Q)) := by
  have hpos := (PW.mul
    (conditional_variance_order_certificate tail heads P R Q c hP hR hQ
      unitP unitR Order)).haar_nonnegative
  have he := ((RatPolyCoeffEqv.mul_add_right W
      (polySmul c (determinant heads R Q)) (polyNeg (determinant heads P Q))).trans
    ((RatPolyCoeffEqv.polyMul_smul_right c W (determinant heads R Q)).add
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => W | _ => determinant heads P Q))))
  have hi := Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append tail _ _)
      (Q'.add_eqv_congr'
        (quaternionHaar_polySmul tail c _)
        (haar_neg tail _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv hi))

end YMGap.Continuum.SU2QuaternionConditionalVarianceOrder

#print axioms YMGap.Continuum.SU2QuaternionConditionalVarianceOrder.centeredSquare
#print axioms YMGap.Continuum.SU2QuaternionConditionalVarianceOrder.centered_square_minimization_pin
#print axioms YMGap.Continuum.SU2QuaternionConditionalVarianceOrder.conditional_variance_order_certificate
#print axioms YMGap.Continuum.SU2QuaternionConditionalVarianceOrder.conditional_variance_order_weighted
