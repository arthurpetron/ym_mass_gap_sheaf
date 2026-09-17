/-
# Haar kernel contraction from exact marginals, not a global density cap

A positive polynomial kernel with both Haar marginals equal to one acts
contractively on the original supported Haar polynomials. If W-delta is
certified positive, subtract the constant kernel before Cauchy--Schwarz:
its two marginals are 1-delta, and its pairing on a centered input is the
original pairing. The squared centered norm contracts by (1-delta)^2.

The following module supplies the actual SU(2) relative-heat instance.
These are ordinary Haar-kernel statements. Interacting spatial weights,
tensorization over the actual kinetic layer, and the physical OS comparison
are not premises silently discharged by this argument.
-/

import YMGap.Continuum.SU2QuaternionHaarKernelBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich

namespace YMGap.Continuum.SU2QuaternionHaarMarkovContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (partialHaarHeads_supported_constant)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem support_mono {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) : SupportedQuaternionBlocks (blocks+blocks) f :=
  fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))

/-- Exact product-Haar factorization for the two ordered, supported slots. -/
theorem haar_split_pairing {blocks : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) (g : RatPoly) :
    quaternionHaar (blocks+blocks) (polyMul f (liftBoundary blocks g)) ≈
      quaternionHaar blocks f * quaternionHaar blocks g :=
  Q'.eqv_trans _ _ _ (head_pairing blocks blocks f g)
    (Q'.eqv_trans _ _ _ (haar_of_coeff
      (((partialHaarHeads_supported_constant blocks hf).mul_right g).trans (cap_mul_left _ g)))
      (quaternionHaar_polySmul _ _ _))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem residual_pair (blocks : Nat) (W p q : RatPoly) (delta : Q') :
    weightedPair blocks (polyAdd W (polyNeg (cap delta))) p q ≈
      weightedPair blocks W p q + -(delta * quaternionHaar blocks (polyMul p q)) := by
  let s := polyMul p q
  have hc : quaternionHaar blocks (polyMul (cap delta) s) ≈
      delta * quaternionHaar blocks s :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left delta s)) (quaternionHaar_polySmul _ _ _)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 0))))
    (by decide) (fun | 0 => s | 1 => W | _ => cap delta)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ hc))))

private theorem factor_margin (delta a : Q') : a + -(delta*a) ≈ (1 + -delta)*a :=
  poly_identity_of_normal_eq (.add (.var 1) (.neg (.mul (.var 0) (.var 1))))
    (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)) (by decide)
    (fun | 0 => delta | _ => a)

private theorem norm_of_pairings {blocks : Nat} {W f : RatPoly} {c : Q'}
    (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    (hf : SupportedQuaternionBlocks blocks f) (hc : (0 : Q') ≤ c)
    (h : ∀ g, SupportedQuaternionBlocks blocks g →
      quaternionHaar blocks (polyMul (kernelMap blocks W f) g) *
          quaternionHaar blocks (polyMul (kernelMap blocks W f) g) ≤
        c * (quaternionHaar blocks (polyMul f f) * quaternionHaar blocks (polyMul g g))) :
    quaternionHaar blocks (polyMul (kernelMap blocks W f) (kernelMap blocks W f)) ≤
      c * quaternionHaar blocks (polyMul f f) := by
  let A := quaternionHaar blocks (polyMul (kernelMap blocks W f) (kernelMap blocks W f))
  let F := quaternionHaar blocks (polyMul f f)
  have hh := h _ (kernelMap_supported hW hf)
  change A*A ≤ c*(F*A) at hh
  change A ≤ c*F
  by_cases hpos : (0 : Q') < A
  · exact Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.mul_comm_eqv _ _)))) hpos
  · have hz : A ≤ (0 : Q') := by
      change ¬ ((0 : Int) * (A.den : Int) < A.num * 1) at hpos
      have hn : A.num ≤ 0 := by simpa only [Int.zero_mul, Int.mul_one] using Int.not_lt.mp hpos
      change A.num * 1 ≤ (0 : Int) * (A.den : Int)
      simpa only [Int.zero_mul, Int.mul_one] using hn
    exact Q'.le_trans' _ _ _ hz
      (Q'.mul_nonneg _ _ hc (Certificate.haar_nonnegative (.square f hf)))

section Marginals

variable {blocks : Nat} {W : RatPoly}
  (left : ∀ f, SupportedQuaternionBlocks blocks f →
    quaternionHaar (blocks+blocks) (polyMul W f) ≈ quaternionHaar blocks f)
  (right : ∀ g, SupportedQuaternionBlocks blocks g →
    quaternionHaar (blocks+blocks) (polyMul W (liftBoundary blocks g)) ≈ quaternionHaar blocks g)

include left in
private theorem left_square {f : RatPoly} (hf : SupportedQuaternionBlocks blocks f) :
    weightedPair (blocks+blocks) W f f ≈ quaternionHaar blocks (polyMul f f) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (left _ (supported_polyMul hf hf))

include right in
private theorem right_square {g : RatPoly} (hg : SupportedQuaternionBlocks blocks g) :
    weightedPair (blocks+blocks) W (liftBoundary blocks g) (liftBoundary blocks g) ≈
      quaternionHaar blocks (polyMul g g) := by
  unfold weightedPair
  rw [← lift_product]
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (right _ (supported_polyMul hg hg))

include left right

/-- No density cap or product of per-coordinate caps enters this norm estimate. -/
theorem kernelMap_square_contraction (HW : Certificate (blocks+blocks) W)
    (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    {f : RatPoly} (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks (polyMul (kernelMap blocks W f) (kernelMap blocks W f)) ≤
      quaternionHaar blocks (polyMul f f) := by
  have hb := norm_of_pairings hW hf (by decide : (0 : Q') ≤ 1) (fun g hg => by
    have hp := kernelMap_pairing blocks W f g
    have hcs := weighted_cauchySchwarz (blocks+blocks) W f (liftBoundary blocks g)
      HW (support_mono hf) (lift_supported hg blocks)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hp hp))
      (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (qmul (left_square left hf) (right_square right hg))
          (Q'.eqv_symm (Q'.one_mul_eqv _))))))
  exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- Subtract the constant kernel BEFORE bounding a centered pairing. -/
theorem kernelMap_centered_bilinear_bound {delta : Q'}
    (D : Certificate (blocks+blocks) (polyAdd W (polyNeg (cap delta))))
    {f g : RatPoly} (hf : SupportedQuaternionBlocks blocks f)
    (hg : SupportedQuaternionBlocks blocks g) (hc : quaternionHaar blocks f ≈ 0) :
    quaternionHaar blocks (polyMul (kernelMap blocks W f) g) *
        quaternionHaar blocks (polyMul (kernelMap blocks W f) g) ≤
      ((1 + -delta)*(1 + -delta)) *
        (quaternionHaar blocks (polyMul f f) * quaternionHaar blocks (polyMul g g)) := by
  let R := polyAdd W (polyNeg (cap delta))
  have hzero : quaternionHaar (blocks+blocks) (polyMul f (liftBoundary blocks g)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_split_pairing hf g)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc) (Q'.zero_mul_eqv _))
  have hp : weightedPair (blocks+blocks) R f (liftBoundary blocks g) ≈
      quaternionHaar blocks (polyMul (kernelMap blocks W f) g) :=
    Q'.eqv_trans _ _ _ (residual_pair _ W f _ delta)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (kernelMap_pairing blocks W f g)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left delta _ _ hzero) (Q'.mul_zero_eqv _))))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : -(0 : Q') ≈ 0))
          (Q'.eqv_of_eq (Q'.add_zero' _))))
  have hl : weightedPair (blocks+blocks) R f f ≈
      (1 + -delta)*quaternionHaar blocks (polyMul f f) :=
    Q'.eqv_trans _ _ _ (residual_pair _ W f f delta)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (left_square left hf)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left delta _ _
          (quaternionHaar_extend_supported_endpoint (by omega) _ (supported_polyMul hf hf)))))
        (factor_margin _ _))
  have hlift : quaternionHaar (blocks+blocks)
      (polyMul (liftBoundary blocks g) (liftBoundary blocks g)) ≈
        quaternionHaar blocks (polyMul g g) := by
    rw [← lift_product]
    exact haar_liftBoundary blocks blocks _
  have hr : weightedPair (blocks+blocks) R (liftBoundary blocks g) (liftBoundary blocks g) ≈
      (1 + -delta)*quaternionHaar blocks (polyMul g g) :=
    Q'.eqv_trans _ _ _ (residual_pair _ W _ _ delta)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (right_square right hg)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left delta _ _ hlift))) (factor_margin _ _))
  have hcs := weighted_cauchySchwarz (blocks+blocks) R f (liftBoundary blocks g)
    D (support_mono hf) (lift_supported hg blocks)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hp hp))
    (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (qmul hl hr)
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (by decide)
        (fun | 0 => 1 + -delta | 1 => quaternionHaar blocks (polyMul f f)
             | _ => quaternionHaar blocks (polyMul g g))))))

/-- The SAME computed output, not an auxiliary norm or selected basis. -/
theorem kernelMap_centered_square_bound {delta : Q'} (hd : delta ≤ (1 : Q'))
    (D : Certificate (blocks+blocks) (polyAdd W (polyNeg (cap delta))))
    (hW : SupportedQuaternionBlocks (blocks+blocks) W)
    {f : RatPoly} (hf : SupportedQuaternionBlocks blocks f) (hc : quaternionHaar blocks f ≈ 0) :
    quaternionHaar blocks (polyMul (kernelMap blocks W f) (kernelMap blocks W f)) ≤
      ((1 + -delta)*(1 + -delta))*quaternionHaar blocks (polyMul f f) :=
  norm_of_pairings hW hf
    (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hd) (Q'.sub_nonneg_of_le hd))
    (fun _ hg => kernelMap_centered_bilinear_bound left right D hf hg hc)

end Marginals
end YMGap.Continuum.SU2QuaternionHaarMarkovContraction

#print axioms YMGap.Continuum.SU2QuaternionHaarMarkovContraction.haar_split_pairing
#print axioms YMGap.Continuum.SU2QuaternionHaarMarkovContraction.kernelMap_square_contraction
#print axioms YMGap.Continuum.SU2QuaternionHaarMarkovContraction.kernelMap_centered_bilinear_bound
#print axioms YMGap.Continuum.SU2QuaternionHaarMarkovContraction.kernelMap_centered_square_bound
