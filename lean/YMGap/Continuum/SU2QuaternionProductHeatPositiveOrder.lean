/-
# Positive-kernel comparison of the SAME kinetic quadratic

For late original heat prefixes, a certificate band 0<=a<=U*A gives
<a,P a><=U^2<A,P A>. This uses positivity preservation of the actual
product kernel, not a false monotonicity assertion for arbitrary signed
quadratic forms. The immediate consumer retains the exterior quadratic
in the original plaquette-response partition.
-/

import YMGap.Continuum.SU2QuaternionProductHeatLocalBand
import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatLocalBand
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Certificate order remains valid under an arbitrary certified insertion. -/
theorem haar_order {n : Nat} {p q r : RatPoly}
    (H : Certificate n (polyAdd q (polyNeg p))) (R : Certificate n r) :
    quaternionHaar n (polyMul p r) ≤ quaternionHaar n (polyMul q r) := by
  have he : quaternionHaar n (polyMul (polyAdd q (polyNeg p)) r) ≈
      quaternionHaar n (polyMul q r) + -(quaternionHaar n (polyMul p r)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 1) (.neg (.var 0))) (.var 2))
      (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => p | 1 => q | _ => r)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg n _)))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (H.mul R).haar_nonnegative (Q'.le_of_eqv he))

/-- The actual late product heat preserves certificate order in each leg. -/
theorem kineticPair_mono_left (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) {p q r : RatPoly}
    (H : Certificate n (polyAdd q (polyNeg p)))
    (hr : SupportedQuaternionBlocks n r) (R : Certificate n r) :
    kineticPair n w K ids p r ≤ kineticPair n w K ids q r :=
  haar_order H (erasedCertificate n hw0 hw1 K hK ids hids hr R)

/-- A positive endpoint band controls the SAME kinetic quadratic; the
reference quadratic is not replaced by the square of a total Haar mass. -/
theorem kineticPair_quadratic_cap (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) {a A : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hA : SupportedQuaternionBlocks n A)
    (CA : Certificate n a) (CR : Certificate n A)
    (U : Q') (hU : (0 : Q') ≤ U)
    (cap : Certificate n (polyAdd (polySmul U A) (polyNeg a))) :
    kineticPair n w K ids a a ≤ (U*U)*kineticPair n w K ids A A := by
  have h1 := kineticPair_mono_left n hw0 hw1 K hK ids hids cap ha CA
  have h2 := kineticPair_mono_left n hw0 hw1 K hK ids hids cap hA CR
  have hleft : kineticPair n w K ids (polySmul U A) a ≈
      U * kineticPair n w K ids a A :=
    Q'.eqv_trans _ _ _ (kineticPair_smul_left n w K ids U A a)
      (Q'.mul_eqv_congr_left _ _ _ (kineticPair_symm n w K ids hids A a hA ha))
  have hright : kineticPair n w K ids (polySmul U A) A ≈
      U * kineticPair n w K ids A A := kineticPair_smul_left n w K ids U A A
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ U
          (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hright)) hU)
        (Q'.ge_of_eqv (Q'.mul_assoc_eqv U U _))))

end YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder

#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder.haar_order
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder.kineticPair_mono_left
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder.kineticPair_quadratic_cap
