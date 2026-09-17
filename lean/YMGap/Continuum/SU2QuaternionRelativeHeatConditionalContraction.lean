/-
# One-link heat contraction with every spectator retained

The original kernel joins blocks zero and one. The input may depend on
block zero and ALL blocks after one, but not on the unused output block
one. Integrating only block zero returns the original output polynomial.
If the input has zero CONDITIONAL head mean, its squared Haar norm contracts
by the same (1-headFloor(w))^2, independently of the number of spectators.

This is the local estimate needed by product-kinetic tensorization. Global
Haar centering is not substituted for conditional centering. Spatial weights
and the physical OS vacuum remain outside this ordinary Haar estimate.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatContraction
import YMGap.Continuum.SU2QuaternionHaarBlockProjection

namespace YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-- Only the integrated input link is removed; all spectators survive. -/
def conditionalHeat (w : Q') (K : Nat) (f : RatPoly) : RatPoly :=
  partialHaarHead (polyMul (relativeHeat w K) f)

theorem conditionalHeat_supported {n : Nat} (hn : 0 < n) (w : Q') (K : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (n+1) f) :
    SupportedQuaternionBlocks n (conditionalHeat w K f) :=
  partialHaarHead_supported (supported_polyMul
    (heat_supported (by omega : 0 < n+1) (by omega : 1 < n+1) w K) hf)

private theorem reversed_heat (w : Q') (K : Nat) :
    RatPolyCoeffEqv (heatAt 1 0 w K) (relativeHeat w K) := by
  have hs : RatPolyCoeffEqv (scalarAt 1 0) relativeScalar := by
    apply RatPolyCoeffEqv.of_canon_termwise
    decide +kernel
  unfold heatAt relativeHeat
  induction List.range (K+1) with
  | nil => exact .refl _
  | cons spin spins ih => exact ((characterPolynomial_coeffEqv hs spin).smul _).add ih

/-- The lower marginal retains arbitrary other links, not just one-link tests. -/
theorem lower_marginal {n : Nat} (hn : 0 < n) (w : Q') (K : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (n+1) f)
    (hd : HasQuaternionBlockDegree 1 0 f) :
    quaternionHaar (n+1) (polyMul (relativeHeat w K) f) ≈ quaternionHaar (n+1) f :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((reversed_heat w K).symm.mul_right f))
    (pair_vacuum n hn ⟨1,by omega⟩ ⟨0,by omega⟩ (by change (1 : Nat) ≠ 0; decide) w K f hf hd)

theorem conditionalHeat_mean {n : Nat} (hn : 0 < n) (w : Q') (K : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (n+1) f)
    (hd : HasQuaternionBlockDegree 1 0 f) :
    quaternionHaar n (conditionalHeat w K f) ≈ quaternionHaar (n+1) f :=
  Q'.eqv_trans _ _ _ (quaternionHaar_partialHaarHeads n 1 _)
    (lower_marginal hn w K hf hd)

/-- The existing all-nome certificate is constructed on the full carrier. -/
def residualCertificate {n : Nat} (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K) :
    Certificate (n+1) (polyAdd (relativeHeat w K) (polyNeg (cap (headFloor w)))) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))
  have hp : Supported (n+1) word :=
    (Supported.coordinate (by omega : 0 < n+1)).mul
      (Supported.coordinate (by omega : 1 < n+1)).conj
  have hu : HaarCarrierEqv (n+1) (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate (by omega : 0 < n+1))
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate (by omega : 1 < n+1)))
  rw [relativeHeat_eq_prefix]
  exact QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1 hp hu K hK

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1))
        (haar_neg n rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem residual_pair (n : Nat) (W p q : RatPoly) (delta : Q') :
    weightedPair n (polyAdd W (polyNeg (cap delta))) p q ≈
      weightedPair n W p q + -(delta * quaternionHaar n (polyMul p q)) := by
  let s := polyMul p q
  have hc : quaternionHaar n (polyMul (cap delta) s) ≈ delta * quaternionHaar n s :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left delta s)) (quaternionHaar_polySmul _ _ _)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 0))))
    (by decide) (fun | 0 => s | 1 => W | _ => cap delta)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ hc))))

private theorem factor_margin (d a : Q') : a + -(d*a) ≈ (1 + -d)*a :=
  poly_identity_of_normal_eq (.add (.var 1) (.neg (.mul (.var 0) (.var 1))))
    (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)) (by decide)
    (fun | 0 => d | _ => a)

/-- Exact pairing of the computed local output, retaining shared spectators. -/
theorem conditionalHeat_pairing (n : Nat) (w : Q') (K : Nat) (f g : RatPoly) :
    weightedPair (n+1) (relativeHeat w K) f (liftBoundary 1 g) ≈
      quaternionHaar n (polyMul (conditionalHeat w K f) g) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
    (fun | 0 => f | 1 => liftBoundary 1 g | _ => relativeHeat w K)))
    (head_pairing n 1 _ g)

/-- Other coordinate steps may be bounded by one, without conditional centering. -/
theorem conditionalHeat_square_contraction {n : Nat} (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (n+1) f)
    (hd : HasQuaternionBlockDegree 1 0 f) :
    quaternionHaar n (polyMul (conditionalHeat w K f) (conditionalHeat w K f)) ≤
      quaternionHaar (n+1) (polyMul f f) := by
  let W := relativeHeat w K
  let g := conditionalHeat w K f
  let G := liftBoundary 1 g
  let A := quaternionHaar n (polyMul g g)
  let F := quaternionHaar (n+1) (polyMul f f)
  have HW : Certificate (n+1) W :=
    .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
      (fun | 0 => W | _ => cap (headFloor w)))
      ((residualCertificate hn hw0 hw1 K hK).add
        (.constant _ (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))))
  have hp : weightedPair (n+1) W f G ≈ A := conditionalHeat_pairing n w K f g
  have hl : weightedPair (n+1) W f f ≈ F :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (lower_marginal hn w K (supported_polyMul hf hf) (hd.mul hd))
  have hr : weightedPair (n+1) W G G ≈ A := by
    change quaternionHaar (n+1) (polyMul (polyMul (liftBoundary 1 g) (liftBoundary 1 g)) W) ≈ _
    rw [← lift_product]
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (heat_vacuum n hn w K _ (lifted_independent (polyMul g g)))
        (haar_liftBoundary 1 n _))
  have hcs := weighted_cauchySchwarz (n+1) W f G HW hf
    (lift_supported (conditionalHeat_supported hn w K hf) 1)
  have hh : A*A ≤ A*F :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hp hp))
      (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (qmul hl hr) (Q'.mul_comm_eqv _ _))))
  change A ≤ F
  by_cases hpos : (0 : Q') < A
  · exact Q'.le_of_mul_le_mul_left hh hpos
  · have hz : A ≤ (0 : Q') := by
      change ¬ ((0 : Int) * (A.den : Int) < A.num * 1) at hpos
      have hn0 : A.num ≤ 0 := by simpa only [Int.zero_mul, Int.mul_one] using Int.not_lt.mp hpos
      change A.num * 1 ≤ (0 : Int) * (A.den : Int)
      simpa only [Int.zero_mul, Int.mul_one] using hn0
    exact Q'.le_trans' _ _ _ hz (Certificate.haar_nonnegative (.square f hf))

/-- Conditional centering kills the constant cross term even with shared spectators. -/
theorem conditionalHeat_centered_pair_bound {n : Nat} (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    {f g : RatPoly} (hf : SupportedQuaternionBlocks (n+1) f)
    (hd : HasQuaternionBlockDegree 1 0 f) (hg : SupportedQuaternionBlocks n g)
    (hc : RatPolyCoeffEqv (partialHaarHead f) polyZero) :
    quaternionHaar n (polyMul (conditionalHeat w K f) g) *
        quaternionHaar n (polyMul (conditionalHeat w K f) g) ≤
      squaredHeatRate w *
        (quaternionHaar (n+1) (polyMul f f) * quaternionHaar n (polyMul g g)) := by
  let W := relativeHeat w K
  let R := polyAdd W (polyNeg (cap (headFloor w)))
  let G := liftBoundary 1 g
  have hp := conditionalHeat_pairing n w K f g
  have hz : quaternionHaar (n+1) (polyMul f G) ≈ 0 :=
    Q'.eqv_trans _ _ _ (head_pairing n 1 f g) (haar_of_coeff (hc.mul_right g))
  have hpR : weightedPair (n+1) R f G ≈ quaternionHaar n (polyMul (conditionalHeat w K f) g) :=
    Q'.eqv_trans _ _ _ (residual_pair _ W f G _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _))))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : -(0 : Q') ≈ 0))
          (Q'.eqv_of_eq (Q'.add_zero' _))))
  have hl : weightedPair (n+1) W f f ≈ quaternionHaar (n+1) (polyMul f f) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (lower_marginal hn w K (supported_polyMul hf hf) (hd.mul hd))
  have hlR : weightedPair (n+1) R f f ≈ heatRate w * quaternionHaar (n+1) (polyMul f f) :=
    Q'.eqv_trans _ _ _ (residual_pair _ W f f _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hl (Q'.eqv_refl _)) (factor_margin _ _))
  have hG : quaternionHaar (n+1) (polyMul G G) ≈ quaternionHaar n (polyMul g g) := by
    change quaternionHaar (n+1) (polyMul (liftBoundary 1 g) (liftBoundary 1 g)) ≈ _
    rw [← lift_product]
    exact haar_liftBoundary 1 n _
  have hr : weightedPair (n+1) W G G ≈ quaternionHaar (n+1) (polyMul G G) := by
    change quaternionHaar (n+1) (polyMul (polyMul (liftBoundary 1 g) (liftBoundary 1 g)) W) ≈ _
    rw [← lift_product]
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (heat_vacuum n hn w K _ (lifted_independent (polyMul g g)))
  have hrR : weightedPair (n+1) R G G ≈ heatRate w * quaternionHaar n (polyMul g g) :=
    Q'.eqv_trans _ _ _ (residual_pair _ W G G _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hr (Q'.eqv_refl _))
        (Q'.eqv_trans _ _ _ (factor_margin _ _) (Q'.mul_eqv_congr_left _ _ _ hG)))
  have hcs := weighted_cauchySchwarz (n+1) R f G
    (residualCertificate hn hw0 hw1 K hK) hf (lift_supported hg 1)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hpR hpR))
    (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (qmul hlR hrR)
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (by decide)
        (fun | 0 => heatRate w | 1 => quaternionHaar (n+1) (polyMul f f)
             | _ => quaternionHaar n (polyMul g g))))))

/-- The original conditional output, with a spectator-count-independent strict rate. -/
theorem conditionalHeat_centered_square_bound {n : Nat} (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (n+1) f)
    (hd : HasQuaternionBlockDegree 1 0 f)
    (hc : RatPolyCoeffEqv (partialHaarHead f) polyZero) :
    quaternionHaar n (polyMul (conditionalHeat w K f) (conditionalHeat w K f)) ≤
      squaredHeatRate w * quaternionHaar (n+1) (polyMul f f) := by
  let A := quaternionHaar n (polyMul (conditionalHeat w K f) (conditionalHeat w K f))
  let F := quaternionHaar (n+1) (polyMul f f)
  have h := conditionalHeat_centered_pair_bound hn hw0 hw1 K hK hf hd
    (conditionalHeat_supported hn w K hf) hc
  change A*A ≤ squaredHeatRate w*(F*A) at h
  change A ≤ squaredHeatRate w*F
  by_cases hpos : (0 : Q') < A
  · exact Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.mul_comm_eqv _ _)))) hpos
  · have hz : A ≤ (0 : Q') := by
      change ¬ ((0 : Int) * (A.den : Int) < A.num * 1) at hpos
      have hn0 : A.num ≤ 0 := by simpa only [Int.zero_mul, Int.mul_one] using Int.not_lt.mp hpos
      change A.num * 1 ≤ (0 : Int) * (A.den : Int)
      simpa only [Int.zero_mul, Int.mul_one] using hn0
    exact Q'.le_trans' _ _ _ hz (Q'.mul_nonneg _ _
      (squaredHeatRate_nonnegative hw0 hw1) (Certificate.haar_nonnegative (.square f hf)))

/-- The conditionally centered input is constructed from the actual polynomial,
not supplied as an unproved centering premise. -/
theorem conditionalHeat_fluctuation_square_bound {n : Nat} (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (n+1) f)
    (hd : HasQuaternionBlockDegree 1 0 f) :
    quaternionHaar n (polyMul
        (conditionalHeat w K (SU2QuaternionHaarBlockProjection.fluctuation 0 f))
        (conditionalHeat w K (SU2QuaternionHaarBlockProjection.fluctuation 0 f))) ≤
      squaredHeatRate w * quaternionHaar (n+1) (polyMul
        (SU2QuaternionHaarBlockProjection.fluctuation 0 f)
        (SU2QuaternionHaarBlockProjection.fluctuation 0 f)) :=
  conditionalHeat_centered_square_bound hn hw0 hw1 K hK
    (SU2QuaternionHaarBlockProjection.fluctuation_supported 0 hf)
    (SU2QuaternionHaarBlockProjection.fluctuation_head_output_independent hd)
    (SU2QuaternionHaarBlockProjection.partialHaarHead_fluctuation_zero f)

end YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.conditionalHeat
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.conditionalHeat_supported
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.lower_marginal
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.conditionalHeat_mean
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.residualCertificate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.conditionalHeat_pairing
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.conditionalHeat_square_contraction
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.conditionalHeat_centered_pair_bound
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.conditionalHeat_centered_square_bound
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction.conditionalHeat_fluctuation_square_bound
