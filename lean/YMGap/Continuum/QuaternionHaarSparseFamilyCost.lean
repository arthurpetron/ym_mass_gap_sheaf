/-
# Sparse finite-family cost under one original normalized Haar weight

The literal finite sum square is exactly its ordered Gram sum. Positivity
supplies near-pair Young bounds; exact off-interference cancellation supplies
the far pairs. The existing rational sparse Gram theorem then charges only
the finite overlap degree, not the full family size, against diagonal costs.
The physical consumer must construct its interference and zero cross moments.
-/

import YMGap.Continuum.QuaternionHaarCenteredResponse
import YMGap.Continuum.RationalFiniteSparseGram

namespace YMGap.Continuum.QuaternionHaarSparseFamilyCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarCenteredResponse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.RationalFiniteSparseGram

local infix:50 " ≈ " => Q'.eqv

theorem normalized_zero {blocks : Nat} {W : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) :
    normalizedMoment blocks W polyZero hW ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right W))) (Q'.zero_mul_eqv _)

/-- Exact normalized finite-sum linearity, with all multiplicities retained. -/
theorem normalized_sum {Index : Type} {blocks : Nat} {W : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) (f : Index → RatPoly) : ∀ xs : List Index,
    normalizedMoment blocks W (finitePolySum f xs) hW ≈
      listQSum (fun i => normalizedMoment blocks W (f i) hW) xs
  | [] => normalized_zero hW
  | _ :: xs => Q'.eqv_trans _ _ _ (normalizedMoment_add hW)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (normalized_sum hW f xs))

private theorem pair_sum_left {Index : Type} {blocks : Nat} {W : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) (f : Index → RatPoly) (p : RatPoly) :
    ∀ xs : List Index,
    normalizedMoment blocks W (polyMul (finitePolySum f xs) p) hW ≈
      listQSum (fun i => normalizedMoment blocks W (polyMul (f i) p) hW) xs
  | [] => normalized_zero hW
  | i :: xs => Q'.eqv_trans _ _ _
      (normalizedMoment_congr hW hW (RatPolyCoeffEqv.refl W)
        (by rw [finitePolySum, polyMul_add_left_exact]; exact RatPolyCoeffEqv.refl _))
      (Q'.eqv_trans _ _ _ (normalizedMoment_add hW)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (pair_sum_left hW f p xs)))

/-- No diagonal approximation: all signed pairs are present in the ordered sum. -/
theorem normalized_sum_square {Index : Type} {blocks : Nat} {W : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) (f : Index → RatPoly) (xs : List Index) :
    normalizedMoment blocks W (polyMul (finitePolySum f xs) (finitePolySum f xs)) hW ≈
      listQSum (fun i => listQSum (fun j => normalizedMoment blocks W (polyMul (f i) (f j)) hW) xs) xs := by
  exact Q'.eqv_trans _ _ _ (pair_sum_left hW f (finitePolySum f xs) xs)
    (listQSum_congr (fun i => Q'.eqv_trans _ _ _ (normalizedMoment_mul_symm hW)
      (Q'.eqv_trans _ _ _ (pair_sum_left hW f (f i) xs)
        (listQSum_congr (fun _ => normalizedMoment_mul_symm hW) xs))) xs)

theorem normalized_square_nonnegative {blocks : Nat} {W p : RatPoly}
    (H : Certificate blocks W) (hW : (0 : Q') < quaternionHaar blocks W)
    (hp : SupportedQuaternionBlocks blocks p) :
    (0 : Q') ≤ normalizedMoment blocks W (polyMul p p) hW :=
  Q'.mul_nonneg _ _
    (Q'.le_trans' _ _ _ (H.square_insertion_nonnegative p hp)
      (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul p p) W))))
    (Q'.le_of_lt (Q'.recipPos_pos _ hW))

private theorem normalized_pair_young {blocks : Nat} {W p q : RatPoly}
    (H : Certificate blocks W) (hW : (0 : Q') < quaternionHaar blocks W)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    2 * normalizedMoment blocks W (polyMul p q) hW ≤
      (1 : Q') * (normalizedMoment blocks W (polyMul p p) hW + normalizedMoment blocks W (polyMul q q) hW) :=
  weighted_young Q'.zero_le_one (normalized_square_nonnegative H hW hp)
    (normalized_square_nonnegative H hW hq)
    (Q'.le_trans' _ _ _ (normalized_cauchySchwarz H hW hp hq)
      (Q'.ge_of_eqv (Q'.one_mul_eqv _)))

/-- A bounded overlap degree controls the actual normalized sum-square by
the sum of its actual diagonal costs. Far pairs vanish exactly. -/
theorem sparse_family_cost {Index : Type} {blocks : Nat} {W : RatPoly}
    (H : Certificate blocks W) (hW : (0 : Q') < quaternionHaar blocks W)
    (f : Index → RatPoly) (xs : List Index) (near : Index → Index → Prop) [DecidableRel near]
    (C : Nat) (hf : ∀ i, i ∈ xs → SupportedQuaternionBlocks blocks (f i))
    (hsym : ∀ i, i ∈ xs → ∀ j, j ∈ xs → (near i j ↔ near j i))
    (hrow : ∀ i, i ∈ xs → (xs.filter (fun j => decide (near i j))).length ≤ C)
    (hfar : ∀ i, i ∈ xs → ∀ j, j ∈ xs → ¬ near i j →
      quaternionHaar blocks (polyMul (polyMul (f i) (f j)) W) ≈ 0) :
    normalizedMoment blocks W (polyMul (finitePolySum f xs) (finitePolySum f xs)) hW ≤
      Q'.ofNat C * listQSum (fun i => normalizedMoment blocks W (polyMul (f i) (f i)) hW) xs := by
  let b := fun i => normalizedMoment blocks W (polyMul (f i) (f i)) hW
  let g := fun i j => normalizedMoment blocks W (polyMul (f i) (f j)) hW
  have hpair : ∀ i, i ∈ xs → ∀ j, j ∈ xs →
      2*g i j ≤ (if near i j then 1 else (0 : Q'))*(b i+b j) := by
    intro i hi j hj
    by_cases hn : near i j
    · rw [if_pos hn]
      exact normalized_pair_young H hW (hf i hi) (hf j hj)
    · rw [if_neg hn]
      have hz : g i j ≈ 0 := Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_comm W _)) (hfar i hi j hj hn))) (Q'.zero_mul_eqv _)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ hz) (Q'.mul_zero_eqv 2)))
        (Q'.ge_of_eqv (Q'.zero_mul_eqv _))
  have h := sparse_gram_bound xs near C 0 b g (Q'.le_refl' _)
    (fun i hi => normalized_square_nonnegative H hW (hf i hi)) hsym hrow hpair
  have hc : Q'.ofNat C + 0*Q'.ofNat xs.length ≈ Q'.ofNat C :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.zero_mul_eqv _))
      (Q'.eqv_of_eq (Q'.add_zero' _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (normalized_sum_square hW f xs))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hc)))

end YMGap.Continuum.QuaternionHaarSparseFamilyCost

#print axioms YMGap.Continuum.QuaternionHaarSparseFamilyCost.normalized_zero
#print axioms YMGap.Continuum.QuaternionHaarSparseFamilyCost.normalized_sum
#print axioms YMGap.Continuum.QuaternionHaarSparseFamilyCost.normalized_sum_square
#print axioms YMGap.Continuum.QuaternionHaarSparseFamilyCost.normalized_square_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarSparseFamilyCost.sparse_family_cost
