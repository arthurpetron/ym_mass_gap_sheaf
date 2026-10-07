/-
# Constant-shift cancellation before estimating the signed Taylor remainder

The SAME full product heat and source are kept. The jump energy and angular
energy are invariant under f -> f-c, hence so is their exact signed Taylor
remainder difference. This holds for every nome and cutoff, without positivity.

Under the existing scalar cutoff guard, the mixed budget can be evaluated at
the shifted observable while the favorable diagonal remainder is RETAINED.
Diagonal positivity also permits a weaker mixed-only ceiling. Neither claims
centering decreases the budget or makes it small on an AF family. Existing
centered square-completion bounds remain valid.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceCentering
import YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare

namespace YMGap.Continuum.SU2QuaternionCenteredSignedRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap productHeat_supported)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatSourceCentering (jump_shifted)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare (blockSquare_shifted)

local infix:50 " ≈ " => Q'.eqv

private theorem jump_energy (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (edgeWeight n w K ids q) (jump n f) (jump n f) ≈
      (2 : Q')*sourceEnergy n w K ids q f := by
  have hm : marginalPair n w K ids q f f ≈
      sourceMoment n w K ids q (polyMul f f) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
      (by decide) (fun | 0 => q | 1 => productMap n w K ids q | _ => f))
  exact Q'.eqv_trans _ _ _ (full_jump_pairing n w K ids hids hq hf hf)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' hm (Q'.eqv_refl _)))

/-- Constant shifts preserve the full source energy on ANY selected heat list.
No source stationarity, nonzero observable, or positivity is assumed. -/
theorem sourceEnergy_shifted (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) (c : Q') :
    sourceEnergy n w K ids q (shifted f c) ≈ sourceEnergy n w K ids q f := by
  have hs := shifted_supported hf c
  let W := edgeWeight n w K ids q
  have hq2 : SupportedQuaternionBlocks (n+n) q :=
    fun t ht => Nat.le_trans (hq t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))
  have hW : SupportedQuaternionBlocks (n+n) W :=
    supported_polyMul (supported_polyMul (productHeat_supported n w K ids hids) hq2)
      (lift_supported hq n)
  have hj := jump_shifted n f c
  have hboth := hj.mul hj
  have hpair : weightedPair (n+n) W (jump n (shifted f c)) (jump n (shifted f c)) ≈
      weightedPair (n+n) W (jump n f) (jump n f) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ W))
      (Q'.eqv_trans _ _ _
        (hboth.haar_insert (supported_polyMul (jump_supported hs) (jump_supported hs))
          (supported_polyMul (jump_supported hf) (jump_supported hf)) W hW)
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm W _)))
  have h2 := Q'.eqv_trans _ _ _ (Q'.eqv_symm (jump_energy n w K ids hids hq hs))
    (Q'.eqv_trans _ _ _ hpair (jump_energy n w K ids hids hq hf))
  let half := Q'.mkPos 1 2 (by decide)
  have hhalf : half*(2 : Q') ≈ 1 := by decide
  have half_two (a : Q') : half*((2 : Q')*a) ≈ a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half 2 a))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a hhalf) (Q'.one_mul_eqv a))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (half_two _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ h2) (half_two _))

/-- The literal source-square angular weight stays fixed; only derivatives
of the shifted observable occur, and those are unchanged. -/
theorem weightedAngularEnergy_shifted (tail : Nat) (q f : RatPoly) (c : Q') :
    weightedAngularEnergy tail q (shifted f c) ≈ weightedAngularEnergy tail q f := by
  unfold weightedAngularEnergy
  exact finSum_eqv_congr_lt _ _ (tail+1) (fun i _ =>
    haar_of_coeff ((blockSquare_shifted i f c).mul_left _))

/-- The TWO signed Taylor terms must be combined before any absolute bound.
Their difference, not either term individually, is exactly shift invariant. -/
theorem signedRemainder_shifted (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) (c : Q') :
    pairRemainder tail w K q (polyMul q (polyMul (shifted f c) (shifted f c))) +
      -(pairRemainder tail w K (polyMul q (shifted f c)) (polyMul q (shifted f c))) ≈
    pairRemainder tail w K q (polyMul q (polyMul f f)) +
      -(pairRemainder tail w K (polyMul q f) (polyMul q f)) := by
  have he := sourceEnergy_shifted (tail+1) w K (List.range (tail+1))
    (fun _ hi => List.mem_range.mp hi) hq hf c
  have ht := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (sourceEnergy_taylor_angular tail w K q (shifted f c) hq
      (shifted_supported hf c)))
    (Q'.eqv_trans _ _ _ he (sourceEnergy_taylor_angular tail w K q f hq hf))
  have ha := Q'.mul_eqv_congr_left ((1 : Q')-w) _ _
    (weightedAngularEnergy_shifted tail q f c)
  have hsum := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_eqv_congr' ha (Q'.eqv_refl _))) ht
  have cancel (a b : Q') : (a+b)+(-a) ≈ b :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => a | _ => b)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (cancel _ _))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hsum (Q'.eqv_refl _)) (cancel _ _))

/-- Estimate only the centered mixed term; KEEP the favorable diagonal
remainder. No variance/source-weight identification is used. -/
theorem signedRemainder_le_centered_mixed_minus_diagonal (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < 1) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) (c : Q') :
    pairRemainder tail w K q (polyMul q (polyMul f f)) +
      -(pairRemainder tail w K (polyMul q f) (polyMul q f)) ≤
      (((1 : Q')-w)*((1 : Q')-w))*
        pairBudget tail q (polyMul q (polyMul (shifted f c) (shifted f c))) +
      -(pairRemainder tail w K (polyMul q (shifted f c)) (polyMul q (shifted f c))) :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (signedRemainder_shifted tail w K q f hq hf c))
    (Q'.add_le_add_right _ _ _ (pairRemainder_le_quadratic tail hw0 hw1 K hK q
      (polyMul q (polyMul (shifted f c) (shifted f c)))))

/-- An explicit rational center may now be chosen BEFORE estimating.
Diagonal positivity removes the second budget; no sign is assigned to the
remaining mixed term and no budget-minimization property is asserted. -/
theorem signedRemainder_le_centered_mixed (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < 1) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) (c : Q') :
    pairRemainder tail w K q (polyMul q (polyMul f f)) +
      -(pairRemainder tail w K (polyMul q f) (polyMul q f)) ≤
      (((1 : Q')-w)*((1 : Q')-w))*
        pairBudget tail q (polyMul q (polyMul (shifted f c) (shifted f c))) := by
  have hs := shifted_supported hf c
  have hr := Q'.add_le_add_left
    ((((1 : Q')-w)*((1 : Q')-w))*
      pairBudget tail q (polyMul q (polyMul (shifted f c) (shifted f c)))) _ _
    (Q'.neg_le_neg (pairRemainder_diagonal_nonnegative tail hw0 hw1 K hK
      (polyMul q (shifted f c)) (supported_polyMul hq hs)))
  have hz (a : Q') : a+(-(0 : Q')) ≈ a :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0))) (.var 0)
      (by decide) (fun _ => a)
  exact Q'.le_trans' _ _ _
    (signedRemainder_le_centered_mixed_minus_diagonal tail hw0 hw1 K hK q f hq hf c)
    (Q'.le_trans' _ _ _ hr (Q'.le_of_eqv (hz _)))

end YMGap.Continuum.SU2QuaternionCenteredSignedRemainder

#print axioms YMGap.Continuum.SU2QuaternionCenteredSignedRemainder.sourceEnergy_shifted
#print axioms YMGap.Continuum.SU2QuaternionCenteredSignedRemainder.weightedAngularEnergy_shifted
#print axioms YMGap.Continuum.SU2QuaternionCenteredSignedRemainder.signedRemainder_shifted
#print axioms YMGap.Continuum.SU2QuaternionCenteredSignedRemainder.signedRemainder_le_centered_mixed_minus_diagonal
#print axioms YMGap.Continuum.SU2QuaternionCenteredSignedRemainder.signedRemainder_le_centered_mixed
