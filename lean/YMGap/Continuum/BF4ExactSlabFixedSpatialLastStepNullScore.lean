/-
# Actual transmitted Haar-null sources have zero direct score and signed bulk

Tangential differentiation preserves equality under EVERY original Haar
insertion. Thus a null actual transmitted numerator has zero direct score,
even when the incoming full conditional noise is positive. The two signed
Taylor terms vanish through their fixed null tests, without any assertion of
linearity or congruence for the adaptive cyclic degree tree.

This is finite exact-source cancellation. No AF budget, changing-action map,
completed OS comparison, continuum survival or Clay closure is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.BF4ExactSlabFixedSpatialNoiseSurvivalObstruction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNullScore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr_lt finSum_zero_seq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt (angularDerivative_carrier_at)
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_congr)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabWidthOneGeometry (baseLinks_length)
open YMGap.Continuum.BF4ExactSlabFixedSpatialNoiseSurvivalObstruction
  (originSource originSource_supported origin_transmitted_pair_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio (blockConditionalRatio blockReciprocal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget (exactScoreAngularBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost (exactScoreSignedBulk)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection (spatialFringeMass)
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion (branchDegrees nextPiece)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (leafSum pairRemainder)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage spatialWeight kineticWeight
  weightedMass blockReciprocal spatialFringeMass projectedEndpointSource originalBlockTransfer

private theorem null_mul {blocks : Nat} {p : RatPoly}
    (factor : RatPoly) (h : HaarCarrierEqv blocks p polyZero) :
    HaarCarrierEqv blocks (polyMul factor p) polyZero :=
  (h.mul_left factor).trans (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right factor))

private theorem null_insert {blocks : Nat} {p : RatPoly}
    (h : HaarCarrierEqv blocks p polyZero) (test : RatPoly) :
    quaternionHaar blocks (polyMul test p) ≈ 0 :=
  Q'.eqv_trans _ _ _ (h test)
    (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right test))

private theorem derivative_zero (i j : Nat) :
    RatPolyCoeffEqv (angularDerivative i j polyZero) polyZero :=
  (angularDerivative_congr i j (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
    ((angularDerivative_smul i j 0 polyOne).trans (RatPolyCoeffEqv.zero_smul _))

private theorem score_null {blocks block i j : Nat} {b : RatPoly}
    (hblock : block < blocks) (hi : i < 4) (hj : j < 4)
    (A : RatPoly) (hb : HaarCarrierEqv blocks b polyZero) :
    HaarCarrierEqv blocks (conditionalScore (4*block+i) (4*block+j) A b) polyZero := by
  have hd := (angularDerivative_carrier_at hblock hi hj hb).trans
    (RatPolyCoeffEqv.haarCarrier (derivative_zero (4*block+i) (4*block+j)))
  have hleft := null_mul A hd
  have hright := (RatPolyCoeffEqv.haarCarrier
    (RatPolyCoeffEqv.mul_comm b (angularDerivative (4*block+i) (4*block+j) A))).trans
    (null_mul (angularDerivative (4*block+i) (4*block+j) A) hb)
  exact HaarCarrierEqv.add hleft (HaarCarrierEqv.neg hright)

private theorem qListSum_map_null {X : Type} (f : X → Q') : ∀ xs : List X,
    (∀ x, x ∈ xs → f x ≈ 0) → qListSum (xs.map f) ≈ 0
  | [], _ => Q'.eqv_refl 0
  | x::xs, h => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (h x List.mem_cons_self)
        (qListSum_map_null f xs (fun y hy => h y (List.mem_cons_of_mem x hy))))
      (Q'.eqv_refl 0)

private theorem leafSum_test_null (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (weight : List Nat → Q'), HaarCarrierEqv (tail+1) test polyZero →
    leafSum tail m p test weight ≈ 0
  | 0, p, test, weight, ht => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (weight []) _ _
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm test p))
          (null_insert ht p))) (Q'.mul_zero_eqv _)
  | m+1, p, test, weight, ht => by
      unfold leafSum
      exact qListSum_map_null _ (branchDegrees tail p) (fun d _ =>
        leafSum_test_null tail m (nextPiece tail p d) test (fun ds => weight (d::ds)) ht)

private theorem pairRemainder_test_null (tail : Nat) (w : Q') (K : Nat)
    (p test : RatPoly) (ht : HaarCarrierEqv (tail+1) test polyZero) :
    pairRemainder tail w K p test ≈ 0 :=
  leafSum_test_null tail (tail+1) p test _ ht

/-- The literal direct-score angular budget vanishes when the ACTUAL original
transmitted numerator is zero under every Haar insertion. No zero-bulk input. -/
theorem exactScoreAngularBudget_zero (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (_hN : 0 < N width)
    (psi : RatPoly) (k : Nat)
    (hb : HaarCarrierEqv (N width)
      (originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi))
      polyZero) :
    exactScoreAngularBudget sigma hw0 hw1 K width hK n r psi k ≈ 0 := by
  unfold exactScoreAngularBudget
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr_lt _ (fun _ => 0) (N width) ?_)
    (Q'.eqv_of_eq (finSum_zero_seq (N width)))
  intro s hs
  split
  · rename_i hactive
    refine Q'.eqv_trans _ _ _ (sixValue_congr _ (fun _ _ => 0) ?_) ?_
    · intro i j hi hj
      have hS := score_null (activeBlocks_lt width s hactive) hi hj
        (terminalMessage w K width (n+(r+1))) hb
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (1+sigma) _ _
          (null_insert (null_mul _ hS) _)) (Q'.mul_zero_eqv _)
    · change sixValue (fun _ _ => (0 : Q')) ≈ 0
      decide
  · exact Q'.eqv_refl 0

/-- BOTH signed Taylor terms vanish through their null test polynomials.
The adaptive source expansion is retained literally; no new heat/gap premise. -/
theorem exactScoreSignedBulk_zero (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    (psi : RatPoly) (k : Nat)
    (hb : HaarCarrierEqv (N width)
      (originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi))
      polyZero) :
    exactScoreSignedBulk sigma hw0 hw1 K width hK n r psi k ≈ 0 := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  have hphi : HaarCarrierEqv (N width) phi polyZero :=
    null_mul (blockReciprocal hw0 hw1 K width hhead n (r+1) k) hb
  have hn : N width-1+1 = N width := Nat.sub_add_cancel hN
  have ht1 : HaarCarrierEqv (N width-1+1) (polyMul q (polyMul phi phi)) polyZero := by
    rw [hn]
    exact null_mul q (null_mul phi hphi)
  have ht2 : HaarCarrierEqv (N width-1+1) (polyMul q phi) polyZero := by
    rw [hn]
    exact null_mul q hphi
  have hR1 := pairRemainder_test_null (N width-1) w K q _ ht1
  have hR2 := pairRemainder_test_null (N width-1) w K (polyMul q phi) _ ht2
  have hangular := exactScoreAngularBudget_zero sigma hw0 hw1 K width hK n r hN psi k hb
  unfold exactScoreSignedBulk
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (1-w) _ _ hangular) (Q'.mul_zero_eqv _))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hR1 (Q'.neg_eqv_congr _ _ hR2))
          (by decide : (0 : Q') + -(0 : Q') ≈ 0))))
    (Q'.mul_zero_eqv _)

/-- The SAME original width-one source from the full-noise obstruction is
annihilated under every insertion, not merely at its unweighted mean. -/
theorem origin_transmitted_null (w : Q') (K : Nat) (hK1 : 1 ≤ K) (n : Nat) :
    HaarCarrierEqv (N 1)
      (originalBlockTransfer w K 1 1 (polyMul (terminalMessage w K 1 n) (originSource w)))
      polyZero := by
  unfold originalBlockTransfer
  change HaarCarrierEqv (N 1)
    (transferStep w K 1 (polyMul (terminalMessage w K 1 n) (originSource w))) polyZero
  apply carrier_of_supported
    (transferStep_supported w K 1
      (supported_polyMul (terminalMessage_supported w K 1 n) (originSource_supported w)))
    (by intro term ht; contradiction)
  intro p hp
  exact Q'.eqv_trans _ _ _ (origin_transmitted_pair_zero w K hK1 n hp)
    (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right p)))

/-- Positive full historical noise does not prevent the literal direct score
from vanishing for the original inactive origin-face source. -/
theorem origin_exactScoreAngularBudget_zero (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K : Nat)
    (hK : relativeCutoff w 32 ≤ K) (hK1 : 1 ≤ K) (n k : Nat) :
    exactScoreAngularBudget sigma hw0 hw1 K 1 hK n 0 (originSource w) k ≈ 0 := by
  have hN : 0 < N 1 := by rw [baseLinks_length]; decide
  exact exactScoreAngularBudget_zero sigma hw0 hw1 K 1 hK n 0 hN
    (originSource w) k (origin_transmitted_null w K hK1 n)

/-- Both original signed remainder terms vanish on this SAME source too.
The full-noise no-go is therefore not a no-go for the actual signed bulk. -/
theorem origin_exactScoreSignedBulk_zero (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K : Nat)
    (hK : relativeCutoff w 32 ≤ K) (hK1 : 1 ≤ K) (n k : Nat) :
    exactScoreSignedBulk sigma hw0 hw1 K 1 hK n 0 (originSource w) k ≈ 0 := by
  have hN : 0 < N 1 := by rw [baseLinks_length]; decide
  exact exactScoreSignedBulk_zero sigma hw0 hw1 K 1 hK n 0 hN
    (originSource w) k (origin_transmitted_null w K hK1 n)

#print axioms null_mul
#print axioms null_insert
#print axioms derivative_zero
#print axioms score_null
#print axioms qListSum_map_null
#print axioms leafSum_test_null
#print axioms pairRemainder_test_null
#print axioms exactScoreAngularBudget_zero
#print axioms exactScoreSignedBulk_zero
#print axioms origin_transmitted_null
#print axioms origin_exactScoreAngularBudget_zero
#print axioms origin_exactScoreSignedBulk_zero

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNullScore
