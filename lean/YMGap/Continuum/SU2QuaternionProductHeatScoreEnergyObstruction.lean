/-
# Zero kernel-score responses do not control temporal jump energy

On the actual one-link SU(2) product kernel, use the flat positive endpoint
source and a nonconstant coordinate test. Every lower one-end angular score
is zero, whereas the SAME normalized squared temporal jump is positive.
The heat cutoff may be arbitrarily late and satisfies the score theorem's
own onset. No finite scalar reverses this degeneracy.

This refutes a universal score-to-energy domination for the admissible source
class. It does not refute a physical Wilson-specific estimate, Yang--Mills,
or the preceding (valid, opposite-direction) score/variance theorem.
-/

import YMGap.Continuum.SU2QuaternionProductHeatScoreSource
import YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor
import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy

namespace YMGap.Continuum.SU2QuaternionProductHeatScoreEnergyObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
open YMGap.Continuum.SU2QuaternionProductHeatScoreSource
open YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (certified_floor)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor)

local infix:50 " ≈ " => Q'.eqv

def probe : RatPoly := polyVar 0
def sourcePair : RatPoly := polyMul polyOne (liftBoundary 1 polyOne)
def kernel (w : Q') (K : Nat) : RatPoly := productHeat 1 w K [0]
def mass (w : Q') (K : Nat) : Q' :=
  quaternionHaar 2 (polyMul sourcePair (kernel w K))
def jumpEnergy (w : Q') (K : Nat) : Q' :=
  quaternionHaar 2 (polyMul sourcePair
    (polyMul (kernel w K) (polyMul (jump 1 probe) (jump 1 probe))))
def score (terms : List (AngularTerm 1)) (w : Q') (K : Nat) : Q' :=
  quaternionHaar 2 (polyMul sourcePair
    (polyMul (signedAngularDirection (upperTerms terms) (kernel w K)) probe))

private theorem ids_valid : ∀ i, i ∈ ([0] : List Nat) → i < 1 := by
  intro i hi
  have h : i = 0 := List.mem_singleton.mp hi
  omega

theorem probe_supported : SupportedQuaternionBlocks 1 probe := by
  intro t ht
  simp only [probe, polyVar, List.mem_singleton] at ht
  subst t
  decide

private def sourceCertificate : Certificate 2 sourcePair :=
  (certificate_extend 1 (supported_one 1) (Certificate.one 1)).mul
    (lift_certificate 1 (Certificate.one 1))

theorem source_mass : quaternionHaar 2 sourcePair ≈ 1 := by decide
theorem bare_jump_square :
    quaternionHaar 2 (polyMul sourcePair (polyMul (jump 1 probe) (jump 1 probe))) ≈
      Q'.mkPos 1 2 (by decide) := by decide

/-- The SAME edge mass is positive at every admissible late cutoff. -/
theorem mass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) : (0 : Q') < mass w K := by
  have hfloor := productHeat_floorCertificate 1 hw0 hw1 K
    (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) [0] ids_valid
  have hb := certified_floor hfloor sourceCertificate
  have hp : (0 : Q') < (headFloor w)^([0] : List Nat).length *
      quaternionHaar 2 sourcePair :=
    Q'.mul_pos (productFloor_positive hw0 hw1 [0])
      (Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (Q'.ge_of_eqv source_mass))
  exact Q'.pos_of_lt_of_le hp (Q'.le_trans' _ _ _ hb
    (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

/-- Strictly positive temporal jump energy, with the actual heat floor.
The diagnostic survives the score theorem's own cutoff guard. -/
theorem jumpEnergy_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) : (0 : Q') < jumpEnergy w K := by
  have hfloor := productHeat_floorCertificate 1 hw0 hw1 K
    (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) [0] ids_valid
  have hb := certified_floor hfloor
    (sourceCertificate.mul (Certificate.square (jump 1 probe) (jump_supported probe_supported)))
  have hp : (0 : Q') < (headFloor w)^([0] : List Nat).length *
      quaternionHaar 2 (polyMul sourcePair (polyMul (jump 1 probe) (jump 1 probe))) :=
    Q'.mul_pos (productFloor_positive hw0 hw1 [0])
      (Q'.pos_of_lt_of_le (by decide : (0 : Q') < Q'.mkPos 1 2 (by decide))
        (Q'.ge_of_eqv bare_jump_square))
  apply Q'.pos_of_lt_of_le hp
  exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => kernel w K | 1 => sourcePair | _ => polyMul (jump 1 probe) (jump 1 probe)))))

/-- All whole angular directions have zero response on this nonconstant test. -/
theorem score_zero (terms : List (AngularTerm 1)) (w : Q') (K : Nat) :
    score terms w K ≈ 0 :=
  productHeat_flat_lower_score_zero 1 terms w K [0] ids_valid probe probe_supported

/-- No scalar cost bounds the positive SAME normalized jump energy by the
squared normalized one-end kernel-score response, even at late cutoff. -/
theorem normalized_score_energy_domination_false
    (terms : List (AngularTerm 1)) (B : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) :
    let r := Q'.recipPos (mass w K) (mass_positive hw0 hw1 K hK)
    ¬ (r * jumpEnergy w K ≤ B * ((r * score terms w K) * (r * score terms w K))) := by
  let r := Q'.recipPos (mass w K) (mass_positive hw0 hw1 K hK)
  change ¬ (r * jumpEnergy w K ≤ B * ((r * score terms w K) * (r * score terms w K)))
  intro h
  have hz : r * score terms w K ≈ 0 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left r _ _ (score_zero terms w K)) (Q'.mul_zero_eqv r)
  have hrhs : B * ((r * score terms w K) * (r * score terms w K)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left B _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz) (Q'.zero_mul_eqv _)))
      (Q'.mul_zero_eqv B)
  have hpositive := Q'.mul_pos (Q'.recipPos_pos (mass w K) (mass_positive hw0 hw1 K hK))
    (jumpEnergy_positive hw0 hw1 K hK)
  have bad : (0 : Q') < 0 := Q'.pos_of_lt_of_le hpositive
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hrhs))
  exact (by decide : ¬ ((0 : Q') < 0)) bad

end YMGap.Continuum.SU2QuaternionProductHeatScoreEnergyObstruction

#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreEnergyObstruction.bare_jump_square
#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreEnergyObstruction.mass_positive
#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreEnergyObstruction.jumpEnergy_positive
#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreEnergyObstruction.score_zero
#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreEnergyObstruction.normalized_score_energy_domination_false
