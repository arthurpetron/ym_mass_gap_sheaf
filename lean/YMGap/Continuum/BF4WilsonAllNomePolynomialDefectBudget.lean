/-
# Polynomial nome cost for the SAME completed plaquette defect

For delta=1-w, the original-action prediction floor is at least
delta^12/F(24582). The literal completed source y=(I-T)v therefore has
norm squared at least delta^24/(16*F(24582)^2). Combining this with its
physical-time orbit bound displays the normalization cost explicitly.

These are width-independent estimates for one source. No lattice-spacing
law, nonzero continuum limit, or every-state spectral gap is asserted.
-/

import YMGap.Continuum.BF4RelativePredictionNomeBudget
import YMGap.Continuum.RationalRelativePredictionScaling
import YMGap.Continuum.BF4WilsonAllNomeRelativeDefectNormalization

namespace YMGap.Continuum.BF4WilsonAllNomePolynomialDefectBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalRelativeWardPrediction
open YMGap.Continuum.RationalRelativePredictionScaling
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCap_positive)
open YMGap.Continuum.BF4RelativePredictionNomeBudget
open YMGap.Continuum.BF4ExactSlabRelativePredictionError
open YMGap.Continuum.BF4WilsonAllNomeRelativeDefectNormalization
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteDefectOrbit

local infix:50 " ≈ " => Q'.eqv
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- The explicit nome-independent cost of squaring the Ward prediction floor. -/
def polynomialNormBudget : Q' := 16 * (predictionFactor 24582 * predictionFactor 24582)

/-- This is `(1-w)^24`, grouped to retain the two Ward squarings. -/
def normWeight (w : Q') : Q' := (cubicDeficit w)^4 * (cubicDeficit w)^4

theorem polynomialNormBudget_positive : (0 : Q') < polynomialNormBudget :=
  Q'.mul_pos (by decide) (Q'.mul_pos (predictionFactor_positive _) (predictionFactor_positive _))

theorem normWeight_positive {w : Q'} (hw1 : w < (1 : Q')) :
    (0 : Q') < normWeight w := by
  have hr := cubicDeficit_positive hw1
  have h : (0 : Q') < (cubicDeficit w)^4 :=
    Q'.mul_pos hr (Q'.mul_pos hr (Q'.mul_pos hr
      (Q'.mul_pos hr (by decide : (0 : Q') < 1))))
  exact Q'.mul_pos h h

/-- The actual original-action prediction coefficient, not an abstract cost. -/
theorem prediction_polynomial_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (cubicDeficit w)^4 ≤ predictionFactor 24582 * relativePredictionFloor w := by
  exact fourth_le_factor_times_floor _ _ _
    (Q'.le_of_lt (cubicDeficit_positive hw1)) (cubicDeficit_le_one hw0 hw1)
    (Q'.le_of_lt (Q'.mul_pos (by decide : (0 : Q') < 6)
      (relativeCap_positive hw0 (by decide))))
    (by decide) (selectedScore_cubic_bound hw0 hw1)

/-- Denominator-cleared lower bound for the improved norm floor. -/
theorem polynomial_norm_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    normWeight w ≤ polynomialNormBudget * relativeDefectNormFloor w := by
  let F := predictionFactor 24582
  let s := relativePredictionFloor w
  have h := prediction_polynomial_floor hw0 hw1
  have h0 := Q'.pow_nonneg (cubicDeficit w) (Q'.le_of_lt (cubicDeficit_positive hw1)) 4
  have hFs := Q'.le_of_lt (Q'.mul_pos (predictionFactor_positive 24582)
    (relativePredictionFloor_positive w))
  have hs := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h h0)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ h hFs)
  have he : polynomialNormBudget * relativeDefectNormFloor w ≈ (F*s)*(F*s) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.const 16) (.mul (.var 0) (.var 0)))
        (.mul (.mul (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1))) (.var 3)))
      (.mul (.mul (.mul (.mul (.const 16) (.var 2)) (.var 2)) (.var 3))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
      (by decide) (fun
        | 0 => F
        | 1 => s
        | 2 => HalfPow.half
        | _ => Q'.recipPos 4 (Q'.ofNat_succ_pos 3)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (by decide : ((16*HalfPow.half)*HalfPow.half)*
            Q'.recipPos 4 (Q'.ofNat_succ_pos 3) ≈ 1))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv he)

private theorem rational_scale (a b : Q') : RCscale a (Rq b) = Rq (a*b) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul a b).symm

private theorem rational_le {a b : Q'} (h : a ≤ b) : RCle (Rq a) (Rq b) := by
  apply leEv_of_le
  intro n
  exact Q'.le_trans' _ _ _ h (Q'.add_le_self_of_nonneg _ _ (Q'.invSucc_nonneg n))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "y" => defect hw0 hw1 v
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Polynomial normalization cost on the literal completed source. -/
theorem plaquette_defect_polynomial_norm_floor :
    RCle (Rq (normWeight w)) (RCscale polynomialNormBudget (B y y)) := by
  have h := RCscale_mono (Q'.le_of_lt polynomialNormBudget_positive)
    (plaquette_relative_defect_norm_floor hw0 hw1 width face hf)
  rw [rational_scale] at h
  exact RCle_trans (rational_le (polynomial_norm_floor hw0 hw1)) h

/-- Physical-time decay normalized by the SAME source norm, with every nome
and time cost visible. No relation between nome and lattice spacing is assumed. -/
theorem plaquette_defect_polynomial_orbit_bound (n : Nat) :
    RCle (RCscale (normWeight w) (B (T n y) (T n y)))
      (RCscale (((Q'.invSucc n * Q'.invSucc n)*4)*polynomialNormBudget) (B y y)) := by
  let b := (Q'.invSucc n * Q'.invSucc n)*4
  have h1 := RCscale_mono (Q'.le_of_lt (normWeight_positive hw1))
    (plaquette_defect_orbit_bound hw0 hw1 width face hf n)
  have h2 := RCscale_mono
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg n)
      (Q'.invSucc_nonneg n)) (by decide : (0 : Q') ≤ 4))
    (plaquette_defect_polynomial_norm_floor hw0 hw1 width face hf)
  rw [rational_scale] at h1
  rw [rational_scale, RCscale_RCscale] at h2
  have hp : Rq (normWeight w * b) = Rq (b * normWeight w) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_comm_eqv _ _))
  rw [hp] at h1
  exact RCle_trans h1 h2

/-- A directly checkable scalar criterion for decay relative to the actual
source norm. A proposed scaling family must supply this displayed inequality;
the theorem does not silently identify nome with physical lattice spacing. -/
theorem plaquette_defect_polynomial_relative_small (epsilon : Q') (n : Nat)
    (hbudget : ((Q'.invSucc n * Q'.invSucc n)*4)*polynomialNormBudget ≤
      epsilon * normWeight w) :
    RCle (B (T n y) (T n y)) (RCscale epsilon (B y y)) := by
  have h := RCle_trans (plaquette_defect_polynomial_orbit_bound hw0 hw1 width face hf n)
    (RCscale_scalar_mono hbudget (completedInner_nonnegative hw0 hw1 y))
  have hp := normWeight_positive hw1
  let r := Q'.recipPos (normWeight w) hp
  have hunit : r * normWeight w ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ hp)
  have hr : r * (epsilon * normWeight w) ≈ epsilon :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => r | 1 => epsilon | _ => normWeight w))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hunit) (Q'.one_mul_eqv _))
  have hs := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos _ hp)) h
  rw [RCscale_RCscale, RCscale_RCscale,
    RCSignedPairBudget.scale_congr hunit, RCscale_one,
    RCSignedPairBudget.scale_congr hr] at hs
  exact hs

#print axioms polynomialNormBudget_positive
#print axioms normWeight_positive
#print axioms prediction_polynomial_floor
#print axioms polynomial_norm_floor
#print axioms plaquette_defect_polynomial_norm_floor
#print axioms plaquette_defect_polynomial_orbit_bound
#print axioms plaquette_defect_polynomial_relative_small

end YMGap.Continuum.BF4WilsonAllNomePolynomialDefectBudget
