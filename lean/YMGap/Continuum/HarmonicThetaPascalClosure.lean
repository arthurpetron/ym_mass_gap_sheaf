/-
# Closure of the harmonic growing-head Pascal certificate

This module consumes the exact projective positivity theorem and the
coefficient-to-residual evaluation identity.  It proves nonnegativity of the
actual growing-head residual at every harmonic scale, then discharges the
theta-head premise and every later retained cutoff.
-/

import YMGap.Continuum.HarmonicThetaPascalEvaluation

namespace YMGap.Continuum.HarmonicThetaPascalClosure

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicRetuneFloor
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaLinearCarrier
open YMGap.Continuum.HarmonicThetaPascalBridge
open YMGap.Continuum.HarmonicThetaPascalEvaluation
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicVariableAnchorThetaBridge
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper

local infix:50 " ≈ " => Q'.eqv

private theorem closure_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "closure_ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, closure_neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem pow_pos (q : Q') (hq : (0 : Q') < q) : ∀ n : Nat,
    (0 : Q') < q ^ n
  | 0 => by
      change (0 : Q') < 1
      decide
  | n + 1 => by
      rw [Q'.pow_succ]
      exact Q'.mul_pos hq (pow_pos q hq n)

private theorem harmonic_complement_mul_den (k : Nat) :
    ((1 : Q') - harmW k) * Q'.ofNat (k + 2) ≈ 1 := by
  have hcomp : ((1 : Q') - harmW k) ≈ harmU k := by
    simpa [harmW, oneSub] using
      (YMGap.Continuum.AFRateCalibration.one_sub_one_sub_eqv (harmU k))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.ofNat (k + 2)) hcomp)
    (harmonicUnit_mul_den k)

/-- The signed Bernstein evaluation itself is nonnegative at the harmonic
schedule.  Projective clearing multiplies it by a strictly positive integer
denominator, so the exact projective certificate can be cancelled back. -/
theorem harmonic_growing_head_signed_eval_nonnegative (k : Nat) :
    let m := growingAnchor k + 2
    let D := 2 * m * m + 1
    (0 : Q') ≤ signedBernsteinEval D
      (growingHeadThetaBernCoeff D m) (harmW k) := by
  let m := growingAnchor k + 2
  let D := 2 * m * m + 1
  let den := Q'.ofNat (k + 2)
  have hprojective :
      (0 : Q') ≤ projectiveDeficitEval D
        (growingHeadThetaBernCoeff D m) (Q'.ofNat (k + 1)) := by
    dsimp [m, D]
    exact growing_head_projective_deficit_schedule_nonnegative k
  have hclear := signedBernsteinEval_mul_den_pow_eqv_projectiveDeficitEval
    D (growingHeadThetaBernCoeff D m) (harmW k) den
      (Q'.ofNat (k + 1))
      (by
        dsimp [den]
        exact harmonicWeight_mul_den k)
      (by
        dsimp [den]
        exact harmonic_complement_mul_den k)
  have hscaled :
      (0 : Q') ≤ signedBernsteinEval D
          (growingHeadThetaBernCoeff D m) (harmW k) * den ^ D :=
    Q'.le_trans' _ _ _ hprojective (Q'.ge_of_eqv hclear)
  have hcomm :
      den ^ D * signedBernsteinEval D
          (growingHeadThetaBernCoeff D m) (harmW k) ≈
        signedBernsteinEval D
          (growingHeadThetaBernCoeff D m) (harmW k) * den ^ D :=
    Q'.mul_comm_eqv _ _
  have hleft :
      (0 : Q') ≤ den ^ D * signedBernsteinEval D
        (growingHeadThetaBernCoeff D m) (harmW k) :=
    Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hcomm)
  have hmul :
      den ^ D * (0 : Q') ≤ den ^ D * signedBernsteinEval D
        (growingHeadThetaBernCoeff D m) (harmW k) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv (den ^ D))) hleft
  have hden : (0 : Q') < den ^ D := by
    apply pow_pos
    dsimp [den]
    exact Q'.ofNat_succ_pos (k + 1)
  exact Q'.le_of_mul_le_mul_left hmul hden

/-- The actual cleared growing-head theta residual is nonnegative at every
harmonic scale. -/
theorem harmonic_growing_head_scaled_theta_residual_nonnegative (k : Nat) :
    (0 : Q') ≤
      growingHeadScaledThetaResidual (harmW k) (growingAnchor k) := by
  let m := growingAnchor k + 2
  let D := 2 * m * m + 1
  have hm : 2 ≤ m := by
    dsimp [m]
    omega
  have heval := growingHeadThetaBernCoeff_scaled_eval_eqv_residual
    m (harmW k) hm
  have hsigned :
      (0 : Q') ≤ signedBernsteinEval D
        (growingHeadThetaBernCoeff D m) (harmW k) := by
    dsimp [m, D]
    exact harmonic_growing_head_signed_eval_nonnegative k
  have hscaled :
      (0 : Q') ≤ (harmW k) ^ 2 * signedBernsteinEval D
        (growingHeadThetaBernCoeff D m) (harmW k) :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg (harmW k) (harmW_nonneg k) 2) hsigned
  have hres :
      (0 : Q') ≤ growingHeadScaledThetaResidual (harmW k) (m - 2) :=
    Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv heval)
  have hmback : m - 2 = growingAnchor k := by
    dsimp [m]
    omega
  rw [hmback] at hres
  exact hres

/-- Exact harmonic theta-head premise, with no residual hypothesis left. -/
theorem harmonic_growing_anchor_theta_premise (k : Nat) :
    harmW k * halfThetaSum (harmW k) (growingAnchor k + 1) ≤
      retuneCube (harmW k) *
        integerThetaSum (harmW k) (growingAnchor k) :=
  harmonic_growing_anchor_theta_premise_of_residual_nonnegative k
    (harmonic_growing_head_scaled_theta_residual_nonnegative k)

/-- The harmonic Pascal certificate closes the retune inequality at every
later retained cutoff. -/
theorem harmonic_growing_anchor_all_later_retune (k M : Nat) :
    adjCorr (harmW k) (growingAnchor k + 1 + M) ≤
      retuneCube (harmW k) *
        coordNormSq (harmW k) (growingAnchor k + 1 + M) :=
  growing_anchor_retune_of_residual_nonnegative k M
    (harmonic_growing_head_scaled_theta_residual_nonnegative k)

/-- At every non-base scale, the hypothesis-free theta certificate reaches
the actual physical quadratic cutoff. -/
theorem harmonic_physical_cutoff_retune {k : Nat} (hk : 1 ≤ k) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) :=
  harmonic_retune_Ncut_of_theta_head hk
    (harmonic_growing_anchor_theta_premise k)

/-- The normalized fundamental Peter--Weyl eigenvalue at the physical
cutoff is bounded by the exact retune cube. -/
theorem harmonic_fundamental_eigenvalue_le_retune {k : Nat} (hk : 1 ≤ k) :
    lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k) :=
  harmonic_lamPW_le_retune_of_theta_head hk
    (harmonic_growing_anchor_theta_premise k)

/-- Uniform harmonic-unit lower floor for the physical mass proxy. -/
theorem harmonic_unit_le_mass {k : Nat} (hk : 1 ≤ k) :
    harmU k ≤ harmonicMass k :=
  harmU_le_harmonicMass_of_theta_head hk
    (harmonic_growing_anchor_theta_premise k)

/-- Sharper quadratic physical mass floor inherited from the exact retune
factorization. -/
theorem harmonic_quadratic_mass_floor {k : Nat} (hk : 1 ≤ k) :
    (Q'.mkPos 1 2 (by decide) * harmU k) *
        (Q'.ofNat 3 +
          -(Q'.ofNat 3 * (Q'.mkPos 1 2 (by decide) * harmU k))) ≤
      harmonicMass k :=
  harmonicMass_quadratic_floor_of_theta_head hk
    (harmonic_growing_anchor_theta_premise k)

#print axioms harmonic_growing_head_signed_eval_nonnegative
#print axioms harmonic_growing_head_scaled_theta_residual_nonnegative
#print axioms harmonic_growing_anchor_theta_premise
#print axioms harmonic_growing_anchor_all_later_retune
#print axioms harmonic_physical_cutoff_retune
#print axioms harmonic_fundamental_eigenvalue_le_retune
#print axioms harmonic_unit_le_mass
#print axioms harmonic_quadratic_mass_floor

end YMGap.Continuum.HarmonicThetaPascalClosure
