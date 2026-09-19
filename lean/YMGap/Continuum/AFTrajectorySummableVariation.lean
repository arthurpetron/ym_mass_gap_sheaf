/-
# Summable variation of the shifted AF trajectory

The two-loop trajectory certificate already proves a reciprocal upper rate for
the positive log-coupling `τ`.  The recurrence therefore gives a genuinely
summable two-sided step budget for the shifted AF stream

    j ↦ τ (k₀ + j).

This module compiles that consequence into the common
`SummableRationalStepVariation` interface.  It is an AF scalar result only:
the stream is not silently identified with the completed BF4 physical gap.
That identification remains the next same-object bridge needed by the
exact-log continuum compiler.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.AFTrajectoryCertificate
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
import YMGap.Continuum.InverseSquareAntitoneTailControl
import YMGap.Continuum.QuadraticRateErrorTailControl
import YMGap.Continuum.SummabilityCapstone
import YMGap.Continuum.SummableRationalStepVariation
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.AFTrajectorySummableVariation

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.InverseSquareAntitoneTailControl
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The elementary signed-step conversion -/

private theorem le_add_of_sub_le
    {a b c : Q'} (h : a + (-b) ≤ c) : a ≤ b + c := by
  have hstep := Q'.add_le_add_right (a + (-b)) c b h
  have hcancel : ((a + (-b)) + b).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a ((-b) + b) 0
        (Q'.neg_add_self_eqv b)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hcancel)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.add_comm_eqv c b)))

private theorem trajectory_step_variation_core
    (t u β E : Q')
    (t_nonnegative : (0 : Q') ≤ t)
    (t_le_one : t ≤ (1 : Q'))
    (β_nonnegative : (0 : Q') ≤ β)
    (E_nonnegative : (0 : Q') ≤ E)
    (habs : Q'.abs (u - (t - β * (t * t))) ≤
      E * (t * (t * t))) :
    u ≤ t + (β + E) * (t * t) /\
    t ≤ u + (β + E) * (t * t) := by
  let square := t * t
  let error := E * (t * (t * t))
  have square_nonnegative : (0 : Q') ≤ square :=
    Q'.mul_nonneg t t t_nonnegative t_nonnegative
  have cubic_le_square : t * (t * t) ≤ square := by
    have hmul := Q'.mul_le_mul_of_nonneg_left t 1 square
      t_le_one square_nonnegative
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv t t t)))
      (Q'.le_trans' _ _ _ hmul
        (Q'.le_of_eqv (Q'.mul_one_eqv square)))
  have error_le_square : error ≤ E * square := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ E cubic_le_square E_nonnegative
  have error_nonnegative : (0 : Q') ≤ error :=
    Q'.mul_nonneg E (t * (t * t)) E_nonnegative
      (Q'.mul_nonneg t square t_nonnegative square_nonnegative)
  have beta_square_nonnegative : (0 : Q') ≤ β * square :=
    Q'.mul_nonneg β square β_nonnegative square_nonnegative
  have hupper_diff :
      u - (t - β * square) ≤ error := by
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs
  have hupper_model : u ≤ (t - β * square) + error := by
    exact le_add_of_sub_le hupper_diff
  have hupper_drop : (t - β * square) + error ≤ t + E * square := by
    have hmodel : t - β * square ≤ t := by
      have hzero : t ≤ (0 : Q') + t :=
        Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' t)))
      have hbt : t ≤ β * square + t :=
        Q'.le_trans' _ _ _ hzero
          (Q'.add_le_add_right 0 (β * square) t beta_square_nonnegative)
      exact Q'.sub_le_of_le_add hbt
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ error hmodel)
      (Q'.add_le_add_left _ _ _ error_le_square)
  have hbetaE : E * square ≤ (β + E) * square := by
    have hsum : E ≤ β + E := by
      have hzero : E ≤ E + 0 :=
        Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' E)))
      have hcomm : E + 0 ≤ 0 + E := Q'.le_of_eqv (Q'.add_comm_eqv _ _)
      exact Q'.le_trans' _ _ _ hzero
        (Q'.le_trans' _ _ _ hcomm
          (Q'.add_le_add_right 0 β E β_nonnegative))
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hsum square_nonnegative
  have hupper_target : t + E * square ≤ t + (β + E) * square :=
    Q'.add_le_add_left _ _ _ hbetaE
  have hupper : u ≤ t + (β + E) * square :=
    Q'.le_trans' _ _ _ hupper_model
      (Q'.le_trans' _ _ _ hupper_drop hupper_target)
  have hneg_diff :
      -(u - (t - β * square)) ≤ error := by
    exact Q'.le_trans' _ _ _ (Q'.neg_le_abs _)
      (Q'.le_trans' _ _ _ habs (Q'.le_refl' _))
  have hlower_model :
      t - β * square ≤ u + error := by
    have hsub : (t - β * square) + (-(u)) ≤ error := by
      have hrewrite :
          ((t - β * square) + (-(u))).eqv
            (-(u - (t - β * square))) := by
        have hneg :
            (-(u - (t - β * square))).eqv
              ((-u) + (t - β * square)) := by
          refine Q'.eqv_trans _ _ _
            (Q'.neg_add_eqv u (-(t - β * square))) ?_
          exact Q'.add_eqv_congr_left (-u) _ _
            (Q'.neg_neg_eqv (t - β * square))
        exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
          (Q'.eqv_symm hneg)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite) hneg_diff
    exact le_add_of_sub_le hsub
  have hmodel_lower : t ≤ (t - β * square) + β * square := by
    have hcancel :
        ((t - β * square) + β * square).eqv t := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv t (-(β * square))
        (β * square)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left t ((-(β * square)) + β * square) 0
          (Q'.neg_add_self_eqv (β * square))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' t)
    exact Q'.le_of_eqv (Q'.eqv_symm hcancel)
  have hlower_add :
      (t - β * square) + β * square ≤ (u + error) + β * square :=
    Q'.add_le_add_right _ _ _ hlower_model
  have hlower_reassoc :
      (u + error) + β * square ≤ u + (β + E) * square := by
    have hsum : error + β * square ≤ (β + E) * square := by
      have herror : error ≤ E * square := error_le_square
      have hadd : error + β * square ≤ E * square + β * square :=
        Q'.add_le_add_right _ _ _ herror
      have hcomm : (E * square + β * square).eqv
          (β * square + E * square) := Q'.add_comm_eqv _ _
      have hdist : ((β + E) * square).eqv
          (β * square + E * square) := ExpNeg.add_mul_eqv β E square
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm)
          (Q'.le_of_eqv (Q'.eqv_symm hdist)))
    have hassoc :
        ((u + error) + β * square).eqv
          (u + (error + β * square)) :=
      Q'.add_assoc_eqv u error (β * square)
    have hadd := Q'.add_le_add_left
      u (error + β * square) ((β + E) * square) hsum
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) hadd
  exact ⟨hupper, Q'.le_trans' _ _ _ hmodel_lower
    (Q'.le_trans' _ _ _ hlower_add hlower_reassoc)⟩

/-! ## 2. The shifted stream and its explicit summable budget -/

def shiftedTau (C : AFTrajectoryCertificate) : Nat → Q' :=
  fun j => C.τ (C.k0 + j)

def shiftedTauVariation (C : AFTrajectoryCertificate) : Nat → Q' :=
  fun j =>
    (C.β + C.E) *
      (C.τ (C.k0 + j) * C.τ (C.k0 + j))

theorem shiftedTauVariation_nonnegative
    (C : AFTrajectoryCertificate) (j : Nat) :
    (0 : Q') ≤ shiftedTauVariation C j := by
  unfold shiftedTauVariation
  exact Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.le_of_lt C.β_pos) C.E_nonneg)
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt (C.τ_pos (C.k0 + j)))
      (Q'.le_of_lt (C.τ_pos (C.k0 + j))))

def shiftedTauVariationTailControl
    (C : AFTrajectoryCertificate) :
    AntitoneTailControl (shiftedTauVariation C) := by
  let afr := afRateModulus_of_AFCertificate C
  let coefficient : Q' :=
    (C.β + C.E) * (rateScaled afr * rateScaled afr)
  have coefficient_nonnegative : (0 : Q') ≤ coefficient := by
    exact Q'.mul_nonneg _ _
      (Q'.zero_le_add _ _ (Q'.le_of_lt C.β_pos) C.E_nonneg)
      (Q'.mul_nonneg _ _ (rateScaled_nonneg afr) (rateScaled_nonneg afr))
  apply inverseSquareTermTailControl
    (shiftedTauVariation C) 2 (by decide) coefficient coefficient_nonnegative
  intro j
  let r := Q'.divPos (rateScaled afr)
    (harmDen2 j) (harmDen2_pos j)
  have hmargin := margin_le_scaled afr j
  have heqv : ((1 : Q') - afr.w j).eqv (shiftedTau C j) := by
    dsimp [afr, afRateModulus_of_AFCertificate, shiftedTau]
    exact AFRateCalibration.one_sub_one_sub_eqv (C.τ (C.k0 + j))
  have hτ : shiftedTau C j ≤ r := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm heqv)) hmargin
  have hτ_nonnegative : (0 : Q') ≤ shiftedTau C j :=
    Q'.le_of_lt (C.τ_pos (C.k0 + j))
  have r_nonnegative : (0 : Q') ≤ r := by
    have hscaled_pos : (0 : Q') < rateScaled afr := by
      unfold rateScaled
      exact Q'.mul_pos
        (InverseSquareAntitoneTailControl.ofNat_pos
          (Nat.lt_of_lt_of_le (by decide) (inflM_ge_one afr))) afr.A_pos
    exact Q'.le_of_lt (Q'.divPos_pos _ _ (harmDen2_pos j) hscaled_pos)
  have hsquare :
      shiftedTau C j * shiftedTau C j ≤ r * r :=
    Q'.mul_le_mul_of_nonneg hτ hτ r_nonnegative hτ_nonnegative
  have hscaled := scaledMargin_sq_le_invSq afr j
  have hleft := Q'.mul_le_mul_of_nonneg_left _ _ _ hsquare
    (Q'.zero_le_add _ _ (Q'.le_of_lt C.β_pos) C.E_nonneg)
  have hregroup :
      ((C.β + C.E) * (rateScaled afr * rateScaled afr)) *
          invSqTerm 2 (by decide) j ≈
        (C.β + C.E) *
          ((rateScaled afr * rateScaled afr) *
            invSqTerm 2 (by decide) j) :=
    Q'.mul_assoc_eqv _ _ _
  change (C.β + C.E) *
      (shiftedTau C j * shiftedTau C j) ≤
    coefficient * invSqTerm 2 (by decide) j
  exact Q'.le_trans' _ _ _ hleft
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hscaled
        (Q'.zero_le_add _ _ (Q'.le_of_lt C.β_pos) C.E_nonneg))
      (Q'.le_of_eqv (Q'.eqv_symm hregroup)))

def shiftedTauSummableVariation
    (C : AFTrajectoryCertificate) :
    SummableRationalStepVariation (shiftedTau C) where
  variation := shiftedTauVariation C
  variation_nonnegative := shiftedTauVariation_nonnegative C
  tailControl := shiftedTauVariationTailControl C
  stepBound := by
    intro j
    let t := C.τ (C.k0 + j)
    let u := C.τ (C.k0 + (j + 1))
    have hstep := trajectory_step_variation_core t u C.β C.E
      (Q'.le_of_lt (C.τ_pos (C.k0 + j)))
      (Q'.le_of_lt (C.τ_lt_one (C.k0 + j)
        (Nat.le_add_right C.k0 j)))
      (Q'.le_of_lt C.β_pos) C.E_nonneg
      (C.recurrence (C.k0 + j) (Nat.le_add_right C.k0 j))
    simpa only [shiftedTau, shiftedTauVariation, t, u, Nat.add_assoc]
      using hstep

def shiftedTauCauchy
    (C : AFTrajectoryCertificate) :
    CReal.ModCauchyEv (fun j => CReal.ofQ' (shiftedTau C j)) :=
  (shiftedTauSummableVariation C).toModCauchyEv

/-! ## 3. The exact same-family bridge -/

/-- The minimal identification needed to move the AF scalar variation onto
the completed BF4 family.  It is intentionally an explicit Type-level field:
the AF recurrence alone does not identify `τ` with the completed transfer's
physical gap. -/
structure PhysicalGapTrajectoryIdentification
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (C : AFTrajectoryCertificate) : Type 1 where
  pointwise : ∀ j, (shiftedTau C j).eqv (family.physicalGap j)

/-- Transport the proved AF summable variation to the definitionally named
completed-family physical gap once the same-object pointwise identification is
supplied.  No spacing floor or reciprocal variation is introduced. -/
def PhysicalGapTrajectoryIdentification.toPhysicalGapVariation
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {C : AFTrajectoryCertificate}
    (identification : PhysicalGapTrajectoryIdentification family C) :
    SummableRationalStepVariation family.physicalGap :=
  SummableRationalStepVariationAlgebra.ofPointwiseEqv
    (shiftedTauSummableVariation C) identification.pointwise

/-! ## 4. Exact-log consequence -/

/-- The AF recurrence, together with an explicit same-family gap
identification, reaches the existing exact-log Cauchy compiler.  The spacing
tail remains the independently supplied physical branch. -/
def exactLogRateCauchyOfAFTrajectory
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {C : AFTrajectoryCertificate}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0)
    (identification : PhysicalGapTrajectoryIdentification family C) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) :=
  DynamicVacuumSectorObservablePin.exactLogRateCauchy
    pin band identification.toPhysicalGapVariation spacingTail

end YMGap.Continuum.AFTrajectorySummableVariation

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.AFTrajectorySummableVariation.shiftedTauVariation_nonnegative
#print axioms
  YMGap.Continuum.AFTrajectorySummableVariation.shiftedTauVariationTailControl
#print axioms
  YMGap.Continuum.AFTrajectorySummableVariation.shiftedTauSummableVariation
#print axioms
  YMGap.Continuum.AFTrajectorySummableVariation.shiftedTauCauchy
#print axioms
  YMGap.Continuum.AFTrajectorySummableVariation.PhysicalGapTrajectoryIdentification.toPhysicalGapVariation
#print axioms
  YMGap.Continuum.AFTrajectorySummableVariation.exactLogRateCauchyOfAFTrajectory
