/-
# Explicit normalization of the SAME positive-time dyadic bond anchor

The norm N=R(2*side) has its existing positive, parameter-dependent floor.
Its constructed inverse square root scales the original anchored sector and
bond point, retaining their range witnesses, completion and vacuum complement.
The exact response satisfies N*Rz(j)=R(2*side+j).

A supplied relative adjacent-response budget at any start <=2*side propagates
to this unit anchor and gives a positive blocked floor, with NO uniform floor
on the original R(1) or N. The budget itself is not produced here. No cross-
scale convergence, uniform inverse normalizer, continuum survival, physical
time calibration or Yang--Mills local-field identification is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchor
import YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
import YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchor
  (anchoredSector anchoredSector_pin)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (ofState bondValue_ofState)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarMulCauchy)
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
  (squareResponseFraction squareResponseFraction_positive)
open YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival
  (response_shifted_step_lower)
open YMGap.Continuum.BF4WilsonAllNomeResponseLower (response_geometric_lower)
open YMGap.Continuum.RationalBlockedSurvival

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "R" j:arg => dyadicUnitResponse hw0 hw1 scale width hwidth j

attribute [local irreducible] dyadicUnitExcitation dyadicUnitResponse

/-- The literal original positive-time norm, with its OWN Cauchy data. -/
def anchorNorm : CReal := R (2*side scale)

def anchorNormCauchy : QCauchy (anchorNorm hw0 hw1 scale width hwidth).approx :=
  dyadicUnitResponseCauchy hw0 hw1 scale width hwidth (2*side scale)

/-- This may collapse with the parameters; it is used only to compute an inverse. -/
def anchorNormFloor : Q' := (squareResponseFraction hw0 hw1 scale)^(2*side scale)

theorem anchorNormFloor_positive : (0 : Q') < anchorNormFloor hw0 hw1 scale :=
  HKPos.pow_pos (squareResponseFraction_positive hw0 hw1 scale) _

theorem anchorNorm_floor :
    leEv (ofQ' (anchorNormFloor hw0 hw1 scale)) (anchorNorm hw0 hw1 scale width hwidth) :=
  dyadicUnitResponse_geometric_floor hw0 hw1 scale width hwidth _

def anchorNormalizer : CReal :=
  PositiveCRealNormalizationScalar.scalar
    (anchorNorm hw0 hw1 scale width hwidth)
    (anchorNormCauchy hw0 hw1 scale width hwidth)
    (anchorNormFloor hw0 hw1 scale) (anchorNormFloor_positive hw0 hw1 scale)

def anchorNormalizerCauchy : QCauchy (anchorNormalizer hw0 hw1 scale width hwidth).approx :=
  PositiveCRealNormalizationScalar.scalarCauchy
    (anchorNorm hw0 hw1 scale width hwidth)
    (anchorNormCauchy hw0 hw1 scale width hwidth)
    (anchorNormFloor hw0 hw1 scale) (anchorNormFloor_positive hw0 hw1 scale)

theorem anchorNormalizer_normalizes :
    Equiv (mul (anchorNormalizer hw0 hw1 scale width hwidth)
      (mul (anchorNormalizer hw0 hw1 scale width hwidth)
        (anchorNorm hw0 hw1 scale width hwidth))) cone :=
  PositiveCRealNormalizationScalar.scalar_normalizes
    (anchorNorm hw0 hw1 scale width hwidth)
    (anchorNormCauchy hw0 hw1 scale width hwidth)
    (anchorNormFloor hw0 hw1 scale) (anchorNormFloor_positive hw0 hw1 scale)
    (anchorNorm_floor hw0 hw1 scale width hwidth)

local notation "normalizer" => anchorNormalizer hw0 hw1 scale width hwidth
local notation "normalizerCauchy" => anchorNormalizerCauchy hw0 hw1 scale width hwidth

/-- Constructive scaling of the EXISTING anchored sector, including its range data. -/
def normalizedSector : BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 normalizer normalizerCauchy
    (anchoredSector hw0 hw1 scale width hwidth 0)

/-- No new carrier: this is the existing completion map applied to explicit range data. -/
def normalizedBondExcitation : BondCompletion hw0 hw1 (width := width) :=
  ofState hw0 hw1 (normalizedSector hw0 hw1 scale width hwidth)

/-- The same vector, with its original vacuum-orthogonality proof retained. -/
def normalizedVacuumExcitation : VacuumComplement hw0 hw1 (width := width) :=
  vacuumComplementRealSmul hw0 hw1 normalizer normalizerCauchy
    (vacuumComplementTime hw0 hw1 (side scale)
      (dyadicUnitExcitation hw0 hw1 scale width hwidth))

local notation "z" => Subtype.val (normalizedVacuumExcitation hw0 hw1 scale width hwidth)

theorem normalizedSector_pin : (normalizedSector hw0 hw1 scale width hwidth).val = z := by
  change completedRealSmul hw0 hw1 normalizer normalizerCauchy
    (anchoredSector hw0 hw1 scale width hwidth 0).val = _
  rw [anchoredSector_pin, Nat.add_zero]
  rfl

theorem normalizedBond_value :
    bondValue hw0 hw1 (normalizedBondExcitation hw0 hw1 scale width hwidth) = z := by
  rw [normalizedBondExcitation, bondValue_ofState, normalizedSector_pin]

/-- Actual normalized response representative, not a cross-scale functional. -/
def normalizedAnchorResponse (j : Nat) : CReal :=
  mul normalizer (mul normalizer (R (2*side scale+j)))

def normalizedAnchorResponseCauchy (j : Nat) :
    QCauchy (normalizedAnchorResponse hw0 hw1 scale width hwidth j).approx :=
  scalarMulCauchy _ _ normalizerCauchy
    (scalarMulCauchy _ _ normalizerCauchy
      (dyadicUnitResponseCauchy hw0 hw1 scale width hwidth _))

theorem normalizedAnchorResponse_pin (j : Nat) : B z (T j z) =
    Quotient.mk crealSetoid (normalizedAnchorResponse hw0 hw1 scale width hwidth j) := by
  change B (completedRealSmul hw0 hw1 normalizer normalizerCauchy (T (side scale) u))
    (T j (completedRealSmul hw0 hw1 normalizer normalizerCauchy (T (side scale) u))) = _
  rw [completedTime_realSmul, completedInner_realSmul_left,
    completedInner_realSmul_right, ← completedTime_add, completedInner_time_sum]
  rw [show side scale+(j+side scale)=2*side scale+j by omega, dyadicUnitResponse_pin]
  rfl

theorem normalizedVacuumExcitation_norm : B z z = Rq 1 := by
  have h := normalizedAnchorResponse_pin hw0 hw1 scale width hwidth 0
  rw [completedTime_zero] at h
  rw [h]
  apply Quotient.sound
  simpa only [normalizedAnchorResponse, Nat.add_zero, anchorNorm] using
    anchorNormalizer_normalizes hw0 hw1 scale width hwidth

theorem normalizedBond_norm :
    bondCompletedInner hw0 hw1 (normalizedBondExcitation hw0 hw1 scale width hwidth)
      (normalizedBondExcitation hw0 hw1 scale width hwidth) = Rq 1 := by
  rw [bondValue_inner, normalizedBond_value, normalizedVacuumExcitation_norm]

/-- A cleared response ratio: division by a CReal is neither assumed nor chosen. -/
theorem normalizedAnchorResponse_cleared_pin (j : Nat) :
    Equiv (mul (anchorNorm hw0 hw1 scale width hwidth)
      (normalizedAnchorResponse hw0 hw1 scale width hwidth j)) (R (2*side scale+j)) := by
  have hr : Equiv
      (mul (anchorNorm hw0 hw1 scale width hwidth)
        (normalizedAnchorResponse hw0 hw1 scale width hwidth j))
      (mul (mul normalizer (mul normalizer (anchorNorm hw0 hw1 scale width hwidth)))
        (R (2*side scale+j))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 1) (.mul (.var 1) (.var 0))) (.var 2))
        (by decide) (fun
          | 0 => (anchorNorm hw0 hw1 scale width hwidth).approx n
          | 1 => (normalizer).approx n
          | _ => (R (2*side scale+j)).approx n))
  exact hr.trans ((Pivot2.mul_congr_left
    (anchorNormalizer_normalizes hw0 hw1 scale width hwidth)).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.one_mul_eqv ((R (2*side scale+j)).approx n))))

private theorem sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B'.approx n)))

private theorem add_sub_first (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

private theorem relative_budget_floor (A E : RC) (C m : Nat) (hm : 1 ≤ m)
    (hbudget : RCle (RCscale (Q'.ofNat m) (RCsub A E)) (RCscale (Q'.ofNat C) A)) :
    RCle (RCscale (blocked_rate C m) A) E := by
  let r := Q'.invSucc (m-1)
  have hi : r*Q'.ofNat m ≈ 1 := by
    have hi' := Q'.ofNat_succ_mul_invSucc (m-1)
    change Q'.ofNat (m-1+1)*Q'.invSucc (m-1) ≈ 1 at hi'
    rw [Nat.sub_add_cancel hm] at hi'
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) hi'
  have h := RCscale_mono (Q'.invSucc_nonneg (m-1)) hbudget
  rw [RCscale_RCscale, RCscale_RCscale,
    RCSignedPairBudget.scale_congr hi, RCscale_one] at h
  have h' := RCadd_le_add h (RCle_refl E)
  rw [sub_add] at h'
  have h'' := RCadd_le_add h' (RCle_refl (RCneg (RCscale (r*Q'.ofNat C) A)))
  change RCle (RCsub A (RCscale (r*Q'.ofNat C) A))
    (RCsub (RCadd (RCscale (r*Q'.ofNat C) A) E) (RCscale (r*Q'.ofNat C) A)) at h''
  rw [add_sub_first] at h''
  have hp : RCsub A (RCscale (r*Q'.ofNat C) A) = RCscale (blocked_rate C m) A := by
    refine Quotient.inductionOn A ?_
    exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 2)) (.var 0))))
        (.mul (.add (.const 1) (.neg (.mul (.var 2) (.var 1)))) (.var 0))
        (by decide) (fun | 0 => X.approx n | 1 => r | _ => Q'.ofNat C)))
  rwa [hp] at h''

attribute [local irreducible] anchorNormalizer normalizedVacuumExcitation

/-- The ORIGINAL shifted relative budget suffices; no uniform original reserve
is required. Its start may be any integer no later than the anchor's norm index. -/
theorem normalizedAnchorResponse_budget_geometric_floor (C m start : Nat)
    (hC : 1 ≤ C) (hm : 4*C ≤ m) (hstart : start ≤ 2*side scale)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) (j : Nat) :
    leEv (ofQ' ((blocked_rate C m)^j))
      (normalizedAnchorResponse hw0 hw1 scale width hwidth j) := by
  let rho := blocked_rate C m
  have hrho := blocked_rate_nonnegative C m hC hm
  have hbudget' : RCle (RCscale (Q'.ofNat m)
      (RCsub (B u (T start u)) (B u (T (start+1) u))))
      (RCscale (Q'.ofNat C) (B u (T start u))) := by
    rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin]
    exact hbudget
  have hfirst := relative_budget_floor _ _ C m (by omega) hbudget'
  have hstep := response_shifted_step_lower hw0 hw1 u rho hrho start hfirst
    (2*side scale-start)
  rw [Nat.add_sub_of_le hstart, dyadicUnitResponse_pin, dyadicUnitResponse_pin] at hstep
  have hstep' : leEv (mul (ofQ' rho) (R (2*side scale))) (R (2*side scale+1)) := hstep
  have hs : leEv czero normalizer := by
    simpa only [anchorNormalizer] using PositiveCRealNormalizationScalar.scalar_nonnegative
      (anchorNorm hw0 hw1 scale width hwidth)
      (anchorNormCauchy hw0 hw1 scale width hwidth)
      (anchorNormFloor hw0 hw1 scale) (anchorNormFloor_positive hw0 hw1 scale)
  have hscaled : leEv
      (mul normalizer (mul normalizer (mul (ofQ' rho) (R (2*side scale)))))
      (mul normalizer (mul normalizer (R (2*side scale+1)))) :=
    leEv_mul_nonneg_left hs (leEv_mul_nonneg_left hs hstep')
  have hnorm : Equiv (mul normalizer (mul normalizer (R (2*side scale)))) cone :=
    anchorNormalizer_normalizes hw0 hw1 scale width hwidth
  have hmult : Equiv
      (mul (ofQ' rho) (mul normalizer (mul normalizer (R (2*side scale)))))
      (mul (ofQ' rho) cone) := Pivot2.mul_congr_right (A := ofQ' rho) hnorm
  have hone : Equiv (mul (ofQ' rho) cone) (ofQ' rho) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv rho)
  have hleft : Equiv (mul normalizer (mul normalizer (mul (ofQ' rho) (R (2*side scale)))))
      (ofQ' rho) :=
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.mul (.var 1) (.mul (.var 0) (.mul (.var 0) (.var 2))))
        (by decide) (fun
          | 0 => (normalizer).approx n
          | 1 => rho
          | _ => (R (2*side scale)).approx n))).trans
      (hmult.trans hone)
  have hnormalized : leEv (ofQ' rho) (normalizedAnchorResponse hw0 hw1 scale width hwidth 1) :=
    leEv_trans (leEv_of_equiv hleft.symm) hscaled
  have hfloor : RCle (RCscale rho (B z z)) (B z (T 1 z)) := by
    rw [normalizedVacuumExcitation_norm, normalizedAnchorResponse_pin]
    have hp : RCscale rho (Rq 1) = Rq rho :=
      Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv rho))
    rw [hp]
    exact hnormalized
  have h := response_geometric_lower hw0 hw1 z rho hrho hfloor j
  rw [normalizedVacuumExcitation_norm, normalizedAnchorResponse_pin] at h
  have hp : RCscale (rho^j) (Rq 1) = Rq (rho^j) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv (rho^j)))
  rwa [hp] at h

/-- Computed positive floor, independent of the original R(1) and anchor norm.
Only the actual shifted budget is supplied; no changing-family claim is made. -/
theorem normalizedAnchorResponse_budget_block_floor (C m start : Nat)
    (hC : 1 ≤ C) (hm : 4*C ≤ m) (hstart : start ≤ 2*side scale)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) :
    leEv (ofQ' (quarter^(2*C)))
      (normalizedAnchorResponse hw0 hw1 scale width hwidth (m-1)) :=
  leEv_trans (leEv_of_le (ofQ'_le_ofQ' (blocked_rate_floor C m hC hm)))
    (normalizedAnchorResponse_budget_geometric_floor hw0 hw1 scale width hwidth
      C m start hC hm hstart hbudget (m-1))

#print axioms anchorNorm
#print axioms anchorNormCauchy
#print axioms anchorNormFloor_positive
#print axioms anchorNorm_floor
#print axioms anchorNormalizer
#print axioms anchorNormalizerCauchy
#print axioms anchorNormalizer_normalizes
#print axioms normalizedSector
#print axioms normalizedBondExcitation
#print axioms normalizedVacuumExcitation
#print axioms normalizedSector_pin
#print axioms normalizedBond_value
#print axioms normalizedAnchorResponse
#print axioms normalizedAnchorResponseCauchy
#print axioms normalizedAnchorResponse_pin
#print axioms normalizedVacuumExcitation_norm
#print axioms normalizedBond_norm
#print axioms normalizedAnchorResponse_cleared_pin
#print axioms normalizedAnchorResponse_budget_geometric_floor
#print axioms normalizedAnchorResponse_budget_block_floor

end YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor
