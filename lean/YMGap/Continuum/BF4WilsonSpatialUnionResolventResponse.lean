/-
# The current resolvent on the existing normalized Wilson excitation

The normalized response module supplies one actual nonzero, unit-orthogonal
Wilson vector with a positive two-step response band.  The current-carrier
resolvent therefore has a concrete non-erasure and quantitative coercivity
consequence on that SAME excitation.  This is fixed-spacing SU(2)
nontriviality, not continuum survival or a physical mass statement.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionResolvent
import YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
import YMGap.Continuum.BF4WilsonSpatialUnionResolventBound
import YMGap.Continuum.ContinuousTransferCalculus

namespace YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
open YMGap.Continuum.BF4WilsonSpatialUnionResolventBound
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation (norm_decay)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
open YMGap.Continuum.BF4WilsonSpatialUnionResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "C" => center nome_pos nome_lt_one hsmall hd hs
local notation "Z" => completedZero nome_pos nome_lt_one hsmall hd hs
local notation "R" => resolvent nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "q" => twoStepRate
  YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate.nome hd

private theorem four_copies (r : RC) :
    RCadd (RCadd r r) (RCadd r r) = RCscale 4 r := by
  refine Quotient.inductionOn r ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
      (.mul (.const 4) (.var 0)) (by decide) (fun _ => A.approx n)))

private theorem q_sq_le_one : q * q ≤ (1 : Q') := by
  have hq0 : (0 : Q') ≤ q := Q'.le_of_lt
    (twoStepRate_positive
      nome_pos hd)
  have hq1 : q ≤ (1 : Q') := Q'.le_of_lt
    (twoStepRate_lt_one nome_pos hd hs)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right q 1 q hq1 hq0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv q)) hq1)

set_option maxRecDepth 100000 in
private theorem resolvent_distance_floor (x : V) (hx : C x = x) :
    RCle (RCscale (Q'.mkPos 1 4 (by decide)) (B x x))
      (B (R x) (R x)) := by
  have htriangle := completedDist_triangle nome_pos nome_lt_one hsmall hd hs
    (R x) Z (T 2 (R x))
  have hdef : completedDist nome_pos nome_lt_one hsmall hd hs
      (R x) (T 2 (R x)) = B x x := by
    unfold completedDist
    change B (defect nome_pos nome_lt_one hsmall hd hs (R x))
      (defect nome_pos nome_lt_one hsmall hd hs (R x)) = B x x
    rw [resolvent_right_inverse, hx]
  have hnorm := norm_decay nome_pos nome_lt_one hsmall hd hs (R x)
    ((center_fixed_iff nome_pos nome_lt_one hsmall hd hs _).mp
      (resolvent_centered nome_pos nome_lt_one hsmall hd hs x)) 2
  have hdist_time :
      RCle (completedDist nome_pos nome_lt_one hsmall hd hs Z (T 2 (R x)))
        (RCscale (q*q) (B (R x) (R x))) := by
    have heq : completedDist nome_pos nome_lt_one hsmall hd hs Z (T 2 (R x)) =
        B (T 2 (R x)) (T 2 (R x)) :=
      (completedDist_symm nome_pos nome_lt_one hsmall hd hs Z (T 2 (R x))).trans
        (completedDist_zero_right nome_pos nome_lt_one hsmall hd hs (T 2 (R x)))
    exact (congrArg (fun z : RC => RCle z (RCscale (q*q) (B (R x) (R x)))) heq).mpr hnorm
  have hbound : RCle (B x x)
      (RCadd (RCadd (B (R x) (R x)) (B (R x) (R x)))
        (RCadd (RCscale (q*q) (B (R x) (R x)))
          (RCscale (q*q) (B (R x) (R x))))) := by
    rw [← hdef]
    rw [completedDist_zero_right] at htriangle
    exact RCle_trans htriangle
      (RCadd_le_add (RCle_refl _) (RCadd_le_add hdist_time hdist_time))
  have hqscale : RCle (RCscale (q*q) (B (R x) (R x)))
      (B (R x) (R x)) := by
    simpa only [RCscale_one] using RCscale_scalar_mono q_sq_le_one
      (completedInner_nonnegative nome_pos nome_lt_one hsmall hd hs (R x))
  have hfour : RCle (B x x) (RCscale 4 (B (R x) (R x))) := by
    have hsum := RCadd_le_add
      (RCle_refl (RCadd (B (R x) (R x)) (B (R x) (R x))))
      (RCadd_le_add hqscale hqscale)
    rw [four_copies] at hsum
    exact RCle_trans hbound hsum
  have hquarter := RCscale_mono
    (by decide : (0 : Q') ≤ Q'.mkPos 1 4 (by decide)) hfour
  rw [RCscale_RCscale,
    scale_congr (by decide :
      (Q'.mkPos 1 4 (by decide) * 4).eqv (1 : Q')),
    RCscale_one] at hquarter
  exact hquarter

theorem unitExcitation_center_fixed : C unitExcitation = unitExcitation :=
  (center_fixed_iff nome_pos nome_lt_one hsmall hd hs _).mpr
    unitExcitation_orthogonal

theorem unitExcitation_ne_zero : unitExcitation ≠ Z := by
  intro hz
  have h := unitExcitation_time_ne_zero 0
  rw [completedTime_zero] at h
  exact h hz

/-- The existing normalized Wilson probe remains nonzero after applying the
    SAME completed-carrier resolvent. -/
theorem unitExcitation_resolvent_ne_zero : R unitExcitation ≠ Z :=
  resolvent_ne_zero nome_pos nome_lt_one hsmall hd hs unitExcitation
    unitExcitation_center_fixed unitExcitation_ne_zero

theorem unitExcitation_resolvent_centered : C (R unitExcitation) = R unitExcitation :=
  resolvent_centered nome_pos nome_lt_one hsmall hd hs unitExcitation

theorem unitExcitation_resolvent_norm_floor :
    RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (B (R unitExcitation) (R unitExcitation)) := by
  have h := resolvent_distance_floor unitExcitation unitExcitation_center_fixed
  rw [unitExcitation_norm] at h
  change RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide)))) _
  exact h

end YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_center_fixed
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_resolvent_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_resolvent_centered
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_resolvent_norm_floor
