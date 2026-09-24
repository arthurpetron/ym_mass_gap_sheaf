/-
# One-state relative energy gives survival on the SAME joint carrier

The actual n-step energy is at most n times the whole one-step energy.
If n*delta+theta<=1, the SAME response retains at least theta of the
SAME centered squared norm. No norm cap is needed for this relative loss
budget. Cancelling the SAME positive norm against the existing strict form
bound also gives `1-twoStepRate <= 2*delta`, without a norm cap, a sampled
response hypothesis, or division by a real norm.

The one-step estimate and a positive norm floor are explicit inputs, not
constructed for a changing-scale observable here. No spatial-union carrier,
continuum theory, physical Hamiltonian or mass identification is substituted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration
import YMGap.Continuum.ContinuousTransferCalculus
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointEnergySurvival

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection
  (center centered_time_pairing center_orthogonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap
  (completedCenteredScalar completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)

private theorem response_lower (r : Q') (norm response : RC)
    (h : RCle (RCsub norm response) (RCscale r norm)) :
    RCle (RCscale (1-r) norm) response := by
  revert h
  refine Quotient.inductionOn₂ norm response ?_
  intro N F h epsilon he
  obtain ⟨index, hN⟩ := h epsilon he
  refine ⟨index, fun k hk => ?_⟩
  have hneg := Q'.add_le_add_left (N.approx k) _ _ (Q'.neg_le_neg_add (hN k hk))
  change (1-r)*N.approx k ≤ F.approx k + epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
      (.add (.var 1) (.neg (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => r | _ => N.approx k)))
    (Q'.le_trans' _ _ _ hneg (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.var 0) (.add (.neg (.add (.var 0) (.neg (.var 1)))) (.var 2)))
        (.add (.var 1) (.var 2)) (by decide)
        (fun | 0 => N.approx k | 1 => F.approx k | _ => epsilon))))

private theorem remaining_fraction {r theta : Q'} (h : r+theta ≤ (1 : Q')) :
    theta ≤ 1-r := by
  have h' := Q'.add_le_add_right _ _ (-r) h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => r | _ => theta))) h'

private theorem scale_rational (c v : Q') :
    RCscale c (Quotient.mk crealSetoid (ofQ' v)) =
      Quotient.mk crealSetoid (ofQ' (c*v)) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c v).symm

/-- A supplied rational floor cancels a quotient-real factor, without
constructing its reciprocal or choosing a representative as data. -/
private theorem rational_scale_cancel_of_floor {a b v : Q'} {X : RC}
    (hv : (0 : Q') < v)
    (hfloor : RCle (Quotient.mk crealSetoid (ofQ' v)) X)
    (hscaled : RCle (RCscale a X) (RCscale b X)) : a ≤ b := by
  revert hfloor hscaled
  refine Quotient.inductionOn X ?_
  intro A hfloor hscaled
  have hc : leEv (ofQ' a) (ofQ' b) :=
    Z4HalfTimeReflectionStrictJointDenseDyadicGap.leEv_cancel_mul_right_posEv
      ⟨v, hv, hfloor⟩ hscaled
  exact GNSQuotient.GNSData.RCofQ'_le_reflect hc

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "C" => center hw0 hw1 width
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- A relative loss bound retains a fraction of the SAME norm; no division
by a possibly zero norm or separate absolute summand estimate is used. -/
theorem response_ge_fraction_of_relative_energy (n : Nat) (x : V) (delta theta : Q')
    (hbudget : Q'.ofNat n*delta+theta ≤ (1 : Q'))
    (henergy : RCle (temporalEnergy hw0 hw1 width 1 x)
      (RCscale delta (B x x))) :
    RCle (RCscale theta (B x x)) (B x (T n x)) := by
  have hn := RCle_trans (temporalEnergy_linear hw0 hw1 width n x)
    (RCscale_mono (Q'.ofNat_nonneg n) henergy)
  rw [RCscale_RCscale] at hn
  exact RCle_trans
    (RCscale_scalar_mono (remaining_fraction hbudget)
      (completedInner_nonnegative hw0 hw1 width x))
    (response_lower (Q'.ofNat n*delta) (B x x) (B x (T n x)) hn)

/-- A supplied original squared-norm floor becomes a response floor.
The loss budget uses n*delta, not the stronger n*delta*cap/floor. -/
theorem response_floor_of_relative_energy (n : Nat) (x : V) (delta theta v : Q')
    (htheta : (0 : Q') ≤ theta)
    (hbudget : Q'.ofNat n*delta+theta ≤ (1 : Q'))
    (hfloor : RCle (Rq v) (B x x))
    (henergy : RCle (temporalEnergy hw0 hw1 width 1 x)
      (RCscale delta (B x x))) :
    RCle (Rq (theta*v)) (B x (T n x)) := by
  have hv := RCscale_mono htheta hfloor
  rw [scale_rational] at hv
  exact RCle_trans hv
    (response_ge_fraction_of_relative_energy hw0 hw1 width n x delta theta hbudget henergy)

/-- The actual completed centering map identifies the surviving response
with the existing SAME-object connected scalar at every integer time. -/
theorem centered_response_floor (n : Nat) (x : V) (delta theta v : Q')
    (htheta : (0 : Q') ≤ theta)
    (hbudget : Q'.ofNat n*delta+theta ≤ (1 : Q'))
    (hfloor : RCle (Rq v) (B (C x) (C x)))
    (henergy : RCle (temporalEnergy hw0 hw1 width 1 (C x))
      (RCscale delta (B (C x) (C x)))) :
    RCle (Rq (theta*v)) (completedCenteredScalar hw0 hw1 width n x x) := by
  rw [← centered_time_pairing]
  exact response_floor_of_relative_energy hw0 hw1 width n (C x) delta theta v
    htheta hbudget hfloor henergy

/-- One actual nonzero centered state constrains the certified two-step
rate. The lower norm witness is pointwise; no uniform cap or floor is used
in the conclusion, and no new observable family is constructed. -/
theorem twoStepRate_ge_of_relative_energy (x : V) (delta v : Q')
    (hv : (0 : Q') < v) (hfloor : RCle (Rq v) (B (C x) (C x)))
    (henergy : RCle (temporalEnergy hw0 hw1 width 1 (C x))
      (RCscale delta (B (C x) (C x)))) :
    1 - 2*delta ≤ twoStepRate hw0 hw1 width := by
  have hn := RCle_trans (temporalEnergy_linear hw0 hw1 width 2 (C x))
    (RCscale_mono (Q'.ofNat_nonneg 2) henergy)
  rw [RCscale_RCscale] at hn
  have hlower := response_lower (2*delta) (B (C x) (C x)) (B (C x) (T 2 (C x))) hn
  have hupper := completed_twoStep_form_gap hw0 hw1 width (C x)
    (center_orthogonal hw0 hw1 width x)
  exact rational_scale_cancel_of_floor hv hfloor (RCle_trans hlower hupper)

/-- The certified margin is at most twice this state's relative one-step
energy. This is a necessary rate constraint, not an all-vector gap producer. -/
theorem margin_le_twice_relative_energy (x : V) (delta v : Q')
    (hv : (0 : Q') < v) (hfloor : RCle (Rq v) (B (C x) (C x)))
    (henergy : RCle (temporalEnergy hw0 hw1 width 1 (C x))
      (RCscale delta (B (C x) (C x)))) :
    1 + -twoStepRate hw0 hw1 width ≤ 2*delta := by
  have h := Q'.le_add_of_sub_le
    (twoStepRate_ge_of_relative_energy hw0 hw1 width x delta v hv hfloor henergy)
  exact Q'.sub_le_of_le_add (Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- A supplied positive TWO-step spacing calibrates the preceding necessary
margin bound. No physical Hamiltonian or spectral-edge identity is claimed. -/
theorem marginRate_le_of_relative_energy (x : V) (delta v : Q')
    (hv : (0 : Q') < v) (hfloor : RCle (Rq v) (B (C x) (C x)))
    (henergy : RCle (temporalEnergy hw0 hw1 width 1 (C x))
      (RCscale delta (B (C x) (C x))))
    (A : PhysicalSpacing) (j : Nat) :
    Q'.divPos (1 + -twoStepRate hw0 hw1 width) (A.spacing j) (A.spacing_pos j) ≤
      Q'.divPos (2*delta) (A.spacing j) (A.spacing_pos j) :=
  Q'.mul_le_mul_of_nonneg_right _ _ _
    (margin_le_twice_relative_energy hw0 hw1 width x delta v hv hfloor henergy)
    (Q'.le_of_lt (Q'.recipPos_pos (A.spacing j) (A.spacing_pos j)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointEnergySurvival

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointEnergySurvival.response_ge_fraction_of_relative_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointEnergySurvival.response_floor_of_relative_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointEnergySurvival.centered_response_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointEnergySurvival.twoStepRate_ge_of_relative_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointEnergySurvival.margin_le_twice_relative_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointEnergySurvival.marginRate_le_of_relative_energy
