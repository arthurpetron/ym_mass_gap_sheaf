/-
# Every integer-lag response of the same completed signed family

The original connected bond covariance at lag k is exactly the original
ambient centered-vector pairing at time k+1. The family bond fraction
therefore supplies an actual lag-one Rayleigh floor. Positivity of all
powers of that SAME completed time map propagates it to every integer lag.

The coefficient-square floor is rho(w,|qs|)^(k+1)*varianceFloor(w)*sum(c^2).
It has no spatial-width or regulator factor. This is a LOWER response bound
at fixed strict nome and family size, not a uniform physical-time decay
rate, cross-width comparison, scaling-surviving excitation or mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor
import YMGap.Continuum.BF4WilsonAllNomeResponseLower

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondOrbit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_add)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeTimeForm (intrinsicForm_time_balance)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
  (centeredTimeMoment intrinsicForm_unit_invariant intrinsicForm_unit_invariant_right)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd_pin)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (bondForm)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay (connected connected_source_pin)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyState)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor (completed_family_bond_fraction)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation_norm_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (familyResponseFraction familyResponseFraction_positive)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
  (varianceFloor varianceFloor_positive)
open YMGap.Continuum.BF4WilsonAllNomeResponseLower (response_geometric_lower)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

attribute [local irreducible] intrinsicForm bondForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

private theorem bondForm_time_pin (x y : IntrinsicExpression width) :
    bondForm hw0 hw1 x y =
      Quotient.mk crealSetoid (intrinsicForm hw0 hw1 x (advance 1 y)) := by
  unfold bondForm
  exact Quotient.sound (crossOdd_pin hw0 hw1 x y).symm

/-- The exact one-step offset is retained for EVERY original intrinsic source,
including multitime sources. Both original vacuum means remain unchanged. -/
theorem connected_source_time_pairing (lag : Nat) (x : IntrinsicExpression width) :
    connected hw0 hw1 lag (ofSource hw0 hw1 x) (ofSource hw0 hw1 x) =
      completedInner hw0 hw1 (centeredVector hw0 hw1 x)
        (completedTime hw0 hw1 (lag+1) (centeredVector hw0 hw1 x)) := by
  rw [connected_source_pin, bondForm_time_pin, bondForm_time_pin, bondForm_time_pin,
    centeredVector_time_pairing]
  apply Quotient.sound
  change Equiv
    (sub (intrinsicForm hw0 hw1 x (advance 1 (advance lag x)))
      (mul (intrinsicForm hw0 hw1 x (advance 1 (unit width)))
        (intrinsicForm hw0 hw1 (unit width) (advance 1 x))))
    (centeredTimeMoment hw0 hw1 (lag+1) x x)
  rw [advance_add, Nat.add_comm 1 lag]
  exact equiv_sub (Equiv.refl _)
    (Pivot2.mul_congr
      ((intrinsicForm_time_balance hw0 hw1 1 x (unit width)).symm.trans
        (intrinsicForm_unit_invariant hw0 hw1 1 x))
      (intrinsicForm_unit_invariant_right hw0 hw1 1 x))

private theorem power_positive (a : Q') (ha : (0 : Q') < a) :
    ∀ n : Nat, (0 : Q') < a^n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos ha (power_positive a ha n)

private theorem scale_rational (r v : Q') :
    RCscale r (Quotient.mk crealSetoid (ofQ' v)) =
      Quotient.mk crealSetoid (ofQ' (r*v)) :=
  Quotient.sound (CRealAlg.ofQ'_mul r v).symm

variable {base : Nat} (hwidth : base < width) (qs : List Z4Plaq)
  (c : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)

local notation "wideFaces" =>
  (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
local notation "x" => familyState width qs c wideFaces
local notation "v" => centeredVector hw0 hw1 x
local notation "rho" => familyResponseFraction hw0 hw1 qs.length
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Construct the Rayleigh input for the ACTUAL whole signed family. -/
theorem family_rayleigh_floor : RCle (RCscale rho (B v v)) (B v (T 1 v)) := by
  have h := completed_family_bond_fraction hw0 hw1 hwidth qs c hqs
  rw [connected_source_time_pairing] at h
  exact h

/-- Every integer power of the SAME transfer retains the supplied fraction. -/
theorem family_time_geometric_floor (lag : Nat) :
    RCle (RCscale (rho^lag) (B v v)) (B v (T lag v)) :=
  response_geometric_lower hw0 hw1 v rho
    (Q'.le_of_lt (familyResponseFraction_positive hw0 hw1 qs.length))
    (family_rayleigh_floor hw0 hw1 hwidth qs c hqs) lag

/-- A positive coefficient-square lower bound for the ORIGINAL physical
connected covariance at EVERY lag, with its exact one-step offset. -/
theorem family_bond_geometric_floor (lag : Nat) (hn : qs.Nodup) :
    RCle (Quotient.mk crealSetoid
      (ofQ' (rho^(lag+1)*(varianceFloor w hw0*listQSum (fun p => c p*c p) qs))))
      (connected hw0 hw1 lag (ofSource hw0 hw1 x) (ofSource hw0 hw1 x)) := by
  have h := RCscale_mono (Q'.le_of_lt
    (power_positive rho (familyResponseFraction_positive hw0 hw1 qs.length) (lag+1)))
    (familyExcitation_norm_floor hw0 hw1 width qs c wideFaces hn)
  rw [scale_rational] at h
  rw [connected_source_time_pairing]
  exact RCle_trans h (family_time_geometric_floor hw0 hw1 hwidth qs c hqs (lag+1))

/-- A nonzero signed coefficient vector on distinct interior faces has a
nonzero physical connected response at every integer lag. Fixed nome only. -/
theorem family_bond_response_ne_zero (lag : Nat) (hn : qs.Nodup)
    (hc : (0 : Q') < listQSum (fun p => c p*c p) qs) :
    connected hw0 hw1 lag (ofSource hw0 hw1 x) (ofSource hw0 hw1 x) ≠ RCzero := by
  intro hz
  have h := family_bond_geometric_floor hw0 hw1 hwidth qs c hqs lag hn
  rw [hz] at h
  have hle : rho^(lag+1)*(varianceFloor w hw0*listQSum (fun p => c p*c p) qs) ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon hp
    obtain ⟨N, hN⟩ := h epsilon hp
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le
      (Q'.mul_pos
        (power_positive rho (familyResponseFraction_positive hw0 hw1 qs.length) (lag+1))
        (Q'.mul_pos (varianceFloor_positive hw0 hw1) hc)) hle)

#print axioms connected_source_time_pairing
#print axioms family_rayleigh_floor
#print axioms family_time_geometric_floor
#print axioms family_bond_geometric_floor
#print axioms family_bond_response_ne_zero

end YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondOrbit
