/-
# An explicit strict excitation of the actual completed physical transfer

Take d = T root - root, using the SAME completed conditional transfer.
Stationarity makes d exactly vacuum-orthogonal. The previously constructed
positive root/probe pairing gives a positive norm floor for d; testing its
own displacement against root gives a positive Rayleigh-deficit floor.

Both floors are rational data, computed from the physical heat-product floor
and two fixed representative norm ceilings. This is one strict excitation
at w=1/400 and extent one, NOT a common rate on the whole complement,
geometric-time identification, vacuum uniqueness, or continuum mass gap.
-/

import YMGap.Continuum.BF4PhysicalCubeDissipation
import YMGap.Continuum.BF4PhysicalCubeTransferNonidentity

namespace YMGap.Continuum.BF4PhysicalCubeStrictExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.ScaledGNSCompletionEstimates
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeCenteredDensity
open YMGap.Continuum.BF4PhysicalCubeDissipation
open YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing
open YMGap.Continuum.BF4PhysicalCubeTransferNonidentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "B" => cubeReflectedInner
local notation "T" => cubeTransfer
local notation "j" => cubeReflectedEmbed

/-- A vector, not a chosen representative of an unspecified quotient point. -/
def excitation : CubeSectorVacuumComplement := centeredDisplacement (j rootVector)

def probeCeiling : Q' := Q'.ofNat ((D).normCeil (constCauchy D probeVector))

private theorem normCeil_pos (data : GNSData) (rep : CauchyGNS data) :
    (0 : Q') < Q'.ofNat (data.normCeil rep) := Q'.ofNat_succ_pos _

theorem probeCeiling_pos : (0 : Q') < probeCeiling := normCeil_pos D (constCauchy D probeVector)

theorem probe_norm_ceiling : RCle (B (j probeVector) (j probeVector)) (Rq probeCeiling) := by
  have h := scaledInner_normCeil D anchorNormalization (constCauchy D probeVector)
  change RCle (scaledCompletedInner D anchorNormalization
    (toScaledCompletion D anchorNormalization (embedV D probeVector))
    (toScaledCompletion D anchorNormalization (embedV D probeVector))) (Rq probeCeiling) at h
  rw [toScaledCompletion_embed] at h
  exact h

theorem excitation_probe_floor : RCle (Rq twoStepFloor) (B excitation.val (j probeVector)) := by
  change RCle (Rq twoStepFloor) (B (displacement (j rootVector)) (j probeVector))
  rw [displacement_pairing, root_probe_pairing_zero, sub_zero]
  exact transferred_root_probe_floor

def excitationNormFloor : Q' := Q'.divPos (twoStepFloor * twoStepFloor) probeCeiling probeCeiling_pos

theorem excitationNormFloor_pos : (0 : Q') < excitationNormFloor :=
  Q'.divPos_pos _ _ _ (Q'.mul_pos twoStepFloor_pos twoStepFloor_pos)

theorem excitation_norm_floor : RCle (Rq excitationNormFloor) (B excitation.val excitation.val) :=
  norm_floor_of_test excitation.val (j probeVector) twoStepFloor probeCeiling
    (Q'.le_of_lt twoStepFloor_pos) probeCeiling_pos probe_norm_ceiling excitation_probe_floor

def excitationNormCeiling : Q' := rootCeiling + rootCeiling

theorem excitationNormCeiling_pos : (0 : Q') < excitationNormCeiling :=
  Q'.add_pos rootCeiling_pos rootCeiling_pos

theorem excitation_norm_ceiling : RCle (B excitation.val excitation.val) (Rq excitationNormCeiling) :=
  displacement_norm_ceiling (j rootVector) rootCeiling root_norm_bound

/-- Self-adjointness pays the second displacement with the first one's norm. -/
theorem excitation_displacement_root :
    B (displacement excitation.val) (j rootVector) = B excitation.val excitation.val :=
  displacement_selfAdjoint excitation.val (j rootVector)

def excitationDeficitFloor : Q' := Q'.divPos (excitationNormFloor * excitationNormFloor)
  (2 * rootCeiling) (Q'.mul_pos (by decide) rootCeiling_pos)

theorem excitationDeficitFloor_pos : (0 : Q') < excitationDeficitFloor :=
  Q'.divPos_pos _ _ _ (Q'.mul_pos excitationNormFloor_pos excitationNormFloor_pos)

theorem excitation_deficit_floor : RCle (Rq excitationDeficitFloor) (dissipation excitation.val) := by
  apply dissipation_floor_of_test excitation.val (j rootVector) excitationNormFloor rootCeiling
    (Q'.le_of_lt excitationNormFloor_pos) rootCeiling_pos root_norm_bound
  rw [excitation_displacement_root]
  exact excitation_norm_floor

/-- A strict, quantitatively witnessed Rayleigh inequality on the SAME
completed vacuum complement, with no supplied gap premise. -/
theorem excitation_strict_form :
    RCle (RCadd (B (sectorComplementTransfer excitation).val excitation.val) (Rq excitationDeficitFloor))
      (B excitation.val excitation.val) :=
  strict_form_of_deficit excitation.val excitationDeficitFloor excitation_deficit_floor

private theorem positive_constant_not_le_zero (q : Q') (hq : (0 : Q') < q) :
    ¬ RCle (Rq q) RCzero := by
  intro h
  obtain ⟨N, hN⟩ := h (HalfPow.half * q) (ExpNeg.half_mul_pos q hq)
  have hbad := hN N (Nat.le_refl N)
  change q ≤ 0 + HalfPow.half * q at hbad
  rw [Q'.zero_add'] at hbad
  have hprod : q * 1 ≤ q * HalfPow.half := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ hbad (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact (by decide : ¬ (1 : Q') ≤ HalfPow.half) (Q'.le_of_mul_le_mul_left hprod hq)

theorem excitation_ne_zero : excitation.val ≠ j [] := by
  intro hzero
  have h := excitation_norm_floor
  rw [hzero, cubeReflectedInner_zero_left] at h
  exact positive_constant_not_le_zero excitationNormFloor excitationNormFloor_pos h

theorem excitation_not_fixed : sectorComplementTransfer excitation ≠ excitation := by
  intro hfixed
  have heq : T excitation.val = excitation.val := congrArg Subtype.val hfixed
  have h := excitation_deficit_floor
  unfold dissipation at h
  rw [heq, sub_self] at h
  exact positive_constant_not_le_zero excitationDeficitFloor excitationDeficitFloor_pos h

end YMGap.Continuum.BF4PhysicalCubeStrictExcitation

#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.probeCeiling
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.probeCeiling_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.probe_norm_ceiling
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation_probe_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitationNormFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitationNormFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation_norm_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitationNormCeiling
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitationNormCeiling_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation_norm_ceiling
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation_displacement_root
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitationDeficitFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitationDeficitFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation_deficit_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation_strict_form
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation_ne_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeStrictExcitation.excitation_not_fixed
