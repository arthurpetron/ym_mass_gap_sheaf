/-
# A necessary coefficient screen for original family reference certificates

Acceptance by the EXISTING finite reference checker forces its coefficient
above the actual unfiltered family Rayleigh floor. The literal family energy,
OWN variance, action and positive partition are transported by their existing
pins. No moments need to be expanded to reject an infeasible coefficient.

This neither constructs an accepted certificate nor bounds a filtered window.
It is a fixed-nome finite-support restriction, not a continuum mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRayleighFloor
import YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor

namespace YMGap.Continuum.BF4WilsonAllNomeFamilyReferenceScreen

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRayleighFloor
  (family_energy_variance_floor)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
  (lower upper upper_positive)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
  (familyExpression family_within)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit
  (finiteEnergy finiteEnergy_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit (finiteVariance)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor
  (finite_family_energy_pin finite_family_variance_pin)
open YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin
  (referenceMargin referenceCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base width : Nat} (hwidth : base < width)
  (qs : List Z4Plaq) (coeff : Z4Plaq → Q') (hn : qs.Nodup)
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)

local notation "wideFaces" =>
  (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
local notation "e" => familyExpression width qs coeff wideFaces
local notation "he" => family_within width qs coeff wideFaces

include hn in
/-- Every accepted ORIGINAL family certificate passes this moment-free
necessary test. Zero coefficients/families cannot evade the positive margin. -/
theorem certificate_coefficient_necessary {s : Nat} {c : Q'}
    (C : BF4WilsonAllNomeFiniteReferenceMargin.Certificate hw0 hw1 e he s c) :
    lower w ≤ (2400*upper w*Q'.ofNat qs.length)*c := by
  have hconditions : (0 : Q') ≤ c ∧ (0 : Q') < C.tolerance ∧
      referenceCutoff hw0 hw1 e he c (s+1) C.tolerance ≤ C.pivot ∧
      C.tolerance+C.tolerance ≤ referenceMargin hw0 hw1 e c C.pivot (s+1) :=
    of_decide_eq_true C.accepted
  let k := C.cutoff hw0 hw1 e he
  have hk : C.cutoff hw0 hw1 e he ≤ k := Nat.le_refl _
  let V := finiteVariance hw0 hw1 e k (s+1)
  let E := finiteEnergy hw0 hw1 e k (s+1)
  let H := 2400*upper w*Q'.ofNat qs.length
  have hE : (0 : Q') ≤ E := finiteEnergy_nonnegative hw0 hw1 e he k (s+1)
  have hslack : C.tolerance ≤ E+C.tolerance := by
    simpa only [Q'.zero_add'] using Q'.add_le_add_right _ _ C.tolerance hE
  have hproduct : (0 : Q') < c*V := Q'.pos_of_lt_of_le hconditions.2.1
    (Q'.le_trans' _ _ _ hslack (C.reference_strict_ratio hw0 hw1 e he k hk))
  have hV : (0 : Q') < V := by
    have hcn : (0 : Int) ≤ c.num := (Q'.zero_le_iff_num_nonneg c).mp hconditions.1
    have hpn : (0 : Int) < c.num*V.num := Q'.num_pos_of_pos hproduct
    rcases Int.lt_or_le 0 V.num with hvn | hvn
    · change (0 : Int)*(V.den : Int) < V.num*(1 : Int)
      simpa only [Int.zero_mul, Int.mul_one] using hvn
    · have hnp : c.num*V.num ≤ c.num*0 :=
        Int.mul_le_mul_of_nonneg_left hvn hcn
      simp only [Int.mul_zero] at hnp
      omega
  have hH : (0 : Q') ≤ H := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt (upper_positive hw0)))
    (Q'.ofNat_nonneg _)
  have hpV := finite_family_variance_pin hw0 hw1 hwidth qs coeff hqs k (s+1)
  have hpE := finite_family_energy_pin hw0 hw1 hwidth qs coeff hqs k (s+1)
  have hcore := family_energy_variance_floor hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) (s+1) qs hn wideFaces coeff
  have hfloor : lower w*V ≤ H*E :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (lower w) _ _ hpV))
      (Q'.le_trans' _ _ _ hcore
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left H _ _ (Q'.eqv_symm hpE))))
  have hratio : E ≤ c*V := C.reference_ratio hw0 hw1 e he k hk
  have hpaid : lower w*V ≤ H*(c*V) := Q'.le_trans' _ _ _ hfloor
    (Q'.mul_le_mul_of_nonneg_left _ _ H hratio hH)
  have hclear : V*lower w ≤ V*(H*c) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv V (lower w)))
      (Q'.le_trans' _ _ _ hpaid
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv H c V))
          (Q'.mul_comm_eqv (H*c) V))))
  exact Q'.le_of_mul_le_mul_left hclear hV

#print axioms certificate_coefficient_necessary

end YMGap.Continuum.BF4WilsonAllNomeFamilyReferenceScreen
