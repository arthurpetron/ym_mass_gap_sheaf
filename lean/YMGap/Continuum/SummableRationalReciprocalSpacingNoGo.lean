/-
# No bounded summable variation for a reciprocal spacing that vanishes

The physical-gap compiler accepts a direct variation witness for
`1 / spacing`.  This file records the constructive compatibility boundary:
such a witness cannot coexist with a positive spacing stream converging to
zero.  The contradiction uses only the global ceiling supplied by
`SummableRationalStepVariation` and the explicit modulus in `SpacingToZero`.

Consequently, a reciprocal-spacing variation witness is a finite-regulator
interface unless it is replaced by a different, unbounded variation notion.
The theorem below prevents the bounded `SummableRationalStepVariation`
interface from being mistaken for a continuum cutoff-removal certificate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.SummableRationalReciprocalSpacingNoGo

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.SummableRationalStepVariation

/-! ## A small strict-order adapter -/

private theorem lt_add_of_pos_right (a b : Q') (hb : (0 : Q') < b) :
    a < a + b := by
  show a.num * ((a + b).den : Int) < (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key : (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  omega

/-! ## Reciprocal spacing cannot have a bounded summable step budget -/

/-- A positive spacing stream with an explicit modulus of convergence to zero
cannot have a `SummableRationalStepVariation` certificate for its reciprocal.
The latter certificate has a global ceiling, while the spacing modulus forces
the reciprocal above every proposed ceiling.
-/
theorem noSummableReciprocalSpacingVariation
    (A : PhysicalSpacing)
    (Z : SpacingToZero A)
    (data :
      SummableRationalStepVariation
        (fun scale =>
          Q'.recipPos (A.spacing scale) (A.spacing_pos scale))) :
    False := by
  let ceiling := data.globalCeiling
  have ceiling_pos : (0 : Q') < ceiling := by
    exact data.globalCeiling_pos (fun scale =>
      Q'.le_of_lt
        (Q'.recipPos_pos (A.spacing scale) (A.spacing_pos scale)))
  let denominator := (1 : Q') + ceiling
  have denominator_pos : (0 : Q') < denominator := by
    exact Q'.add_pos (by decide) ceiling_pos
  have ceiling_lt_denominator : ceiling < denominator := by
    have hplus : ceiling < ceiling + 1 :=
      lt_add_of_pos_right ceiling 1 (by decide)
    have hcomm : ceiling + 1 ≤ 1 + ceiling :=
      Q'.le_of_eqv (Q'.add_comm_eqv ceiling 1)
    exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hplus hcomm
  let threshold := Q'.divPos 1 denominator denominator_pos
  have threshold_pos : (0 : Q') < threshold := by
    exact Q'.divPos_pos 1 denominator denominator_pos (by decide)
  let j := Z.modulus threshold
  have spacing_le : A.spacing j ≤ threshold := by
    exact Z.spacing_le threshold threshold_pos j (Nat.le_refl _)
  have denominator_mul_spacing_le_one : denominator * A.spacing j ≤ 1 := by
    have hscaled : denominator * A.spacing j ≤ denominator * threshold :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ spacing_le
        (Q'.le_of_lt denominator_pos)
    have hcollapse : (denominator * threshold).eqv (1 : Q') := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv denominator threshold)
        (Q'.divPos_mul_eqv 1 denominator denominator_pos)
    exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)
  have denominator_le_reciprocal : denominator ≤
      Q'.recipPos (A.spacing j) (A.spacing_pos j) := by
    have hquotient : denominator ≤
        Q'.divPos 1 (A.spacing j) (A.spacing_pos j) :=
      Q'.le_divPos_of_mul_le 1 (A.spacing j) (A.spacing_pos j)
        denominator_mul_spacing_le_one
    exact Q'.le_trans' _ _ _ hquotient
      (Q'.le_of_eqv
        (Q'.one_mul_eqv
          (Q'.recipPos (A.spacing j) (A.spacing_pos j))))
  have reciprocal_le_ceiling :
      Q'.recipPos (A.spacing j) (A.spacing_pos j) ≤ ceiling := by
    exact data.le_globalCeiling j
  have denominator_le_ceiling : denominator ≤ ceiling :=
    Q'.le_trans' _ _ _ denominator_le_reciprocal reciprocal_le_ceiling
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' ceiling
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      ceiling_lt_denominator denominator_le_ceiling)

end YMGap.Continuum.SummableRationalReciprocalSpacingNoGo

#print axioms
  YMGap.Continuum.SummableRationalReciprocalSpacingNoGo.noSummableReciprocalSpacingVariation
