/-
# Quantitative rational-parameter continuity on the original physical bond

The already constructed Cayley-product maps obey positive rational addition
and are exact isometries.  An ordered parameter difference is therefore
exactly the displacement from zero at that difference.  The existing
source-computed zero-parameter radius for ONE supplied original Rows input
controls both parameter orders, with no further analytic premise.

This is fixed-nome, fixed-width continuity.  It is not a positive-real
parameter extension, physical-time calibration, or continuum QFT statement.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitAddition
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameterContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_parameter_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitAddition
  (limitMap_add_parameter)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
  (limitMap_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
  (radius limitMap_near_identity_ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_symm distance_self)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "F" => limitMap hw0 hw1
local notation "D" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Ordered rational parameters have a constructive positive difference. -/
theorem positive_difference {a b : Q'} (h : a < b) :
    (0 : Q') < b-a := by
  apply CReal.pos_of_num_pos
  show 0 < (b + -a).num
  show 0 < b.num * (a.den : Int) + (-a.num) * (b.den : Int)
  have hs : (0 : Int) < b.num * (a.den : Int) - a.num * (b.den : Int) :=
    Int.sub_pos.mpr h
  rw [Int.sub_eq_add_neg] at hs
  rw [Int.neg_mul]
  exact hs

private theorem rational_rat_le {a b : Q'} (h : a ≤ b) :
    RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

/-- For an ordered positive rational pair, the exact SAME physical squared
distance is the displacement at their strictly positive difference. -/
theorem parameter_ordered_distance (a b : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) (hab : a < b) (x : H) :
    D (F b hb x) (F a ha x) =
      D (F (b-a) (positive_difference hab) x) x := by
  have hsum : Q'.eqv b ((b-a)+a) :=
    Q'.eqv_trans _ _ _ (Q'.add_sub_cancel_eqv b a)
      (Q'.add_comm_eqv a (b-a))
  have hparameter : F b hb x =
      F ((b-a)+a) (Q'.add_pos (positive_difference hab) ha) x :=
    limitMap_parameter_congr hw0 hw1 hb
      (Q'.add_pos (positive_difference hab) ha) hsum x
  rw [hparameter,limitMap_add_parameter hw0 hw1 (b-a) a
    (positive_difference hab) ha x,
    limitMap_distance]

/-- One source-computed zero-time radius controls BOTH positive rational
parameters.  The two numerical inequalities express their closeness without
selecting an order or taking a square root of the physical distance. -/
theorem parameter_close_bound (X : R) (e : Q') (he : (0 : Q') < e)
    (a b : Q') (ha : (0 : Q') < a) (hb : (0 : Q') < b)
    (hab : a ≤ b + radius hw0 hw1 X e he)
    (hba : b ≤ a + radius hw0 hw1 X e he) :
    RCle (D (F a ha (ofRows hw0 hw1 X))
        (F b hb (ofRows hw0 hw1 X))) (rat e) := by
  by_cases hlt : a < b
  · have hgap : b-a ≤ radius hw0 hw1 X e he :=
      Q'.sub_le_of_le_add hba
    have hsmall := limitMap_near_identity_ofRows hw0 hw1 X e he (b-a)
      (positive_difference hlt) hgap
    rw [distance_symm,parameter_ordered_distance hw0 hw1 a b ha hb hlt]
    exact hsmall
  · by_cases hgt : b < a
    · have hgap : a-b ≤ radius hw0 hw1 X e he :=
        Q'.sub_le_of_le_add hab
      have hsmall := limitMap_near_identity_ofRows hw0 hw1 X e he (a-b)
        (positive_difference hgt) hgap
      rw [parameter_ordered_distance hw0 hw1 b a hb ha hgt]
      exact hsmall
    · have heq : Q'.eqv a b := by
        show a.num * (b.den : Int) = b.num * (a.den : Int)
        exact Int.le_antisymm (Int.le_of_not_gt hgt) (Int.le_of_not_gt hlt)
      have hmap : F a ha (ofRows hw0 hw1 X) = F b hb (ofRows hw0 hw1 X) :=
        limitMap_parameter_congr hw0 hw1 ha hb heq (ofRows hw0 hw1 X)
      rw [hmap,distance_self]
      exact rational_rat_le (Q'.le_of_lt he)

#print axioms positive_difference
#print axioms parameter_ordered_distance
#print axioms parameter_close_bound

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameterContinuity
