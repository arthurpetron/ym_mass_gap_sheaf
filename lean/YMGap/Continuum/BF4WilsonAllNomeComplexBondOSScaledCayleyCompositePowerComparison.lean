/-
# Actual mixed Cayley powers on the original physical carrier

Commuting finite powers are exact isometries. A squared triangle therefore
amplifies a one-step mixed defect by at most 4^n at exponent 2^n.
The composite is the ACTUAL product of two original Cayley operators,
not an assumed replacement operator or a parameter-addition law.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCompositePowerComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison
  (iterate_add_index iterate_cross_commute)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (iterate_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (fourCopies fourCopies_eq_scale_four)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1

/-- Equal exponents of the two ACTUAL commuting original Cayley maps. -/
def compositeIterate (a b : Q') (ha : (0 : Q') < a) (hb : (0 : Q') < b)
    (x : H) (n : Nat) : H :=
  iterate hw0 hw1 b hb (iterate hw0 hw1 a ha x n) n

theorem compositeIterate_distance (a b : Q') (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (x y : H) (n : Nat) :
    D (compositeIterate hw0 hw1 a b ha hb x n)
      (compositeIterate hw0 hw1 a b ha hb y n) = D x y := by
  unfold compositeIterate
  rw [iterate_distance,iterate_distance]

theorem compositeIterate_add_index (a b : Q') (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (x : H) (m n : Nat) :
    compositeIterate hw0 hw1 a b ha hb x (m+n) =
      compositeIterate hw0 hw1 a b ha hb
        (compositeIterate hw0 hw1 a b ha hb x m) n := by
  unfold compositeIterate
  rw [iterate_add_index,iterate_add_index]
  rw [iterate_cross_commute hw0 hw1 a b ha hb
    (iterate hw0 hw1 a ha x m) n m]

theorem compositeIterate_cross_commute (a b c : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) (hc : (0 : Q') < c)
    (x : H) (m n : Nat) :
    compositeIterate hw0 hw1 a b ha hb (iterate hw0 hw1 c hc x n) m =
      iterate hw0 hw1 c hc (compositeIterate hw0 hw1 a b ha hb x m) n := by
  unfold compositeIterate
  rw [iterate_cross_commute hw0 hw1 a c ha hc x m n,
    iterate_cross_commute hw0 hw1 b c hb hc
      (iterate hw0 hw1 a ha x m) m n]

private theorem square_distance_le_four (a b c : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) (hc : (0 : Q') < c)
    (x : H) (m : Nat) :
    RCle (D (compositeIterate hw0 hw1 a b ha hb x (m+m))
      (iterate hw0 hw1 c hc x (m+m)))
      (RCscale 4 (D (compositeIterate hw0 hw1 a b ha hb x m)
        (iterate hw0 hw1 c hc x m))) := by
  rw [compositeIterate_add_index,iterate_add_index]
  have h := distance_triangle hw0 hw1
    (compositeIterate hw0 hw1 a b ha hb
      (compositeIterate hw0 hw1 a b ha hb x m) m)
    (compositeIterate hw0 hw1 a b ha hb (iterate hw0 hw1 c hc x m) m)
    (iterate hw0 hw1 c hc (iterate hw0 hw1 c hc x m) m)
  rw [compositeIterate_distance,compositeIterate_cross_commute,
    iterate_distance] at h
  change RCle _ (fourCopies (D (compositeIterate hw0 hw1 a b ha hb x m)
    (iterate hw0 hw1 c hc x m))) at h
  rw [fourCopies_eq_scale_four] at h
  exact h

/-- The ACTUAL mixed-step one-point error controls every dyadic composite
power. No uniform bound over input vectors or analytic field is assumed. -/
theorem dyadic_composite_comparison (a b c : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) (hc : (0 : Q') < c)
    (x : H) (n : Nat) :
    RCle (D (compositeIterate hw0 hw1 a b ha hb x (2^n))
      (iterate hw0 hw1 c hc x (2^n)))
      (RCscale ((4 : Q')^n) (D (C b hb (C a ha x)) (C c hc x))) := by
  induction n with
  | zero =>
      simp only [Nat.pow_zero,Q'.pow_zero,RCscale_one]
      exact RCle_refl _
  | succ n ih =>
      have hcount : 2^(n+1) = 2^n+2^n := by
        rw [Nat.pow_succ,Nat.mul_two]
      rw [hcount]
      have h := RCle_trans (square_distance_le_four hw0 hw1 a b c ha hb hc x (2^n))
        (RCscale_mono (by decide : (0 : Q') ≤ 4) ih)
      rw [RCscale_RCscale] at h
      rw [Q'.pow_succ]
      exact h

#print axioms compositeIterate
#print axioms compositeIterate_distance
#print axioms compositeIterate_add_index
#print axioms compositeIterate_cross_commute
#print axioms dyadic_composite_comparison

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCompositePowerComparison
