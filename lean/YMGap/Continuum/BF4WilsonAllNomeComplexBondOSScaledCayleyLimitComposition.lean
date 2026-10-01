/-
# Exact doubling of the original physical Cayley-product limit

The SAME finite products obey P_(n+1)(2t)=P_n(t)^2. Their constructed
original Rows limits therefore obey F_(2t)=F_t composed with F_t.
Two computed forward moduli give an explicit comparison rate. This is
the doubling case only, not arbitrary parameter addition, physical-time
calibration, continuum QFT or a mass-gap theorem.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInverse

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameter
  (iterate_parameter_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison
  (iterate_add_index)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos double_step_eqv)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue productLimitRows productLimitRate iterate_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_ofRows limitMap_bound productLimit_unique)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "F" => limitMap hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def doublePositive (t : Q') (ht : (0 : Q') < t) : (0 : Q') < 2*t :=
  Q'.mul_pos (by decide : (0 : Q') < 2) ht

private def quarter (e : Q') : Q' := HalfPow.half*(HalfPow.half*e)

private theorem quarter_positive {e : Q'} (he : (0 : Q') < e) :
    (0 : Q') < quarter e :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)

private theorem four_quarters (e : Q') :
    RCadd (RCadd (rat (quarter e)) (rat (quarter e)))
      (RCadd (rat (quarter e)) (rat (quarter e))) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*e))
        (ExpNeg.two_halves (HalfPow.half*e))) (ExpNeg.two_halves e)))

theorem doubled_step_eqv (t : Q') (n : Nat) :
    Q'.eqv (step (2*t) (n+1)) (step t n) := by
  have h : Q'.eqv (step (2*t) (n+1)) (2*step t (n+1)) := by
    unfold step
    exact poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.var 1))
      (.mul (.const 2) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => t | _ => HalfPow.half^(n+1))
  exact Q'.eqv_trans _ _ _ h (double_step_eqv t n)

/-- The actual doubled-parameter product is an exact finite square. -/
theorem product_double_succ (X : R) (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    productValue hw0 hw1 X (2*t) (doublePositive t ht) (n+1) =
      iterate hw0 hw1 (step t n) (step_pos t ht n)
        (productValue hw0 hw1 X t ht n) (2^n) := by
  unfold productValue
  rw [iterate_parameter_congr hw0 hw1
    (step_pos (2*t) (doublePositive t ht) (n+1)) (step_pos t ht n)
    (doubled_step_eqv t n)]
  have hcount : 2^(n+1) = 2^n+2^n := by
    rw [Nat.pow_succ,Nat.mul_two]
  rw [hcount,iterate_add_index]

/-- Both moduli are computed from constructed ORIGINAL Rows. The extra
one aligns the exact finite square at index n with parameter 2t at n+1. -/
def doubleRate (X : R) (t : Q') (ht : (0 : Q') < t) (e : Q') : Nat :=
  max (productLimitRate hw0 hw1 X t ht (quarter e))
    (productLimitRate hw0 hw1 (productLimitRows hw0 hw1 X t ht) t ht
      (quarter e))+1

theorem product_double_limit_bound (X : R) (t : Q') (ht : (0 : Q') < t)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : doubleRate hw0 hw1 X t ht e ≤ n) :
    RCle (D (productValue hw0 hw1 X (2*t) (doublePositive t ht) n)
      (F t ht (F t ht (ofRows hw0 hw1 X)))) (rat e) := by
  cases n with
  | zero =>
      unfold doubleRate at hn
      exact False.elim (Nat.not_succ_le_zero _ hn)
  | succ n =>
      let L := productLimitRows hw0 hw1 X t ht
      have hmax : max (productLimitRate hw0 hw1 X t ht (quarter e))
          (productLimitRate hw0 hw1 L t ht (quarter e)) ≤ n :=
        Nat.le_of_succ_le_succ hn
      have hfirst : productLimitRate hw0 hw1 X t ht (quarter e) ≤ n := by
        exact Nat.le_trans (Nat.le_max_left _ _) hmax
      have hsecond : productLimitRate hw0 hw1 L t ht (quarter e) ≤ n := by
        exact Nat.le_trans (Nat.le_max_right _ _) hmax
      have ha := limitMap_bound hw0 hw1 X t ht (quarter e)
        (quarter_positive he) n hfirst
      have hb := limitMap_bound hw0 hw1 L t ht (quarter e)
        (quarter_positive he) n hsecond
      have ha' : RCle
          (D (iterate hw0 hw1 (step t n) (step_pos t ht n)
              (productValue hw0 hw1 X t ht n) (2^n))
            (productValue hw0 hw1 L t ht n)) (rat (quarter e)) := by
        unfold productValue
        rw [iterate_distance,← limitMap_ofRows]
        exact ha
      have hb' : RCle (D (productValue hw0 hw1 L t ht n)
          (F t ht (F t ht (ofRows hw0 hw1 X)))) (rat (quarter e)) := by
        rw [limitMap_ofRows]
        exact hb
      rw [product_double_succ]
      have h := RCle_trans (distance_triangle hw0 hw1
          (iterate hw0 hw1 (step t n) (step_pos t ht n)
            (productValue hw0 hw1 X t ht n) (2^n))
          (productValue hw0 hw1 L t ht n) (F t ht (F t ht (ofRows hw0 hw1 X))))
        (RCadd_le_add (RCadd_le_add ha' ha') (RCadd_le_add hb' hb'))
      rw [four_quarters] at h
      exact h

/-- Exact doubling of the ACTUAL represented physical limit. -/
theorem limitMap_double_ofRows (X : R) (t : Q') (ht : (0 : Q') < t) :
    F (2*t) (doublePositive t ht) (ofRows hw0 hw1 X) =
      F t ht (F t ht (ofRows hw0 hw1 X)) := by
  let L := productLimitRows hw0 hw1 X t ht
  let Y := productLimitRows hw0 hw1 L t ht
  have hy : ofRows hw0 hw1 Y = F t ht (F t ht (ofRows hw0 hw1 X)) := by
    rw [← limitMap_ofRows,← limitMap_ofRows]
  calc
    F (2*t) (doublePositive t ht) (ofRows hw0 hw1 X) =
      ofRows hw0 hw1 (productLimitRows hw0 hw1 X (2*t) (doublePositive t ht)) :=
        limitMap_ofRows hw0 hw1 (2*t) (doublePositive t ht) X
    _ = ofRows hw0 hw1 Y := by
      apply productLimit_unique hw0 hw1 X Y (2*t) (doublePositive t ht)
        (doubleRate hw0 hw1 X t ht)
      intro e he n hn
      rw [hy]
      exact product_double_limit_bound hw0 hw1 X t ht e he n hn
    _ = F t ht (F t ht (ofRows hw0 hw1 X)) := hy

/-- The doubling law holds on EVERY original complex physical class.
This is not asserted to be arbitrary rational parameter addition. -/
theorem limitMap_double (t : Q') (ht : (0 : Q') < t) (x : H) :
    F (2*t) (doublePositive t ht) x = F t ht (F t ht x) := by
  rcases x with ⟨x,y⟩
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact limitMap_double_ofRows hw0 hw1 (X,Y) t ht

#print axioms doublePositive
#print axioms doubled_step_eqv
#print axioms product_double_succ
#print axioms doubleRate
#print axioms product_double_limit_bound
#print axioms limitMap_double_ofRows
#print axioms limitMap_double

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitComposition
