/-
# Rational addition of the original physical Cayley-product limits

The actual mixed-product comparison has a computed all-Rows rate. Two
existing original product-limit rates then identify its limit with the
composition of the two constructed physical maps. Uniqueness in the SAME
completion proves arbitrary positive rational addition on every class.

Nome and width stay fixed. This is not full-real time, identification with
the transfer logarithm, physical spacing calibration, or continuum QFT.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsMixedComparison
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitComposition

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitAddition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue productLimitRows productLimitRate iterate_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsMixedComparison
  (mixedRate mixed_allRows_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCompositePowerComparison
  (compositeIterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_ofRows limitMap_bound productLimit_unique limitMap_parameter_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle distance_symm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "F" => limitMap hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def oneSixteenth : Q' := Q'.mkPos 1 16 (by decide)
private def tolerance (e : Q') : Q' := oneSixteenth*e

private theorem tolerance_pos (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < tolerance e := Q'.mul_pos (by decide) he

private theorem ten_tolerances_le (e : Q') (he : (0 : Q') < e) :
    10*tolerance e ≤ e := by
  have h := Q'.mul_le_mul_of_nonneg_right
    (10*oneSixteenth) 1 e (by decide) (Q'.le_of_lt he)
  have hform : Q'.eqv (10*tolerance e) ((10*oneSixteenth)*e) :=
    poly_identity_of_normal_eq
      (.mul (.const 10) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 10) (.var 0)) (.var 1))
      (by decide) (fun | 0 => oneSixteenth | _ => e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hform)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv e)))

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro eps heps
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b eps (Q'.le_of_lt heps))⟩

private theorem three_bridge (a b c d : H) (q : Q')
    (hab : RCle (D a b) (rat q))
    (hbc : RCle (D b c) (rat q))
    (hcd : RCle (D c d) (rat q)) :
    RCle (D a d) (rat (10*q)) := by
  have hinner := RCle_trans (distance_triangle hw0 hw1 b c d)
    (RCadd_le_add (RCadd_le_add hbc hbc) (RCadd_le_add hcd hcd))
  have houter := RCle_trans (distance_triangle hw0 hw1 a b d)
    (RCadd_le_add (RCadd_le_add hab hab) (RCadd_le_add hinner hinner))
  have hcoef : RCadd (RCadd (rat q) (rat q))
      (RCadd
        (RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)))
        (RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)))) =
      rat (10*q) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0))
          (.add
            (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
            (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))))
        (.mul (.const 10) (.var 0)) (by decide) (fun _ => q)))
  rw [hcoef] at houter
  exact houter

/-- The three cutoffs are computed from ORIGINAL Rows and their actual
constructed first limit, with no representative selection or extra input. -/
def additionRate (X : R) (a b : Q') (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (e : Q') : Nat :=
  max (mixedRate hw0 hw1 X a b (tolerance e))
    (max (productLimitRate hw0 hw1 X a ha (tolerance e))
      (productLimitRate hw0 hw1 (productLimitRows hw0 hw1 X a ha)
        b hb (tolerance e)))

/-- The ACTUAL summed-parameter products converge to the composed actual
maps at a computed rate; only existing source-dependent moduli are used. -/
theorem product_addition_limit_bound (X : R) (a b : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : additionRate hw0 hw1 X a b ha hb e ≤ n) :
    RCle (D (productValue hw0 hw1 X (a+b) (Q'.add_pos ha hb) n)
      (F b hb (F a ha (ofRows hw0 hw1 X)))) (rat e) := by
  let L := productLimitRows hw0 hw1 X a ha
  let q := tolerance e
  have hq : (0 : Q') < q := tolerance_pos e he
  have hmixed : mixedRate hw0 hw1 X a b q ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hlimits : max (productLimitRate hw0 hw1 X a ha q)
      (productLimitRate hw0 hw1 L b hb q) ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hfirst : productLimitRate hw0 hw1 X a ha q ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hlimits
  have hsecond : productLimitRate hw0 hw1 L b hb q ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hlimits
  have hm : RCle
      (D (productValue hw0 hw1 X (a+b) (Q'.add_pos ha hb) n)
        (compositeIterate hw0 hw1 (step a n) (step b n)
          (step_pos a ha n) (step_pos b hb n) (ofRows hw0 hw1 X) (2^n)))
      (rat q) := by
    rw [distance_symm]
    exact mixed_allRows_bound hw0 hw1 X a b ha hb q hq n hmixed
  have ha' : RCle
      (D (compositeIterate hw0 hw1 (step a n) (step b n)
          (step_pos a ha n) (step_pos b hb n) (ofRows hw0 hw1 X) (2^n))
        (productValue hw0 hw1 L b hb n)) (rat q) := by
    unfold compositeIterate productValue
    rw [iterate_distance,← limitMap_ofRows]
    exact limitMap_bound hw0 hw1 X a ha q hq n hfirst
  have hb' : RCle (D (productValue hw0 hw1 L b hb n)
      (F b hb (F a ha (ofRows hw0 hw1 X)))) (rat q) := by
    rw [limitMap_ofRows]
    exact limitMap_bound hw0 hw1 L b hb q hq n hsecond
  have h := three_bridge hw0 hw1 _ _ _ _ q hm ha' hb'
  exact RCle_trans h (rat_le (ten_tolerances_le e he))

/-- Arbitrary positive rational addition on the ACTUAL original Rows limit. -/
theorem limitMap_add_parameter_ofRows (X : R) (a b : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    F (a+b) (Q'.add_pos ha hb) (ofRows hw0 hw1 X) =
      F b hb (F a ha (ofRows hw0 hw1 X)) := by
  let L := productLimitRows hw0 hw1 X a ha
  let Y := productLimitRows hw0 hw1 L b hb
  have hy : ofRows hw0 hw1 Y = F b hb (F a ha (ofRows hw0 hw1 X)) := by
    rw [← limitMap_ofRows,← limitMap_ofRows]
  calc
    F (a+b) (Q'.add_pos ha hb) (ofRows hw0 hw1 X) =
        ofRows hw0 hw1 (productLimitRows hw0 hw1 X (a+b) (Q'.add_pos ha hb)) :=
      limitMap_ofRows hw0 hw1 (a+b) (Q'.add_pos ha hb) X
    _ = ofRows hw0 hw1 Y := by
      apply productLimit_unique hw0 hw1 X Y (a+b) (Q'.add_pos ha hb)
        (additionRate hw0 hw1 X a b ha hb)
      intro e he n hn
      rw [hy]
      exact product_addition_limit_bound hw0 hw1 X a b ha hb e he n hn
    _ = F b hb (F a ha (ofRows hw0 hw1 X)) := hy

/-- The positive rational addition law holds on EVERY original physical
class by quotient induction, not by choosing representatives. -/
theorem limitMap_add_parameter (a b : Q') (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (x : H) :
    F (a+b) (Q'.add_pos ha hb) x = F b hb (F a ha x) := by
  rcases x with ⟨x,y⟩
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact limitMap_add_parameter_ofRows hw0 hw1 (X,Y) a b ha hb

/-- The ACTUAL limit maps commute for arbitrary positive rational parameters. -/
theorem limitMap_commute (a b : Q') (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (x : H) :
    F b hb (F a ha x) = F a ha (F b hb x) := by
  rw [← limitMap_add_parameter,← limitMap_add_parameter]
  exact limitMap_parameter_congr hw0 hw1 (Q'.add_pos ha hb)
    (Q'.add_pos hb ha) (Q'.add_comm_eqv a b) x

#print axioms additionRate
#print axioms product_addition_limit_bound
#print axioms limitMap_add_parameter_ofRows
#print axioms limitMap_add_parameter
#print axioms limitMap_commute

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitAddition
