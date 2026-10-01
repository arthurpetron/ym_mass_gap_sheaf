/-
# Mixed finite-product comparison for every supplied original physical Row

One computed second-core source approximates the supplied Rows for a requested
precision. The checked homogeneous mixed-error estimate and its original
preimage ceiling then give a computed geometric depth. Finite Cayley
isometries transport the same source on both sides of the comparison.
No arbitrary source cap, choice, physical-time identification, continuum
limit, or parameter-addition law is assumed here.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedProducts
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsMixedComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative (input)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCore (first)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (coreSource coreSource_near productValue product_near_core tolerance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCompositePowerComparison
  (compositeIterate compositeIterate_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedBound
  (mixedCoefficient)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedProducts
  (mixed_products_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (preimageCeiling preimageCeiling_nonnegative preimageNorm_le_ceiling)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (quarter distance_triangle distance_symm)
open YMGap.Continuum.PositiveContractionResidual
  (geometricCutoff geometric_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro eps heps
  exact ⟨0, fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b eps (Q'.le_of_lt heps))⟩

private theorem mixedCoefficient_nonnegative (a b : Q')
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ mixedCoefficient a b := by
  have hsqA : (0 : Q') ≤ a*a := Q'.mul_nonneg _ _ ha ha
  have hsqB : (0 : Q') ≤ b*b := Q'.mul_nonneg _ _ hb hb
  have hsum : (0 : Q') ≤ a+b := Q'.zero_le_add _ _ ha hb
  have hsqC : (0 : Q') ≤ (a+b)*(a+b) := Q'.mul_nonneg _ _ hsum hsum
  have ha4 := Q'.mul_nonneg _ _ hsqA hsqA
  have hb4 := Q'.mul_nonneg _ _ hsqB hsqB
  have hc4 := Q'.mul_nonneg _ _ hsqC hsqC
  have hcross : (0 : Q') ≤ ((b*b)*4)*(4*(a*a)) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hsqB (by decide))
      (Q'.mul_nonneg _ _ (by decide) hsqA)
  unfold mixedCoefficient
  dsimp only
  apply Q'.zero_le_add
  · apply Q'.mul_nonneg _ _ (by decide)
    apply Q'.zero_le_add
    · apply Q'.mul_nonneg _ _ (by decide)
      apply Q'.zero_le_add
      · exact Q'.mul_nonneg _ _ (by decide)
          (Q'.mul_nonneg _ _ (by decide) hb4)
      · exact Q'.mul_nonneg _ _ (by decide)
          (Q'.mul_nonneg _ _ (by decide) ha4)
    · exact Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ (by decide) hc4)
  · exact Q'.mul_nonneg _ _ (by decide) hcross

/-- The rational budget is computed from the SAME requested source and the
exact (unrounded) mixed-step coefficient. -/
def mixedBudget (X : R) (a b e : Q') : Q' :=
  mixedCoefficient a b * preimageCeiling hw0 hw1 (coreSource hw0 hw1 X e)

theorem mixedBudget_nonnegative (X : R) (a b : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) (e : Q') :
    (0 : Q') ≤ mixedBudget hw0 hw1 X a b e := by
  unfold mixedBudget
  exact Q'.mul_nonneg _ _
    (mixedCoefficient_nonnegative a b (Q'.le_of_lt ha) (Q'.le_of_lt hb))
    (preimageCeiling_nonnegative hw0 hw1 (coreSource hw0 hw1 X e))

/-- One source choice at requested precision, then a finite geometric
cutoff depending on its actual represented preimage ceiling. -/
def mixedRate (X : R) (a b e : Q') : Nat :=
  geometricCutoff quarter (mixedBudget hw0 hw1 X a b e) (tolerance e)

private theorem ten_tolerances_le (e : Q') (he : (0 : Q') < e) :
    10*tolerance e ≤ e := by
  have h := Q'.mul_le_mul_of_nonneg_right
    (10*(Q'.mkPos 1 16 (by decide))) 1 e (by decide) (Q'.le_of_lt he)
  have ha : Q'.eqv (10*tolerance e)
      ((10*(Q'.mkPos 1 16 (by decide)))*e) := by
    unfold tolerance
    exact poly_identity_of_normal_eq
      (.mul (.const 10) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 10) (.var 0)) (.var 1))
      (by decide)
      (fun | 0 => (Q'.mkPos 1 16 (by decide)) | _ => e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ha)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv e)))

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
        (.mul (.const 10) (.var 0))
        (by decide) (fun _ => q)))
  rw [hcoef] at houter
  exact houter

/-- Every index past the computed cutoff compares the two ACTUAL mixed
finite products on the supplied original Rows. -/
theorem mixed_allRows_bound (X : R) (a b : Q')
    (ha : (0 : Q') < a) (hb : (0 : Q') < b)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : mixedRate hw0 hw1 X a b e ≤ n) :
    RCle
      (D
        (compositeIterate hw0 hw1 (step a n) (step b n)
          (step_pos a ha n) (step_pos b hb n) (ofRows hw0 hw1 X) (2^n))
        (productValue hw0 hw1 X (a+b) (Q'.add_pos ha hb) n))
      (rat e) := by
  let Y := coreSource hw0 hw1 X e
  let x := ofRows hw0 hw1 X
  let y := input hw0 hw1 (first hw0 hw1 Y)
  let q := tolerance e
  have hq : (0 : Q') < q :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit.tolerance_positive e he
  have hnear : RCle (D x y) (rat q) := coreSource_near hw0 hw1 X e he
  have hleft : RCle
      (D
        (compositeIterate hw0 hw1 (step a n) (step b n)
          (step_pos a ha n) (step_pos b hb n) x (2^n))
        (compositeIterate hw0 hw1 (step a n) (step b n)
          (step_pos a ha n) (step_pos b hb n) y (2^n)))
      (rat q) := by
    rw [compositeIterate_distance]
    exact hnear
  have hcore := mixed_products_bound hw0 hw1 Y a b ha hb n
  have hcap := preimageNorm_le_ceiling hw0 hw1 Y
  have hcoefficient : (0 : Q') ≤ quarter^n*mixedCoefficient a b :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg quarter (by decide) n)
      (mixedCoefficient_nonnegative a b (Q'.le_of_lt ha) (Q'.le_of_lt hb))
  have hscaled := RCscale_mono hcoefficient hcap
  have hcore' := RCle_trans hcore hscaled
  have hrat : RCscale (quarter^n*mixedCoefficient a b)
      (rat (preimageCeiling hw0 hw1 Y)) =
      rat (quarter^n*mixedBudget hw0 hw1 X a b e) := by
    have hmul : RCscale (quarter^n*mixedCoefficient a b)
        (rat (preimageCeiling hw0 hw1 Y)) =
        rat ((quarter^n*mixedCoefficient a b)*preimageCeiling hw0 hw1 Y) :=
      Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
    rw [hmul]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_assoc_eqv (quarter^n) (mixedCoefficient a b)
        (preimageCeiling hw0 hw1 Y)))
  rw [hrat] at hcore'
  have hgeom : quarter^n*mixedBudget hw0 hw1 X a b e ≤ q :=
    geometric_bound (q := quarter)
      (by decide) (by decide)
      (mixedBudget_nonnegative hw0 hw1 X a b ha hb e) hq n hn
  have hmiddle := RCle_trans hcore' (rat_le hgeom)
  have hright : RCle
      (D
        (iterate hw0 hw1 (step (a+b) n)
          (step_pos (a+b) (Q'.add_pos ha hb) n) y (2^n))
        (productValue hw0 hw1 X (a+b) (Q'.add_pos ha hb) n))
      (rat q) := by
    rw [distance_symm]
    exact product_near_core hw0 hw1 X e he (a+b) (Q'.add_pos ha hb) n
  have h := three_bridge hw0 hw1 _ _ _ _ q hleft hmiddle hright
  exact RCle_trans h (rat_le (ten_tolerances_le e he))

#print axioms mixedBudget
#print axioms mixedBudget_nonnegative
#print axioms mixedRate
#print axioms mixed_allRows_bound

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsMixedComparison
