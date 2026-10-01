/-
# Limit displacement on the original physical derivative graph

The constructed dyadic Cayley products have a uniform squared-distance bound
on each original graph input. Their supplied represented-product rate passes
that bound to the actual physical limit. The squared-distance triangle doubles
the finite coefficient; no sharp distance-limit continuity is assumed.

The modulus is computed from a supplied represented domain point. Quotient
induction is used only to prove the final proposition for every original
physical graph class. Nome and width remain fixed; this is not a physical
clock or continuum generator calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyProductContinuity
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
import YMGap.Continuum.RationalScalarTwoSidedError
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDomainDisplacement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows ofState rowsOfState ofRows_rowsOfState
    value value_injective value_ofState distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain Point input output ofPoint value_input_ofPoint)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue productLimitRate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyProductContinuity
  (product_domain_distance_le_four)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle distance_symm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "dist" => distance hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The original represented input state supplies both range-bearing Rows. -/
def pointRows (p : Point hw0 hw1 (width := width)) : R :=
  rowsOfState hw0 hw1
    (BF4WilsonAllNomeComplexSectorDerivative.input hw0 hw1 p)

theorem pointRows_input (p : Point hw0 hw1 (width := width)) :
    ofRows hw0 hw1 (pointRows hw0 hw1 p) = input hw0 hw1 (ofPoint hw0 hw1 p) := by
  unfold pointRows
  rw [ofRows_rowsOfState]
  apply value_injective hw0 hw1
  rw [value_ofState]
  exact (value_input_ofPoint hw0 hw1 p).symm

private theorem half_budget (e : Q') :
    RCadd (rat (HalfPow.half*e)) (rat (HalfPow.half*e)) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => ExpNeg.two_halves e))

private theorem rc_add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (A.approx n) (B.approx n)))

private theorem scale_add (a b : Q') (z : RC) :
    RCadd (RCscale a z) (RCscale b z) = RCscale (a+b) z := by
  refine Quotient.inductionOn z ?_
  intro Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.add_mul_eqv a b (Z.approx n))))

private theorem twice_four (t : Q') :
    Q'.eqv ((4*(t*t))+(4*(t*t))) (8*(t*t)) :=
  poly_identity_of_normal_eq
    (.add (.mul (.const 4) (.mul (.var 0) (.var 0)))
      (.mul (.const 4) (.mul (.var 0) (.var 0))))
    (.mul (.const 8) (.mul (.var 0) (.var 0)))
    (by decide) (fun _ => t)

/-- The same finite coefficient is paid twice by the available squared-
distance triangle. This limit bound uses only the ORIGINAL product rate. -/
theorem point_limit_distance_le_eight (t : Q') (ht : (0 : Q') < t)
    (p : Point hw0 hw1 (width := width)) :
    RCle (dist (limitMap hw0 hw1 t ht (input hw0 hw1 (ofPoint hw0 hw1 p)))
      (input hw0 hw1 (ofPoint hw0 hw1 p)))
      (RCscale (8*(t*t)) (N (output hw0 hw1 (ofPoint hw0 hw1 p)))) := by
  let X := pointRows hw0 hw1 p
  let x := input hw0 hw1 (ofPoint hw0 hw1 p)
  let b := RCscale (4*(t*t)) (N (output hw0 hw1 (ofPoint hw0 hw1 p)))
  have hx : ofRows hw0 hw1 X = x := pointRows_input hw0 hw1 p
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro e he
  let q := HalfPow.half*e
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos e he
  let n := productLimitRate hw0 hw1 X t ht q
  have hlim : RCle (dist (limitMap hw0 hw1 t ht x)
      (productValue hw0 hw1 X t ht n)) (rat q) := by
    rw [distance_symm]
    have h := limitMap_bound hw0 hw1 X t ht q hq n (Nat.le_refl n)
    rw [hx] at h
    exact h
  have hfinite : RCle (dist (productValue hw0 hw1 X t ht n) x) b := by
    unfold productValue
    rw [hx]
    exact product_domain_distance_le_four hw0 hw1 t ht
      (ofPoint hw0 hw1 p) n
  have h := RCle_trans
    (distance_triangle hw0 hw1 (limitMap hw0 hw1 t ht x)
      (productValue hw0 hw1 X t ht n) x)
    (RCadd_le_add (RCadd_le_add hlim hlim)
      (RCadd_le_add hfinite hfinite))
  change RCle (dist (limitMap hw0 hw1 t ht x) x)
    (RCadd (RCadd (rat q) (rat q)) (RCadd b b)) at h
  change RCle _ (RCadd (RCadd (rat (HalfPow.half*e))
    (rat (HalfPow.half*e))) (RCadd b b)) at h
  rw [half_budget,rc_add_comm (rat e) (RCadd b b)] at h
  change RCle _ (RCadd
    (RCadd (RCscale (4*(t*t)) (N (output hw0 hw1 (ofPoint hw0 hw1 p))))
      (RCscale (4*(t*t)) (N (output hw0 hw1 (ofPoint hw0 hw1 p)))))
    (rat e)) at h
  rw [scale_add,RCSignedPairBudget.scale_congr (twice_four t)] at h
  exact h

/-- Limit displacement on EVERY class of the original maximal physical
derivative graph; the represented modulus is used only inside Prop. -/
theorem limitMap_domain_distance_le_eight (t : Q') (ht : (0 : Q') < t)
    (d : D) :
    RCle (dist (limitMap hw0 hw1 t ht (input hw0 hw1 d))
      (input hw0 hw1 d))
      (RCscale (8*(t*t)) (N (output hw0 hw1 d))) := by
  rcases d with ⟨a,b⟩
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  exact point_limit_distance_le_eight hw0 hw1 t ht (p,q)

#print axioms pointRows
#print axioms pointRows_input
#print axioms point_limit_distance_le_eight
#print axioms limitMap_domain_distance_le_eight

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDomainDisplacement
