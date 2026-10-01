/-
# Infinitesimal phase of the original physical Cayley product

The finite dyadic products of the ACTUAL physical Cayley map have a
second-core tangent with coefficient `-2 i`, not `-i`.  This is a fixed
nome/width statement about the existing bond derivative graph.  It does
not identify that derivative with the logarithm of the lattice transfer,
choose a physical lattice spacing, or assert continuum survival.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledBound
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyInfinitesimal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance inner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos double_step_pos double_step_eqv)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameter
  (iterate_parameter_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison
  (dyadic_iterate_comparison)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff graphError)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le linked_error_norm_le_four)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (quarter distance_triangle distance_self)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "N" => normSq hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "dist" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Literal finite product on the same completed physical carrier, with no
represented-source restriction. -/
def orbit (t : Q') (ht : (0 : Q') < t) (x : H) (n : Nat) : H :=
  iterate hw0 hw1 (step t n) (step_pos t ht n) x (2^n)

private def fourth (a : Q') : Q' := (a*a)*(a*a)

private def fourthExpr (p : PolyExpr) : PolyExpr := .mul (.mul p p) (.mul p p)

private def coefficient (t : Q') (n : Nat) : Q' :=
  ((4 : Q')^n)*(352*fourth (step t (n+1)))

private theorem coefficient_eqv (t : Q') (n : Nat) :
    Q'.eqv (coefficient t n) ((22*fourth t)*quarter^n) := by
  have hhalf : Q'.eqv ((4 : Q')*fourth HalfPow.half) quarter := by decide
  have hbase : Q'.eqv (352*fourth HalfPow.half) 22 := by decide
  induction n with
  | zero =>
      have h₁ : Q'.eqv (coefficient t 0)
          ((352*fourth HalfPow.half)*fourth t) := by
        unfold coefficient fourth step
        simp only [Q'.pow_zero,Q'.pow_succ]
        exact poly_identity_of_normal_eq
          (.mul (.const 1)
            (.mul (.const 352)
              (fourthExpr (.mul (.var 0) (.mul (.var 1) (.const 1))))))
          (.mul (.mul (.const 352) (fourthExpr (.var 1)))
            (fourthExpr (.var 0)))
          (by decide) (fun | 0 => t | _ => HalfPow.half)
      have h₂ := Q'.mul_eqv_congr_right
        (352*fourth HalfPow.half) 22 (fourth t) hbase
      have h₃ : Q'.eqv (22*fourth t) ((22*fourth t)*quarter^0) := by
        simp only [Q'.pow_zero]
        exact Q'.eqv_symm (Q'.mul_one_eqv _)
      exact Q'.eqv_trans _ _ _ h₁ (Q'.eqv_trans _ _ _ h₂ h₃)
  | succ n ih =>
      have h₁ : Q'.eqv (coefficient t (n+1))
          ((4*fourth HalfPow.half)*coefficient t n) := by
        unfold coefficient fourth step
        rw [Q'.pow_succ (4 : Q') n,Q'.pow_succ HalfPow.half (n+1)]
        exact poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.var 1))
            (.mul (.const 352)
              (fourthExpr (.mul (.var 0) (.mul (.var 2) (.var 3))))))
          (.mul (.mul (.const 4) (fourthExpr (.var 2)))
            (.mul (.var 1)
              (.mul (.const 352)
                (fourthExpr (.mul (.var 0) (.var 3))))))
          (by decide)
          (fun | 0 => t | 1 => (4 : Q')^n
               | 2 => HalfPow.half | _ => HalfPow.half^(n+1))
      have h₂ := Q'.mul_eqv_congr_right
        (4*fourth HalfPow.half) quarter (coefficient t n) hhalf
      have h₃ := Q'.mul_eqv_congr_left quarter (coefficient t n)
        ((22*fourth t)*quarter^n) ih
      have h₄ : Q'.eqv (quarter*((22*fourth t)*quarter^n))
          ((22*fourth t)*quarter^(n+1)) := by
        rw [Q'.pow_succ]
        exact poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2)))
          (by decide)
          (fun | 0 => quarter | 1 => 22*fourth t | _ => quarter^n)
      exact Q'.eqv_trans _ _ _ h₁
        (Q'.eqv_trans _ _ _ h₂ (Q'.eqv_trans _ _ _ h₃ h₄))

/-- The actual linked physical graph controls every consecutive dyadic
product; its norm is the second graph output, not an external preimage cap. -/
theorem orbit_consecutive (t : Q') (ht : (0 : Q') < t)
    (d e : D) (hlink : Out d = In e) (n : Nat) :
    RCle (dist (orbit hw0 hw1 t ht (In d) n)
        (orbit hw0 hw1 t ht (In d) (n+1)))
      (RCscale ((22*fourth t)*quarter^n) (N (Out e))) := by
  let h := step t (n+1)
  let hh := step_pos t ht (n+1)
  let h2 := double_step_pos t ht n
  have hp := iterate_parameter_congr hw0 hw1
    (step_pos t ht n) h2 (Q'.eqv_symm (double_step_eqv t n))
    (In d) (2^n)
  have hcount : 2^(n+1) = 2*2^n := by rw [Nat.pow_succ,Nat.mul_comm]
  have hpow := dyadic_iterate_comparison hw0 hw1 h (2*h) hh h2 (In d) 2 1 n
  have hlocal := BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledBound.doubled_error_norm_le
    hw0 hw1 h hh h2 d e hlink
  have hscaled := RCscale_mono (Q'.pow_nonneg 4 (by decide) n) hlocal
  have hfinal := RCle_trans hpow hscaled
  rw [RCscale_RCscale] at hfinal
  have hnorm : RCle
      (N (diff hw0 hw1
        (orbit hw0 hw1 t ht (In d) (n+1))
        (orbit hw0 hw1 t ht (In d) n)))
      (RCscale (coefficient t n) (N (Out e))) := by
    unfold orbit
    rw [hcount,hp]
    simpa only [Nat.one_mul] using hfinal
  rw [BF4WilsonAllNomeComplexBondOSGeometricRowsLimit.distance_symm,
    distance_eq_norm_difference]
  rw [scale_congr (coefficient_eqv t n)] at hnorm
  exact hnorm

private theorem scale_zero (c : Q') : RCscale c RCzero = RCzero := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.mul_zero_eqv c))

private theorem scale_add (a b : Q') (z : RC) :
    RCadd (RCscale a z) (RCscale b z) = RCscale (a+b) z := by
  refine Quotient.inductionOn z ?_
  intro Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.add_mul_eqv a b (Z.approx n))))

private theorem tail_coefficient (B : Q') (n : Nat) :
    Q'.eqv
      ((B*quarter^n+B*quarter^n)+
        (4*(B*quarter^(n+1))+4*(B*quarter^(n+1))))
      (4*(B*quarter^n)) := by
  rw [Q'.pow_succ]
  have h : Q'.eqv
      ((B*quarter^n+B*quarter^n)+
        (4*(B*(quarter*quarter^n))+4*(B*(quarter*quarter^n))))
      ((2+8*quarter)*(B*quarter^n)) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.add (.mul (.const 4) (.mul (.var 0) (.mul (.var 2) (.var 1))))
          (.mul (.const 4) (.mul (.var 0) (.mul (.var 2) (.var 1))))))
      (.mul (.add (.const 2) (.mul (.const 8) (.var 2))) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => B | 1 => quarter^n | _ => quarter)
  exact Q'.eqv_trans _ _ _ h
    (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (2+8*quarter) 4))

private theorem budget_nonnegative (B : Q') (hB : (0 : Q') ≤ B)
    (z : RC) (hz : RCnonneg z) (n : Nat) :
    RCnonneg (RCscale (4*(B*quarter^n)) z) := by
  have hc : (0 : Q') ≤ 4*(B*quarter^n) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hB (Q'.pow_nonneg quarter (by decide) n))
  have h := RCscale_mono hc hz
  rw [scale_zero] at h
  exact h

/-- A CReal-valued geometric tail, with no rational cap substituted for the
actual output norm. -/
theorem orbit_tail (t : Q') (ht : (0 : Q') < t)
    (d e : D) (hlink : Out d = In e) (k n : Nat) :
    RCle (dist (orbit hw0 hw1 t ht (In d) n)
      (orbit hw0 hw1 t ht (In d) (n+k)))
      (RCscale (4*((22*fourth t)*quarter^n)) (N (Out e))) := by
  let B := 22*fourth t
  have hB : (0 : Q') ≤ B := by
    dsimp [B,fourth]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))
        (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht)))
  have hz := inner_nonnegative hw0 hw1 (Out e)
  change RCnonneg (N (Out e)) at hz
  change RCle _ (RCscale (4*(B*quarter^n)) (N (Out e)))
  induction k generalizing n with
  | zero =>
      rw [Nat.add_zero,distance_self]
      exact budget_nonnegative B hB (N (Out e)) hz n
  | succ k ih =>
      have htail := ih (n+1)
      rw [show (n+1)+k = n+(k+1) by
        rw [Nat.add_assoc,Nat.add_comm 1 k]] at htail
      have hstep := orbit_consecutive hw0 hw1 t ht d e hlink n
      have h := RCle_trans
        (distance_triangle hw0 hw1
          (orbit hw0 hw1 t ht (In d) n)
          (orbit hw0 hw1 t ht (In d) (n+1))
          (orbit hw0 hw1 t ht (In d) (n+(k+1))))
        (RCadd_le_add (RCadd_le_add hstep hstep)
          (RCadd_le_add htail htail))
      rw [scale_add,scale_add,scale_add,
        scale_congr (tail_coefficient B n)] at h
      exact h

private theorem diff_trans (a b c : H) :
    A (diff hw0 hw1 a b) (diff hw0 hw1 b c) = diff hw0 hw1 a c := by
  have hassoc : ∀ x y z : H, A (A x y) z = A x (A y z) :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_assoc hw0 hw1
  have hcomm : ∀ x y : H, A x y = A y x :=
    BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_comm hw0 hw1
  unfold diff
  calc
    A (A a (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b))
        (A b (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c)) =
      A (A a (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c))
        (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b) b) := by
          calc
            A (A a (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b))
                (A b (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c)) =
              A (A a (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b))
                (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c) b) := by
                  rw [hcomm b (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c)]
            _ = A (A a (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c))
                (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b) b) := by
                  calc
                    A (A a (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b))
                        (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c) b) =
                      A a (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b)
                        (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c) b)) :=
                          hassoc _ _ _
                    _ = A a (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c)
                        (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b) b)) := by
                          rw [← hassoc
                            (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b)
                            (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c) b,
                            hcomm
                              (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b)
                              (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c),hassoc]
                    _ = A (A a (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c))
                        (A (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 b) b) :=
                          (hassoc _ _ _).symm
    _ = A a (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg hw0 hw1 c) := by
      rw [BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.neg_add,
        BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_zero]

/-- The full original second-core phase is exactly `-2 i t A` to quadratic
order in norm.  No square root, third graph point, or physical-time premise
occurs in the statement. -/
theorem finite_product_tangent (t : Q') (ht : (0 : Q') < t)
    (d e : D) (hlink : Out d = In e) (n : Nat) :
    RCle
      (N (A (diff hw0 hw1 (orbit hw0 hw1 t ht (In d) n) (In d))
        (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.imagScale
          hw0 hw1 t (A (Out d) (Out d)))))
      (RCscale ((184 : Q')*fourth t) (N (Out e))) := by
  let x := In d
  let y := Out d
  let z := Out e
  have htail := orbit_tail hw0 hw1 t ht d e hlink n 0
  have hbase : orbit hw0 hw1 t ht x 0 = C t ht x := by
    unfold orbit
    simp only [Nat.pow_zero]
    rw [iterate_parameter_congr hw0 hw1 (step_pos t ht 0) ht
      (Q'.mul_one_eqv t) x 1]
    rfl
  rw [Nat.zero_add,hbase] at htail
  have htail' : RCle (N (diff hw0 hw1 (orbit hw0 hw1 t ht x n) (C t ht x)))
      (RCscale ((88 : Q')*fourth t) (N z)) := by
    rw [← distance_eq_norm_difference]
    have hc : Q'.eqv (4*((22*fourth t)*quarter^0)) (88*fourth t) := by
      simp only [Q'.pow_zero]
      exact poly_identity_of_normal_eq
        (.mul (.const 4) (.mul (.mul (.const 22) (.var 0)) (.const 1)))
        (.mul (.const 88) (.var 0)) (by decide) (fun _ => fourth t)
    rw [scale_congr hc] at htail
    rw [BF4WilsonAllNomeComplexBondOSGeometricRowsLimit.distance_symm] at htail
    exact htail
  have hlocal := linked_error_norm_le_four hw0 hw1 t ht d e hlink
  change RCle (N (graphError hw0 hw1 t ht d))
    (RCscale (4*fourth t) (N z)) at hlocal
  have hsum := RCle_trans
    (normSq_add_le hw0 hw1
      (diff hw0 hw1 (orbit hw0 hw1 t ht x n) (C t ht x))
      (graphError hw0 hw1 t ht d))
    (RCadd_le_add (RCadd_le_add htail' htail')
      (RCadd_le_add hlocal hlocal))
  have hidentity :
      A (diff hw0 hw1 (orbit hw0 hw1 t ht x n) (C t ht x))
        (graphError hw0 hw1 t ht d) =
      A (diff hw0 hw1 (orbit hw0 hw1 t ht x n) x)
        (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.imagScale
          hw0 hw1 t (A y y)) := by
    unfold graphError
    calc
      A (diff hw0 hw1 (orbit hw0 hw1 t ht x n) (C t ht x))
          (A (diff hw0 hw1 (C t ht x) x)
            (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.imagScale
              hw0 hw1 t (A y y))) =
        A (A (diff hw0 hw1 (orbit hw0 hw1 t ht x n) (C t ht x))
            (diff hw0 hw1 (C t ht x) x))
          (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.imagScale
            hw0 hw1 t (A y y)) :=
              (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_assoc
                hw0 hw1 _ _ _).symm
      _ = A (diff hw0 hw1 (orbit hw0 hw1 t ht x n) x)
          (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.imagScale
            hw0 hw1 t (A y y)) :=
              congrArg (fun v => A v
                (BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.imagScale
                  hw0 hw1 t (A y y)))
                (diff_trans hw0 hw1 _ _ _)
  rw [hidentity] at hsum
  have hcoef :
      RCadd
        (RCadd (RCscale (88*fourth t) (N z)) (RCscale (88*fourth t) (N z)))
        (RCadd (RCscale (4*fourth t) (N z)) (RCscale (4*fourth t) (N z))) =
      RCscale (184*fourth t) (N z) := by
    rw [scale_add,scale_add,scale_add]
    exact scale_congr (poly_identity_of_normal_eq
      (.add (.add (.mul (.const 88) (.var 0)) (.mul (.const 88) (.var 0)))
        (.add (.mul (.const 4) (.var 0)) (.mul (.const 4) (.var 0))))
      (.mul (.const 184) (.var 0)) (by decide) (fun _ => fourth t)) (N z)
  rw [hcoef] at hsum
  exact hsum

#print axioms orbit
#print axioms orbit_consecutive
#print axioms orbit_tail
#print axioms finite_product_tangent

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyInfinitesimal
