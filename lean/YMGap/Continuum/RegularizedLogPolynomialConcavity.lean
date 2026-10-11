/-
# Finite entropy-polynomial tangent bounds

The ACTUAL `RegularizedLogPolynomial.partialSum`, not a new logarithm or
surrogate, has a rational upper tangent on [0,1]. The proof expands its
complement into a linear term minus positive powers. Each power's tangent
remainder is nonnegative by a finite recurrence with an explicit square.

The intended consumer is original finite-product Haar order at its own
partition value. This scalar leaf does not supply localized partition
control, an interacting relative estimate, physical scaling, or a mass gap.
-/

import YMGap.Continuum.RegularizedLogPolynomial
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.RegularizedLogPolynomialConcavity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum term)

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem sub_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a-c ≈ b-d :=
  Q'.add_eqv_congr' h (Q'.neg_eqv_congr _ _ k)

private theorem add_le_add {a b c d : Q'} (h : a ≤ b) (k : c ≤ d) : a+c ≤ b+d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h) (Q'.add_le_add_left _ _ _ k)

private theorem partial_congr {a b : Q'} (h : a ≈ b) :
    ∀ n, partialSum a n ≈ partialSum b n
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.add_eqv_congr' (partial_congr h n)
      (mul_congr (Q'.eqv_refl _) (mul_congr h
        (BernsteinSequenceWrap.pow_eqv_congr (sub_congr (Q'.eqv_refl _) h) (n+1))))

private def powerGap (n : Nat) (y b : Q') : Q' :=
  y^(n+1)-b^(n+1)-Q'.ofNat (n+1)*b^n*(y-b)

private theorem powerGap_zero (y b : Q') : powerGap 0 y b ≈ 0 := by
  change y*1-b*1-(1 : Q')*1*(y-b) ≈ 0
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.const 1)) (.neg (.mul (.var 1) (.const 1))))
      (.neg (.mul (.mul (.const 1) (.const 1)) (.add (.var 0) (.neg (.var 1))))))
    (.const 0) (by decide) (fun | 0 => y | _ => b)

private theorem powerGap_step (n : Nat) (y b : Q') :
    powerGap (n+1) y b ≈ y*powerGap n y b +
      Q'.ofNat (n+1)*b^n*((y-b)*(y-b)) := by
  have hc : Q'.ofNat (n+1+1) ≈ Q'.ofNat (n+1)+1 := Q'.ofNat_add_eqv (n+1) 1
  refine Q'.eqv_trans _ _ _ (sub_congr (Q'.eqv_refl _)
    (mul_congr (mul_congr hc (Q'.eqv_refl _)) (Q'.eqv_refl _))) ?_
  change (y*y^(n+1)-b*(b*b^n)-(Q'.ofNat (n+1)+1)*(b*b^n)*(y-b)) ≈ _
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.mul (.var 1) (.var 3)))))
      (.neg (.mul (.mul (.add (.var 4) (.const 1)) (.mul (.var 1) (.var 3)))
        (.add (.var 0) (.neg (.var 1))))))
    (.add (.mul (.var 0)
      (.add (.add (.var 2) (.neg (.mul (.var 1) (.var 3))))
        (.neg (.mul (.mul (.var 4) (.var 3)) (.add (.var 0) (.neg (.var 1)))))))
      (.mul (.mul (.var 4) (.var 3))
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))))
    (by decide) (fun | 0 => y | 1 => b | 2 => y^(n+1) | 3 => b^n | _ => Q'.ofNat (n+1))

private theorem powerGap_nonnegative (y b : Q') (hy : (0 : Q') ≤ y)
    (hb : (0 : Q') ≤ b) : ∀ n, (0 : Q') ≤ powerGap n y b
  | 0 => Q'.ge_of_eqv (powerGap_zero y b)
  | n+1 => Q'.le_trans' _ _ _
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hy (powerGap_nonnegative y b hy hb n))
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' (n+1)) (Q'.pow_nonneg b hb n))
          (SumOfSquares.q_mul_self_nonneg (y-b))))
      (Q'.ge_of_eqv (powerGap_step n y b))

/-- Every nonnegative rational power has its explicit supporting tangent.
The index n denotes degree n+1, so no truncated subtraction at degree zero occurs. -/
theorem power_tangent (n : Nat) (y b : Q') (hy : (0 : Q') ≤ y) (hb : (0 : Q') ≤ b) :
    b^(n+1)+Q'.ofNat (n+1)*b^n*(y-b) ≤ y^(n+1) := by
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ (powerGap_nonnegative y b hy hb n)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
      (.add (.var 0) (.neg (.add (.var 1) (.var 2))))
      (by decide) (fun | 0 => y^(n+1) | 1 => b^(n+1) | _ => Q'.ofNat (n+1)*b^n*(y-b))))

private def coefficient (n : Nat) : Q' := Q'.invSucc n*Q'.invSucc (n+1)

private def debt (y : Q') : Nat → Q'
  | 0 => 0
  | n+1 => debt y n + coefficient n*y^(n+2)

private def debtSlope (b : Q') : Nat → Q'
  | 0 => 0
  | n+1 => debtSlope b n + coefficient n*(Q'.ofNat (n+2)*b^(n+1))

private def complement (n : Nat) (y : Q') : Q' :=
  y-debt y n-Q'.invSucc n*y^(n+2)

private def complementSlope (n : Nat) (b : Q') : Q' :=
  1-debtSlope b n-Q'.invSucc n*(Q'.ofNat (n+2)*b^(n+1))

private theorem inverse_split (n : Nat) :
    Q'.invSucc n ≈ coefficient n + Q'.invSucc (n+1) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ExpNeg.invSucc_cancel n)) ?_
  exact poly_identity_of_normal_eq
    (.mul (.var 1) (.add (.var 0) (.const 1)))
    (.add (.mul (.var 0) (.var 1)) (.var 1))
    (by decide) (fun | 0 => Q'.invSucc n | _ => Q'.invSucc (n+1))

private theorem complement_step (n : Nat) (y : Q') :
    complement (n+1) y ≈ complement n y + Q'.invSucc (n+1)*((1-y)*y^(n+2)) := by
  have hc : complement n y ≈ y-debt y n-(coefficient n+Q'.invSucc (n+1))*y^(n+2) :=
    sub_congr (Q'.eqv_refl _) (Q'.mul_eqv_congr_right _ _ _ (inverse_split n))
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.add_eqv_congr' hc (Q'.eqv_refl _)))
  change (y-(debt y n+coefficient n*y^(n+2))-Q'.invSucc (n+1)*(y*y^(n+2))) ≈ _
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.add (.var 1) (.mul (.var 2) (.var 3)))))
      (.neg (.mul (.var 4) (.mul (.var 0) (.var 3)))))
    (.add (.add (.add (.var 0) (.neg (.var 1)))
      (.neg (.mul (.add (.var 2) (.var 4)) (.var 3))))
      (.mul (.var 4) (.mul (.add (.const 1) (.neg (.var 0))) (.var 3))))
    (by decide) (fun
      | 0 => y
      | 1 => debt y n
      | 2 => coefficient n
      | 3 => y^(n+2)
      | _ => Q'.invSucc (n+1))

/-- Exact positive-power decomposition of the existing entropy partial sum. -/
theorem partial_complement (n : Nat) (y : Q') : partialSum (1-y) (n+1) ≈ complement n y := by
  have hcomp : 1-(1-y) ≈ y := poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0))))) (.var 0)
    (by decide) (fun _ => y)
  induction n with
  | zero =>
      have h := mul_congr (Q'.eqv_refl (Q'.invSucc 0))
        (mul_congr (Q'.eqv_refl (1-y)) (BernsteinSequenceWrap.pow_eqv_congr hcomp 1))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) h) ?_
      change (0+(1 : Q')*((1-y)*(y*1))) ≈ y-0-1*(y*(y*1))
      exact poly_identity_of_normal_eq
        (.add (.const 0) (.mul (.const 1) (.mul (.add (.const 1) (.neg (.var 0)))
          (.mul (.var 0) (.const 1)))))
        (.add (.add (.var 0) (.neg (.const 0)))
          (.neg (.mul (.const 1) (.mul (.var 0) (.mul (.var 0) (.const 1))))))
        (by decide) (fun _ => y)
  | succ n ih =>
      have ht : term (1-y) (n+1) ≈ Q'.invSucc (n+1)*((1-y)*y^(n+2)) :=
        mul_congr (Q'.eqv_refl _) (mul_congr (Q'.eqv_refl _)
          (BernsteinSequenceWrap.pow_eqv_congr hcomp (n+2)))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ih ht) (Q'.eqv_symm (complement_step n y))

private theorem debt_tangent (y b : Q') (hy : (0 : Q') ≤ y) (hb : (0 : Q') ≤ b) :
    ∀ n, debt b n+debtSlope b n*(y-b) ≤ debt y n
  | 0 => by
      apply Q'.le_of_eqv
      change (0 : Q')+0*(y-b) ≈ 0
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.zero_mul_eqv _)) (by decide)
  | n+1 => by
      have hc := Q'.mul_nonneg _ _ (Q'.invSucc_nonneg n) (Q'.invSucc_nonneg (n+1))
      have hp := Q'.mul_le_mul_of_nonneg_left _ _ (coefficient n) (power_tangent (n+1) y b hy hb) hc
      have h := add_le_add (debt_tangent y b hy hb n) hp
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h
      exact poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.add (.var 3) (.mul (.var 1) (.var 4))) (.var 5)))
        (.add (.add (.var 0) (.mul (.var 3) (.var 5)))
          (.mul (.var 1) (.add (.var 2) (.mul (.var 4) (.var 5)))))
        (by decide) (fun
          | 0 => debt b n
          | 1 => coefficient n
          | 2 => b^(n+2)
          | 3 => debtSlope b n
          | 4 => Q'.ofNat (n+2)*b^(n+1)
          | _ => y-b)

private theorem complement_tangent (n : Nat) (y b : Q') (hy : (0 : Q') ≤ y)
    (hb : (0 : Q') ≤ b) : complement n y ≤ complement n b+complementSlope n b*(y-b) := by
  have hp := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.invSucc n)
    (power_tangent (n+1) y b hy hb) (Q'.invSucc_nonneg n)
  have h := Q'.add_le_add_left y _ _ (Q'.neg_le_neg (add_le_add (debt_tangent y b hy hb n) hp))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_))
  · exact poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.mul (.var 2) (.var 3))))
      (.add (.var 0) (.neg (.add (.var 1) (.mul (.var 2) (.var 3)))))
      (by decide) (fun | 0 => y | 1 => debt y n | 2 => Q'.invSucc n | _ => y^(n+2))
  · let delta : RingNormaliser.PolyExpr := .add (.var 0) (.neg (.var 1))
    let lhs : RingNormaliser.PolyExpr := .add (.var 0) (.neg
      (.add (.add (.var 2) (.mul (.var 3) delta))
        (.mul (.var 4) (.add (.var 5) (.mul (.var 6) delta)))))
    let rhs : RingNormaliser.PolyExpr := .add
      (.add (.add (.var 1) (.neg (.var 2))) (.neg (.mul (.var 4) (.var 5))))
      (.mul (.add (.add (.const 1) (.neg (.var 3))) (.neg (.mul (.var 4) (.var 6)))) delta)
    exact poly_identity_of_normal_eq lhs rhs (by decide) (fun
      | 0 => y
      | 1 => b
      | 2 => debt b n
      | 3 => debtSlope b n
      | 4 => Q'.invSucc n
      | 5 => b^(n+2)
      | _ => Q'.ofNat (n+2)*b^(n+1))

/-- The rational slope is computed from the exact finite decomposition. -/
def tangentSlope (n : Nat) (b : Q') : Q' := -(complementSlope n (1-b))

/-- The actual degree-(n+2) entropy polynomial lies below its explicit upper
tangent at b. Only the upper endpoint is needed for this finite inequality. -/
theorem partial_tangent (n : Nat) (x b : Q') (hx : x ≤ 1) (hb : b ≤ 1) :
    partialSum x (n+1) ≤ partialSum b (n+1)+tangentSlope n b*(x-b) := by
  have hcx : 1-(1-x) ≈ x := poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0))))) (.var 0)
    (by decide) (fun _ => x)
  have hcb : 1-(1-b) ≈ b := poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0))))) (.var 0)
    (by decide) (fun _ => b)
  have hpin (t : Q') (ht : 1-(1-t) ≈ t) : partialSum t (n+1) ≈ complement n (1-t) := by
    exact Q'.eqv_trans _ _ _ (partial_congr (Q'.eqv_symm ht) (n+1))
      (partial_complement n (1-t))
  have h := complement_tangent n (1-x) (1-b) (Q'.sub_nonneg_of_le hx) (Q'.sub_nonneg_of_le hb)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (hpin x hcx))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_symm (hpin b hcb)) (Q'.eqv_refl _)) ?_
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.var 1)
      (.add (.add (.const 1) (.neg (.var 2))) (.neg (.add (.const 1) (.neg (.var 3)))))))
    (.add (.var 0) (.mul (.neg (.var 1)) (.add (.var 2) (.neg (.var 3)))))
    (by decide) (fun | 0 => partialSum b (n+1) | 1 => complementSlope n (1-b) | 2 => x | _ => b)

end YMGap.Continuum.RegularizedLogPolynomialConcavity

#print axioms YMGap.Continuum.RegularizedLogPolynomialConcavity.power_tangent
#print axioms YMGap.Continuum.RegularizedLogPolynomialConcavity.partial_complement
#print axioms YMGap.Continuum.RegularizedLogPolynomialConcavity.tangentSlope
#print axioms YMGap.Continuum.RegularizedLogPolynomialConcavity.partial_tangent
