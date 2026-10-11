/-
# Quantitative lower mass for the original polynomial localization kernel

The EXISTING original Haar recurrence for b=(1+x0)/2 gives
(2n+6) H[b^(n+1)] = (2n+3) H[b^n]. Its scalar coefficient comparison
(2n+3)(n+2)^2 >= (2n+6)(n+1)^2 proves H[b^n] >= 1/(n+1)^2.
No new moment formula or Haar law is assumed. This pays a finite one-link
localization cost, not typical concentration of interacting raw links,
an interacting partition lower bound, H1, physical scaling or a mass gap.
-/

import YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration
import YMGap.Constructive.Soundness
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.SU2QuaternionKernelMomentLower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := RingNormaliser.PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩
private def v (i : Nat) : PE := .var i

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem add_nonnegative {a b : Q'} (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a+b :=
  Q'.le_trans' _ _ _ ha
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' a)))
      (Q'.add_le_add_left a 0 b hb))

private def square (n : Nat) : Q' := Q'.ofNat (n+1)*Q'.ofNat (n+1)

private theorem square_positive (n : Nat) : (0 : Q') < square n :=
  Q'.mul_pos (Q'.ofNat_succ_pos n) (Q'.ofNat_succ_pos n)

private theorem nat_linear (n a b : Nat) :
    Q'.ofNat (a*n+b) ≈ Q'.ofNat a*Q'.ofNat n+Q'.ofNat b := by
  change ((a*n+b : Nat) : Int)*1 = ((a : Int)*(n : Int)*1+(b : Int)*1)*1
  simp only [Int.natCast_add, Int.natCast_mul, Int.mul_one]

private theorem coefficient_comparison (n : Nat) :
    Q'.ofNat (2*n+6)*square n ≤ Q'.ofNat (2*n+3)*square (n+1) := by
  have hn : (0 : Q') ≤ Q'.ofNat n := by
    change 0*1 ≤ (n : Int)*1
    omega
  have h1 : Q'.ofNat (n+1) ≈ Q'.ofNat n+1 := Q'.ofNat_add_eqv n 1
  have h2 : Q'.ofNat (n+1+1) ≈ Q'.ofNat n+2 := by
    simpa only [Nat.add_assoc] using Q'.ofNat_add_eqv n 2
  have hd := mc (nat_linear n 2 6) (mc h1 h1)
  have ha := mc (nat_linear n 2 3) (mc h2 h2)
  have he : Q'.ofNat (2*n+3)*square (n+1)-Q'.ofNat (2*n+6)*square n ≈
      Q'.ofNat n*Q'.ofNat n+6*Q'.ofNat n+6 := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hd)) ?_
    exact poly_identity_of_normal_eq
      ((2*v 0+3)*((v 0+2)*(v 0+2))+ -((2*v 0+6)*((v 0+1)*(v 0+1))))
      (v 0*v 0+6*v 0+6) (by decide) (fun _ => Q'.ofNat n)
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _
    (add_nonnegative (add_nonnegative (Q'.mul_nonneg _ _ hn hn)
      (Q'.mul_nonneg _ _ (by decide) hn)) (by decide)) (Q'.ge_of_eqv he)

/-- Division-free original Haar mass lower bound, including exponent zero. -/
theorem kernelMoment_cleared_lower : ∀ n,
    (1 : Q') ≤ square n*kernelMoment n
  | 0 => Q'.ge_of_eqv (by decide)
  | n+1 => by
      let D := Q'.ofNat (2*n+6)
      let A := Q'.ofNat (2*n+3)
      have hstep : D*(square (n+1)*kernelMoment (n+1)) ≈
          (A*square (n+1))*kernelMoment n := by
        exact Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq (v 0*(v 1*v 2)) (v 1*(v 0*v 2))
            (by decide) (fun | 0 => D | 1 => square (n+1) | _ => kernelMoment (n+1)))
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (kernelMoment_recurrence n))
            (poly_identity_of_normal_eq (v 0*(v 1*v 2)) ((v 1*v 0)*v 2)
              (by decide) (fun | 0 => square (n+1) | 1 => A | _ => kernelMoment n)))
      have hcoef := Q'.mul_le_mul_of_nonneg_right _ _ (kernelMoment n)
        (coefficient_comparison n) (Q'.le_of_lt (kernelMoment_positive n))
      have hi := Q'.mul_le_mul_of_nonneg_left _ _ D
        (kernelMoment_cleared_lower n) (Q'.le_of_lt (recurrenceDenominator_positive n))
      apply Q'.le_of_mul_le_mul_left (c := D) _ (recurrenceDenominator_positive n)
      exact Q'.le_trans' _ _ _ hi (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
        (Q'.le_trans' _ _ _ hcoef (Q'.ge_of_eqv hstep)))

/-- Computable finite localization mass floor; no logarithm or limit is used. -/
def localizationFloor (n : Nat) : Q' := Q'.invSucc n*Q'.invSucc n

theorem localizationFloor_positive (n : Nat) : (0 : Q') < localizationFloor n :=
  Q'.mul_pos (Q'.invSucc_pos n) (Q'.invSucc_pos n)

private theorem floor_cancel (n : Nat) : square n*localizationFloor n ≈ (1 : Q') := by
  refine Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq ((v 0*v 0)*(v 1*v 1)) ((v 0*v 1)*(v 0*v 1))
      (by decide) (fun | 0 => Q'.ofNat (n+1) | _ => Q'.invSucc n)) ?_
  exact Q'.eqv_trans _ _ _
    (mc (Q'.ofNat_succ_mul_invSucc n) (Q'.ofNat_succ_mul_invSucc n)) (by decide)

/-- The literal ORIGINAL one-block moment of ((1+x0)/2)^n is at least
1/(n+1)^2. It is not a mass statement for the interacting gauge measure. -/
theorem localizationFloor_le_kernelMoment (n : Nat) :
    localizationFloor n ≤ kernelMoment n :=
  Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (floor_cancel n)) (kernelMoment_cleared_lower n))
    (square_positive n)

end YMGap.Continuum.SU2QuaternionKernelMomentLower

#print axioms YMGap.Continuum.SU2QuaternionKernelMomentLower.kernelMoment_cleared_lower
#print axioms YMGap.Continuum.SU2QuaternionKernelMomentLower.localizationFloor
#print axioms YMGap.Continuum.SU2QuaternionKernelMomentLower.localizationFloor_positive
#print axioms YMGap.Continuum.SU2QuaternionKernelMomentLower.localizationFloor_le_kernelMoment
