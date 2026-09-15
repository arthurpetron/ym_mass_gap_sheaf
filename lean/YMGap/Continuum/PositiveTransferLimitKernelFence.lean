/-
# Strict finite positivity and a uniform vacuum gap do not prevent a limit kernel

COUNTEREXAMPLE ONLY, not a Yang--Mills carrier or a frontier discharge.
On rational pairs, T_n=diag(1, (1/16)*2^(-n)) is symmetric and strictly
positive, fixes the vacuum, and has a common excited-sector form cap 1/16.
Its limit P=diag(1,0) kills the unit excitation. The convergence estimate
is uniform over vectors, with the explicit squared-operator-error modulus
epsilon.den. Thus even operator-norm convergence cannot pass strict finite
positivity to an injective limit. A volume-independent test-relative bound
is additional information, not a consequence of the common upper gap.

The consumer is the T2 comparison audit: do not use finite-box strict
positivity to close the original thermodynamic kernel by taking limits.
No claim about the actual T2 kernel is made by this counterexample.
-/

import YMGap.Constructive.HalfPow
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Sqrt
import YMGap.Constructive.Soundness
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.PositiveTransferLimitKernelFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

abbrev Vector := Q' × Q'
def inner (x y : Vector) : Q' := x.1*y.1 + x.2*y.2
def normSq (x : Vector) : Q' := inner x x
def gapCap : Q' := Q'.invSucc 15
def rate (n : Nat) : Q' := gapCap * HalfPow.half^n
def transfer (n : Nat) (x : Vector) : Vector := (x.1, rate n*x.2)
def limitTransfer (x : Vector) : Vector := (x.1, 0)
def vacuum : Vector := (1,0)
def excitation : Vector := (0,1)
def distanceSq (x y : Vector) : Q' := normSq (x.1 + -y.1, x.2 + -y.2)

private theorem half_pos : ∀ n : Nat, (0 : Q') < HalfPow.half^n
  | 0 => by decide
  | n+1 => Q'.mul_pos (by decide : (0 : Q') < HalfPow.half) (half_pos n)

private theorem half_le_one : ∀ n : Nat, HalfPow.half^n ≤ (1 : Q')
  | 0 => Q'.le_refl' _
  | n+1 => Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (half_le_one n) HalfPow.half_nonneg)
      (by decide : HalfPow.half*1 ≤ (1 : Q'))

private theorem half_antitone {m n : Nat} (h : m ≤ n) : HalfPow.half^n ≤ HalfPow.half^m := by
  induction n with
  | zero => have hm : m=0 := Nat.eq_zero_of_le_zero h; subst m; exact Q'.le_refl' _
  | succ n ih =>
      by_cases he : m=n+1
      · subst m; exact Q'.le_refl' _
      · exact Q'.le_trans' _ _ _
          (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : HalfPow.half ≤ (1 : Q'))
            (Q'.le_of_lt (half_pos n))) (Q'.le_of_eqv (Q'.one_mul_eqv _))) (ih (by omega))

theorem rate_positive (n : Nat) : (0 : Q') < rate n := Q'.mul_pos (by decide : (0 : Q') < gapCap) (half_pos n)

theorem rate_le_gap (n : Nat) : rate n ≤ gapCap :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (half_le_one n) (by decide : (0 : Q') ≤ gapCap))
    (Q'.le_of_eqv (Q'.mul_one_eqv _))

private theorem rate_le_one (n : Nat) : rate n ≤ (1 : Q') := Q'.le_trans' _ _ _ (rate_le_gap n) (by decide)

private theorem rate_square_le_half (n : Nat) : rate n*rate n ≤ HalfPow.half^n := by
  have h : rate n*rate n ≤ rate n := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (rate_le_one n) (Q'.le_of_lt (rate_positive n)))
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : gapCap ≤ (1 : Q')) (Q'.le_of_lt (half_pos n)))
    (Q'.le_of_eqv (Q'.one_mul_eqv _)))

theorem transfer_symmetric (n : Nat) (x y : Vector) : inner (transfer n x) y ≈ inner x (transfer n y) :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.var 4) (.var 2)) (.var 3)))
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 4) (.var 3))))
    (by decide) (fun | 0 => x.1 | 1 => y.1 | 2 => x.2 | 3 => y.2 | _ => rate n)

theorem transfer_coercive (n : Nat) (x : Vector) : rate n * normSq x ≤ inner x (transfer n x) := by
  have h := Q'.add_le_add_right _ _ (rate n*(x.2*x.2)) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (rate_le_one n) (SumOfSquares.q_mul_self_nonneg x.1))
    (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 0)) (.mul (.var 2) (.mul (.var 1) (.var 1))))
      (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 1))))
      (by decide) (fun | 0 => x.1 | 1 => x.2 | _ => rate n))))

theorem transfer_strictly_positive (n : Nat) (x : Vector) (hx : (0 : Q') < normSq x) :
    (0 : Q') < inner x (transfer n x) :=
  Q'.pos_of_lt_of_le (Q'.mul_pos (rate_positive n) hx) (transfer_coercive n x)

theorem vacuum_fixed (n : Nat) : (transfer n vacuum).1 ≈ vacuum.1 ∧ (transfer n vacuum).2 ≈ vacuum.2 :=
  ⟨Q'.eqv_refl _, Q'.mul_zero_eqv _⟩

/-- The excited-sector cap is the same 1/16 at every index. -/
theorem uniform_excited_form_bound (n : Nat) (b : Q') :
    inner (0,b) (transfer n (0,b)) ≤ gapCap * normSq (0,b) := by
  have h := Q'.mul_le_mul_of_nonneg_right _ _ _ (rate_le_gap n) (SumOfSquares.q_mul_self_nonneg b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.add (.mul (.const 0) (.const 0)) (.mul (.var 0) (.mul (.var 1) (.var 0))))
    (.mul (.var 1) (.mul (.var 0) (.var 0))) (by decide) (fun | 0 => b | _ => rate n)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 1) (.mul (.var 0) (.var 0)))
      (.mul (.var 1) (.add (.mul (.const 0) (.const 0)) (.mul (.var 0) (.var 0))))
      (by decide) (fun | 0 => b | _ => gapCap))))

theorem operator_error (n : Nat) (x : Vector) :
    distanceSq (transfer n x) (limitTransfer x) ≤ HalfPow.half^n * normSq x := by
  have hp : distanceSq (transfer n x) (limitTransfer x) ≈ (rate n*rate n)*(x.2*x.2) :=
    poly_identity_of_normal_eq
      (.add (.mul (.add (.var 0) (.neg (.var 0))) (.add (.var 0) (.neg (.var 0))))
        (.mul (.add (.mul (.var 2) (.var 1)) (.neg (.const 0))) (.add (.mul (.var 2) (.var 1)) (.neg (.const 0)))))
      (.mul (.mul (.var 2) (.var 2)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => x.1 | 1 => x.2 | _ => rate n)
  have hb : x.2*x.2 ≤ normSq x := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg x.1))
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (rate_square_le_half n) (SumOfSquares.q_mul_self_nonneg x.2))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hb (Q'.le_of_lt (half_pos n))))

def operatorErrorModulus (epsilon : Q') : Nat := epsilon.den

/-- A uniform-over-vectors squared-operator-error estimate, not mere weak convergence. -/
theorem operator_error_atModulus (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : operatorErrorModulus epsilon ≤ n) (x : Vector) :
    distanceSq (transfer n x) (limitTransfer x) ≤ epsilon * normSq x :=
  Q'.le_trans' _ _ _ (operator_error n x) (Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.le_trans' _ _ _ (half_antitone hn) (HalfPow.pow_half_le epsilon he))
    (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg x.1) (SumOfSquares.q_mul_self_nonneg x.2)))

theorem limit_nonzero_kernel : normSq excitation ≈ 1 ∧ limitTransfer excitation = (0,0) := ⟨by decide, rfl⟩

theorem limit_test_bound_impossible (C : Q') : ¬ ((inner excitation excitation)*(inner excitation excitation) ≤
    C * normSq (limitTransfer excitation)) := by
  intro h
  have hz : C * normSq (limitTransfer excitation) ≈ 0 := Q'.mul_zero_eqv C
  have hc : (1 : Q') ≤ (0 : Q') := Q'.le_trans' _ _ _ h (Q'.le_of_eqv hz)
  exact (by decide : ¬ ((1 : Q') ≤ (0 : Q'))) hc

end YMGap.Continuum.PositiveTransferLimitKernelFence

#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.inner
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.normSq
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.gapCap
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.rate
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.transfer
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.limitTransfer
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.vacuum
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.excitation
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.distanceSq
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.rate_positive
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.rate_le_gap
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.transfer_symmetric
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.transfer_coercive
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.transfer_strictly_positive
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.vacuum_fixed
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.uniform_excited_form_bound
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.operator_error
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.operatorErrorModulus
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.operator_error_atModulus
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.limit_nonzero_kernel
#print axioms YMGap.Continuum.PositiveTransferLimitKernelFence.limit_test_bound_impossible
