/-
# The even Chebyshev character is an exact finite sum of squares

For every `m : Nat` and every constructive rational `x : Q'`, this module
proves the polynomial identity

```
  (2m+1) + U_{2m}(x)  ≃
    2 + 4 * sum_{k<m} T_{k+1}(x)^2.
```

This is the exact all-order SOS decomposition of the even SU(2) character
after adding its dimension.  No interval hypothesis on `x` is needed: the
statement is a polynomial identity over `Q'`.

The proof has two constructive layers.

1.  Package `U_{n-1}` as the second coordinate of the Chebyshev rotation
    pair.  The already-proved ladder relations then give its one-step
    rotation law.  Induction gives the addition formula, and its diagonal
    specialization together with `Cheb.pythForm_all` gives

    `1 + T_{2n}(x) ≃ 2*T_n(x)^2`.

2.  `ChebU.Ushift` says

    `U_{2m+2} ≃ U_{2m} + 2*T_{2m+2}`.

    Hence increasing `m` adds `2 + 2*T_{2m+2}`, which the diagonal identity
    identifies exactly with `4*T_{m+1}^2`.  This is precisely the new final
    summand of `RationalTail.finSum`.

All equality is `Q'.eqv`; no quotient normalization, choice, or excluded
middle is used.  The small `ring_qeqv` closer merely expands the defining
integer cross-products of `Q'.eqv` and closes commutative polynomial
rearrangements by `ac_rfl`.

# Axiom gate

No `Classical`, `sorry`, `native_decide`, or custom axiom.  The public
theorems are intended to report only `[propext]` / `[propext, Quot.sound]`.
-/

import YMGap.Continuum.ChebyshevU
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.RegularCReal

namespace YMGap.Continuum.ChebyshevEvenSOS

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail
open YMGap.Continuum.Cheb

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

/-! ## Polynomial rearrangement closer over `Q'.eqv` -/

private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast, zero_num_cast, zero_den_cast,
               one_num_cast, one_den_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero];
             try ac_rfl))

/-! ## The constructive Chebyshev rotation pair -/

/-- The radical-free sine coordinate accompanying `T_n`:
`sinCoord 0 = 0` and `sinCoord (n+1) = U_n`.

At `x = cos θ` this is `sin(nθ)/sin θ`, but only the polynomial
recurrence is used here. -/
def sinCoord : Nat → Q' → Q'
  | 0, _ => 0
  | n + 1, x => U n x

@[simp] theorem sinCoord_zero (x : Q') : sinCoord 0 x = 0 := rfl

@[simp] theorem sinCoord_succ (n : Nat) (x : Q') :
    sinCoord (n + 1) x = U n x := rfl

/-- First coordinate of the one-step Chebyshev rotation:
`T_{n+1} ≃ x*T_n - (1-x^2)*S_n`. -/
theorem T_succ_rotation (n : Nat) (x : Q') :
    T (n + 1) x ≈
      x * T n x + (-((1 + (-(x * x))) * sinCoord n x)) := by
  cases n with
  | zero =>
      simp only [T_zero, sinCoord_zero]
      ring_qeqv
  | succ k =>
      change T (k + 2) x ≈
        x * T (k + 1) x + (-((1 + (-(x * x))) * U k x))
      exact (linRel_all k x).1

/-- Second coordinate of the one-step Chebyshev rotation:
`S_{n+1} ≃ T_n + x*S_n`. -/
theorem sinCoord_succ_rotation (n : Nat) (x : Q') :
    sinCoord (n + 1) x ≈ T n x + x * sinCoord n x := by
  cases n with
  | zero =>
      simp only [sinCoord_zero, sinCoord_succ, U_zero, T_zero]
      ring_qeqv
  | succ k =>
      change U (k + 1) x ≈ T (k + 1) x + x * U k x
      exact (linRel_all k x).2

/-- **Chebyshev rotation addition law**, simultaneously for both coordinates:

`T_{m+n} ≃ T_m*T_n - (1-x^2)*S_m*S_n`,

`S_{m+n} ≃ S_m*T_n + T_m*S_n`.

The induction is entirely over the already-closed one-step ladder. -/
theorem rotation_add (m n : Nat) (x : Q') :
    (T (m + n) x ≈
      T m x * T n x +
        (-((1 + (-(x * x))) * (sinCoord m x * sinCoord n x)))) ∧
    (sinCoord (m + n) x ≈
      sinCoord m x * T n x + T m x * sinCoord n x) := by
  induction n with
  | zero =>
      constructor
      · simp only [Nat.add_zero, T_zero, sinCoord_zero]
        ring_qeqv
      · simp only [Nat.add_zero, T_zero, sinCoord_zero]
        ring_qeqv
  | succ n ih =>
      have hTsum := T_succ_rotation (m + n) x
      have hSsum := sinCoord_succ_rotation (m + n) x
      have hTstep := T_succ_rotation n x
      have hSstep := sinCoord_succ_rotation n x
      have hidx : m + (n + 1) = (m + n) + 1 := by omega
      rw [hidx]
      constructor
      · calc
          T ((m + n) + 1) x
              ≈ x * T (m + n) x +
                  (-((1 + (-(x * x))) * sinCoord (m + n) x)) := hTsum
          _ ≈ x *
                (T m x * T n x +
                  (-((1 + (-(x * x))) *
                    (sinCoord m x * sinCoord n x)))) +
                (-((1 + (-(x * x))) *
                  (sinCoord m x * T n x + T m x * sinCoord n x))) := by
              exact add_eqv_congr
                _ _ _ _
                (mul_eqv_congr_left _ _ _ ih.1)
                (neg_eqv_congr _ _
                  (mul_eqv_congr_left _ _ _ ih.2))
          _ ≈ T m x *
                (x * T n x +
                  (-((1 + (-(x * x))) * sinCoord n x))) +
                (-((1 + (-(x * x))) *
                  (sinCoord m x *
                    (T n x + x * sinCoord n x)))) := by
              ring_qeqv
          _ ≈ T m x * T (n + 1) x +
                (-((1 + (-(x * x))) *
                  (sinCoord m x * sinCoord (n + 1) x))) := by
              exact add_eqv_congr
                _ _ _ _
                (mul_eqv_congr_left _ _ _ (Q'.eqv_symm hTstep))
                (neg_eqv_congr _ _
                  (mul_eqv_congr_left _ _ _
                    (mul_eqv_congr_left _ _ _ (Q'.eqv_symm hSstep))))
      · calc
          sinCoord ((m + n) + 1) x
              ≈ T (m + n) x + x * sinCoord (m + n) x := hSsum
          _ ≈ (T m x * T n x +
                  (-((1 + (-(x * x))) *
                    (sinCoord m x * sinCoord n x)))) +
                x * (sinCoord m x * T n x + T m x * sinCoord n x) := by
              exact add_eqv_congr
                _ _ _ _ ih.1 (mul_eqv_congr_left _ _ _ ih.2)
          _ ≈ sinCoord m x *
                (x * T n x +
                  (-((1 + (-(x * x))) * sinCoord n x))) +
                T m x * (T n x + x * sinCoord n x) := by
              ring_qeqv
          _ ≈ sinCoord m x * T (n + 1) x +
                T m x * sinCoord (n + 1) x := by
              exact add_eqv_congr
                _ _ _ _
                (mul_eqv_congr_left _ _ _ (Q'.eqv_symm hTstep))
                (mul_eqv_congr_left _ _ _ (Q'.eqv_symm hSstep))

/-! ## Diagonal rotation and the Chebyshev double-angle square -/

/-- The Pythagorean invariant in rotation-coordinate form, including `n=0`:
`T_n^2 + (1-x^2)*S_n^2 ≃ 1`. -/
theorem rotation_pythagorean (n : Nat) (x : Q') :
    T n x * T n x +
      (1 + (-(x * x))) * (sinCoord n x * sinCoord n x) ≈ (1 : Q') := by
  cases n with
  | zero =>
      simp only [T_zero, sinCoord_zero]
      ring_qeqv
  | succ k =>
      change T (k + 1) x * T (k + 1) x +
        (1 + (-(x * x))) * (U k x * U k x) ≈ (1 : Q')
      exact pythForm_all k x

/-- Diagonal specialization of the addition law:
`T_{2n} ≃ T_n^2 - (1-x^2)*S_n^2`. -/
theorem T_double_rotation (n : Nat) (x : Q') :
    T (2 * n) x ≈
      T n x * T n x +
        (-((1 + (-(x * x))) * (sinCoord n x * sinCoord n x))) := by
  have h := (rotation_add n n x).1
  have hidx : n + n = 2 * n := by omega
  rw [hidx] at h
  exact h

/-- **Chebyshev double-angle square identity**:
`1 + T_{2n}(x) ≃ 2*T_n(x)^2`, for every `n` and every `x : Q'`. -/
theorem one_add_T_double_eqv_two_sq (n : Nat) (x : Q') :
    (1 : Q') + T (2 * n) x ≈
      (2 : Q') * (T n x * T n x) := by
  have hdouble := T_double_rotation n x
  have hpyth := rotation_pythagorean n x
  calc
    (1 : Q') + T (2 * n) x
        ≈ (T n x * T n x +
            (1 + (-(x * x))) * (sinCoord n x * sinCoord n x)) +
          (T n x * T n x +
            (-((1 + (-(x * x))) *
              (sinCoord n x * sinCoord n x)))) := by
            exact add_eqv_congr
              _ _ _ _ (Q'.eqv_symm hpyth) hdouble
    _ ≈ ((T n x * T n x) + (T n x * T n x)) +
          (((1 + (-(x * x))) * (sinCoord n x * sinCoord n x)) +
            (-((1 + (-(x * x))) *
              (sinCoord n x * sinCoord n x)))) :=
          add_swap_inner
            (T n x * T n x)
            ((1 + (-(x * x))) * (sinCoord n x * sinCoord n x))
            (T n x * T n x)
            (-((1 + (-(x * x))) * (sinCoord n x * sinCoord n x)))
    _ ≈ ((T n x * T n x) + (T n x * T n x)) + (0 : Q') :=
          add_eqv_congr_left _ _ _
            (add_neg_self_eqv
              ((1 + (-(x * x))) * (sinCoord n x * sinCoord n x)))
    _ ≈ (T n x * T n x) + (T n x * T n x) := by
          rw [add_zero']
          exact eqv_refl _
    _ ≈ (2 : Q') * (T n x * T n x) :=
          Q'.eqv_symm (two_mul_eqv (T n x * T n x))

/-- The increment form used by the finite SOS telescope:
`2 + 2*T_{2n} ≃ 4*T_n^2`. -/
theorem two_add_two_T_double_eqv_four_sq (n : Nat) (x : Q') :
    (2 : Q') + (2 : Q') * T (2 * n) x ≈
      (4 : Q') * (T n x * T n x) := by
  calc
    (2 : Q') + (2 : Q') * T (2 * n) x
        ≈ (2 : Q') * ((1 : Q') + T (2 * n) x) := by
            ring_qeqv
    _ ≈ (2 : Q') * ((2 : Q') * (T n x * T n x)) :=
          mul_eqv_congr_left _ _ _ (one_add_T_double_eqv_two_sq n x)
    _ ≈ ((2 : Q') * (2 : Q')) * (T n x * T n x) :=
          Q'.eqv_symm
            (mul_assoc_eqv (2 : Q') (2 : Q') (T n x * T n x))
    _ ≈ (4 : Q') * (T n x * T n x) :=
          mul_eqv_congr_right _ _ _ (by decide)

/-! ## The all-even finite SOS identity -/

/-- The odd dimension grows by exactly two. -/
private theorem oddDimension_succ (m : Nat) :
    Q'.ofNat (2 * (m + 1) + 1) ≈
      Q'.ofNat (2 * m + 1) + (2 : Q') := by
  have hidx : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
  rw [hidx]
  exact Q'.eqv_symm (ChebU.ofNat_add_eqv (2 * m + 1) 2)

/-- **All-`m` even Chebyshev SOS identity over `Q'`.**

```
ofNat (2*m+1) + U (2*m) x
  ≃ 2 + 4 * finSum (fun k => T (k+1) x * T (k+1) x) m.
```

Every summand on the right is a literal rational square. -/
theorem ofNat_odd_add_U_even_eqv_two_add_four_Tsq_finSum
    (m : Nat) (x : Q') :
    Q'.ofNat (2 * m + 1) + U (2 * m) x ≈
      (2 : Q') + (4 : Q') *
        finSum (fun k => T (k + 1) x * T (k + 1) x) m := by
  induction m with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, U_zero, finSum_zero]
      decide
  | succ m ih =>
      have hidx : 2 * (m + 1) = 2 * m + 2 := by omega
      have hU : U (2 * (m + 1)) x ≈
          U (2 * m) x + (2 : Q') * T (2 * (m + 1)) x := by
        rw [hidx]
        exact ChebU.Ushift (2 * m) x
      have hsq := two_add_two_T_double_eqv_four_sq (m + 1) x
      calc
        Q'.ofNat (2 * (m + 1) + 1) + U (2 * (m + 1)) x
            ≈ (Q'.ofNat (2 * m + 1) + (2 : Q')) +
                (U (2 * m) x +
                  (2 : Q') * T (2 * (m + 1)) x) := by
                exact add_eqv_congr
                  _ _ _ _ (oddDimension_succ m) hU
        _ ≈ (Q'.ofNat (2 * m + 1) + U (2 * m) x) +
              ((2 : Q') + (2 : Q') * T (2 * (m + 1)) x) := by
                ring_qeqv
        _ ≈ ((2 : Q') + (4 : Q') *
                finSum (fun k => T (k + 1) x * T (k + 1) x) m) +
              (4 : Q') * (T (m + 1) x * T (m + 1) x) := by
                exact add_eqv_congr _ _ _ _ ih hsq
        _ ≈ (2 : Q') + (4 : Q') *
              (finSum (fun k => T (k + 1) x * T (k + 1) x) m +
                T (m + 1) x * T (m + 1) x) := by
                ring_qeqv
        _ ≈ (2 : Q') + (4 : Q') *
              finSum (fun k => T (k + 1) x * T (k + 1) x) (m + 1) := by
                rw [finSum_succ]
                exact Q'.eqv_refl _

end YMGap.Continuum.ChebyshevEvenSOS

#print axioms YMGap.Continuum.ChebyshevEvenSOS.rotation_add
#print axioms YMGap.Continuum.ChebyshevEvenSOS.one_add_T_double_eqv_two_sq
#print axioms YMGap.Continuum.ChebyshevEvenSOS.two_add_two_T_double_eqv_four_sq
#print axioms YMGap.Continuum.ChebyshevEvenSOS.ofNat_odd_add_U_even_eqv_two_add_four_Tsq_finSum
