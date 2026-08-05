/-
# Division-free Abel transform for physical Bernstein rows

Suppose an even physical polynomial is written in the quarter-scaled variable

    F(u) = sum_k a_k (u / 4)^k,

with signed integer monomial numerators `a_k`, and fix a common Bernstein
degree `D`.  After clearing the single harmless denominator `4^D`, its
unnormalised Bernstein coefficient in channel `j` is

    C_j = sum_{k <= j} a_k 4^(D-k) C(D-k,j-k).

Define the four-adic prefix reserve by

    T_0       = a_0,
    T_(k + 1) = 4 T_k + a_(k + 1).

The constructive Abel/Pascal identity proved below is

    C_j = T_j 4^(D-j)
          + sum_{k < j} T_k 4^(D-k) C(D-k-1,j-k).

Every weight on the right is a nonnegative integer.  Consequently, the
first-order invariant `0 <= T_k` for `k <= D` implies coefficientwise
nonnegativity of the entire cleared degree-`D` Bernstein row.  This is a
uniform consumer: `D` is arbitrary and there is no bounded computation,
division, ratio comparison, or induction claiming that the row at cutoff
`N + 1` dominates the row at cutoff `N`.

This module deliberately does not assert the remaining heat-box-specific
claim that its concrete monomial numerators have nonnegative four-adic
prefixes.  That is the analytic/combinatorial producer still required by the
all-`N` campaign; the theorem here turns exactly that producer into the
desired Bernstein certificate.

Axiom gate (AGENTS.md Rules 1, 2, and 8): no classical reasoning, sorry,
native_decide, quotient construction, or noncomputable declaration.
-/

import YMGap.RG.PolylogTail

namespace YMGap.Continuum.BernsteinPrefixAbel

open YMGap.RG

/-! ## Constructive finite sums and the four-adic reserve -/

/-- Recursive sum of the first `n` integer entries. -/
def intPrefixSum (f : Nat -> Int) : Nat -> Int
  | 0 => 0
  | n + 1 => intPrefixSum f n + f n

@[simp] theorem intPrefixSum_zero (f : Nat -> Int) :
    intPrefixSum f 0 = 0 := rfl

theorem intPrefixSum_succ (f : Nat -> Int) (n : Nat) :
    intPrefixSum f (n + 1) = intPrefixSum f n + f n := rfl

/-- `4^n`, kept as a recursive integer object so all sign arguments stay
division-free and reduce to integer addition and multiplication. -/
def fourPow : Nat -> Int
  | 0 => 1
  | n + 1 => 4 * fourPow n

@[simp] theorem fourPow_zero : fourPow 0 = 1 := rfl

theorem fourPow_succ (n : Nat) :
    fourPow (n + 1) = 4 * fourPow n := rfl

/-- Four-adic prefix reserve `T_k = sum_{i <= k} a_i 4^(k-i)`, presented by
the first-order recurrence used by the uniform producer. -/
def fourPrefix (a : Nat -> Int) : Nat -> Int
  | 0 => a 0
  | k + 1 => 4 * fourPrefix a k + a (k + 1)

@[simp] theorem fourPrefix_zero (a : Nat -> Int) :
    fourPrefix a 0 = a 0 := rfl

theorem fourPrefix_succ (a : Nat -> Int) (k : Nat) :
    fourPrefix a (k + 1) = 4 * fourPrefix a k + a (k + 1) := rfl

/-- A finite sum of nonnegative integers is nonnegative. -/
theorem intPrefixSum_nonnegative (f : Nat -> Int) : forall n,
    (forall k, k < n -> 0 <= f k) -> 0 <= intPrefixSum f n
  | 0, _ => by
      rw [intPrefixSum_zero]
      omega
  | n + 1, h => by
      rw [intPrefixSum_succ]
      exact Int.add_nonneg
        (intPrefixSum_nonnegative f n (fun k hk => h k (by omega)))
        (h n (by omega))

/-- The recursively presented power `4^n` is nonnegative. -/
theorem fourPow_nonnegative : forall n, 0 <= fourPow n
  | 0 => by
      rw [fourPow_zero]
      omega
  | n + 1 => by
      rw [fourPow_succ]
      exact Int.mul_nonneg (by omega) (fourPow_nonnegative n)

/-! ## Pascal weights and the local payment identity -/

/-- Weight of `a_k` in the denominator-cleared unnormalised degree-`D`
Bernstein coefficient in channel `j`. -/
def clearedPascalWeight (D j k : Nat) : Int :=
  fourPow (D - k) * Int.ofNat (binom (D - k) (j - k))

/-- Nonnegative Abel payment left by the prefix reserve at index `k`. -/
def abelPaymentWeight (D j k : Nat) : Int :=
  fourPow (D - k) * Int.ofNat (binom (D - k - 1) (j - k))

/-- Pascal's identity with all physical powers of four retained.  This is the
local conservation law behind the Abel transform: the weight at `n - 1`
splits into four copies of the weight at `n` and one nonnegative payment. -/
theorem clearedPascalWeight_pred
    (D j n : Nat) (hn : 0 < n) (hnj : n <= j) (hjD : j <= D) :
    clearedPascalWeight D j (n - 1) =
      4 * clearedPascalWeight D j n + abelPaymentWeight D j (n - 1) := by
  have hD : D - (n - 1) = (D - n) + 1 := by omega
  have hj : j - (n - 1) = (j - n) + 1 := by omega
  unfold clearedPascalWeight abelPaymentWeight
  rw [hD, hj, binom_succ_succ, fourPow_succ]
  simp only [Nat.add_sub_cancel, Int.ofNat_eq_natCast, Int.natCast_add,
    Int.mul_add]
  ac_rfl

/-- The Abel payment weight is visibly nonnegative. -/
theorem abelPaymentWeight_nonnegative (D j k : Nat) :
    0 <= abelPaymentWeight D j k := by
  unfold abelPaymentWeight
  exact Int.mul_nonneg (fourPow_nonnegative _) (Int.natCast_nonneg _)

/-- On the diagonal `k = j`, the Pascal factor is one. -/
theorem clearedPascalWeight_diagonal (D j : Nat) :
    clearedPascalWeight D j j = fourPow (D - j) := by
  unfold clearedPascalWeight
  rw [Nat.sub_self, binom_zero_right]
  simp

/-! ## Exact Abel identity and uniform nonnegativity consumer -/

/-- The cleared physical Bernstein coefficient in channel `j`.  Only the
first `j + 1` monomials can contribute to that channel. -/
def clearedBernsteinCoefficient
    (D : Nat) (a : Nat -> Int) (j : Nat) : Int :=
  intPrefixSum (fun k => a k * clearedPascalWeight D j k) (j + 1)

/-- The manifestly prefix-positive side of the Abel identity. -/
def prefixAbelCoefficient
    (D : Nat) (a : Nat -> Int) (j : Nat) : Int :=
  fourPrefix a j * fourPow (D - j) +
    intPrefixSum
      (fun k => fourPrefix a k * abelPaymentWeight D j k) j

/-- Partial Abel identity through source index `n`.  Keeping this stronger
form public makes the proof reusable for truncated producer recurrences. -/
theorem clearedBernsteinPrefix_eq_abelPrefix
    (D j : Nat) (a : Nat -> Int) (hjD : j <= D) : forall n,
    n <= j ->
    intPrefixSum (fun k => a k * clearedPascalWeight D j k) (n + 1) =
      fourPrefix a n * clearedPascalWeight D j n +
        intPrefixSum
          (fun k => fourPrefix a k * abelPaymentWeight D j k) n := by
  intro n
  induction n with
  | zero =>
      intro _
      simp only [intPrefixSum_succ, intPrefixSum_zero, fourPrefix_zero,
        Int.zero_add, Int.add_zero]
  | succ n ih =>
      intro hnj
      have hweight :
          clearedPascalWeight D j n =
            4 * clearedPascalWeight D j (n + 1) +
              abelPaymentWeight D j n := by
        simpa using
          (clearedPascalWeight_pred D j (n + 1)
            (by omega) hnj hjD)
      calc
        intPrefixSum
              (fun k => a k * clearedPascalWeight D j k) ((n + 1) + 1) =
            intPrefixSum
                (fun k => a k * clearedPascalWeight D j k) (n + 1) +
              a (n + 1) * clearedPascalWeight D j (n + 1) := rfl
        _ =
            (fourPrefix a n * clearedPascalWeight D j n +
              intPrefixSum
                (fun k => fourPrefix a k * abelPaymentWeight D j k) n) +
              a (n + 1) * clearedPascalWeight D j (n + 1) := by
            rw [ih (by omega)]
        _ =
            fourPrefix a (n + 1) * clearedPascalWeight D j (n + 1) +
              intPrefixSum
                (fun k => fourPrefix a k * abelPaymentWeight D j k) (n + 1) := by
            rw [hweight, fourPrefix_succ, intPrefixSum_succ]
            simp only [Int.mul_add, Int.add_mul]
            ac_rfl

/-- **Division-free Abel/Pascal identity.**  The cleared Bernstein
coefficient is exactly a sum of four-adic prefix reserves against
nonnegative Pascal weights. -/
theorem clearedBernsteinCoefficient_eq_prefixAbelCoefficient
    (D : Nat) (a : Nat -> Int) (j : Nat) (hjD : j <= D) :
    clearedBernsteinCoefficient D a j = prefixAbelCoefficient D a j := by
  unfold clearedBernsteinCoefficient prefixAbelCoefficient
  rw [clearedBernsteinPrefix_eq_abelPrefix D j a hjD j (by omega),
    clearedPascalWeight_diagonal]

/-- One-channel nonnegativity consumer: nonnegative four-adic prefixes up to
`j` imply nonnegativity of the cleared Bernstein coefficient in channel
`j`. -/
theorem clearedBernsteinCoefficient_nonnegative_of_prefix
    (D : Nat) (a : Nat -> Int) (j : Nat) (hjD : j <= D)
    (hprefix : forall k, k <= j -> 0 <= fourPrefix a k) :
    0 <= clearedBernsteinCoefficient D a j := by
  rw [clearedBernsteinCoefficient_eq_prefixAbelCoefficient D a j hjD]
  unfold prefixAbelCoefficient
  exact Int.add_nonneg
    (Int.mul_nonneg (hprefix j (by omega)) (fourPow_nonnegative _))
    (intPrefixSum_nonnegative _ j (fun k hk =>
      Int.mul_nonneg (hprefix k (by omega))
        (abelPaymentWeight_nonnegative D j k)))

/-- **All-degree consumer family.**  A single nonnegative-prefix producer
through degree `D` yields every coefficient of the denominator-cleared
degree-`D` physical Bernstein row. -/
theorem clearedBernsteinRow_nonnegative_of_prefixes
    (D : Nat) (a : Nat -> Int)
    (hprefix : forall k, k <= D -> 0 <= fourPrefix a k) :
    forall j, j <= D -> 0 <= clearedBernsteinCoefficient D a j := by
  intro j hjD
  exact clearedBernsteinCoefficient_nonnegative_of_prefix D a j hjD
    (fun k hk => hprefix k (by omega))

#print axioms intPrefixSum_nonnegative
#print axioms fourPow_nonnegative
#print axioms clearedPascalWeight_pred
#print axioms abelPaymentWeight_nonnegative
#print axioms clearedBernsteinPrefix_eq_abelPrefix
#print axioms clearedBernsteinCoefficient_eq_prefixAbelCoefficient
#print axioms clearedBernsteinCoefficient_nonnegative_of_prefix
#print axioms clearedBernsteinRow_nonnegative_of_prefixes

end YMGap.Continuum.BernsteinPrefixAbel
