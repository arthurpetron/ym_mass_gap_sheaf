/-
# Core-B canonical four-square shells

This module aggregates the four canonical antidiagonal coordinates belonging
to one numerator/midpoint atom pair.  The endpoint degree is supplied by the
nontruncated equality

  numeratorExponent + midpointExponent = 2 * content + 2 + g.

That formulation is deliberate: at odd length the fully centered equality
case has signed raw degree `-2`, whereas Nat subtraction would report zero.

Axiom gate: no classical reasoning, sorry, native_decide, noncomputable
declaration, or custom axiom.
-/

import YMGap.Continuum.CoreBAtomwiseGapBounds

namespace YMGap.Continuum.CoreBCanonicalSquareShell

open YMGap.Continuum
open YMGap.Continuum.CoreBBoundedMonomialNormalForm
open YMGap.Continuum.CoreBAtomwiseGapBounds

/-- Sum of the four Nat-safe centered coordinate squares attached to a
canonical numerator/midpoint atom pair. -/
def canonicalCenteredShell
    (n t i j p q u v : Nat) : Nat :=
  centeredIndexSquare (n + 1) (canonicalALeftIndex (t + 1) i p) +
    centeredIndexSquare (n + 3) (canonicalARightIndex (t + 1) i q) +
    centeredIndexSquare (n + 2) (canonicalMLeftIndex (t + 1) j u) +
    centeredIndexSquare (n + 2) (canonicalMRightIndex (t + 1) j v)

/-- Index-independent Casimir constant left after completing all four
antidiagonal exponents to squares. -/
def canonicalShellConstant (n : Nat) : Nat :=
  (n + 1) * (n + 1 + 4) +
    (n + 3) * (n + 3 + 4) +
    (n + 2) * (n + 2 + 4) +
    (n + 2) * (n + 2 + 4)

private theorem sum_four_twice
    {a b c d za zb zc zd ca cb cc cd : Nat}
    (ha : 2 * a = za + ca) (hb : 2 * b = zb + cb)
    (hc : 2 * c = zc + cc) (hd : 2 * d = zd + cd) :
    2 * ((a + b) + (c + d)) =
      (za + zb + zc + zd) + (ca + cb + cc + cd) := by
  omega

private theorem shiftedConstant_one (n : Nat) :
    (n + 1) * (n + 1 + 4) = n * n + 6 * n + 5 := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

private theorem shiftedConstant_two (n : Nat) :
    (n + 2) * (n + 2 + 4) = n * n + 8 * n + 12 := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

private theorem shiftedConstant_three (n : Nat) :
    (n + 3) * (n + 3 + 4) = n * n + 10 * n + 21 := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem canonicalShellConstant_formula (n : Nat) :
    canonicalShellConstant n = 4 * (n * n) + 32 * n + 50 := by
  unfold canonicalShellConstant
  rw [shiftedConstant_one, shiftedConstant_three,
    shiftedConstant_two]
  omega

theorem canonicalShellConstant_even (k : Nat) :
    canonicalShellConstant (2 * k) = 4 * evenContent k + 2 := by
  rw [canonicalShellConstant_formula]
  have hsq : (2 * k) * (2 * k) = 4 * (k * k) := by
    change (2 * k) * (2 * k) = (2 * 2) * (k * k)
    ac_rfl
  have hcenter : (k + 1) * (k + 3) = k * k + 4 * k + 3 := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  unfold evenContent
  rw [hsq]
  rw [show 4 * (k + 1) * (k + 3) =
    4 * ((k + 1) * (k + 3)) by rw [Nat.mul_assoc]]
  rw [hcenter]
  omega

theorem canonicalShellConstant_odd (k : Nat) :
    canonicalShellConstant (2 * k + 1) + 2 = 4 * oddContent k := by
  rw [canonicalShellConstant_formula]
  have hsq0 : (2 * k) * (2 * k) = 4 * (k * k) := by
    change (2 * k) * (2 * k) = (2 * 2) * (k * k)
    ac_rfl
  have hsq :
      (2 * k + 1) * (2 * k + 1) = 4 * (k * k) + 4 * k + 1 := by
    simp only [Nat.add_mul, Nat.mul_add]
    rw [hsq0]
    omega
  have h4 : (4 * k) * k = 4 * (k * k) := by
    ac_rfl
  unfold oddContent
  rw [hsq, h4]
  omega

private theorem canonical_twice_exponent_sum
    (n t i j p q u v : Nat) (ht : t < n)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    2 * ((aAtomicMonomial (t + 1) (n - 1 - t) i p q).exponent +
        (mAtomicMonomial (t + 1) (n - 1 - t) j u v).exponent) =
      canonicalCenteredShell n t i j p q u v + canonicalShellConstant n := by
  have ha := canonical_a_atom_exponent_all n t i p q ht
  have hm := canonical_m_atom_exponent_all n t j u v ht
  rw [ha, hm]
  have h1 := twice_antidiagonalExponent_eq_centeredSquare_add
    (n + 1) (canonicalALeftIndex (t + 1) i p)
    (canonicalALeftIndex_le n t i p ht hp)
  have h2 := twice_antidiagonalExponent_eq_centeredSquare_add
    (n + 3) (canonicalARightIndex (t + 1) i q)
    (canonicalARightIndex_le n t i q ht hq)
  have h3 := twice_antidiagonalExponent_eq_centeredSquare_add
    (n + 2) (canonicalMLeftIndex (t + 1) j u)
    (canonicalMLeftIndex_le n t j u ht hu)
  have h4 := twice_antidiagonalExponent_eq_centeredSquare_add
    (n + 2) (canonicalMRightIndex (t + 1) j v)
    (canonicalMRightIndex_le n t j v ht hv)
  exact sum_four_twice h1 h2 h3 h4

/-- Once the combined endpoint exponent lies above the two-content,
two-square-gap threshold, `quotientEndpointDegree` is no longer truncated and
recovers the exact raw endpoint equality. -/
theorem endpoint_sum_eq_content_add_quotientEndpointDegree
    (content numerator midpoint : Nat)
    (hbalance : 2 * content + 2 ≤ numerator + midpoint) :
    numerator + midpoint =
      2 * content + 2 + quotientEndpointDegree content numerator midpoint := by
  unfold quotientEndpointDegree
  omega

/-- Exact selector-independent four-square shell at even length. -/
theorem canonical_even_four_square_shell
    (k t i j p q u v g : Nat) (ht : t < 2 * k)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hg :
      (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent +
          (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).exponent =
        2 * evenContent k + 2 + g) :
    canonicalCenteredShell (2 * k) t i j p q u v = 2 * g + 2 := by
  have hsum := canonical_twice_exponent_sum
    (2 * k) t i j p q u v ht hp hq hu hv
  have hconst := canonicalShellConstant_even k
  omega

/-- Exact selector-independent four-square shell at odd length for every
nonnegative raw endpoint degree `g`. -/
theorem canonical_odd_four_square_shell
    (k t i j p q u v g : Nat) (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hg :
      (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent +
          (mAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) j u v).exponent =
        2 * oddContent k + 2 + g) :
    canonicalCenteredShell (2 * k + 1) t i j p q u v = 2 * g + 6 := by
  have hsum := canonical_twice_exponent_sum
    (2 * k + 1) t i j p q u v ht hp hq hu hv
  have hconst := canonicalShellConstant_odd k
  omega

/-- The even canonical shell expressed directly through its actual
square-gap quotient endpoint degree.  The nontruncation condition is automatic
for every valid even selector. -/
theorem canonical_even_four_square_shell_quotient
    (k t i j p q u v : Nat) (ht : t < 2 * k)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j) :
    canonicalCenteredShell (2 * k) t i j p q u v =
      2 * quotientEndpointDegree (evenContent k)
        (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent
        (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).exponent + 2 := by
  have hbalance := canonical_even_endpoint_balance_all
    k t i j p q u v ht hp hq hu hv
  have hraw := endpoint_sum_eq_content_add_quotientEndpointDegree
    (evenContent k)
    (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent
    (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).exponent
    hbalance
  exact canonical_even_four_square_shell
    k t i j p q u v
    (quotientEndpointDegree (evenContent k)
      (aAtomicMonomial (t + 1) (2 * k - 1 - t) i p q).exponent
      (mAtomicMonomial (t + 1) (2 * k - 1 - t) j u v).exponent)
    ht hp hq hu hv hraw

/-- The odd canonical shell expressed directly through its actual square-gap
quotient endpoint degree whenever the endpoint degree is nontruncated. -/
theorem canonical_odd_four_square_shell_quotient
    (k t i j p q u v : Nat) (ht : t < 2 * k + 1)
    (hp : p < aLeftCount (t + 1) i)
    (hq : q < aRightCount (t + 1) i)
    (hu : u < mLeftCount (t + 1) j)
    (hv : v < mRightCount (t + 1) j)
    (hbalance :
      2 * oddContent k + 2 ≤
        (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent +
          (mAtomicMonomial (t + 1)
            (2 * k + 1 - 1 - t) j u v).exponent) :
    canonicalCenteredShell (2 * k + 1) t i j p q u v =
      2 * quotientEndpointDegree (oddContent k)
        (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent
        (mAtomicMonomial (t + 1)
          (2 * k + 1 - 1 - t) j u v).exponent + 6 := by
  have hraw := endpoint_sum_eq_content_add_quotientEndpointDegree
    (oddContent k)
    (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent
    (mAtomicMonomial (t + 1)
      (2 * k + 1 - 1 - t) j u v).exponent
    hbalance
  exact canonical_odd_four_square_shell
    k t i j p q u v
    (quotientEndpointDegree (oddContent k)
      (aAtomicMonomial (t + 1) (2 * k + 1 - 1 - t) i p q).exponent
      (mAtomicMonomial (t + 1)
        (2 * k + 1 - 1 - t) j u v).exponent)
    ht hp hq hu hv hraw

#print axioms canonicalShellConstant_formula
#print axioms canonicalShellConstant_even
#print axioms canonicalShellConstant_odd
#print axioms endpoint_sum_eq_content_add_quotientEndpointDegree
#print axioms canonical_even_four_square_shell
#print axioms canonical_odd_four_square_shell
#print axioms canonical_even_four_square_shell_quotient
#print axioms canonical_odd_four_square_shell_quotient

end YMGap.Continuum.CoreBCanonicalSquareShell
