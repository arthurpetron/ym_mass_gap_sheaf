/-
Track 11.7-fusion / R4x -- parametric endpoint-ratio coefficient compiler.

For endpoint depth `m`, the active ordered Clebsch pairs are the parity
triangle

    i + j <= m,    i + j = m (mod 2).

Writing a monotone endpoint coefficient sequence as a base plus nonnegative
successive increments expands the adjacent-depth slack into quadratic
increment monomials.  The coefficient at thresholds `(a,b)` is controlled by
the number of parity-triangle cells above those thresholds.  Translation by
`(a,b)` shows that count is

    T(n) = (floor(n/2)+1) * (floor((n+1)/2)+1),
    n = m-a-b.

If `R = ceil(m/2)`, every slack coefficient is nonnegative because

    (R+1) * T(n-1) <= R * T(n),    1 <= n <= m <= 2*R.

This module proves that arithmetic schema once, by parity and monotone Nat
multiplication.  It is the proof-about-computation core behind the fixed
reflected certificates through the ninth shell; the next layer will connect
the generic coefficient expansion to `Q'` endpoint boxes.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeEndpointRatioCompiler

/-- Number of ordered cells in the parity triangle of depth `n`. -/
def parityTriangleCount (n : Nat) : Nat :=
  (n / 2 + 1) * ((n + 1) / 2 + 1)

/-- The even parity triangle of depth `2*q` has `(q+1)^2` cells. -/
theorem parityTriangleCount_even (q : Nat) :
    parityTriangleCount (2 * q) = (q + 1) * (q + 1) := by
  have h0 : (2 * q) / 2 = q := by omega
  have h1 : (2 * q + 1) / 2 = q := by omega
  simp only [parityTriangleCount, h0, h1]

/-- The odd parity triangle of depth `2*q+1` has `(q+1)(q+2)` cells. -/
theorem parityTriangleCount_odd (q : Nat) :
    parityTriangleCount (2 * q + 1) = (q + 1) * (q + 2) := by
  have h0 : (2 * q + 1) / 2 = q := by omega
  have h1 : (2 * q + 1 + 1) / 2 = q + 1 := by omega
  simp only [parityTriangleCount, h0, h1]

/-- Immediately before a positive even depth `2*q`, the odd triangle has
`q(q+1)` cells. -/
theorem parityTriangleCount_even_pred (q : Nat) (hq : 0 < q) :
    parityTriangleCount (2 * q - 1) = q * (q + 1) := by
  have hindex : 2 * q - 1 = 2 * (q - 1) + 1 := by omega
  rw [hindex, parityTriangleCount_odd]
  have hsucc : q - 1 + 1 = q := by omega
  rw [hsucc]
  congr 1
  omega

/-- Immediately before odd depth `2*q+1`, the even triangle has
`(q+1)^2` cells. -/
theorem parityTriangleCount_odd_pred (q : Nat) :
    parityTriangleCount (2 * q + 1 - 1) = (q + 1) * (q + 1) := by
  have hindex : 2 * q + 1 - 1 = 2 * q := by omega
  rw [hindex, parityTriangleCount_even]

/-- Even-depth coefficient inequality.  After cancelling the positive
factor `q+1`, this is exactly `q <= R`. -/
theorem scaled_even_triangle_step (R q : Nat) (hq : q <= R) :
    (R + 1) * (q * (q + 1)) <= R * ((q + 1) * (q + 1)) := by
  have hbase : (R + 1) * q <= R * (q + 1) := by
    simpa only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one] using
      Nat.add_le_add_left hq (R * q)
  have hscaled := Nat.mul_le_mul_right (q + 1) hbase
  simpa only [Nat.mul_assoc] using hscaled

/-- Odd-depth coefficient inequality.  After cancelling `q+1`, this is
exactly `q+1 <= R`. -/
theorem scaled_odd_triangle_step (R q : Nat) (hq : q + 1 <= R) :
    (R + 1) * ((q + 1) * (q + 1)) <=
      R * ((q + 1) * (q + 2)) := by
  have hbase : (R + 1) * (q + 1) <= R * (q + 2) := by
    have h := Nat.add_le_add_left hq (R * (q + 1))
    have hq2 : q + 2 = (q + 1) + 1 := by omega
    rw [hq2, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    exact h
  have hscaled := Nat.mul_le_mul_right (q + 1) hbase
  calc
    (R + 1) * ((q + 1) * (q + 1)) =
        ((R + 1) * (q + 1)) * (q + 1) := by ac_rfl
    _ <= (R * (q + 2)) * (q + 1) := hscaled
    _ = R * ((q + 1) * (q + 2)) := by ac_rfl

/-- Uniform parity-triangle ratio.  This is the arithmetic statement needed
for every quadratic increment coefficient in an endpoint slack. -/
theorem scaled_parityTriangleCount_pred
    (R n : Nat) (hn : 0 < n) (hnR : n <= 2 * R) :
    (R + 1) * parityTriangleCount (n - 1) <=
      R * parityTriangleCount n := by
  have hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
  cases hpar with
  | inl heven =>
      let q := n / 2
      have hnform : n = 2 * q := by unfold q; omega
      have hqpos : 0 < q := by omega
      have hqR : q <= R := by omega
      rw [hnform, parityTriangleCount_even,
        parityTriangleCount_even_pred q hqpos]
      exact scaled_even_triangle_step R q hqR
  | inr hodd =>
      let q := n / 2
      have hnform : n = 2 * q + 1 := by unfold q; omega
      have hqR : q + 1 <= R := by omega
      rw [hnform, parityTriangleCount_odd,
        parityTriangleCount_odd_pred]
      exact scaled_odd_triangle_step R q hqR

/-- Count of parity-triangle cells remaining after imposing the coordinate
thresholds `i>=a`, `j>=b`. -/
def thresholdTriangleCount (m a b : Nat) : Nat :=
  if a + b <= m then parityTriangleCount (m - (a + b)) else 0

/-- Every threshold coefficient in the adjacent-depth endpoint slack is
nonnegative.  Boundary thresholds present only at depth `m` are handled by
the zero branch; interior thresholds reduce to
`scaled_parityTriangleCount_pred`. -/
theorem scaled_thresholdTriangleCount_pred
    (R m a b : Nat) (hm : 0 < m) (hmR : m <= 2 * R) :
    (R + 1) * thresholdTriangleCount (m - 1) a b <=
      R * thresholdTriangleCount m a b := by
  by_cases hprev : a + b <= m - 1
  · have hnow : a + b <= m := by omega
    have hnpos : 0 < m - (a + b) := by omega
    have hnR : m - (a + b) <= 2 * R := by omega
    have hpred : m - 1 - (a + b) = (m - (a + b)) - 1 := by omega
    rw [thresholdTriangleCount, if_pos hprev,
      thresholdTriangleCount, if_pos hnow, hpred]
    exact scaled_parityTriangleCount_pred R (m - (a + b)) hnpos hnR
  · rw [thresholdTriangleCount, if_neg hprev, Nat.mul_zero]
    exact Nat.zero_le _

/-- At the canonical scale `R=ceil(m/2)`, the constant coefficient balances
exactly.  The inequalities `m<=2R<=m+1` state that relation without division. -/
theorem parityTriangleCount_boundary_balance
    (R m : Nat) (hm : 0 < m) (hmR : m <= 2 * R)
    (hRm : 2 * R <= m + 1) :
    (R + 1) * parityTriangleCount (m - 1) =
      R * parityTriangleCount m := by
  have hpar : m % 2 = 0 ∨ m % 2 = 1 := by omega
  cases hpar with
  | inl heven =>
      let q := m / 2
      have hmform : m = 2 * q := by unfold q; omega
      have hq : q = R := by omega
      subst R
      rw [hmform, parityTriangleCount_even]
      rw [parityTriangleCount_even_pred q (by omega)]
      ac_rfl
  | inr hodd =>
      let q := m / 2
      have hmform : m = 2 * q + 1 := by unfold q; omega
      have hq : q + 1 = R := by omega
      subst R
      rw [hmform, parityTriangleCount_odd, parityTriangleCount_odd_pred]
      ac_rfl

end YMGap.Continuum.P2HalfTimeEndpointRatioCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCompiler.parityTriangleCount_even
#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCompiler.scaled_parityTriangleCount_pred
#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCompiler.scaled_thresholdTriangleCount_pred
#print axioms YMGap.Continuum.P2HalfTimeEndpointRatioCompiler.parityTriangleCount_boundary_balance
