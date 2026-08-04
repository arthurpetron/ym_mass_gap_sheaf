/-
`FusionPathRowLogConcave` — all-step support-row log-concavity for the
fundamental reflected SU(2) fusion walk.

# Computation-theoretic route

The executable path count now has the exact two-neighbour recurrence proved in
`FusionBallotRecurrence`.  Rather than expand a fresh ballot formula at every
step, this file proves a reusable closure theorem for the stronger PF2 ratio
order

    a i * a (j+1) <= a (i+1) * a j       (i <= j).

Both operations appearing in the reflected Pascal recurrence preserve this
order: adjacent summation, and adjoining a zero at the reflecting wall before
adjacent summation.  Starting from the delta row therefore proves the property
for every even and odd row simultaneously.  The diagonal specialization is
the desired all-`p` log-concavity on the parity support lattice.

# Honest scope

This is an unweighted statement about the fundamental (`j = 1`) path counts.
It does not prove the heat-weighted box interlacing or inhabit
`FusionConvLogConcaveCore`; those require additional weighted input.

# Constructive contract

Mathlib-free; pure `Nat` core.  No `Classical`, `native_decide`, `sorry`, new
axiom, or noncomputable definition.  Every load-bearing theorem is axiom-gated
below.
-/

import YMGap.Continuum.FusionBallotRecurrence

namespace YMGap.Continuum.FusionPathRowLogConcave

open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusionBallotRecurrence

/-! ## 1. A strong ratio-order interface and its Pascal closures -/

/-- The cross-multiplied monotone-ratio property of a nonnegative sequence.
Its nearest-neighbour case is ordinary log-concavity. -/
def RatioOrdered (a : Nat → Nat) : Prop :=
  ∀ i j, i < j → a i * a (j + 1) ≤ a (i + 1) * a j

/-- Adjacent Pascal summation. -/
def adjacentSum (a : Nat → Nat) (i : Nat) : Nat := a i + a (i + 1)

/-- Adjoin the reflecting-wall zero on the left. -/
def prependZero (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => a i

/-- Four-term algebra for the nearest-neighbour closure. -/
private theorem adjacentSum_local_core (x0 x1 x2 x3 : Nat)
    (h0 : x0 * x2 ≤ x1 * x1)
    (h1 : x0 * x3 ≤ x1 * x2)
    (h2 : x1 * x3 ≤ x2 * x2) :
    (x0 + x1) * (x2 + x3) ≤ (x1 + x2) * (x1 + x2) := by
  calc
    (x0 + x1) * (x2 + x3) =
        (x0 * x2 + x0 * x3) + (x1 * x2 + x1 * x3) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    _ ≤ (x1 * x1 + x1 * x2) + (x1 * x2 + x2 * x2) :=
      Nat.add_le_add
        (Nat.add_le_add h0 h1)
        (Nat.add_le_add (Nat.le_refl _) h2)
    _ = (x1 + x2) * (x1 + x2) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm x2 x1]

/-- Four-term algebra for separated monotone-ratio windows. -/
private theorem adjacentSum_cross_core (x0 x1 x2 y0 y1 y2 : Nat)
    (h0 : x0 * y1 ≤ x1 * y0)
    (h1 : x0 * y2 ≤ x1 * y1)
    (h2 : x1 * y1 ≤ x2 * y0)
    (h3 : x1 * y2 ≤ x2 * y1) :
    (x0 + x1) * (y1 + y2) ≤ (x1 + x2) * (y0 + y1) := by
  calc
    (x0 + x1) * (y1 + y2) =
        (x0 * y1 + x0 * y2) + (x1 * y1 + x1 * y2) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    _ ≤ (x1 * y0 + x1 * y1) + (x2 * y0 + x2 * y1) :=
      Nat.add_le_add (Nat.add_le_add h0 h1) (Nat.add_le_add h2 h3)
    _ = (x1 + x2) * (y0 + y1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]

/-- Monotone ratios are preserved by adjacent Pascal summation. -/
theorem ratioOrdered_adjacentSum {a : Nat → Nat} (ha : RatioOrdered a) :
    RatioOrdered (adjacentSum a) := by
  intro i j hij
  by_cases heq : i + 1 = j
  · subst j
    have h0 := ha i (i + 1) (by omega)
    have h1 := ha i (i + 2) (by omega)
    have h2 := ha (i + 1) (i + 2) (by omega)
    have h0' : a i * a (i + 2) ≤ a (i + 1) * a (i + 1) := by
      simpa only [show i + 1 + 1 = i + 2 by omega] using h0
    have h1' : a i * a (i + 3) ≤ a (i + 1) * a (i + 2) := by
      simpa only [show i + 2 + 1 = i + 3 by omega] using h1
    have h2' : a (i + 1) * a (i + 3) ≤ a (i + 2) * a (i + 2) := by
      simpa only [show i + 1 + 1 = i + 2 by omega,
        show i + 2 + 1 = i + 3 by omega] using h2
    simpa only [adjacentSum, show i + 1 + 1 = i + 2 by omega,
      show i + 2 + 1 = i + 3 by omega] using
        adjacentSum_local_core (a i) (a (i + 1)) (a (i + 2)) (a (i + 3))
          h0' h1' h2'
  · have hij' : i + 1 < j := by omega
    have h0 := ha i j hij
    have h1 := ha i (j + 1) (by omega)
    have h2 := ha (i + 1) j hij'
    have h3 := ha (i + 1) (j + 1) (by omega)
    have h1' : a i * a (j + 2) ≤ a (i + 1) * a (j + 1) := by
      simpa only [show j + 1 + 1 = j + 2 by omega] using h1
    have h2' : a (i + 1) * a (j + 1) ≤ a (i + 2) * a j := by
      simpa only [show i + 1 + 1 = i + 2 by omega] using h2
    have h3' : a (i + 1) * a (j + 2) ≤ a (i + 2) * a (j + 1) := by
      simpa only [show i + 1 + 1 = i + 2 by omega,
        show j + 1 + 1 = j + 2 by omega] using h3
    simpa only [adjacentSum, show i + 1 + 1 = i + 2 by omega,
      show j + 1 + 1 = j + 2 by omega] using
        adjacentSum_cross_core (a i) (a (i + 1)) (a (i + 2))
          (a j) (a (j + 1)) (a (j + 2)) h0 h1' h2' h3'

/-- Monotone ratios survive adjoining a zero at the reflecting wall. -/
theorem ratioOrdered_prependZero {a : Nat → Nat} (ha : RatioOrdered a) :
    RatioOrdered (prependZero a) := by
  intro i j hij
  cases i with
  | zero =>
      simp [prependZero]
  | succ i =>
      cases j with
      | zero => omega
      | succ j =>
          simpa only [prependZero, Nat.succ_eq_add_one] using ha i j (by omega)

/-! ## 2. Even and odd support rows of the reflected walk -/

/-- The even-time row, indexed only on its even endpoint support. -/
def evenRow (n r : Nat) : Nat := pathCount 1 (2 * n) (2 * r)

/-- The odd-time row, indexed only on its odd endpoint support. -/
def oddRow (n r : Nat) : Nat := pathCount 1 (2 * n + 1) (2 * r + 1)

/-- Odd rows are adjacent sums of the preceding even row. -/
theorem oddRow_eq_adjacentSum (n r : Nat) :
    oddRow n r = adjacentSum (evenRow n) r := by
  unfold oddRow adjacentSum evenRow
  have h := pathCount_j1_succ (2 * n) (2 * r + 1)
  rw [h]
  simp only [if_neg (by omega : 2 * r + 1 ≠ 0)]
  congr 1 <;> omega

/-- The next even row is an adjacent sum after adjoining the reflecting-wall
zero to the preceding odd row. -/
theorem evenRow_succ_eq_reflectedAdjacentSum (n r : Nat) :
    evenRow (n + 1) r = adjacentSum (prependZero (oddRow n)) r := by
  cases r with
  | zero =>
      unfold evenRow adjacentSum prependZero oddRow
      have h := pathCount_j1_succ (2 * n + 1) 0
      have htime : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      rw [htime, h]
      simp
  | succ r =>
      unfold evenRow adjacentSum prependZero oddRow
      have h := pathCount_j1_succ (2 * n + 1) (2 * (r + 1))
      have htime : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      rw [htime, h]
      simp only [if_neg (by omega : 2 * (r + 1) ≠ 0)]
      congr 1 <;> omega

/-- The time-zero support row is ratio ordered. -/
theorem evenRow_zero_ratioOrdered : RatioOrdered (evenRow 0) := by
  intro i j hij
  unfold evenRow pathCount
  simp only [Nat.mul_zero, Nat.zero_mul, beq_iff_eq]
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      decide
    · simp [hj]
  · simp [hi]

/-- Every even-time support row has monotone adjacent ratios. -/
theorem evenRow_ratioOrdered : ∀ n, RatioOrdered (evenRow n)
  | 0 => evenRow_zero_ratioOrdered
  | n + 1 => by
      have ho : RatioOrdered (oddRow n) := by
        simpa only [RatioOrdered, oddRow_eq_adjacentSum] using
          ratioOrdered_adjacentSum (evenRow_ratioOrdered n)
      simpa only [RatioOrdered, evenRow_succ_eq_reflectedAdjacentSum] using
        ratioOrdered_adjacentSum (ratioOrdered_prependZero ho)

/-- Every odd-time support row has monotone adjacent ratios. -/
theorem oddRow_ratioOrdered (n : Nat) : RatioOrdered (oddRow n) := by
  simpa only [RatioOrdered, oddRow_eq_adjacentSum] using
    ratioOrdered_adjacentSum (evenRow_ratioOrdered n)

/-! ## 3. All-step support-lattice row log-concavity -/

/-- Even-time rows are log-concave at every support index. -/
theorem evenRow_logConcave (n r : Nat) :
    pathCount 1 (2 * n) (2 * r) * pathCount 1 (2 * n) (2 * r + 4)
      ≤ pathCount 1 (2 * n) (2 * r + 2) * pathCount 1 (2 * n) (2 * r + 2) := by
  have h := evenRow_ratioOrdered n r (r + 1) (by omega)
  unfold evenRow at h
  simpa only [show 2 * (r + 1) = 2 * r + 2 by omega,
    show 2 * (r + 1 + 1) = 2 * r + 4 by omega] using h

/-- Odd-time rows are log-concave at every support index. -/
theorem oddRow_logConcave (n r : Nat) :
    pathCount 1 (2 * n + 1) (2 * r + 1) *
        pathCount 1 (2 * n + 1) (2 * r + 5)
      ≤ pathCount 1 (2 * n + 1) (2 * r + 3) *
        pathCount 1 (2 * n + 1) (2 * r + 3) := by
  have h := oddRow_ratioOrdered n r (r + 1) (by omega)
  unfold oddRow at h
  simpa only [show 2 * (r + 1) + 1 = 2 * r + 3 by omega,
    show 2 * (r + 1 + 1) + 1 = 2 * r + 5 by omega] using h

/-- **All-`p` row log-concavity on the fundamental support lattice.**
For every walk length and endpoint, consecutive reachable endpoints (spacing
two) form a log-concave row.  When `s` has the wrong parity, all three terms
vanish; on the parity lattice this is exactly the diagonal specialization of
the ratio-order theorem above. -/
theorem pathCount_j1_row_logConcave (p s : Nat) :
    pathCount 1 p s * pathCount 1 p (s + 4)
      ≤ pathCount 1 p (s + 2) * pathCount 1 p (s + 2) := by
  have hpdm := Nat.div_add_mod p 2
  have hsdm := Nat.div_add_mod s 2
  have hpmod : p % 2 = 0 ∨ p % 2 = 1 := by omega
  have hsmod : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases hpmod with hp0 | hp1 <;> rcases hsmod with hs0 | hs1
  · have hp : p = 2 * (p / 2) := by omega
    have hs : s = 2 * (s / 2) := by omega
    rw [hp, hs]
    exact evenRow_logConcave (p / 2) (s / 2)
  · have h0 : pathCount 1 p s = 0 :=
      pathCount_j1_eq_zero_of_parity_ne p s (by omega)
    rw [h0, Nat.zero_mul]
    exact Nat.zero_le _
  · have h0 : pathCount 1 p s = 0 :=
      pathCount_j1_eq_zero_of_parity_ne p s (by omega)
    rw [h0, Nat.zero_mul]
    exact Nat.zero_le _
  · have hp : p = 2 * (p / 2) + 1 := by omega
    have hs : s = 2 * (s / 2) + 1 := by omega
    rw [hp, hs]
    exact oddRow_logConcave (p / 2) (s / 2)

end YMGap.Continuum.FusionPathRowLogConcave

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusionPathRowLogConcave.ratioOrdered_adjacentSum
#print axioms YMGap.Continuum.FusionPathRowLogConcave.ratioOrdered_prependZero
#print axioms YMGap.Continuum.FusionPathRowLogConcave.oddRow_eq_adjacentSum
#print axioms YMGap.Continuum.FusionPathRowLogConcave.evenRow_succ_eq_reflectedAdjacentSum
#print axioms YMGap.Continuum.FusionPathRowLogConcave.evenRow_zero_ratioOrdered
#print axioms YMGap.Continuum.FusionPathRowLogConcave.evenRow_ratioOrdered
#print axioms YMGap.Continuum.FusionPathRowLogConcave.oddRow_ratioOrdered
#print axioms YMGap.Continuum.FusionPathRowLogConcave.evenRow_logConcave
#print axioms YMGap.Continuum.FusionPathRowLogConcave.oddRow_logConcave
#print axioms YMGap.Continuum.FusionPathRowLogConcave.pathCount_j1_row_logConcave
