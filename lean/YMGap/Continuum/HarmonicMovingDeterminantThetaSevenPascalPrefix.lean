/-
Seven-coordinate prefix calculus for Pascal elevation.

This module splits an arbitrary deficit sequence into its first seven point
masses and a suffix supported from deficit seven onward.  Pascal elevation is
linear, each point mass evolves by an exact binomial coefficient, and the
suffix cannot propagate backward into deficits zero through six.  This is the
finite-prefix interface needed by the symbolic formulas for the exceptional
coordinates.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPrefix

open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence

/-- A sequence supported at one deficit. -/
def sevenPointSeq (j : Nat) (x : Int) : Nat → Int :=
  fun r => if r = j then x else 0

/-- The first seven point masses of a deficit sequence. -/
def sevenPointPrefix (b : Nat → Int) : Nat → Int :=
  fun r =>
    sevenPointSeq 0 (b 0) r + sevenPointSeq 1 (b 1) r +
    sevenPointSeq 2 (b 2) r + sevenPointSeq 3 (b 3) r +
    sevenPointSeq 4 (b 4) r + sevenPointSeq 5 (b 5) r +
    sevenPointSeq 6 (b 6) r

/-- Suffix supported from deficit seven onward. -/
def sevenPointBulk (b : Nat → Int) : Nat → Int :=
  fun r => if 7 ≤ r then b r else 0

/-- Exact point-prefix/suffix decomposition. -/
theorem seven_point_bulk (b : Nat → Int) (r : Nat) :
    b r = sevenPointPrefix b r + sevenPointBulk b r := by
  by_cases h0 : r = 0
  · subst r; simp [sevenPointPrefix, sevenPointSeq, sevenPointBulk]
  by_cases h1 : r = 1
  · subst r; simp [sevenPointPrefix, sevenPointSeq, sevenPointBulk]
  by_cases h2 : r = 2
  · subst r; simp [sevenPointPrefix, sevenPointSeq, sevenPointBulk]
  by_cases h3 : r = 3
  · subst r; simp [sevenPointPrefix, sevenPointSeq, sevenPointBulk]
  by_cases h4 : r = 4
  · subst r; simp [sevenPointPrefix, sevenPointSeq, sevenPointBulk]
  by_cases h5 : r = 5
  · subst r; simp [sevenPointPrefix, sevenPointSeq, sevenPointBulk]
  by_cases h6 : r = 6
  · subst r; simp [sevenPointPrefix, sevenPointSeq, sevenPointBulk]
  have hr : 7 ≤ r := by omega
  simp [sevenPointPrefix, sevenPointSeq, sevenPointBulk, h0, h1, h2, h3,
    h4, h5, h6, hr]

/-- Pascal elevation respects pointwise equality. -/
theorem sevenPascalElevate_congr (d : Nat) {a b : Nat → Int}
    (h : ∀ r, a r = b r) (r : Nat) :
    sevenPascalElevate d a r = sevenPascalElevate d b r := by
  induction d generalizing r with
  | zero => exact h r
  | succ d ih =>
      cases r with
      | zero => exact ih 0
      | succ r => simp only [sevenPascalElevate, ih]

/-- Pascal elevation is additive. -/
theorem sevenPascalElevate_add (d : Nat) (a b : Nat → Int) (r : Nat) :
    sevenPascalElevate d (fun j => a j + b j) r =
      sevenPascalElevate d a r + sevenPascalElevate d b r := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
      cases r with
      | zero => exact ih 0
      | succ r =>
          simp only [sevenPascalElevate, ih]
          ac_rfl

private theorem choose_zero_of_lt : ∀ n k : Nat,
    n < k → PNPaths.choose n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      simp only [PNPaths.choose]
      rw [choose_zero_of_lt n k (by omega)]
      rw [choose_zero_of_lt n (k + 1) (by omega)]

/-- Exact binomial evolution of one point mass. -/
theorem sevenPascalElevate_point (d j r : Nat) (x : Int) :
    sevenPascalElevate d (sevenPointSeq j x) r =
      if j ≤ r then (PNPaths.choose d (r - j) : Int) * x else 0 := by
  induction d generalizing r with
  | zero =>
      by_cases heq : r = j
      · subst r
        simp [sevenPascalElevate, sevenPointSeq, PNPaths.choose]
      · by_cases hjr : j ≤ r
        · have hlt : j < r := by omega
          have hz := choose_zero_of_lt 0 (r - j) (by omega)
          simp [sevenPascalElevate, sevenPointSeq, heq, hjr, hz]
        · simp [sevenPascalElevate, sevenPointSeq, heq, hjr]
  | succ d ih =>
      cases r with
      | zero =>
          by_cases hj : j = 0
          · subst j
            have h0 := ih 0
            simpa [PNPaths.choose] using h0
          · have hj0 : ¬ j ≤ 0 := by omega
            simp [sevenPascalElevate, ih, hj0]
      | succ r =>
          simp only [sevenPascalElevate, ih]
          by_cases hjr : j ≤ r
          · have hjr1 : j ≤ r + 1 := by omega
            have hd : r + 1 - j = (r - j) + 1 := by omega
            simp only [if_pos hjr, if_pos hjr1, hd, PNPaths.choose,
              Int.natCast_add, Int.add_mul]
            ac_rfl
          · by_cases heq : j = r + 1
            · subst j
              rw [if_neg hjr]
              simp [PNPaths.choose]
            · have hjr1 : ¬ j ≤ r + 1 := by omega
              simp [hjr, hjr1]

/-- A suffix initially supported at seven remains zero in deficits zero
through six under any number of Pascal elevations. -/
theorem sevenPascalElevate_bulk_zero (d : Nat) (b : Nat → Int) (r : Nat)
    (hr : r ≤ 6) : sevenPascalElevate d (sevenPointBulk b) r = 0 := by
  induction d generalizing r with
  | zero => simp [sevenPascalElevate, sevenPointBulk, show ¬ 7 ≤ r by omega]
  | succ d ih =>
      cases r with
      | zero => exact ih 0 (by omega)
      | succ r =>
          simp only [sevenPascalElevate]
          rw [ih (r + 1) (by omega), ih r (by omega)]
          rfl

/-- Closed seven-coordinate formula for every output deficit at most six. -/
theorem sevenPascalElevate_prefix_formula (d : Nat) (b : Nat → Int) (r : Nat)
    (hr : r ≤ 6) :
    sevenPascalElevate d b r =
      (if 0 ≤ r then (PNPaths.choose d (r - 0) : Int) * b 0 else 0) +
      (if 1 ≤ r then (PNPaths.choose d (r - 1) : Int) * b 1 else 0) +
      (if 2 ≤ r then (PNPaths.choose d (r - 2) : Int) * b 2 else 0) +
      (if 3 ≤ r then (PNPaths.choose d (r - 3) : Int) * b 3 else 0) +
      (if 4 ≤ r then (PNPaths.choose d (r - 4) : Int) * b 4 else 0) +
      (if 5 ≤ r then (PNPaths.choose d (r - 5) : Int) * b 5 else 0) +
      (if 6 ≤ r then (PNPaths.choose d (r - 6) : Int) * b 6 else 0) := by
  rw [sevenPascalElevate_congr d (seven_point_bulk b) r]
  unfold sevenPointPrefix
  simp only [sevenPascalElevate_add, sevenPascalElevate_point]
  rw [sevenPascalElevate_bulk_zero d b r hr]
  simp only [Int.add_zero]

#print axioms sevenPointSeq
#print axioms sevenPointPrefix
#print axioms sevenPointBulk
#print axioms seven_point_bulk
#print axioms sevenPascalElevate_congr
#print axioms sevenPascalElevate_add
#print axioms sevenPascalElevate_point
#print axioms sevenPascalElevate_bulk_zero
#print axioms sevenPascalElevate_prefix_formula

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPrefix
