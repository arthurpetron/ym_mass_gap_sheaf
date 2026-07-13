/-
Deficit-coordinate recurrence for the seven-unit theta gap.

This module turns the coefficient recurrences into the exact one-scale
identity used by the bulk induction.  All rows are extended by zero beyond
their Bernstein degree, so Pascal elevation is valid at both boundaries.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence

open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow
open YMGap.Continuum.HarmonicThetaPascalBridge

/-- Minimal common Bernstein degree for the head ending immediately before
mode `m`. -/
def sevenGapDegree (m : Nat) : Nat := 2 * m * m + 1

/-- Minimal seven-gap row in deficit order, extended by zero. -/
def sevenGapDeficit (m r : Nat) : Int :=
  if r ≤ sevenGapDegree m then
    sevenGapBernCoeff (sevenGapDegree m) m (sevenGapDegree m - r)
  else 0

/-- Iterated Pascal elevation in deficit coordinates. -/
def sevenPascalElevate : Nat → (Nat → Int) → Nat → Int
  | 0, b, r => b r
  | d + 1, b, 0 => sevenPascalElevate d b 0
  | d + 1, b, r + 1 =>
      sevenPascalElevate d b (r + 1) + sevenPascalElevate d b r

private theorem choose_zero_of_lt : ∀ n k : Nat,
    n < k → PNPaths.choose n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      simp only [PNPaths.choose]
      rw [choose_zero_of_lt n k (by omega)]
      rw [choose_zero_of_lt n (k + 1) (by omega)]

private theorem choose_self : ∀ n : Nat, PNPaths.choose n n = 1
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose]
      rw [choose_self n]
      rw [choose_zero_of_lt n (n + 1) (by omega)]

private theorem thetaMonoBernCoeff_top (D e : Nat) (heD : e ≤ D) :
    thetaMonoBernCoeff D e D = 1 := by
  simp [thetaMonoBernCoeff, heD, choose_self]

private theorem sevenMassCellBernCoeff_top (D n : Nat)
    (hD : 2 * n * n ≤ D) : sevenMassCellBernCoeff D n D = 0 := by
  have h0 : 2 * n * n - 2 ≤ D := by omega
  have h1 : 2 * n * n - 1 ≤ D := by omega
  simp [sevenMassCellBernCoeff, thetaMonoBernCoeff_top D _ h0,
    thetaMonoBernCoeff_top D _ h1, thetaMonoBernCoeff_top D _ hD]

private theorem sevenMassHeadBernCoeff_top (D : Nat) : ∀ m,
    (hD : 2 * m * m ≤ D) → sevenMassHeadBernCoeff D D m = 0
  | 0, _ => rfl
  | m + 1, hD => by
      simp only [sevenMassHeadBernCoeff]
      have hm : 2 * m * m ≤ D := by
        have hle : m ≤ m + 1 := by omega
        have hsq := Nat.mul_le_mul hle hle
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      rw [sevenMassHeadBernCoeff_top D m hm,
        sevenMassCellBernCoeff_top D (m + 1) hD]
      rfl

private theorem thetaDiagBernCoeff_top (D n : Nat)
    (hD : 2 * n * n + 1 ≤ D) :
    thetaDiagBernCoeff D n D = Int.ofNat (8 * n * n) := by
  have h0 : 2 * n * n - 2 ≤ D := by omega
  have h1 : 2 * n * n - 1 ≤ D := by omega
  have h2 : 2 * n * n ≤ D := by omega
  simp [thetaDiagBernCoeff, thetaMonoBernCoeff_top D _ h0,
    thetaMonoBernCoeff_top D _ h1, thetaMonoBernCoeff_top D _ h2,
    thetaMonoBernCoeff_top D _ hD]
  ac_rfl

private theorem sevenGapBernCoeff_top (D m : Nat) (hm : 1 ≤ m)
    (hD : sevenGapDegree m ≤ D) :
    sevenGapBernCoeff D m D = 4 * (m : Int) * ((m : Int) - 1) := by
  have hmass : sevenMassHeadBernCoeff D D (m - 1) = 0 := by
    apply sevenMassHeadBernCoeff_top
    have hle : m - 1 ≤ m := Nat.sub_le m 1
    have hsq := Nat.mul_le_mul hle hle
    have hmD : 2 * m * m ≤ D := by
      have hD' := hD
      simp only [sevenGapDegree] at hD'
      omega
    exact Nat.le_trans (by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hsq) hmD
  have hend : 1 + (m - 1) = m := by omega
  have htail :
      cumulativeThetaBernCoeff D 1 D (m - 1) =
        Int.ofNat (4 * (2 * 1 * (1 + (m - 1)) + (m - 1) * m)) := by
    rw [cumulativeThetaBernCoeff_eq_reverseTailCoeff]
    rw [ThetaResidualPascalTelescope.reverseTailCoeff_top D 1 (m - 1)
      (by rw [hend]; simpa [sevenGapDegree] using hD)]
    unfold ThetaResidualPascalTelescope.reverseTopFluxNat
    rw [hend]
    rw [show m - 1 + 1 = m by omega]
  have hdiag := thetaDiagBernCoeff_top D m (by
    simpa [sevenGapDegree] using hD)
  unfold sevenGapBernCoeff growingHeadThetaBernCoeff
  rw [hmass, htail, hdiag, hend]
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
  have hmcast : (((m - 1 : Nat) : Int) = (m : Int) - 1) := by omega
  rw [hmcast]
  rw [Int.zero_sub]
  let x : Int := (m : Int)
  change -(4 * (2 * x + (x - 1) * x) - 8 * x * x) = 4 * x * (x - 1)
  simp only [Int.mul_add, Int.add_mul, Int.sub_eq_add_neg, Int.mul_neg,
    Int.neg_mul, Int.neg_add, Int.neg_neg]
  simp only [Int.one_mul, Int.mul_one]
  have h8 : 8 * x * x = 8 * (x * x) := by ac_rfl
  have h4 : 4 * x * x = 4 * (x * x) := by ac_rfl
  have h42 : 4 * (2 * x) = 8 * x := by
    calc
      4 * (2 * x) = (4 * 2) * x := by ac_rfl
      _ = 8 * x := by rw [show (4 : Int) * 2 = 8 by decide]
  rw [h8, h4, h42]
  omega

private theorem thetaMonoBernCoeff_degree_bottom (D e : Nat) :
    thetaMonoBernCoeff (D + 1) e 0 = thetaMonoBernCoeff D e 0 := by
  cases e with
  | zero => simp [thetaMonoBernCoeff, PNPaths.choose]
  | succ e => simp [thetaMonoBernCoeff]

private theorem sevenMassCellBernCoeff_degree_bottom (D n : Nat) :
    sevenMassCellBernCoeff (D + 1) n 0 = sevenMassCellBernCoeff D n 0 := by
  simp only [sevenMassCellBernCoeff, thetaMonoBernCoeff_degree_bottom]

private theorem sevenMassHeadBernCoeff_degree_bottom (D : Nat) : ∀ c,
    sevenMassHeadBernCoeff (D + 1) 0 c = sevenMassHeadBernCoeff D 0 c
  | 0 => rfl
  | c + 1 => by
      simp only [sevenMassHeadBernCoeff,
        sevenMassHeadBernCoeff_degree_bottom D c]
      rw [sevenMassCellBernCoeff_degree_bottom D (c + 1)]

private theorem thetaDiagBernCoeff_degree_bottom (D n : Nat) :
    thetaDiagBernCoeff (D + 1) n 0 = thetaDiagBernCoeff D n 0 := by
  simp only [thetaDiagBernCoeff, thetaMonoBernCoeff_degree_bottom]

private theorem thetaOffBernCoeff_degree_bottom (D n : Nat) :
    thetaOffBernCoeff (D + 1) n 0 = thetaOffBernCoeff D n 0 := by
  simp only [thetaOffBernCoeff, thetaMonoBernCoeff_degree_bottom]

private theorem cumulativeThetaBernCoeff_degree_bottom (D n : Nat) : ∀ c,
    cumulativeThetaBernCoeff (D + 1) n 0 c = cumulativeThetaBernCoeff D n 0 c
  | 0 => thetaDiagBernCoeff_degree_bottom D n
  | c + 1 => by
      simp only [cumulativeThetaBernCoeff,
        thetaDiagBernCoeff_degree_bottom, thetaOffBernCoeff_degree_bottom,
        cumulativeThetaBernCoeff_degree_bottom D (n + 1) c]

private theorem growingHeadThetaBernCoeff_degree_bottom (D m : Nat) :
    growingHeadThetaBernCoeff (D + 1) m 0 =
      growingHeadThetaBernCoeff D m 0 := by
  simp only [growingHeadThetaBernCoeff,
    cumulativeThetaBernCoeff_degree_bottom,
    thetaDiagBernCoeff_degree_bottom]

private theorem sevenGapBernCoeff_degree_bottom (D m : Nat) :
    sevenGapBernCoeff (D + 1) m 0 = sevenGapBernCoeff D m 0 := by
  simp only [sevenGapBernCoeff, sevenMassHeadBernCoeff_degree_bottom,
    growingHeadThetaBernCoeff_degree_bottom]

/-- One degree elevation is one Pascal step, including zero extension. -/
theorem sevenGapDeficit_degree_step (D m r : Nat)
    (hm : 1 ≤ m) (hD : sevenGapDegree m ≤ D) :
    (if r ≤ D + 1 then sevenGapBernCoeff (D + 1) m (D + 1 - r)
      else 0) =
    (if r ≤ D then sevenGapBernCoeff D m (D - r) else 0) +
      (if r = 0 then 0 else
        if r - 1 ≤ D then sevenGapBernCoeff D m (D - (r - 1)) else 0) := by
  cases r with
  | zero =>
      simp only [Nat.zero_le, if_pos, Nat.sub_zero, if_true, Int.add_zero]
      rw [sevenGapBernCoeff_top (D + 1) m hm (by omega)]
      rw [sevenGapBernCoeff_top D m hm hD]
  | succ r =>
      have hne : r + 1 ≠ 0 := by omega
      simp only [hne, if_false, Nat.add_sub_cancel]
      by_cases hr : r < D
      · have hr1D : r + 1 ≤ D := by omega
        have hrD : r ≤ D := by omega
        have hr1D1 : r + 1 ≤ D + 1 := by omega
        simp only [if_pos hr1D1, if_pos hr1D, if_pos hrD]
        have hsupport : 2 * m * m + 1 ≤ D := by simpa [sevenGapDegree] using hD
        have hs := sevenGapBernCoeff_degree_step D m (D - (r + 1)) hm
          hsupport
        have hk : D - (r + 1) + 1 = D - r := by omega
        have hk' : D + 1 - (r + 1) = D - r := by omega
        simpa [hk, hk'] using hs
      · by_cases heq : r = D
        · subst r
          simp only [Nat.le_refl, if_pos, Nat.sub_self, Int.zero_add]
          have hn : ¬ D + 1 ≤ D := by omega
          rw [if_neg hn]
          simpa only [Int.zero_add] using sevenGapBernCoeff_degree_bottom D m
        · have hlarge : D < r := by omega
          have hn0 : ¬ r + 1 ≤ D + 1 := by omega
          have hn1 : ¬ r + 1 ≤ D := by omega
          have hn2 : ¬ r ≤ D := by omega
          simp [hn0, hn1, hn2]

/-- Exact iteration of degree elevation. -/
theorem sevenGapDeficit_elevate (D m d r : Nat)
    (hm : 1 ≤ m) (hD : sevenGapDegree m ≤ D) :
    (if r ≤ D + d then sevenGapBernCoeff (D + d) m (D + d - r)
      else 0) =
      sevenPascalElevate d
        (fun s => if s ≤ D then sevenGapBernCoeff D m (D - s) else 0) r := by
  induction d generalizing r with
  | zero => simp [sevenPascalElevate]
  | succ d ih =>
      have hsupp : sevenGapDegree m ≤ D + d := by omega
      rw [show D + (d + 1) = (D + d) + 1 by omega]
      rw [sevenGapDeficit_degree_step (D + d) m r hm hsupp]
      cases r with
      | zero => simp only [if_pos, ih, sevenPascalElevate, Int.add_zero]
      | succ r =>
          have hne : r + 1 ≠ 0 := by omega
          simp only [hne, if_false, Nat.add_sub_cancel, ih, sevenPascalElevate]

private theorem choose_symm : ∀ n k : Nat, k ≤ n →
    PNPaths.choose n k = PNPaths.choose n (n - k)
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by omega
  | n + 1, 0, _ => by
      have hs : n + 1 - 0 = n + 1 := by omega
      rw [hs, choose_self]
      rfl
  | n + 1, k + 1, h => by
      by_cases heq : k = n
      · subst n
        rw [choose_self]
        have hs : k + 1 - (k + 1) = 0 := by omega
        rw [hs]
        rfl
      · have hk : k < n := by omega
        have hk1 : k + 1 ≤ n := by omega
        have hs : n + 1 - (k + 1) = n - k := by omega
        have hsucc : n - k = (n - k - 1) + 1 := by omega
        rw [hs, hsucc, PNPaths.choose, PNPaths.choose]
        have h0 := choose_symm n k (by omega)
        have h1 := choose_symm n (k + 1) hk1
        have harg : n - (k + 1) = n - k - 1 := by omega
        rw [harg] at h1
        rw [h0, h1, ← hsucc]
        exact Nat.add_comm _ _

private theorem thetaMono_top_deficit (D e r : Nat)
    (heD : e ≤ D) (hrD : r ≤ D) :
    thetaMonoBernCoeff D e (D - r) =
      Int.ofNat (PNPaths.choose (D - e) r) := by
  by_cases hr : r ≤ D - e
  · have he : e ≤ D - r := by omega
    have harg : D - r - e = D - e - r := by omega
    simp only [thetaMonoBernCoeff, if_pos he, harg]
    rw [choose_symm (D - e) r hr]
  · have hnot : ¬ e ≤ D - r := by omega
    have hz := choose_zero_of_lt (D - e) r (by omega)
    simp [thetaMonoBernCoeff, hnot, hz]

/-- Closed binomial presentation of the newly appended cell at the next
minimal degree.  Put `S=4m+2`; the five displayed binomial tops are exactly
`S+3,S+2,S+1,S,2m+4`. -/
theorem sevenGapCellBernCoeff_next_deficit
    (m r : Nat) (hm : 1 ≤ m) (hr : r ≤ sevenGapDegree (m + 1)) :
    let D := sevenGapDegree (m + 1)
    let S := 4 * m + 2
    sevenGapCellBernCoeff D m (D - r) =
      Int.ofNat (7 * m * m) *
          (if 2 ≤ r then Int.ofNat (PNPaths.choose (S + 1) (r - 2)) else 0) -
        Int.ofNat (m * m) *
          (Int.ofNat (PNPaths.choose (S + 3) r) +
            3 * Int.ofNat (PNPaths.choose (S + 2) r) +
            3 * Int.ofNat (PNPaths.choose (S + 1) r) +
            Int.ofNat (PNPaths.choose S r)) +
        Int.ofNat (8 * m * (m + 1)) *
          Int.ofNat (PNPaths.choose (2 * m + 4) r) := by
  dsimp only
  let D := sevenGapDegree (m + 1)
  let S := 4 * m + 2
  change sevenGapCellBernCoeff D m (D - r) =
    Int.ofNat (7 * m * m) *
        (if 2 ≤ r then Int.ofNat (PNPaths.choose (S + 1) (r - 2)) else 0) -
      Int.ofNat (m * m) *
        (Int.ofNat (PNPaths.choose (S + 3) r) +
          3 * Int.ofNat (PNPaths.choose (S + 2) r) +
          3 * Int.ofNat (PNPaths.choose (S + 1) r) +
          Int.ofNat (PNPaths.choose S r)) +
      Int.ofNat (8 * m * (m + 1)) *
        Int.ofNat (PNPaths.choose (2 * m + 4) r)
  have hD0 : 2 * m * m - 2 ≤ D := by
    dsimp only [D, sevenGapDegree]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hD1 : 2 * m * m - 1 ≤ D := by
    dsimp only [D, sevenGapDegree]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hD2 : 2 * m * m ≤ D := by
    dsimp only [D, sevenGapDegree]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hD3 : 2 * m * m + 1 ≤ D := by
    dsimp only [D, sevenGapDegree]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hDO : 2 * m * (m + 1) - 1 ≤ D := by
    dsimp only [D, sevenGapDegree]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  unfold sevenGapCellBernCoeff sevenMassCellBernCoeff thetaDiagBernCoeff
    thetaOffBernCoeff
  have hrD : r ≤ D := by simpa only [D] using hr
  rw [thetaMono_top_deficit D (2 * m * m - 2) r hD0 hrD]
  rw [thetaMono_top_deficit D (2 * m * m - 1) r hD1 hrD]
  rw [thetaMono_top_deficit D (2 * m * m) r hD2 hrD]
  rw [thetaMono_top_deficit D (2 * m * m + 1) r hD3 hrD]
  rw [thetaMono_top_deficit D (2 * m * (m + 1) - 1) r hDO hrD]
  have hDform : D = 2 * m * m + 4 * m + 3 := by
    dsimp only [D, sevenGapDegree]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hmm : 1 ≤ m * m := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hm hm
  have hbase : 2 ≤ 2 * m * m := by
    simpa only [Nat.mul_assoc, Nat.mul_one] using Nat.mul_le_mul_left 2 hmm
  have h0 : D - (2 * m * m - 2) = S + 3 := by
    rw [hDform]
    dsimp only [S]
    omega
  have h1 : D - (2 * m * m - 1) = S + 2 := by
    rw [hDform]
    dsimp only [S]
    omega
  have h2 : D - 2 * m * m = S + 1 := by
    rw [hDform]
    dsimp only [S]
    omega
  have h3 : D - (2 * m * m + 1) = S := by
    rw [hDform]
    dsimp only [S]
    omega
  have ho : D - (2 * m * (m + 1) - 1) = 2 * m + 4 := by
    rw [hDform]
    simp only [Nat.mul_add]
    omega
  rw [h0, h1, h2, h3, ho]
  -- The second difference of a binomial row is its two-step predecessor.
  have hpascal :
      (PNPaths.choose (S + 3) r : Int) -
          2 * (PNPaths.choose (S + 2) r : Int) +
          (PNPaths.choose (S + 1) r : Int) =
        (if 2 ≤ r then (PNPaths.choose (S + 1) (r - 2) : Int) else 0) := by
    cases r with
    | zero => simp [PNPaths.choose]
    | succ r =>
      cases r with
      | zero =>
          simp [PNPaths.choose]
          omega
      | succ r =>
        rw [if_pos (by omega)]
        simp only [Nat.add_sub_cancel, PNPaths.choose]
        push_cast
        omega
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
  rw [hpascal]
  dsimp only [S]
  omega

/-- Exact one-scale recurrence: elevate the old minimal row by `4m+2`, then
append the new mode `m`. -/
theorem sevenGapDeficit_succ (m r : Nat) (hm : 1 ≤ m) :
    r ≤ sevenGapDegree (m + 1) →
    sevenGapDeficit (m + 1) r =
      sevenPascalElevate (4 * m + 2) (sevenGapDeficit m) r +
        sevenGapCellBernCoeff (sevenGapDegree (m + 1)) m
          (sevenGapDegree (m + 1) - r) := by
  intro hr
  have hdeg : sevenGapDegree m + (4 * m + 2) =
      sevenGapDegree (m + 1) := by
    simp only [sevenGapDegree, Nat.mul_add, Nat.add_mul]
    omega
  have he := sevenGapDeficit_elevate (sevenGapDegree m) m
    (4 * m + 2) r hm (Nat.le_refl _)
  have happ := sevenGapBernCoeff_append (sevenGapDegree (m + 1)) m
    (sevenGapDegree (m + 1) - r) hm
  unfold sevenGapDeficit
  rw [if_pos hr, happ]
  rw [hdeg] at he
  rw [if_pos hr] at he
  rw [← he]

#print axioms sevenGapDegree
#print axioms sevenGapDeficit
#print axioms sevenPascalElevate
#print axioms sevenGapDeficit_degree_step
#print axioms sevenGapDeficit_elevate
#print axioms sevenGapCellBernCoeff_next_deficit
#print axioms sevenGapDeficit_succ

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence
