/-
Pascal coefficient row for the seven-unit theta gap.

At degree `D`, the mass part is the Bernstein lift of

  `7 (1-w)^2 * sum n^2 w^(2n^2-2)`.

Subtracting the already-public growing-head residual row gives an exact
integer coefficient carrier for the seven-unit gap.  This module establishes
the two recurrences needed by the symbolic bulk proof: ordinary degree
elevation and appending one physical theta cell.
-/

import YMGap.Continuum.HarmonicThetaPascalEvaluation

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicThetaPascalBridge

/-- Bernstein coefficient of one seven-unit integer-theta mass cell after
the common `w^2` factor has been removed. -/
def sevenMassCellBernCoeff (D n j : Nat) : Int :=
  Int.ofNat (7 * n * n) *
    (thetaMonoBernCoeff D (2 * n * n - 2) j -
      2 * thetaMonoBernCoeff D (2 * n * n - 1) j +
      thetaMonoBernCoeff D (2 * n * n) j)

/-- Sum of the first `c` seven-unit mass cells, beginning at mode one. -/
def sevenMassHeadBernCoeff (D j : Nat) : Nat → Int
  | 0 => 0
  | c + 1 =>
      sevenMassHeadBernCoeff D j c + sevenMassCellBernCoeff D (c + 1) j

/-- One coefficient of the exact seven-unit gap at arbitrary Bernstein
degree.  The physical head contains modes `1,...,m-1`. -/
def sevenGapBernCoeff (D m j : Nat) : Int :=
  sevenMassHeadBernCoeff D j (m - 1) - growingHeadThetaBernCoeff D m j

/-- The coefficient of the newly appended seven-unit cell. -/
def sevenGapCellBernCoeff (D n j : Nat) : Int :=
  sevenMassCellBernCoeff D n j -
    (thetaDiagBernCoeff D n j - thetaOffBernCoeff D n j)

private theorem thetaMonoBernCoeff_degree_step {D e k : Nat}
    (heD : e ≤ D) :
    thetaMonoBernCoeff (D + 1) e (k + 1) =
      thetaMonoBernCoeff D e k + thetaMonoBernCoeff D e (k + 1) := by
  by_cases hek : e ≤ k
  · have hek1 : e ≤ k + 1 := by omega
    have hDe : D + 1 - e = (D - e) + 1 := by omega
    have hke : k + 1 - e = (k - e) + 1 := by omega
    simp only [thetaMonoBernCoeff, if_pos hek, if_pos hek1]
    rw [hDe, hke, PNPaths.choose]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  · by_cases hek1 : e ≤ k + 1
    · have heq : e = k + 1 := by omega
      subst e
      simp [thetaMonoBernCoeff, PNPaths.choose, hek]
    · simp [thetaMonoBernCoeff, hek, hek1]

private theorem sevenMassCellBernCoeff_degree_step {D n k : Nat}
    (hD : 2 * n * n ≤ D) :
    sevenMassCellBernCoeff (D + 1) n (k + 1) =
      sevenMassCellBernCoeff D n k + sevenMassCellBernCoeff D n (k + 1) := by
  have h0 : 2 * n * n - 2 ≤ D := by omega
  have h1 : 2 * n * n - 1 ≤ D := by omega
  simp only [sevenMassCellBernCoeff,
    thetaMonoBernCoeff_degree_step h0,
    thetaMonoBernCoeff_degree_step h1,
    thetaMonoBernCoeff_degree_step hD,
    Int.mul_add]
  simp only [Int.sub_eq_add_neg, Int.neg_add, Int.mul_add, Int.mul_neg]
  ac_rfl

private theorem thetaDiagBernCoeff_degree_step {D n k : Nat}
    (hD : 2 * n * n + 1 ≤ D) :
    thetaDiagBernCoeff (D + 1) n (k + 1) =
      thetaDiagBernCoeff D n k + thetaDiagBernCoeff D n (k + 1) := by
  have h0 : 2 * n * n - 2 ≤ D := by omega
  have h1 : 2 * n * n - 1 ≤ D := by omega
  have h2 : 2 * n * n ≤ D := by omega
  simp only [thetaDiagBernCoeff,
    thetaMonoBernCoeff_degree_step h0,
    thetaMonoBernCoeff_degree_step h1,
    thetaMonoBernCoeff_degree_step h2,
    thetaMonoBernCoeff_degree_step hD,
    Int.mul_add]
  omega

private theorem thetaOffBernCoeff_degree_step {D n k : Nat}
    (hD : 2 * n * (n + 1) - 1 ≤ D) :
    thetaOffBernCoeff (D + 1) n (k + 1) =
      thetaOffBernCoeff D n k + thetaOffBernCoeff D n (k + 1) := by
  simp only [thetaOffBernCoeff, thetaMonoBernCoeff_degree_step hD,
    Int.mul_add]

private theorem cumulativeThetaBernCoeff_degree_step
    (D n k c : Nat)
    (hD : 2 * (n + c) * (n + c) + 1 ≤ D) :
    cumulativeThetaBernCoeff (D + 1) n (k + 1) c =
      cumulativeThetaBernCoeff D n k c +
        cumulativeThetaBernCoeff D n (k + 1) c := by
  induction c generalizing n with
  | zero =>
      simp only [cumulativeThetaBernCoeff]
      exact thetaDiagBernCoeff_degree_step (by simpa using hD)
  | succ c ih =>
      simp only [cumulativeThetaBernCoeff]
      have hn : 2 * n * n + 1 ≤ D := by
        have hle : n ≤ n + (c + 1) := by omega
        have hsq := Nat.mul_le_mul hle hle
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      have hoff : 2 * n * (n + 1) - 1 ≤ D := by
        have h0 : n ≤ n + (c + 1) := by omega
        have h1 : n + 1 ≤ n + (c + 1) := by omega
        have hp := Nat.mul_le_mul h0 h1
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      rw [thetaDiagBernCoeff_degree_step hn,
        thetaOffBernCoeff_degree_step hoff]
      rw [ih (n + 1) (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hD)]
      omega

private theorem growingHeadThetaBernCoeff_degree_step
    (D m k : Nat) (hm : 1 ≤ m) (hD : 2 * m * m + 1 ≤ D) :
    growingHeadThetaBernCoeff (D + 1) m (k + 1) =
      growingHeadThetaBernCoeff D m k +
        growingHeadThetaBernCoeff D m (k + 1) := by
  unfold growingHeadThetaBernCoeff
  have hc : 2 * (1 + (m - 1)) * (1 + (m - 1)) + 1 ≤ D := by
    have hend : 1 + (m - 1) = m := by omega
    rw [hend]
    exact hD
  rw [cumulativeThetaBernCoeff_degree_step D 1 k (m - 1) hc]
  rw [thetaDiagBernCoeff_degree_step hD]
  omega

private theorem sevenMassHeadBernCoeff_degree_step
    (D m k : Nat) (hD : 2 * m * m ≤ D) :
    sevenMassHeadBernCoeff (D + 1) (k + 1) m =
      sevenMassHeadBernCoeff D k m +
        sevenMassHeadBernCoeff D (k + 1) m := by
  induction m with
  | zero => simp [sevenMassHeadBernCoeff]
  | succ m ih =>
      simp only [sevenMassHeadBernCoeff]
      have hm : 2 * m * m ≤ D := by
        have hle : m ≤ m + 1 := by omega
        have hsq := Nat.mul_le_mul hle hle
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      rw [ih hm, sevenMassCellBernCoeff_degree_step hD]
      omega

/-- One Pascal degree elevation replaces the seven-gap coefficient by the
sum of its two parents. -/
theorem sevenGapBernCoeff_degree_step
    (D m k : Nat) (hm0 : 1 ≤ m) (hD : 2 * m * m + 1 ≤ D) :
    sevenGapBernCoeff (D + 1) m (k + 1) =
      sevenGapBernCoeff D m k + sevenGapBernCoeff D m (k + 1) := by
  unfold sevenGapBernCoeff
  have hm : 2 * (m - 1) * (m - 1) ≤ D := by
    have hle : m - 1 ≤ m := Nat.sub_le m 1
    have hsq := Nat.mul_le_mul hle hle
    simp only [Nat.mul_assoc] at hD ⊢
    omega
  rw [sevenMassHeadBernCoeff_degree_step D (m - 1) k hm]
  rw [growingHeadThetaBernCoeff_degree_step D m k hm0 hD]
  omega

private theorem cumulative_append (D n j c : Nat) :
    cumulativeThetaBernCoeff D n j (c + 1) =
      cumulativeThetaBernCoeff D n j c - thetaOffBernCoeff D (n + c) j +
        thetaDiagBernCoeff D (n + c + 1) j := by
  induction c generalizing n with
  | zero => simp [cumulativeThetaBernCoeff]
  | succ c ih =>
      change
        thetaDiagBernCoeff D n j - thetaOffBernCoeff D n j +
            cumulativeThetaBernCoeff D (n + 1) j (c + 1) =
          (thetaDiagBernCoeff D n j - thetaOffBernCoeff D n j +
              cumulativeThetaBernCoeff D (n + 1) j c) -
            thetaOffBernCoeff D (n + (c + 1)) j +
              thetaDiagBernCoeff D (n + (c + 1) + 1) j
      rw [ih (n + 1)]
      have hnc : n + 1 + c = n + (c + 1) := by omega
      rw [hnc]
      simp only [Int.sub_eq_add_neg]
      ac_rfl

private theorem growingHeadThetaBernCoeff_append
    (D m j : Nat) (hm : 1 ≤ m) :
    growingHeadThetaBernCoeff D (m + 1) j =
      growingHeadThetaBernCoeff D m j +
        (thetaDiagBernCoeff D m j - thetaOffBernCoeff D m j) := by
  unfold growingHeadThetaBernCoeff
  have hpred : m + 1 - 1 = m := by omega
  have hm1 : m - 1 + 1 = m := by omega
  have hone : 1 + (m - 1) = m := by omega
  have hsucc : 1 + (m - 1) + 1 = m + 1 := by omega
  rw [hpred]
  have happ := cumulative_append D 1 j (m - 1)
  rw [hm1, hone] at happ
  rw [happ]
  omega

/-- Appending one mode adds exactly its seven-unit cell coefficient. -/
theorem sevenGapBernCoeff_append
    (D m j : Nat) (hm : 1 ≤ m) :
    sevenGapBernCoeff D (m + 1) j =
      sevenGapBernCoeff D m j + sevenGapCellBernCoeff D m j := by
  unfold sevenGapBernCoeff sevenGapCellBernCoeff
  have hpred : m + 1 - 1 = m := by omega
  have hm1 : m - 1 + 1 = m := by omega
  rw [hpred]
  rw [show sevenMassHeadBernCoeff D j m =
      sevenMassHeadBernCoeff D j (m - 1) +
        sevenMassCellBernCoeff D m j by
    rw [← hm1]
    rfl]
  rw [growingHeadThetaBernCoeff_append D m j hm]
  omega

#print axioms sevenMassCellBernCoeff
#print axioms sevenMassHeadBernCoeff
#print axioms sevenGapBernCoeff
#print axioms sevenGapCellBernCoeff
#print axioms sevenGapBernCoeff_degree_step
#print axioms sevenGapBernCoeff_append

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow
