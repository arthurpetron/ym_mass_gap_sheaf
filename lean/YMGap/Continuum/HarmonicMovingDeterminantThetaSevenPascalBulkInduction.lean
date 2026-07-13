/-
The binomial clearing and induction interface for the seven-coordinate
boundary certificate.

The first step below is deliberately independent of the later gap-row
induction: it identifies the manifestly positive polynomial certificate with
the exact seven-term signed binomial convolution.  Thus no sign information
is lost in the passage from the polynomial calculation back to coefficients.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBulkBoundary

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBulkInduction

open YMGap.Continuum
open YMGap.Continuum.ThetaResidualPascalTelescope
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBulkBoundary
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPrefix
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCore
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCoreBoundaryBridge

/-- Product `(k+1) ... (k+s)` used to clear an `s`-step binomial ratio. -/
def bulkRisingFirst (k : Int) : Nat → Int
  | 0 => 1
  | s + 1 => bulkRisingFirst k s * (k + ((s + 1 : Nat) : Int))

/-- Repeated adjacent-binomial identity in subtraction-free, integer-cast
form. -/
theorem bulk_choose_shift_cross (d k s : Nat) (hks : k + s ≤ d) :
    bulkRisingFirst (k : Int) s * (PNPaths.choose d (k + s) : Int) =
      bulkFalling ((d : Int) - (k : Int)) s *
        (PNPaths.choose d k : Int) := by
  induction s with
  | zero => simp [bulkRisingFirst, bulkFalling]
  | succ s ih =>
      have hlt : k + s < d := by omega
      have hadjNat := choose_adjacent_cross d (k + s) hlt
      have hadj := congrArg Int.ofNat hadjNat
      have hcastSub : (((d - (k + s) : Nat) : Int)) =
          (d : Int) - (k + s : Nat) := by omega
      have hadj' :
          ((k : Int) + (s : Int) + 1) *
              (PNPaths.choose d (k + s + 1) : Int) =
            ((d : Int) - (k + s : Nat)) *
              (PNPaths.choose d (k + s) : Int) := by
        rw [← hcastSub]
        simpa only [Int.ofNat_eq_natCast, Int.natCast_mul,
          Int.natCast_add, Int.natCast_one] using hadj
      have hsub :
          (d : Int) - ((k : Int) + (s : Int)) =
            ((d : Int) - (k : Int)) - (s : Int) := by omega
      simp only [bulkRisingFirst, bulkFalling]
      rw [show (k : Int) + ((s + 1 : Nat) : Int) =
        ((k + s + 1 : Nat) : Int) by omega]
      calc
        bulkRisingFirst (k : Int) s * (k + s + 1 : Int) *
              (PNPaths.choose d (k + s + 1) : Int) =
            bulkRisingFirst (k : Int) s *
              ((k + s + 1 : Int) *
                (PNPaths.choose d (k + s + 1) : Int)) := by ac_rfl
        _ = bulkRisingFirst (k : Int) s *
              (((d : Int) - (k + s : Nat)) *
                (PNPaths.choose d (k + s) : Int)) := by rw [hadj']
        _ = (bulkRisingFirst (k : Int) s *
              (PNPaths.choose d (k + s) : Int)) *
                (((d : Int) - (k : Int)) - (s : Int)) := by
              rw [show ((d : Int) - (k + s : Nat)) =
                (d : Int) - ((k : Int) + (s : Int)) by push_cast; rfl, hsub]
              ac_rfl
        _ = (bulkFalling ((d : Int) - (k : Int)) s *
              (PNPaths.choose d k : Int)) *
                (((d : Int) - (k : Int)) - (s : Int)) := by rw [ih (by omega)]
        _ = (bulkFalling ((d : Int) - (k : Int)) s *
              (((d : Int) - (k : Int)) - (s : Int))) *
                (PNPaths.choose d k : Int) := by ac_rfl

private theorem bulk_choose_zero_of_lt : ∀ n r : Nat,
    n < r → PNPaths.choose n r = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, r + 1, h => by
      simp only [PNPaths.choose]
      rw [bulk_choose_zero_of_lt n r (by omega)]
      rw [bulk_choose_zero_of_lt n (r + 1) (by omega)]

/-- Once the length exceeds the natural starting value, the falling product
contains an exact zero factor. -/
theorem bulkFalling_natCast_zero_of_lt (q s : Nat) (hqs : q < s) :
    bulkFalling (q : Int) s = 0 := by
  induction s with
  | zero => omega
  | succ s ih =>
      simp only [bulkFalling]
      by_cases hq : q = s
      · subst q
        have hz : (s : Int) - (s : Int) = 0 := by omega
        rw [hz, Int.mul_zero]
      · have hlt : q < s := by omega
        rw [ih hlt, Int.zero_mul]

/-- The cleared shift identity remains valid after the shifted binomial has
left its support: both sides then vanish exactly. -/
theorem bulk_choose_shift_cross_of_le (d k s : Nat) (hk : k ≤ d) :
    bulkRisingFirst (k : Int) s * (PNPaths.choose d (k + s) : Int) =
      bulkFalling ((d : Int) - (k : Int)) s *
        (PNPaths.choose d k : Int) := by
  by_cases hks : k + s ≤ d
  · exact bulk_choose_shift_cross d k s hks
  · have hzC := bulk_choose_zero_of_lt d (k + s) (by omega)
    have hq : d - k < s := by omega
    have hzF := bulkFalling_natCast_zero_of_lt (d - k) s hq
    have hcast : ((d - k : Nat) : Int) = (d : Int) - (k : Int) := by omega
    rw [hzC, Int.natCast_zero, Int.mul_zero, ← hcast, hzF, Int.zero_mul]

private theorem cases_le_six {s : Nat} (hs : s ≤ 6) :
    s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by
  omega

/-- The first `s` factors and the remaining tail partition the common
six-factor clearing product. -/
theorem bulkRising_split_six (k : Int) (s : Nat) (hs : s ≤ 6) :
    bulkRisingFirst k s * bulkRisingTailSix k s =
      bulkRisingTailSix k 0 := by
  have e1 : k + (((0 + 1 : Nat) : Int)) = k + 1 := by omega
  have e2 : k + (((1 + 1 : Nat) : Int)) = k + 2 := by omega
  have e3 : k + (((2 + 1 : Nat) : Int)) = k + 3 := by omega
  have e4 : k + (((3 + 1 : Nat) : Int)) = k + 4 := by omega
  have e5 : k + (((4 + 1 : Nat) : Int)) = k + 5 := by omega
  have e6 : k + (((5 + 1 : Nat) : Int)) = k + 6 := by omega
  rcases cases_le_six hs with h | h | h | h | h | h | h <;>
    subst s <;> simp only [bulkRisingFirst, bulkRisingTailSix,
      e1, e2, e3, e4, e5, e6, Int.one_mul] <;>
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.one_mul]

/-- One binomial summand after clearing the common six-factor denominator. -/
theorem bulk_clear_choose_term (d k s : Nat) (w : Int)
    (hs : s ≤ 6) (hks : k + s ≤ d) :
    bulkRisingTailSix (k : Int) 0 *
        ((PNPaths.choose d (k + s) : Int) * w) =
      (PNPaths.choose d k : Int) *
        (w * bulkFalling ((d : Int) - (k : Int)) s *
          bulkRisingTailSix (k : Int) s) := by
  calc
    bulkRisingTailSix (k : Int) 0 *
          ((PNPaths.choose d (k + s) : Int) * w) =
        (bulkRisingFirst (k : Int) s * bulkRisingTailSix (k : Int) s) *
          ((PNPaths.choose d (k + s) : Int) * w) := by
            rw [bulkRising_split_six (k : Int) s hs]
    _ = (bulkRisingFirst (k : Int) s *
          (PNPaths.choose d (k + s) : Int)) *
            (w * bulkRisingTailSix (k : Int) s) := by ac_rfl
    _ = (bulkFalling ((d : Int) - (k : Int)) s *
          (PNPaths.choose d k : Int)) *
            (w * bulkRisingTailSix (k : Int) s) := by
              rw [bulk_choose_shift_cross d k s hks]
    _ = (PNPaths.choose d k : Int) *
          (w * bulkFalling ((d : Int) - (k : Int)) s *
            bulkRisingTailSix (k : Int) s) := by ac_rfl

/-- Support-complete version of `bulk_clear_choose_term`. -/
theorem bulk_clear_choose_term_of_le (d k s : Nat) (w : Int)
    (hs : s ≤ 6) (hk : k ≤ d) :
    bulkRisingTailSix (k : Int) 0 *
        ((PNPaths.choose d (k + s) : Int) * w) =
      (PNPaths.choose d k : Int) *
        (w * bulkFalling ((d : Int) - (k : Int)) s *
          bulkRisingTailSix (k : Int) s) := by
  calc
    bulkRisingTailSix (k : Int) 0 *
          ((PNPaths.choose d (k + s) : Int) * w) =
        (bulkRisingFirst (k : Int) s * bulkRisingTailSix (k : Int) s) *
          ((PNPaths.choose d (k + s) : Int) * w) := by
            rw [bulkRising_split_six (k : Int) s hs]
    _ = (bulkRisingFirst (k : Int) s *
          (PNPaths.choose d (k + s) : Int)) *
            (w * bulkRisingTailSix (k : Int) s) := by ac_rfl
    _ = (bulkFalling ((d : Int) - (k : Int)) s *
          (PNPaths.choose d k : Int)) *
            (w * bulkRisingTailSix (k : Int) s) := by
              rw [bulk_choose_shift_cross_of_le d k s hk]
    _ = (PNPaths.choose d k : Int) *
          (w * bulkFalling ((d : Int) - (k : Int)) s *
            bulkRisingTailSix (k : Int) s) := by ac_rfl

/-- The seven signed binomial weights at output deficit `r`. -/
def sevenBulkBoundaryConvolution (m r : Nat) : Int :=
  let d := 4 * m + 2
  (PNPaths.choose d r : Int) * sevenBulkBoundaryWeight 0 (m : Int) +
  ((PNPaths.choose d (r - 1) : Int) * sevenBulkBoundaryWeight 1 (m : Int) +
  ((PNPaths.choose d (r - 2) : Int) * sevenBulkBoundaryWeight 2 (m : Int) +
  ((PNPaths.choose d (r - 3) : Int) * sevenBulkBoundaryWeight 3 (m : Int) +
  ((PNPaths.choose d (r - 4) : Int) * sevenBulkBoundaryWeight 4 (m : Int) +
  ((PNPaths.choose d (r - 5) : Int) * sevenBulkBoundaryWeight 5 (m : Int) +
   (PNPaths.choose d (r - 6) : Int) * sevenBulkBoundaryWeight 6 (m : Int))))))

/-- Exact identification of the seven-term binomial convolution with the
cleared two-variable polynomial. -/
theorem sevenBulkBoundaryConvolution_cleared (m k : Nat)
    (hk : k ≤ 4 * m + 2) :
    bulkRisingTailSix (k : Int) 0 *
        sevenBulkBoundaryConvolution m (k + 6) =
      (PNPaths.choose (4 * m + 2) k : Int) *
        sevenBulkBoundaryCleared (m : Int) (k : Int) := by
  have h0 := bulk_clear_choose_term_of_le (4 * m + 2) k 6
    (sevenBulkBoundaryWeight 0 (m : Int)) (by omega) hk
  have h1 := bulk_clear_choose_term_of_le (4 * m + 2) k 5
    (sevenBulkBoundaryWeight 1 (m : Int)) (by omega) hk
  have h2 := bulk_clear_choose_term_of_le (4 * m + 2) k 4
    (sevenBulkBoundaryWeight 2 (m : Int)) (by omega) hk
  have h3 := bulk_clear_choose_term_of_le (4 * m + 2) k 3
    (sevenBulkBoundaryWeight 3 (m : Int)) (by omega) hk
  have h4 := bulk_clear_choose_term_of_le (4 * m + 2) k 2
    (sevenBulkBoundaryWeight 4 (m : Int)) (by omega) hk
  have h5 := bulk_clear_choose_term_of_le (4 * m + 2) k 1
    (sevenBulkBoundaryWeight 5 (m : Int)) (by omega) hk
  have h6 := bulk_clear_choose_term_of_le (4 * m + 2) k 0
    (sevenBulkBoundaryWeight 6 (m : Int)) (by omega) hk
  have hs1 : k + 6 - 1 = k + 5 := by omega
  have hs2 : k + 6 - 2 = k + 4 := by omega
  have hs3 : k + 6 - 3 = k + 3 := by omega
  have hs4 : k + 6 - 4 = k + 2 := by omega
  have hs5 : k + 6 - 5 = k + 1 := by omega
  have hs6 : k + 6 - 6 = k := by omega
  unfold sevenBulkBoundaryConvolution
  rw [hs1, hs2, hs3, hs4, hs5, hs6]
  simp only [Int.mul_add]
  rw [h0, h1, h2, h3, h4, h5]
  have h6' :
      bulkRisingTailSix (k : Int) 0 *
          ((PNPaths.choose (4 * m + 2) k : Int) *
            sevenBulkBoundaryWeight 6 (m : Int)) =
        (PNPaths.choose (4 * m + 2) k : Int) *
          (sevenBulkBoundaryWeight 6 (m : Int) *
            bulkFalling (((4 * m + 2 : Nat) : Int) - (k : Int)) 0 *
              bulkRisingTailSix (k : Int) 0) := by
    simpa only [Nat.add_zero] using h6
  rw [h6']
  unfold sevenBulkBoundaryCleared bulkBoundaryTerm
  push_cast
  have hbase : 4 * (m : Int) + 1 + 1 = 4 * (m : Int) + 2 := by omega
  rw [hbase]
  simp only [Int.mul_add]
  repeat rw [← Int.mul_add]

/-- In the full-overlap range, the exact signed binomial convolution is
nonnegative.  The common clearing factor is strictly positive and is removed
constructively after applying the polynomial certificate. -/
theorem sevenBulkBoundaryConvolution_nonnegative_main (m k : Nat)
    (hm : 3 ≤ m) (hk : 1 ≤ k) (hmax : k + 6 ≤ 4 * m + 2) :
    0 ≤ sevenBulkBoundaryConvolution m (k + 6) := by
  have hkp : (0 : Int) < (k : Int) + 1 := by omega
  have hk2 : (0 : Int) < (k : Int) + 2 := by omega
  have hk3 : (0 : Int) < (k : Int) + 3 := by omega
  have hk4 : (0 : Int) < (k : Int) + 4 := by omega
  have hk5 : (0 : Int) < (k : Int) + 5 := by omega
  have hk6 : (0 : Int) < (k : Int) + 6 := by omega
  have hR : (0 : Int) < bulkRisingTailSix (k : Int) 0 := by
    simp only [bulkRisingTailSix]
    exact Int.mul_pos
      (Int.mul_pos
        (Int.mul_pos
          (Int.mul_pos (Int.mul_pos hkp hk2) hk3) hk4)
        hk5)
      hk6
  have hchoose : (0 : Int) ≤ (PNPaths.choose (4 * m + 2) k : Int) :=
    Int.natCast_nonneg _
  have hpoly := sevenBulkBoundaryCleared_nonnegative m k hm hk
  have hscaled :
      (0 : Int) ≤ bulkRisingTailSix (k : Int) 0 *
        sevenBulkBoundaryConvolution m (k + 6) := by
    rw [sevenBulkBoundaryConvolution_cleared m k (by omega)]
    exact Int.mul_nonneg hchoose hpoly
  have hzero :
      bulkRisingTailSix (k : Int) 0 * 0 ≤
        bulkRisingTailSix (k : Int) 0 *
          sevenBulkBoundaryConvolution m (k + 6) := by
    simpa using hscaled
  exact Int.le_of_mul_le_mul_left hzero hR

/-- Support-complete convolution sign, including the six right endpoints. -/
theorem sevenBulkBoundaryConvolution_nonnegative_through_endpoint (m k : Nat)
    (hm : 3 ≤ m) (hk : 1 ≤ k) (hkD : k ≤ 4 * m + 2) :
    0 ≤ sevenBulkBoundaryConvolution m (k + 6) := by
  have hkp : (0 : Int) < (k : Int) + 1 := by omega
  have hk2 : (0 : Int) < (k : Int) + 2 := by omega
  have hk3 : (0 : Int) < (k : Int) + 3 := by omega
  have hk4 : (0 : Int) < (k : Int) + 4 := by omega
  have hk5 : (0 : Int) < (k : Int) + 5 := by omega
  have hk6 : (0 : Int) < (k : Int) + 6 := by omega
  have hR : (0 : Int) < bulkRisingTailSix (k : Int) 0 := by
    simp only [bulkRisingTailSix]
    exact Int.mul_pos
      (Int.mul_pos
        (Int.mul_pos
          (Int.mul_pos (Int.mul_pos hkp hk2) hk3) hk4)
        hk5)
      hk6
  have hchoose : (0 : Int) ≤ (PNPaths.choose (4 * m + 2) k : Int) :=
    Int.natCast_nonneg _
  have hpoly := sevenBulkBoundaryCleared_nonnegative m k hm hk
  have hscaled :
      (0 : Int) ≤ bulkRisingTailSix (k : Int) 0 *
        sevenBulkBoundaryConvolution m (k + 6) := by
    rw [sevenBulkBoundaryConvolution_cleared m k hkD]
    exact Int.mul_nonneg hchoose hpoly
  have hzero :
      bulkRisingTailSix (k : Int) 0 * 0 ≤
        bulkRisingTailSix (k : Int) 0 *
          sevenBulkBoundaryConvolution m (k + 6) := by
    simpa using hscaled
  exact Int.le_of_mul_le_mul_left hzero hR

/-- The same binomial convolution with the exact closed boundary formulas. -/
def sevenBoundaryFormulaConvolution (m r : Nat) : Int :=
  let d := 4 * m + 2
  (PNPaths.choose d r : Int) * sevenBoundaryScaledFormula 0 (m : Int) +
  ((PNPaths.choose d (r - 1) : Int) * sevenBoundaryScaledFormula 1 (m : Int) +
  ((PNPaths.choose d (r - 2) : Int) * sevenBoundaryScaledFormula 2 (m : Int) +
  ((PNPaths.choose d (r - 3) : Int) * sevenBoundaryScaledFormula 3 (m : Int) +
  ((PNPaths.choose d (r - 4) : Int) * sevenBoundaryScaledFormula 4 (m : Int) +
  ((PNPaths.choose d (r - 5) : Int) * sevenBoundaryScaledFormula 5 (m : Int) +
   (PNPaths.choose d (r - 6) : Int) * sevenBoundaryScaledFormula 6 (m : Int))))))

def sevenBoundaryAdjustmentConvolution (m r : Nat) : Int :=
  let d := 4 * m + 2
  (PNPaths.choose d r : Int) * sevenBulkBoundaryAdjustment 0 (m : Int) +
  ((PNPaths.choose d (r - 1) : Int) * sevenBulkBoundaryAdjustment 1 (m : Int) +
  ((PNPaths.choose d (r - 2) : Int) * sevenBulkBoundaryAdjustment 2 (m : Int) +
  ((PNPaths.choose d (r - 3) : Int) * sevenBulkBoundaryAdjustment 3 (m : Int) +
  ((PNPaths.choose d (r - 4) : Int) * sevenBulkBoundaryAdjustment 4 (m : Int) +
  ((PNPaths.choose d (r - 5) : Int) * sevenBulkBoundaryAdjustment 5 (m : Int) +
   (PNPaths.choose d (r - 6) : Int) * sevenBulkBoundaryAdjustment 6 (m : Int))))))

theorem sevenBoundaryFormulaConvolution_split (m r : Nat) :
    sevenBoundaryFormulaConvolution m r =
      sevenBulkBoundaryConvolution m r +
        sevenBoundaryAdjustmentConvolution m r := by
  unfold sevenBoundaryFormulaConvolution sevenBulkBoundaryConvolution
    sevenBoundaryAdjustmentConvolution
  rw [sevenBoundaryScaledFormula_eq_weight_adjustment 0 (m : Int) (by omega)]
  rw [sevenBoundaryScaledFormula_eq_weight_adjustment 1 (m : Int) (by omega)]
  rw [sevenBoundaryScaledFormula_eq_weight_adjustment 2 (m : Int) (by omega)]
  rw [sevenBoundaryScaledFormula_eq_weight_adjustment 3 (m : Int) (by omega)]
  rw [sevenBoundaryScaledFormula_eq_weight_adjustment 4 (m : Int) (by omega)]
  rw [sevenBoundaryScaledFormula_eq_weight_adjustment 5 (m : Int) (by omega)]
  rw [sevenBoundaryScaledFormula_eq_weight_adjustment 6 (m : Int) (by omega)]
  simp only [Int.mul_add]
  ac_rfl

/-- The actual newly appended cell, in deficit coordinates. -/
def sevenActualCell (m r : Nat) : Int :=
  let D := sevenGapDegree (m + 1)
  sevenGapCellBernCoeff D m (D - r)

def sevenBoundaryPayment (m r : Nat) : Int :=
  sevenBoundaryFormulaConvolution m r + 5670 * sevenActualCell m r

private theorem choose_succ_at_pos (n r : Nat) (hr : 1 ≤ r) :
    PNPaths.choose (n + 1) r =
      PNPaths.choose n (r - 1) + PNPaths.choose n r := by
  cases r with
  | zero => omega
  | succ r => rfl

/-- Three Pascal expansions of the four shifted tops in the appended cell. -/
theorem choose_three_top_bundle (d r : Nat) (hr : 3 ≤ r) :
    PNPaths.choose (d + 3) r + 3 * PNPaths.choose (d + 2) r +
        3 * PNPaths.choose (d + 1) r + PNPaths.choose d r =
      8 * PNPaths.choose d r + 12 * PNPaths.choose d (r - 1) +
        6 * PNPaths.choose d (r - 2) + PNPaths.choose d (r - 3) := by
  have h3 := choose_succ_at_pos (d + 2) r (by omega)
  have h2r := choose_succ_at_pos (d + 1) r (by omega)
  have h2p := choose_succ_at_pos (d + 1) (r - 1) (by omega)
  have h1r := choose_succ_at_pos d r (by omega)
  have h1p := choose_succ_at_pos d (r - 1) (by omega)
  have h1q := choose_succ_at_pos d (r - 2) (by omega)
  have hd3 : d + 2 + 1 = d + 3 := by omega
  have hd2 : d + 1 + 1 = d + 2 := by omega
  have hr2 : r - 1 - 1 = r - 2 := by omega
  have hr3 : r - 2 - 1 = r - 3 := by omega
  rw [hd3] at h3
  rw [hd2] at h2r h2p
  rw [hr2] at h2p h1p
  rw [hr3] at h1q
  omega

theorem choose_one_top_shift_two (d r : Nat) (hr : 3 ≤ r) :
    PNPaths.choose (d + 1) (r - 2) =
      PNPaths.choose d (r - 3) + PNPaths.choose d (r - 2) := by
  exact choose_succ_at_pos d (r - 2) (by omega)

/-- Exact cancellation of the four adjustment coordinates against the
nonpositive portion of the appended cell. -/
theorem sevenBoundaryPayment_eq_weight (m r : Nat)
    (hm : 1 ≤ m) (hr : 7 ≤ r) (hrD : r ≤ sevenGapDegree (m + 1)) :
    sevenBoundaryPayment m r =
      sevenBulkBoundaryConvolution m r +
        5670 * (8 * m * (m + 1) : Nat) *
          (PNPaths.choose (2 * m + 4) r : Int) := by
  rw [sevenBoundaryPayment, sevenBoundaryFormulaConvolution_split]
  have hcell := sevenGapCellBernCoeff_next_deficit m r hm hrD
  have hcell' : sevenActualCell m r =
      (7 * m * m : Nat) *
          (PNPaths.choose (4 * m + 3) (r - 2) : Int) -
        (m * m : Nat) *
          ((PNPaths.choose (4 * m + 5) r : Int) +
            3 * (PNPaths.choose (4 * m + 4) r : Int) +
            3 * (PNPaths.choose (4 * m + 3) r : Int) +
            (PNPaths.choose (4 * m + 2) r : Int)) +
        (8 * m * (m + 1) : Nat) *
          (PNPaths.choose (2 * m + 4) r : Int) := by
    unfold sevenActualCell
    simpa only [if_pos (show 2 ≤ r by omega), Int.ofNat_eq_natCast,
      Int.natCast_mul, Int.natCast_add] using hcell
  rw [hcell']
  have hbundleNat := choose_three_top_bundle (4 * m + 2) r (by omega)
  have hbundle := congrArg Int.ofNat hbundleNat
  have hbundle' :
      (PNPaths.choose (4 * m + 5) r : Int) +
          3 * (PNPaths.choose (4 * m + 4) r : Int) +
          3 * (PNPaths.choose (4 * m + 3) r : Int) +
          (PNPaths.choose (4 * m + 2) r : Int) =
        8 * (PNPaths.choose (4 * m + 2) r : Int) +
          12 * (PNPaths.choose (4 * m + 2) (r - 1) : Int) +
          6 * (PNPaths.choose (4 * m + 2) (r - 2) : Int) +
          (PNPaths.choose (4 * m + 2) (r - 3) : Int) := by
    simpa only [Int.ofNat_eq_natCast, Int.natCast_add,
      Int.natCast_mul] using hbundle
  have hshiftNat := choose_one_top_shift_two (4 * m + 2) r (by omega)
  have hshift := congrArg Int.ofNat hshiftNat
  have hshift' :
      (PNPaths.choose (4 * m + 3) (r - 2) : Int) =
        (PNPaths.choose (4 * m + 2) (r - 3) : Int) +
          (PNPaths.choose (4 * m + 2) (r - 2) : Int) := by
    simpa only [Int.ofNat_eq_natCast, Int.natCast_add] using hshift
  rw [hbundle', hshift']
  unfold sevenBoundaryAdjustmentConvolution sevenBulkBoundaryAdjustment
  push_cast
  simp only [Int.mul_add, Int.sub_eq_add_neg, Int.neg_mul, Int.mul_neg,
    Int.mul_zero, Int.add_zero, Int.mul_assoc, Int.mul_comm,
    Int.mul_left_comm]
  have hc0 :
      (m : Int) * ((m : Int) *
          (45360 * (PNPaths.choose (4 * m + 2) r : Int))) =
        (m : Int) * ((m : Int) *
          (8 * (5670 * (PNPaths.choose (4 * m + 2) r : Int)))) := by
    rw [show (45360 : Int) = 8 * 5670 by decide]
    simp only [Int.mul_assoc]
  have hc1 :
      (m : Int) * ((m : Int) *
          (68040 * (PNPaths.choose (4 * m + 2) (r - 1) : Int))) =
        (m : Int) * ((m : Int) *
          (12 * (5670 * (PNPaths.choose (4 * m + 2) (r - 1) : Int)))) := by
    rw [show (68040 : Int) = 12 * 5670 by decide]
    simp only [Int.mul_assoc]
  have hc2 :
      (m : Int) * ((m : Int) *
          (7 * (5670 * (PNPaths.choose (4 * m + 2) (r - 2) : Int)))) =
        (m : Int) * ((m : Int) *
            (6 * (5670 * (PNPaths.choose (4 * m + 2) (r - 2) : Int)))) +
          (m : Int) * ((m : Int) *
            (5670 * (PNPaths.choose (4 * m + 2) (r - 2) : Int))) := by
    rw [show (7 : Int) = 6 + 1 by decide]
    simp only [Int.add_mul, Int.one_mul, Int.mul_add]
  have hc3 :
      (m : Int) * ((m : Int) *
          (7 * (5670 * (PNPaths.choose (4 * m + 2) (r - 3) : Int)))) =
        (m : Int) * ((m : Int) *
            (5670 * (PNPaths.choose (4 * m + 2) (r - 3) : Int))) +
          (m : Int) * ((m : Int) *
            (6 * (5670 * (PNPaths.choose (4 * m + 2) (r - 3) : Int)))) := by
    rw [show (7 : Int) = 1 + 6 by decide]
    simp only [Int.add_mul, Int.one_mul, Int.mul_add]
  have hc4 :
      (m : Int) * ((m : Int) *
          (34020 * (PNPaths.choose (4 * m + 2) (r - 3) : Int))) =
        (m : Int) * ((m : Int) *
          (6 * (5670 * (PNPaths.choose (4 * m + 2) (r - 3) : Int)))) := by
    rw [show (34020 : Int) = 6 * 5670 by decide]
    simp only [Int.mul_assoc]
  rw [hc0, hc1, hc2, hc3, hc4]
  omega

/-- The complete boundary payment is nonnegative in the full-overlap bulk
range. -/
theorem sevenBoundaryPayment_nonnegative_main (m k : Nat)
    (hm : 3 ≤ m) (hk : 1 ≤ k) (hmax : k + 6 ≤ 4 * m + 2) :
    0 ≤ sevenBoundaryPayment m (k + 6) := by
  have hrD : k + 6 ≤ sevenGapDegree (m + 1) := by
    have htop : 4 * m + 2 ≤ sevenGapDegree (m + 1) := by
      unfold sevenGapDegree
      simp only [Nat.mul_add, Nat.add_mul]
      omega
    exact Nat.le_trans hmax htop
  rw [sevenBoundaryPayment_eq_weight m (k + 6) (by omega) (by omega) hrD]
  apply Int.add_nonneg
  · exact sevenBulkBoundaryConvolution_nonnegative_main m k hm hk hmax
  · exact Int.mul_nonneg
      (Int.mul_nonneg (by decide) (Int.natCast_nonneg _))
      (Int.natCast_nonneg _)

/-- Boundary payment through the last coordinate touched by the seven-point
prefix, including all six right endpoints. -/
theorem sevenBoundaryPayment_nonnegative_through_endpoint (m k : Nat)
    (hm : 3 ≤ m) (hk : 1 ≤ k) (hkD : k ≤ 4 * m + 2) :
    0 ≤ sevenBoundaryPayment m (k + 6) := by
  have hsq : 9 ≤ m * m := Nat.mul_le_mul hm hm
  have h18 : 18 ≤ 2 * m * m := by
    have h := Nat.mul_le_mul_left 2 hsq
    simpa only [Nat.mul_assoc] using h
  have hrD : k + 6 ≤ sevenGapDegree (m + 1) := by
    have htop : 4 * m + 2 + 6 ≤ sevenGapDegree (m + 1) := by
      unfold sevenGapDegree
      simp only [Nat.mul_add, Nat.add_mul]
      omega
    exact Nat.le_trans (Nat.add_le_add_right hkD 6) htop
  rw [sevenBoundaryPayment_eq_weight m (k + 6) (by omega) (by omega) hrD]
  apply Int.add_nonneg
  · exact sevenBulkBoundaryConvolution_nonnegative_through_endpoint m k hm hk hkD
  · exact Int.mul_nonneg
      (Int.mul_nonneg (by decide) (Int.natCast_nonneg _))
      (Int.natCast_nonneg _)

/-- Uniform fence for the six endpoint coordinates `d+1,...,d+6`. -/
theorem sevenBoundaryPayment_six_endpoints_nonnegative (m a : Nat)
    (hm : 3 ≤ m) (ha : 1 ≤ a) (ha6 : a ≤ 6) :
    0 ≤ sevenBoundaryPayment m ((4 * m + 2) + a) := by
  let k := (4 * m + 2) + a - 6
  have hrep : k + 6 = (4 * m + 2) + a := by
    dsimp only [k]
    omega
  have hk : 1 ≤ k := by
    dsimp only [k]
    omega
  have hkD : k ≤ 4 * m + 2 := by
    dsimp only [k]
    omega
  rw [← hrep]
  exact sevenBoundaryPayment_nonnegative_through_endpoint m k hm hk hkD

theorem sevenBulkBoundaryConvolution_far_zero (m r : Nat)
    (hr : 4 * m + 2 + 7 ≤ r) :
    sevenBulkBoundaryConvolution m r = 0 := by
  have h0 := bulk_choose_zero_of_lt (4 * m + 2) r (by omega)
  have h1 := bulk_choose_zero_of_lt (4 * m + 2) (r - 1) (by omega)
  have h2 := bulk_choose_zero_of_lt (4 * m + 2) (r - 2) (by omega)
  have h3 := bulk_choose_zero_of_lt (4 * m + 2) (r - 3) (by omega)
  have h4 := bulk_choose_zero_of_lt (4 * m + 2) (r - 4) (by omega)
  have h5 := bulk_choose_zero_of_lt (4 * m + 2) (r - 5) (by omega)
  have h6 := bulk_choose_zero_of_lt (4 * m + 2) (r - 6) (by omega)
  simp [sevenBulkBoundaryConvolution, h0, h1, h2, h3, h4, h5, h6]

/-- Beyond the six endpoints every boundary-payment term is exactly zero. -/
theorem sevenBoundaryPayment_far_zero (m r : Nat)
    (hm : 3 ≤ m) (hr : 4 * m + 2 + 7 ≤ r)
    (hrD : r ≤ sevenGapDegree (m + 1)) :
    sevenBoundaryPayment m r = 0 := by
  rw [sevenBoundaryPayment_eq_weight m r (by omega) (by omega) hrD]
  rw [sevenBulkBoundaryConvolution_far_zero m r hr]
  have hz := bulk_choose_zero_of_lt (2 * m + 4) r (by omega)
  rw [hz, Int.natCast_zero, Int.mul_zero, Int.add_zero]

/-- Full-support boundary-payment sign for every bulk deficit. -/
theorem sevenBoundaryPayment_nonnegative_all (m r : Nat)
    (hm : 3 ≤ m) (hr : 7 ≤ r) (hrD : r ≤ sevenGapDegree (m + 1)) :
    0 ≤ sevenBoundaryPayment m r := by
  by_cases hend : r ≤ 4 * m + 2 + 6
  · let k := r - 6
    have hrep : k + 6 = r := by dsimp only [k]; omega
    have hk : 1 ≤ k := by dsimp only [k]; omega
    have hkD : k ≤ 4 * m + 2 := by dsimp only [k]; omega
    rw [← hrep]
    exact sevenBoundaryPayment_nonnegative_through_endpoint m k hm hk hkD
  · rw [sevenBoundaryPayment_far_zero m r hm (by omega) hrD]
    exact Int.le_refl 0

/-- Pascal elevation preserves pointwise nonnegativity. -/
theorem sevenPascalElevate_nonnegative (d : Nat) (b : Nat → Int)
    (hb : ∀ j, 0 ≤ b j) : ∀ r, 0 ≤ sevenPascalElevate d b r := by
  induction d with
  | zero => exact hb
  | succ d ih =>
      intro r
      cases r with
      | zero => exact ih 0
      | succ r =>
          simp only [sevenPascalElevate]
          exact Int.add_nonneg (ih (r + 1)) (ih r)

/-- Exact seven-point prefix formula in the bulk range. -/
theorem sevenPascalElevate_prefix_formula_all (d : Nat) (b : Nat → Int)
    (r : Nat) (hr : 6 ≤ r) :
    sevenPascalElevate d (sevenPointPrefix b) r =
      (PNPaths.choose d r : Int) * b 0 +
      ((PNPaths.choose d (r - 1) : Int) * b 1 +
      ((PNPaths.choose d (r - 2) : Int) * b 2 +
      ((PNPaths.choose d (r - 3) : Int) * b 3 +
      ((PNPaths.choose d (r - 4) : Int) * b 4 +
      ((PNPaths.choose d (r - 5) : Int) * b 5 +
       (PNPaths.choose d (r - 6) : Int) * b 6))))) := by
  unfold sevenPointPrefix
  simp only [sevenPascalElevate_add, sevenPascalElevate_point,
    if_pos (show 0 ≤ r by omega), if_pos (show 1 ≤ r by omega),
    if_pos (show 2 ≤ r by omega), if_pos (show 3 ≤ r by omega),
    if_pos (show 4 ≤ r by omega), if_pos (show 5 ≤ r by omega),
    if_pos (show 6 ≤ r by omega), Nat.sub_zero]
  ac_rfl

/-- The scaled Pascal image of the exceptional prefix is exactly the closed
formula convolution used in the boundary payment. -/
theorem sevenGapPrefix_elevate_scaled (m r : Nat)
    (hm : 1 ≤ m) (hr : 6 ≤ r) :
    5670 * sevenPascalElevate (4 * m + 2)
        (sevenPointPrefix (sevenGapDeficit m)) r =
      sevenBoundaryFormulaConvolution m r := by
  rw [sevenPascalElevate_prefix_formula_all (4 * m + 2)
    (sevenGapDeficit m) r hr]
  have h0 := sevenGapDeficit_boundary_scaled m 0 hm (by omega)
  have h1 := sevenGapDeficit_boundary_scaled m 1 hm (by omega)
  have h2 := sevenGapDeficit_boundary_scaled m 2 hm (by omega)
  have h3 := sevenGapDeficit_boundary_scaled m 3 hm (by omega)
  have h4 := sevenGapDeficit_boundary_scaled m 4 hm (by omega)
  have h5 := sevenGapDeficit_boundary_scaled m 5 hm (by omega)
  have h6 := sevenGapDeficit_boundary_scaled m 6 hm (by omega)
  unfold sevenBoundaryFormulaConvolution
  simp only [Int.mul_add]
  rw [show 5670 * ((PNPaths.choose (4 * m + 2) r : Int) *
      sevenGapDeficit m 0) =
      (PNPaths.choose (4 * m + 2) r : Int) *
        (5670 * sevenGapDeficit m 0) by ac_rfl]
  rw [show 5670 * ((PNPaths.choose (4 * m + 2) (r - 1) : Int) *
      sevenGapDeficit m 1) =
      (PNPaths.choose (4 * m + 2) (r - 1) : Int) *
        (5670 * sevenGapDeficit m 1) by ac_rfl]
  rw [show 5670 * ((PNPaths.choose (4 * m + 2) (r - 2) : Int) *
      sevenGapDeficit m 2) =
      (PNPaths.choose (4 * m + 2) (r - 2) : Int) *
        (5670 * sevenGapDeficit m 2) by ac_rfl]
  rw [show 5670 * ((PNPaths.choose (4 * m + 2) (r - 3) : Int) *
      sevenGapDeficit m 3) =
      (PNPaths.choose (4 * m + 2) (r - 3) : Int) *
        (5670 * sevenGapDeficit m 3) by ac_rfl]
  rw [show 5670 * ((PNPaths.choose (4 * m + 2) (r - 4) : Int) *
      sevenGapDeficit m 4) =
      (PNPaths.choose (4 * m + 2) (r - 4) : Int) *
        (5670 * sevenGapDeficit m 4) by ac_rfl]
  rw [show 5670 * ((PNPaths.choose (4 * m + 2) (r - 5) : Int) *
      sevenGapDeficit m 5) =
      (PNPaths.choose (4 * m + 2) (r - 5) : Int) *
        (5670 * sevenGapDeficit m 5) by ac_rfl]
  rw [show 5670 * ((PNPaths.choose (4 * m + 2) (r - 6) : Int) *
      sevenGapDeficit m 6) =
      (PNPaths.choose (4 * m + 2) (r - 6) : Int) *
        (5670 * sevenGapDeficit m 6) by ac_rfl]
  rw [h0, h1, h2, h3, h4, h5, h6]

theorem sevenPascalElevate_point_bulk_split (d : Nat) (b : Nat → Int)
    (r : Nat) :
    sevenPascalElevate d b r =
      sevenPascalElevate d (sevenPointPrefix b) r +
        sevenPascalElevate d (sevenPointBulk b) r := by
  rw [sevenPascalElevate_congr d (seven_point_bulk b) r]
  exact sevenPascalElevate_add d (sevenPointPrefix b) (sevenPointBulk b) r

/-- Exact scaled recurrence after separating the old seven-point prefix. -/
theorem sevenGapDeficit_bulk_recurrence_scaled (m r : Nat)
    (hm : 1 ≤ m) (hr : 7 ≤ r) (hrD : r ≤ sevenGapDegree (m + 1)) :
    5670 * sevenGapDeficit (m + 1) r =
      5670 * sevenPascalElevate (4 * m + 2)
        (sevenPointBulk (sevenGapDeficit m)) r +
      sevenBoundaryPayment m r := by
  rw [sevenGapDeficit_succ m r hm hrD]
  rw [sevenPascalElevate_point_bulk_split]
  rw [Int.mul_add, Int.mul_add]
  rw [sevenGapPrefix_elevate_scaled m r hm (by omega)]
  unfold sevenBoundaryPayment sevenActualCell
  ac_rfl

theorem sevenGapDeficit_zero_of_degree_lt (m r : Nat)
    (hr : sevenGapDegree m < r) : sevenGapDeficit m r = 0 := by
  unfold sevenGapDeficit
  rw [if_neg (by omega)]

/-- Every supported deficit from six onward is nonnegative.  This is the
bulk induction consumed by the corrected projective boundary theorem. -/
theorem sevenGapDeficit_bulk_nonnegative (m r : Nat)
    (hm : 4 ≤ m) (hr : 6 ≤ r) (hrD : r ≤ sevenGapDegree m) :
    0 ≤ sevenGapDeficit m r := by
  obtain ⟨q, hmq⟩ := Nat.exists_eq_add_of_le hm
  subst m
  induction q generalizing r with
  | zero =>
      have hD : sevenGapDegree 4 = 33 := by decide
      rw [hD] at hrD
      have hcases :
          r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨
          r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨
          r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨
          r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨
          r = 30 ∨ r = 31 ∨ r = 32 ∨ r = 33 := by omega
      rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst r <;> decide
  | succ q ih =>
      have hnext : 4 + (q + 1) = (4 + q) + 1 := by omega
      rw [hnext]
      by_cases h6 : r = 6
      · subst r
        exact sevenGapDeficit_six_nonnegative ((4 + q) + 1) (by omega)
      · have hr7 : 7 ≤ r := by omega
        have hsource : ∀ j,
            0 ≤ sevenPointBulk (sevenGapDeficit (4 + q)) j := by
          intro j
          unfold sevenPointBulk
          by_cases hj : 7 ≤ j
          · rw [if_pos hj]
            by_cases hjD : j ≤ sevenGapDegree (4 + q)
            · exact ih j (by omega) (by omega) hjD
            · rw [sevenGapDeficit_zero_of_degree_lt (4 + q) j (by omega)]
              exact Int.le_refl 0
          · rw [if_neg hj]
            exact Int.le_refl 0
        have helev : 0 ≤ sevenPascalElevate (4 * (4 + q) + 2)
            (sevenPointBulk (sevenGapDeficit (4 + q))) r :=
          sevenPascalElevate_nonnegative _ _ hsource r
        have hpay : 0 ≤ sevenBoundaryPayment (4 + q) r :=
          sevenBoundaryPayment_nonnegative_all (4 + q) r (by omega) hr7 hrD
        have hscaled : 0 ≤ 5670 * sevenGapDeficit ((4 + q) + 1) r := by
          rw [sevenGapDeficit_bulk_recurrence_scaled (4 + q) r
            (by omega) hr7 hrD]
          exact Int.add_nonneg (Int.mul_nonneg (by decide) helev) hpay
        have hzero : (5670 : Int) * 0 ≤
            5670 * sevenGapDeficit ((4 + q) + 1) r := by
          simpa using hscaled
        exact Int.le_of_mul_le_mul_left hzero (by decide)

/-- Kernel-checked fence: scale three cannot be used as the bulk induction
anchor. -/
theorem sevenGapDeficit_three_eight_negative :
    sevenGapDeficit 3 8 < 0 := by decide

theorem sevenGapDeficit_three_nine_negative :
    sevenGapDeficit 3 9 < 0 := by decide

theorem sevenCoreDeficit_bulk_nonnegative (m r : Nat)
    (hm : 4 ≤ m) (hr : 6 ≤ r) (hrD : r ≤ sevenGapDegree m) :
    0 ≤ sevenCoreDeficit m r := by
  rw [sevenCoreDeficit_eq_sevenGapDeficit_of_four_le m r (by omega) (by omega)]
  exact sevenGapDeficit_bulk_nonnegative m r hm hr hrD

/-- Closed projective-deficit sign theorem at every physical scale. -/
theorem sevenCore_projectiveDeficit_nonnegative (t : Nat) :
    let m := 2 * t + 4
    let D := sevenGapDegree m
    (0 : YMGap.Constructive.Q') ≤
      YMGap.Continuum.BernsteinMonomialReconstruction.projectiveDeficitEval D
        (sevenCoreBernCoeff D m) (YMGap.Constructive.Q'.ofNat t) := by
  apply sevenCore_projectiveDeficit_nonnegative_of_bulk t
  dsimp only
  intro r hr hrD
  have hc := sevenCoreDeficit_bulk_nonnegative (2 * t + 4) r
    (by omega) hr hrD
  unfold sevenCoreDeficit at hc
  rw [if_pos hrD] at hc
  exact hc

#print axioms bulkRisingFirst
#print axioms bulk_choose_shift_cross
#print axioms bulkFalling_natCast_zero_of_lt
#print axioms bulk_choose_shift_cross_of_le
#print axioms bulkRising_split_six
#print axioms bulk_clear_choose_term
#print axioms bulk_clear_choose_term_of_le
#print axioms sevenBulkBoundaryConvolution
#print axioms sevenBulkBoundaryConvolution_cleared
#print axioms sevenBulkBoundaryConvolution_nonnegative_main
#print axioms sevenBulkBoundaryConvolution_nonnegative_through_endpoint
#print axioms sevenBoundaryFormulaConvolution_split
#print axioms sevenActualCell
#print axioms sevenBoundaryPayment
#print axioms choose_three_top_bundle
#print axioms choose_one_top_shift_two
#print axioms sevenBoundaryPayment_eq_weight
#print axioms sevenBoundaryPayment_nonnegative_main
#print axioms sevenBoundaryPayment_nonnegative_through_endpoint
#print axioms sevenBoundaryPayment_six_endpoints_nonnegative
#print axioms sevenBulkBoundaryConvolution_far_zero
#print axioms sevenBoundaryPayment_far_zero
#print axioms sevenBoundaryPayment_nonnegative_all
#print axioms sevenPascalElevate_nonnegative
#print axioms sevenPascalElevate_prefix_formula_all
#print axioms sevenGapPrefix_elevate_scaled
#print axioms sevenPascalElevate_point_bulk_split
#print axioms sevenGapDeficit_bulk_recurrence_scaled
#print axioms sevenGapDeficit_zero_of_degree_lt
#print axioms sevenGapDeficit_bulk_nonnegative
#print axioms sevenGapDeficit_three_eight_negative
#print axioms sevenGapDeficit_three_nine_negative
#print axioms sevenCoreDeficit_bulk_nonnegative
#print axioms sevenCore_projectiveDeficit_nonnegative


end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBulkInduction
