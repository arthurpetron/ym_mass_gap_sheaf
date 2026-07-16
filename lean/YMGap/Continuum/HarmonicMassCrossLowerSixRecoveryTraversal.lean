/-
# Constructive traversal of the fixed-center recovery cells

This module contains no analytic positivity estimate.  It proves the exact
combinatorial fact needed to consume such an estimate: within-cell drops and
the two alternating endpoint drops propagate the terminal center-127 slack
back through every square-root cell.  Keeping this traversal separate prevents
the remaining polynomial sign proof from being hidden inside finite case
enumeration.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryClearing
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTerminal8189
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix
import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTraversal

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryCellCompression
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryClearing
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTerminal8189
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands

local infix:50 " ≈ " => Q'.eqv

private theorem isqrt_lt_succ_sq_local (n : Nat) :
    n < (ChebOrthoMidpointEst.isqrt n + 1) *
      (ChebOrthoMidpointEst.isqrt n + 1) := by
  rcases Nat.lt_or_ge n
      ((ChebOrthoMidpointEst.isqrt n + 1) *
        (ChebOrthoMidpointEst.isqrt n + 1)) with h | h
  · exact h
  · have hbad := ChebOrthoMidpointEst.isqrt_ge
      (m := n) (K := ChebOrthoMidpointEst.isqrt n + 1) h
    omega

private theorem linear_square_local (a b q : Nat) :
    (a * q + b) * (a * q + b) =
      (a * a) * (q * q) + (a * b) * q + (a * b) * q + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  ac_rfl

private theorem even_square_local (m : Nat) :
    (2 * m) * (2 * m) = 4 * (m * m) := by
  simpa using linear_square_local 2 0 m

private theorem even_succ_square_local (m : Nat) :
    (2 * m + 1) * (2 * m + 1) =
      4 * (m * m) + 4 * m + 1 := by
  rw [linear_square_local]
  omega

private theorem odd_square_local (m : Nat) :
    (2 * m + 1) * (2 * m + 1) =
      4 * (m * m) + 4 * m + 1 :=
  even_succ_square_local m

private theorem odd_succ_square_local (m : Nat) :
    (2 * m + 2) * (2 * m + 2) =
      4 * (m * m) + 8 * m + 4 := by
  rw [linear_square_local]
  omega

/-- The stated even endpoint really is the last scale whose square-root
center is `2m`. -/
theorem thetaWindowCenter_even_rightScale
    (m : Nat) (hm : 1 ≤ m) :
    thetaWindowCenter (lowerSixEvenCenterRightScale m) = 2 * m := by
  let k := lowerSixEvenCenterRightScale m
  let L := thetaWindowLength k
  let c := thetaWindowCenter k
  have hkden : k + 2 = 2 * m * m + 2 * m - 1 := by
    dsimp only [k]
    unfold lowerSixEvenCenterRightScale
    have hmm : 1 ≤ m * m := Nat.mul_le_mul hm hm
    have hquad : 2 ≤ 2 * m * m := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hmm
    omega
  have hassoc : 2 * m * m = 2 * (m * m) := by ac_rfl
  have hL : L = 4 * (m * m) + 4 * m - 1 := by
    dsimp only [L]
    unfold thetaWindowLength
    rw [hkden]
    rw [hassoc]
    omega
  apply Nat.le_antisymm
  · have hsq := ChebOrthoMidpointEst.isqrt_sq_le L
    change c * c ≤ L at hsq
    change c ≤ 2 * m
    rcases Nat.lt_or_ge (2 * m) c with h | h
    · have hlo : 2 * m + 1 ≤ c := by omega
      have hmul := Nat.mul_le_mul hlo hlo
      have hsquare : (2 * m + 1) * (2 * m + 1) ≤ L :=
        Nat.le_trans hmul hsq
      rw [even_succ_square_local, hL] at hsquare
      omega
    · exact h
  · change 2 * m ≤ c
    dsimp only [c, thetaWindowCenter]
    apply ChebOrthoMidpointEst.isqrt_ge
    change (2 * m) * (2 * m) ≤ L
    rw [even_square_local, hL]
    omega

/-- The stated odd endpoint really is the last scale whose square-root center
is `2m+1`. -/
theorem thetaWindowCenter_odd_rightScale
    (m : Nat) (hm : 1 ≤ m) :
    thetaWindowCenter (lowerSixOddCenterRightScale m) = 2 * m + 1 := by
  let k := lowerSixOddCenterRightScale m
  let L := thetaWindowLength k
  let c := thetaWindowCenter k
  have hkden : k + 2 = 2 * m * (m + 1) + 2 * m + 1 := by
    dsimp only [k]
    unfold lowerSixOddCenterRightScale
    omega
  have hprod : 2 * m * (m + 1) = 2 * (m * m) + 2 * m := by
    calc
      2 * m * (m + 1) = 2 * m * m + 2 * m * 1 := by
        rw [Nat.mul_add]
      _ = 2 * (m * m) + 2 * m := by
        simp only [Nat.mul_one]
        ac_rfl
  have hL : L = 4 * (m * m) + 8 * m + 3 := by
    dsimp only [L]
    unfold thetaWindowLength
    rw [hkden]
    rw [hprod]
    omega
  apply Nat.le_antisymm
  · have hsq := ChebOrthoMidpointEst.isqrt_sq_le L
    change c * c ≤ L at hsq
    change c ≤ 2 * m + 1
    rcases Nat.lt_or_ge (2 * m + 1) c with h | h
    · have hlo : 2 * m + 2 ≤ c := by omega
      have hmul := Nat.mul_le_mul hlo hlo
      have hsquare : (2 * m + 2) * (2 * m + 2) ≤ L :=
        Nat.le_trans hmul hsq
      rw [odd_succ_square_local, hL] at hsquare
      omega
    · exact h
  · change 2 * m + 1 ≤ c
    dsimp only [c, thetaWindowCenter]
    apply ChebOrthoMidpointEst.isqrt_ge
    change (2 * m + 1) * (2 * m + 1) ≤ L
    rw [odd_square_local, hL]
    omega

/-- Monotonicity of the square-root center over an arbitrary finite scale
interval, derived constructively from the checked one-step theorem. -/
theorem thetaWindowCenter_mono {a b : Nat} (hab : a ≤ b) :
    thetaWindowCenter a ≤ thetaWindowCenter b := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      rcases Nat.lt_or_ge b a with hlt | hle
      · have ha : a = b + 1 := by omega
        subst a
        exact Nat.le_refl _
      · exact Nat.le_trans (ih hle) (thetaWindowCenter_mono_step b)

/-- Every scale at least 48 lies in an explicitly parameterized even or odd
center cell and is bounded by that cell's exact right endpoint. -/
theorem thetaWindowCenter_cell_right_data
    {k : Nat} (hk : 48 ≤ k) :
    (∃ m : Nat, 5 ≤ m ∧
      thetaWindowCenter k = 2 * m ∧
      k ≤ lowerSixEvenCenterRightScale m) ∨
    (∃ m : Nat, 5 ≤ m ∧
      thetaWindowCenter k = 2 * m + 1 ∧
      k ≤ lowerSixOddCenterRightScale m) := by
  rcases thetaWindowCenter_band_data hk with
    ⟨M, r, hc, hD, hr⟩ | ⟨M, r, hc, hD, hr⟩
  · left
    refine ⟨M + 5, by omega, by simpa using hc, ?_⟩
    unfold lowerSixEvenCenterRightScale
    omega
  · right
    refine ⟨M + 5, by omega, by simpa using hc, ?_⟩
    have hm6 : M + 6 = M + 5 + 1 := by omega
    rw [hm6] at hD
    unfold lowerSixOddCenterRightScale
    omega

/-! ## Order propagation once the polynomial signs are supplied -/

/-- Sparse slack at the right endpoint of an even center cell. -/
def lowerSixEvenEndpointSlack (m : Nat) : Q' :=
  lowerSixFixedCenterSparseSlack (lowerSixEvenCenterRightScale m) (2 * m)

/-- Sparse slack at the right endpoint of an odd center cell. -/
def lowerSixOddEndpointSlack (m : Nat) : Q' :=
  lowerSixFixedCenterSparseSlack (lowerSixOddCenterRightScale m) (2 * m + 1)

/-- Nonnegative consecutive drops telescope through an arbitrary fixed-center
interval. -/
theorem lowerSixFixedCenterSparseSlack_antitone_add
    (k c d : Nat)
    (hdrop : ∀ i : Nat, i < d →
      (0 : Q') ≤ lowerSixFixedCenterDrop (k + i) c) :
    lowerSixFixedCenterSparseSlack (k + d) c ≤
      lowerSixFixedCenterSparseSlack k c := by
  induction d with
  | zero =>
      simpa using Q'.le_refl' (lowerSixFixedCenterSparseSlack k c)
  | succ d ih =>
      have hprev := ih (fun i hi => hdrop i (by omega))
      have hlast0 := hdrop d (by omega)
      have hlast :
          lowerSixFixedCenterSparseSlack (k + d + 1) c ≤
            lowerSixFixedCenterSparseSlack (k + d) c := by
        apply Q'.le_of_sub_nonneg
        simpa [lowerSixFixedCenterDrop, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hlast0
      exact Q'.le_trans' _ _ _
        (by simpa [Nat.add_assoc] using hlast) hprev

/-- A cleared even-to-odd endpoint sign has the expected order orientation. -/
theorem lowerSixOddEndpointSlack_le_even_of_cleared
    (m : Nat) (hm : 1 ≤ m)
    (h : (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop m) :
    lowerSixOddEndpointSlack m ≤ lowerSixEvenEndpointSlack m := by
  apply Q'.le_of_sub_nonneg
  have hraw := lowerSixEvenOddEndpointDrop_nonnegative_of_cleared m hm h
  simpa [lowerSixEvenOddEndpointDrop, lowerSixEvenEndpointSlack,
    lowerSixOddEndpointSlack] using hraw

/-- A cleared odd-to-next-even endpoint sign has the expected order
orientation. -/
theorem lowerSixEvenEndpointSlack_succ_le_odd_of_cleared
    (m : Nat) (hm : 1 ≤ m)
    (h : (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop m) :
    lowerSixEvenEndpointSlack (m + 1) ≤ lowerSixOddEndpointSlack m := by
  apply Q'.le_of_sub_nonneg
  have hraw := lowerSixOddEvenEndpointDrop_nonnegative_of_cleared m hm h
  simpa [lowerSixOddEvenEndpointDrop, lowerSixEvenEndpointSlack,
    lowerSixOddEndpointSlack] using hraw

/-- Alternating endpoint signs telescope from odd cell `m+d` back to odd
cell `m`. -/
theorem lowerSixOddEndpointSlack_antitone_add_of_cleared
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    (m d : Nat) (hm : 5 ≤ m) :
    lowerSixOddEndpointSlack (m + d) ≤ lowerSixOddEndpointSlack m := by
  induction d with
  | zero =>
      simpa using Q'.le_refl' (lowerSixOddEndpointSlack m)
  | succ d ih =>
      let p := m + d
      have hp5 : 5 ≤ p := by dsimp only [p]; omega
      have hOddEvenStep :
          lowerSixEvenEndpointSlack (p + 1) ≤
            lowerSixOddEndpointSlack p :=
        lowerSixEvenEndpointSlack_succ_le_odd_of_cleared p (by omega)
          (hOddEven p hp5)
      have hEvenOddStep :
          lowerSixOddEndpointSlack (p + 1) ≤
            lowerSixEvenEndpointSlack (p + 1) :=
        lowerSixOddEndpointSlack_le_even_of_cleared (p + 1) (by omega)
          (hEvenOdd (p + 1) (by omega))
      have hstep :
          lowerSixOddEndpointSlack (p + 1) ≤
            lowerSixOddEndpointSlack p :=
        Q'.le_trans' _ _ _ hEvenOddStep hOddEvenStep
      exact Q'.le_trans' _ _ _
        (by simpa [p, Nat.add_assoc] using hstep) ih

/-- Every odd endpoint through `m=63` dominates the terminal odd endpoint. -/
theorem lowerSixOddEndpointSlack_terminal_le_of_cleared
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    (m : Nat) (hm5 : 5 ≤ m) (hm63 : m ≤ 63) :
    lowerSixOddEndpointSlack 63 ≤ lowerSixOddEndpointSlack m := by
  have hsum : m + (63 - m) = 63 := by omega
  have h := lowerSixOddEndpointSlack_antitone_add_of_cleared
    hEvenOdd hOddEven m (63 - m) hm5
  rwa [hsum] at h

/-- Every even endpoint through `m=63` also dominates the terminal odd
endpoint. -/
theorem lowerSixEvenEndpointSlack_terminal_le_of_cleared
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    (m : Nat) (hm5 : 5 ≤ m) (hm63 : m ≤ 63) :
    lowerSixOddEndpointSlack 63 ≤ lowerSixEvenEndpointSlack m := by
  have hterminal := lowerSixOddEndpointSlack_terminal_le_of_cleared
    hEvenOdd hOddEven m hm5 hm63
  have hcross := lowerSixOddEndpointSlack_le_even_of_cleared m (by omega)
    (hEvenOdd m hm5)
  exact Q'.le_trans' _ _ _ hterminal hcross

/-- If two scales in an interval have the same center, then every consecutive
pair before the right endpoint lies in the exact fixed-center polynomial
domain. -/
theorem lowerSixWithinCenterCell_of_common_center
    {k r t c : Nat}
    (hkt : k ≤ t) (htr : t < r) (hc10 : 10 ≤ c)
    (hck : thetaWindowCenter k = c)
    (hcr : thetaWindowCenter r = c) :
    LowerSixWithinCenterCell (t + 2) c := by
  have htrle : t ≤ r := by omega
  have ht1r : t + 1 ≤ r := by omega
  have hkt1 : k ≤ t + 1 := by omega
  have hctLower := thetaWindowCenter_mono hkt
  have hctUpper := thetaWindowCenter_mono htrle
  have hct1Lower := thetaWindowCenter_mono hkt1
  have hct1Upper := thetaWindowCenter_mono ht1r
  rw [hck] at hctLower hct1Lower
  rw [hcr] at hctUpper hct1Upper
  have hct : thetaWindowCenter t = c := by omega
  have hct1 : thetaWindowCenter (t + 1) = c := by omega
  have hsq := ChebOrthoMidpointEst.isqrt_sq_le (thetaWindowLength t)
  change thetaWindowCenter t * thetaWindowCenter t ≤
    thetaWindowLength t at hsq
  rw [hct] at hsq
  have hupper := isqrt_lt_succ_sq_local (thetaWindowLength (t + 1))
  change thetaWindowLength (t + 1) <
    (thetaWindowCenter (t + 1) + 1) *
      (thetaWindowCenter (t + 1) + 1) at hupper
  rw [hct1] at hupper
  unfold thetaWindowLength at hsq hupper
  unfold LowerSixWithinCenterCell
  constructor
  · omega
  constructor
  · exact hc10
  constructor <;> omega

/-- A uniform cleared within-cell sign propagates each physical cell to its
right endpoint. -/
theorem lowerSixFixedCenterSparseSlack_right_le_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    {k r c : Nat} (hkr : k ≤ r) (hc10 : 10 ≤ c)
    (hck : thetaWindowCenter k = c)
    (hcr : thetaWindowCenter r = c) :
    lowerSixFixedCenterSparseSlack r c ≤
      lowerSixFixedCenterSparseSlack k c := by
  let d := r - k
  have hrd : k + d = r := by
    dsimp only [d]
    omega
  have h := lowerSixFixedCenterSparseSlack_antitone_add k c d
    (fun i hi => by
      let t := k + i
      have hkt : k ≤ t := by dsimp only [t]; omega
      have htr : t < r := by dsimp only [t, d] at hi ⊢; omega
      have hcell := lowerSixWithinCenterCell_of_common_center
        hkt htr hc10 hck hcr
      exact lowerSixFixedCenterDrop_nonnegative_of_cleared t c
        (hWithin (t + 2) c hcell))
  rwa [hrd] at h

/-- The three cleared sign families are sufficient to propagate the exact
terminal sparse slack back to every scale in the finite bridge.  This theorem
contains the complete traversal, but deliberately leaves the analytic sign
proofs as explicit inputs. -/
theorem lowerSixFixedCenterSparseSlack_terminal_le_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    {k : Nat} (hk48 : 48 ≤ k) (hk8190 : k ≤ 8189) :
    lowerSixFixedCenterSparseSlack 8189 127 ≤
      lowerSixFixedCenterSparseSlack k (thetaWindowCenter k) := by
  have hcenterTop := thetaWindowCenter_mono hk8190
  rw [thetaWindowCenter_8189] at hcenterTop
  rcases thetaWindowCenter_cell_right_data hk48 with
    ⟨m, hm5, hcenter, hkright⟩ | ⟨m, hm5, hcenter, hkright⟩
  · have hm63 : m ≤ 63 := by rw [hcenter] at hcenterTop; omega
    have hrightCenter := thetaWindowCenter_even_rightScale m (by omega)
    have hcell := lowerSixFixedCenterSparseSlack_right_le_of_cleared
      hWithin hkright (by omega) hcenter hrightCenter
    have hterminal := lowerSixEvenEndpointSlack_terminal_le_of_cleared
      hEvenOdd hOddEven m hm5 hm63
    have hterminal' :
        lowerSixFixedCenterSparseSlack 8189 127 ≤
          lowerSixEvenEndpointSlack m := by
      simpa [lowerSixOddEndpointSlack, lowerSixOddCenterRightScale] using
        hterminal
    rw [hcenter]
    exact Q'.le_trans' _ _ _ hterminal' hcell
  · have hm63 : m ≤ 63 := by rw [hcenter] at hcenterTop; omega
    have hrightCenter := thetaWindowCenter_odd_rightScale m (by omega)
    have hcell := lowerSixFixedCenterSparseSlack_right_le_of_cleared
      hWithin hkright (by omega) hcenter hrightCenter
    have hterminal := lowerSixOddEndpointSlack_terminal_le_of_cleared
      hEvenOdd hOddEven m hm5 hm63
    have hterminal' :
        lowerSixFixedCenterSparseSlack 8189 127 ≤
          lowerSixOddEndpointSlack m := by
      simpa [lowerSixOddEndpointSlack, lowerSixOddCenterRightScale] using
        hterminal
    rw [hcenter]
    exact Q'.le_trans' _ _ _ hterminal' hcell

/-- The terminal exact check and the three symbolic cleared signs make the
sparse compressed slack nonnegative throughout the entire finite bridge. -/
theorem lowerSixFixedCenterSparseSlack_nonnegative_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    {k : Nat} (hk48 : 48 ≤ k) (hk8189 : k ≤ 8189) :
    (0 : Q') ≤
      lowerSixFixedCenterSparseSlack k (thetaWindowCenter k) := by
  exact Q'.le_trans' _ _ _
    lowerSixFixedCenterSparseSlack_8189_127_nonnegative
    (lowerSixFixedCenterSparseSlack_terminal_le_of_cleared
      hWithin hEvenOdd hOddEven hk48 hk8189)

/-- Transport the sparse sign through the exact finite-difference,
fixed-center, and recovery-compression identities. -/
theorem lowerSixRecoverySlack_nonnegative_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    {k : Nat} (hk48 : 48 ≤ k) (hk8189 : k ≤ 8189) :
    (0 : Q') ≤ lowerSixRecoverySlack k := by
  have hsparse := lowerSixFixedCenterSparseSlack_nonnegative_of_cleared
    hWithin hEvenOdd hOddEven hk48 hk8189
  have hfixed : (0 : Q') ≤
      lowerSixFixedCenterSlack k (thetaWindowCenter k) :=
    Q'.le_trans' _ _ _ hsparse
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (lowerSixFixedCenterSlack_eqv_sparse k
            (thetaWindowCenter k))))
  have hcenter : (0 : Q') ≤ lowerSixCenterSlack k :=
    Q'.le_trans' _ _ _ hfixed
      (Q'.le_of_eqv
        (Q'.eqv_symm (lowerSixCenterSlack_eqv_fixed k)))
  exact Q'.le_trans' _ _ _ hcenter
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixRecoverySlack_eqv_centerSlack k)))

/-- Rewrite nonnegativity of the recovery slack as the subtraction form
consumed by the ordered-rational payment lemma. -/
theorem lowerSixRecoverySlack_eqv_subtraction (k : Nat) :
    lowerSixRecoverySlack k ≈
      lowerSixRecoveryReserve k + -(-lowerSixWindowPrefix k) := by
  unfold lowerSixRecoverySlack
  refine Q'.eqv_trans _
    (lowerSixRecoveryReserve k + lowerSixWindowPrefix k) _
    (Q'.add_comm_eqv _ _) ?_
  exact Q'.add_eqv_congr_left (lowerSixRecoveryReserve k) _ _
    (Q'.eqv_symm (Q'.neg_neg_eqv (lowerSixWindowPrefix k)))

/-- Conditional exact recovery payment on every finite bridge scale.  The
only hypotheses are the three analytic cleared-polynomial signs. -/
theorem lowerSixRecoveryPayment_48_8189_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    {k : Nat} (hk48 : 48 ≤ k) (hk8189 : k ≤ 8189) :
    -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k := by
  have hsub : (0 : Q') ≤
      lowerSixRecoveryReserve k + -(-lowerSixWindowPrefix k) :=
    Q'.le_trans' _ _ _
      (lowerSixRecoverySlack_nonnegative_of_cleared
        hWithin hEvenOdd hOddEven hk48 hk8189)
      (Q'.le_of_eqv (lowerSixRecoverySlack_eqv_subtraction k))
  exact Q'.le_of_sub_nonneg hsub

/-- Conditional physical lower-six residual on the finite bridge, ready to
splice directly into the already-green production theorem at scale 8189. -/
theorem growingResidualLowerSix_48_8189_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    {k : Nat} (hk48 : 48 ≤ k) (hk8189 : k ≤ 8189) :
    GrowingResidualLowerSix k := by
  apply growingResidualLowerSix_of_interior_nonnegative hk48
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual hk48
    (lowerSixRecoveryPayment_48_8189_of_cleared
      hWithin hEvenOdd hOddEven hk48 hk8189)

#print axioms thetaWindowCenter_even_rightScale
#print axioms thetaWindowCenter_odd_rightScale
#print axioms thetaWindowCenter_mono
#print axioms thetaWindowCenter_cell_right_data
#print axioms lowerSixFixedCenterSparseSlack_antitone_add
#print axioms lowerSixOddEndpointSlack_le_even_of_cleared
#print axioms lowerSixEvenEndpointSlack_succ_le_odd_of_cleared
#print axioms lowerSixOddEndpointSlack_terminal_le_of_cleared
#print axioms lowerSixEvenEndpointSlack_terminal_le_of_cleared
#print axioms lowerSixWithinCenterCell_of_common_center
#print axioms lowerSixFixedCenterSparseSlack_right_le_of_cleared
#print axioms lowerSixFixedCenterSparseSlack_terminal_le_of_cleared
#print axioms lowerSixFixedCenterSparseSlack_nonnegative_of_cleared
#print axioms lowerSixRecoverySlack_nonnegative_of_cleared
#print axioms lowerSixRecoverySlack_eqv_subtraction
#print axioms lowerSixRecoveryPayment_48_8189_of_cleared
#print axioms growingResidualLowerSix_48_8189_of_cleared

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTraversal
