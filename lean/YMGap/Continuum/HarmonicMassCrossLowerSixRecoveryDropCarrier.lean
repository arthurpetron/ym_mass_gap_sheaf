/-
Exact one-mode coordinates for the fixed-center recovery drop.

The normalized total drop is positive, but its summands are not pointwise
positive.  This file exposes the finite signed mode sum and the terminal
boundary drop exactly, then banks the first physical sign-change fence.  The
resulting coordinate is intended for a one-crossing/Abel proof rather than a
termwise estimate.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryEnergy
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryEnergy
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem recovery_drop_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "recovery_drop_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               recovery_drop_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- One sparse recovery mode before taking the scale difference. -/
def lowerSixRecoverySparseMode (k n : Nat) : Q' :=
  (qpow ((1 : Q') + harmW k) 3 +
      -(Q'.ofNat 6 * (harmU k * harmU k))) *
      integerThetaTerm (harmW k) n +
    -(Q'.ofNat 8 * (harmW k * halfThetaTerm (harmW k) n))

/-- Raw adjacent-scale drop of one sparse recovery mode. -/
def lowerSixRecoverySparseModeDrop (k n : Nat) : Q' :=
  lowerSixRecoverySparseMode k n +
    -lowerSixRecoverySparseMode (k + 1) n

/-- Boundary contribution to the adjacent-scale drop after the common block
through mode `N` has been separated. -/
def lowerSixRecoveryTerminalDrop (k N : Nat) : Q' :=
  Q'.ofNat 4 * integerThetaTerm (harmW k) (N + 1) +
    -(Q'.ofNat 4 * integerThetaTerm (harmW (k + 1)) (N + 1))

/-! ## Positive-weight factorization of a mode drop -/

/-- Cleared coefficient of one sparse mode relative to its positive integer
theta weight.  It is the old residual slope with the exact lower-six debt
`6u²n` removed. -/
def lowerSixRecoveryModeSlope (k n : Nat) : Q' :=
  thetaResidualCellSlope (harmW k) n +
    -(Q'.ofNat 6 * (harmU k * harmU k) * Q'.ofNat n)

/-- Carrier left after transporting the next-scale mode back through the
exact positive harmonic drift factor. -/
def lowerSixRecoveryModeDropCarrier (k n : Nat) : Q' :=
  lowerSixRecoveryModeSlope k n +
    -(lowerSixWeightDriftFactor k n *
      lowerSixRecoveryModeSlope (k + 1) n)

/-- Positive old-scale weight left after cancelling the mode index from the
integer-theta factor. -/
def lowerSixRecoveryDropWeight (k n : Nat) : Q' :=
  Q'.ofNat n * lowerSixModeWeight k n

/-- Exact adjacent-mode growth of the transported squared weight. -/
theorem lowerSixWeightDriftFactor_succ_eqv (k n : Nat) :
    lowerSixWeightDriftFactor k (n + 1) ≈
      lowerSixWeightDriftFactor k n *
        qpow (driftRatio k * driftRatio k) (2 * n + 1) := by
  have hexp : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega
  unfold lowerSixWeightDriftFactor
  rw [hexp]
  exact HeatKernelRGStep.qpow_add
    (driftRatio k * driftRatio k) (n * n) (2 * n + 1)

theorem lowerSixWeightDriftFactor_zero_eqv (k : Nat) :
    lowerSixWeightDriftFactor k 0 ≈ (1 : Q') := by
  unfold lowerSixWeightDriftFactor qpow
  exact Q'.eqv_refl _

/-- The recovery drift at mode `p+1` is exactly the existing compensated-Abel
square drift at node `p`, up to the single leading squared scale ratio.  Thus
the two independently developed coordinates use the same geometric carrier. -/
theorem lowerSixWeightDriftFactor_shift_eqv_driftSqFactor (k p : Nat) :
    lowerSixWeightDriftFactor k (p + 1) ≈
      (driftRatio k * driftRatio k) * driftSqFactor k p := by
  have hexp : (p + 1) * (p + 1) = 1 + c4 p := by
    unfold c4
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  unfold lowerSixWeightDriftFactor
  rw [hexp]
  refine Q'.eqv_trans _
    (qpow (driftRatio k * driftRatio k) 1 *
      qpow (driftRatio k * driftRatio k) (c4 p)) _
    (HeatKernelRGStep.qpow_add
      (driftRatio k * driftRatio k) 1 (c4 p)) ?_
  have hone : qpow (driftRatio k * driftRatio k) 1 ≈
      driftRatio k * driftRatio k := by
    unfold qpow
    exact Q'.one_mul_eqv _
  have hsq : qpow (driftRatio k * driftRatio k) (c4 p) ≈
      driftSqFactor k p := by
    unfold driftSqFactor
    exact FusionQuotientCollapse.qpow_mul_self (driftRatio k) (c4 p)
  refine Q'.eqv_trans _
    ((driftRatio k * driftRatio k) *
      qpow (driftRatio k * driftRatio k) (c4 p)) _
    (Q'.mul_eqv_congr_right _ _ _ hone) ?_
  exact Q'.mul_eqv_congr_left _ _ _ hsq

private theorem recovery_one_le_qpow {q : Q'} (hq : (1 : Q') ≤ q) :
    ∀ n, (1 : Q') ≤ qpow q n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hq0 : (0 : Q') ≤ q :=
        Q'.le_trans' _ _ _ Q'.zero_le_one hq
      have hn0 : (0 : Q') ≤ qpow q n := qpow_nonneg q hq0 n
      have hmul : qpow q n * (1 : Q') ≤ qpow q n * q :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hq hn0
      exact Q'.le_trans' _ _ _ (recovery_one_le_qpow hq n)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) hmul)

theorem one_le_lowerSixWeightDriftFactor (k n : Nat) :
    (1 : Q') ≤ lowerSixWeightDriftFactor k n := by
  have hr : (1 : Q') ≤ driftRatio k :=
    HarmonicDriftAntisymmetry.one_le_driftRatio k
  have hr0 : (0 : Q') ≤ driftRatio k :=
    Q'.le_trans' _ _ _ Q'.zero_le_one hr
  have hrmul : driftRatio k * (1 : Q') ≤
      driftRatio k * driftRatio k :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hr hr0
  have hr2 : (1 : Q') ≤ driftRatio k * driftRatio k :=
    Q'.le_trans' _ _ _ hr
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) hrmul)
  unfold lowerSixWeightDriftFactor
  exact recovery_one_le_qpow hr2 (n * n)

theorem lowerSixRecoverySparseMode_factor (k n : Nat) :
    Q'.ofNat n * lowerSixRecoverySparseMode k n ≈
      integerThetaTerm (harmW k) n * lowerSixRecoveryModeSlope k n := by
  have hcell := thetaResidualCell_factor (harmW k) n
  refine Q'.eqv_trans _
    (Q'.ofNat n * growingThetaResidualCell (harmW k) n +
      -(Q'.ofNat n *
        (Q'.ofNat 6 * (harmU k * harmU k) *
          integerThetaTerm (harmW k) n))) _ ?_ ?_
  · unfold lowerSixRecoverySparseMode growingThetaResidualCell
    recovery_drop_ring
  refine Q'.eqv_trans _
    (integerThetaTerm (harmW k) n *
        thetaResidualCellSlope (harmW k) n +
      -(Q'.ofNat n *
        (Q'.ofNat 6 * (harmU k * harmU k) *
          integerThetaTerm (harmW k) n))) _
    ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ hcell
  · unfold lowerSixRecoveryModeSlope
    recovery_drop_ring

/-- Removing the fixed lower-six debt preserves the cross-multiplied
monotonicity of the normalized residual slope.  Hence each scale's mode
slope still has at most one sign crossing. -/
theorem lowerSixRecoveryModeSlope_cross_mono (k n : Nat) :
    Q'.ofNat (n + 1) * lowerSixRecoveryModeSlope k n ≤
      Q'.ofNat n * lowerSixRecoveryModeSlope k (n + 1) := by
  have hcross := thetaResidualCellSlope_cross_mono
    (harmW_nonneg k) (harmW_le_one k) n
  let C := -(Q'.ofNat 6 * (harmU k * harmU k) *
    (Q'.ofNat (n + 1) * Q'.ofNat n))
  have hadd := Q'.add_le_add_right _ _ C hcross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by
      unfold lowerSixRecoveryModeSlope
      dsimp only [C]
      recovery_drop_ring))
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (by
        unfold lowerSixRecoveryModeSlope
        dsimp only [C]
        recovery_drop_ring)))

theorem lowerSixRecoveryModeSlope_nonnegative_succ
    {k n : Nat} (hn : 0 < n)
    (hcell : (0 : Q') ≤ lowerSixRecoveryModeSlope k n) :
    (0 : Q') ≤ lowerSixRecoveryModeSlope k (n + 1) := by
  cases n with
  | zero => omega
  | succ n =>
      have hleft : (0 : Q') ≤
          Q'.ofNat (n + 1 + 1) *
            lowerSixRecoveryModeSlope k (n + 1) :=
        Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) hcell
      have hcross := lowerSixRecoveryModeSlope_cross_mono k (n + 1)
      have hscaled : (0 : Q') ≤
          Q'.ofNat (n + 1) *
            lowerSixRecoveryModeSlope k (n + 1 + 1) :=
        Q'.le_trans' _ _ _ hleft hcross
      have hcancel : Q'.ofNat (n + 1) * (0 : Q') ≤
          Q'.ofNat (n + 1) *
            lowerSixRecoveryModeSlope k (n + 1 + 1) :=
        Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.mul_zero_eqv (Q'.ofNat (n + 1)))) hscaled
      exact Q'.le_of_mul_le_mul_left hcancel (Q'.ofNat_succ_pos n)

theorem lowerSixRecoveryModeSlope_nonpositive_pred
    {k n : Nat}
    (hcell : lowerSixRecoveryModeSlope k (n + 1) ≤ (0 : Q')) :
    lowerSixRecoveryModeSlope k n ≤ (0 : Q') := by
  have hcross := lowerSixRecoveryModeSlope_cross_mono k n
  have hright : Q'.ofNat n * lowerSixRecoveryModeSlope k (n + 1) ≤
      Q'.ofNat n * (0 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcell
      (ExpNeg.ofNat_nonneg' n)
  have hscaled : Q'.ofNat (n + 1) * lowerSixRecoveryModeSlope k n ≤
      Q'.ofNat (n + 1) * (0 : Q') :=
    Q'.le_trans' _ _ _ hcross
      (Q'.le_trans' _ _ _ hright
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_zero_eqv (Q'.ofNat n))
          (Q'.eqv_symm (Q'.mul_zero_eqv (Q'.ofNat (n + 1)))))))
  exact Q'.le_of_mul_le_mul_left hscaled (Q'.ofNat_succ_pos n)

theorem integerThetaTerm_step_eqv (k n : Nat) :
    integerThetaTerm (harmW (k + 1)) n ≈
      integerThetaTerm (harmW k) n * lowerSixWeightDriftFactor k n := by
  have hw := lowerSixModeWeight_step_eqv k n
  unfold integerThetaTerm
  change Q'.ofNat (n * n) * lowerSixModeWeight (k + 1) n ≈
    (Q'.ofNat (n * n) * lowerSixModeWeight k n) *
      lowerSixWeightDriftFactor k n
  refine Q'.eqv_trans _
    (Q'.ofNat (n * n) *
      (lowerSixModeWeight k n *
        lowerSixWeightDriftFactor k n)) _
    (Q'.mul_eqv_congr_left (Q'.ofNat (n * n)) _ _ hw) ?_
  recovery_drop_ring

/-- Every signed mode drop is one explicit carrier times the old positive
integer-theta weight.  This is the exact coordinate for the one-crossing
attack. -/
theorem lowerSixRecoverySparseModeDrop_factor (k n : Nat) :
    Q'.ofNat n * lowerSixRecoverySparseModeDrop k n ≈
      integerThetaTerm (harmW k) n *
        lowerSixRecoveryModeDropCarrier k n := by
  have hold := lowerSixRecoverySparseMode_factor k n
  have hnew := lowerSixRecoverySparseMode_factor (k + 1) n
  have hstep := integerThetaTerm_step_eqv k n
  unfold lowerSixRecoverySparseModeDrop
  refine Q'.eqv_trans _
    (Q'.ofNat n * lowerSixRecoverySparseMode k n +
      -(Q'.ofNat n * lowerSixRecoverySparseMode (k + 1) n)) _
    (by recovery_drop_ring) ?_
  refine Q'.eqv_trans _
    (integerThetaTerm (harmW k) n * lowerSixRecoveryModeSlope k n +
      -(integerThetaTerm (harmW (k + 1)) n *
        lowerSixRecoveryModeSlope (k + 1) n)) _
    (Q'.add_eqv_congr' hold (Q'.neg_eqv_congr _ _ hnew)) ?_
  refine Q'.eqv_trans _
    (integerThetaTerm (harmW k) n * lowerSixRecoveryModeSlope k n +
      -((integerThetaTerm (harmW k) n *
          lowerSixWeightDriftFactor k n) *
        lowerSixRecoveryModeSlope (k + 1) n)) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ _ hstep))) ?_
  unfold lowerSixRecoveryModeDropCarrier
  recovery_drop_ring

private theorem recovery_drop_ofNat_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  rcases n with _ | n
  · omega
  · exact Q'.ofNat_succ_pos n

/-- The undifferenced sparse mode is the same positive Gaussian weight times
its normalized one-crossing slope. -/
theorem lowerSixRecoverySparseMode_eqv_weightSlope
    (k n : Nat) (hn : 1 ≤ n) :
    lowerSixRecoverySparseMode k n ≈
      lowerSixRecoveryDropWeight k n * lowerSixRecoveryModeSlope k n := by
  have hfactor := lowerSixRecoverySparseMode_factor k n
  have hscaled :
      Q'.ofNat n * lowerSixRecoverySparseMode k n ≈
        Q'.ofNat n *
          (lowerSixRecoveryDropWeight k n *
            lowerSixRecoveryModeSlope k n) := by
    refine Q'.eqv_trans _ _ _ hfactor ?_
    unfold lowerSixRecoveryDropWeight lowerSixModeWeight integerThetaTerm
    recovery_drop_ring
  exact Q'.mul_left_cancel_of_pos
    (recovery_drop_ofNat_pos (by omega)) hscaled

/-- Division-free cancellation of the common positive mode index gives the
direct weight-times-carrier form. -/
theorem lowerSixRecoverySparseModeDrop_eqv_weightCarrier
    (k n : Nat) (hn : 1 ≤ n) :
    lowerSixRecoverySparseModeDrop k n ≈
      lowerSixRecoveryDropWeight k n *
        lowerSixRecoveryModeDropCarrier k n := by
  have hfactor := lowerSixRecoverySparseModeDrop_factor k n
  have hscaled :
      Q'.ofNat n * lowerSixRecoverySparseModeDrop k n ≈
        Q'.ofNat n *
          (lowerSixRecoveryDropWeight k n *
            lowerSixRecoveryModeDropCarrier k n) := by
    refine Q'.eqv_trans _ _ _ hfactor ?_
    unfold lowerSixRecoveryDropWeight lowerSixModeWeight integerThetaTerm
    recovery_drop_ring
  exact Q'.mul_left_cancel_of_pos
    (recovery_drop_ofNat_pos (by omega)) hscaled

theorem integerThetaTerm_harmonic_nonnegative (k n : Nat) :
    (0 : Q') ≤ integerThetaTerm (harmW k) n := by
  unfold integerThetaTerm
  exact Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' (n * n))
    (qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _)

theorem integerThetaTerm_harmonic_pos {k n : Nat} (hn : 1 ≤ n) :
    (0 : Q') < integerThetaTerm (harmW k) n := by
  have hnpos : 0 < n := by omega
  have hn2pos : 0 < n * n := Nat.mul_pos hnpos hnpos
  unfold integerThetaTerm
  exact Q'.mul_pos (recovery_drop_ofNat_pos hn2pos)
    (BondMovingScaledNorm.qpow_pos
      (Q'.mul_pos
        (HarmonicFusedSchurObstruction.harmW_pos k)
        (HarmonicFusedSchurObstruction.harmW_pos k)) _)

theorem lowerSixRecoveryDropWeight_pos {k n : Nat} (hn : 1 ≤ n) :
    (0 : Q') < lowerSixRecoveryDropWeight k n := by
  unfold lowerSixRecoveryDropWeight lowerSixModeWeight
  exact Q'.mul_pos (recovery_drop_ofNat_pos (by omega))
    (BondMovingScaledNorm.qpow_pos
      (Q'.mul_pos
        (HarmonicFusedSchurObstruction.harmW_pos k)
        (HarmonicFusedSchurObstruction.harmW_pos k)) _)

/-- The separated terminal mode is always adverse (or zero): the harmonic
weight grows with scale, and its exact transport factor is at least one. -/
theorem lowerSixRecoveryTerminalDrop_nonpositive (k N : Nat) :
    lowerSixRecoveryTerminalDrop k N ≤ (0 : Q') := by
  let n := N + 1
  let I := integerThetaTerm (harmW k) n
  let J := integerThetaTerm (harmW (k + 1)) n
  let F := lowerSixWeightDriftFactor k n
  have hI0 : (0 : Q') ≤ I := by
    dsimp only [I]
    exact integerThetaTerm_harmonic_nonnegative k n
  have hF1 : (1 : Q') ≤ F := by
    dsimp only [F]
    exact one_le_lowerSixWeightDriftFactor k n
  have hmul : I * (1 : Q') ≤ I * F :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hF1 hI0
  have hIF : I ≤ I * F :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv I))) hmul
  have hstep : J ≈ I * F := by
    dsimp only [J, I, F, n]
    exact integerThetaTerm_step_eqv k (N + 1)
  have hIJ : I ≤ J :=
    Q'.le_trans' _ _ _ hIF (Q'.ge_of_eqv hstep)
  have hfour : Q'.ofNat 4 * I ≤ Q'.ofNat 4 * J :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hIJ (ExpNeg.ofNat_nonneg' 4)
  have hsub := Q'.add_le_add_right
    (Q'.ofNat 4 * I) (Q'.ofNat 4 * J) (-(Q'.ofNat 4 * J)) hfour
  unfold lowerSixRecoveryTerminalDrop
  dsimp only [I, J, n] at hsub ⊢
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv (Q'.add_neg_self_eqv _))

/-- Carrier nonnegativity implies the corresponding physical mode-drop sign;
both cancelled factors are explicit positive rationals. -/
theorem lowerSixRecoverySparseModeDrop_nonnegative_of_carrier
    {k n : Nat} (hn : 1 ≤ n)
    (hcarrier : (0 : Q') ≤ lowerSixRecoveryModeDropCarrier k n) :
    (0 : Q') ≤ lowerSixRecoverySparseModeDrop k n := by
  have hproduct : (0 : Q') ≤
      integerThetaTerm (harmW k) n *
        lowerSixRecoveryModeDropCarrier k n :=
    Q'.mul_nonneg _ _ (integerThetaTerm_harmonic_nonnegative k n) hcarrier
  have hscaled : (0 : Q') ≤
      Q'.ofNat n * lowerSixRecoverySparseModeDrop k n :=
    Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (Q'.eqv_symm (lowerSixRecoverySparseModeDrop_factor k n)))
  exact Q'.nonneg_of_mul_pos
    (recovery_drop_ofNat_pos (by omega)) hscaled

/-- Conversely, a physical mode-drop sign can be cancelled back to its exact
one-crossing carrier. -/
theorem lowerSixRecoveryModeDropCarrier_nonnegative_of_modeDrop
    {k n : Nat} (hn : 1 ≤ n)
    (hmode : (0 : Q') ≤ lowerSixRecoverySparseModeDrop k n) :
    (0 : Q') ≤ lowerSixRecoveryModeDropCarrier k n := by
  have hn0 : (0 : Q') ≤ Q'.ofNat n := ExpNeg.ofNat_nonneg' n
  have hscaled : (0 : Q') ≤
      Q'.ofNat n * lowerSixRecoverySparseModeDrop k n :=
    Q'.mul_nonneg _ _ hn0 hmode
  have hproduct : (0 : Q') ≤
      integerThetaTerm (harmW k) n *
        lowerSixRecoveryModeDropCarrier k n :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (lowerSixRecoverySparseModeDrop_factor k n))
  exact Q'.nonneg_of_mul_pos (integerThetaTerm_harmonic_pos hn) hproduct

private theorem lowerSixRecoverySparseModeSum_even_eqv (k c : Nat) :
    finSum (fun j => lowerSixRecoverySparseMode k (j + 1)) (2 * c) ≈
      (qpow ((1 : Q') + harmW k) 3 +
          -(Q'.ofNat 6 * (harmU k * harmU k))) *
          lowerSixFixedIntegerMass k c +
        -(Q'.ofNat 8 *
          (harmW k * lowerSixFixedHalfMass k c)) := by
  unfold lowerSixFixedIntegerMass lowerSixFixedHalfMass
  let A := qpow ((1 : Q') + harmW k) 3 +
    -(Q'.ofNat 6 * (harmU k * harmU k))
  have hadd := RationalTail.finSum_add
    (fun j => A * integerThetaTerm (harmW k) (j + 1))
    (fun j => -(Q'.ofNat 8 *
      (harmW k * halfThetaTerm (harmW k) (j + 1)))) (2 * c)
  have hI := RationalTail.const_mul_finSum
    (fun j => integerThetaTerm (harmW k) (j + 1)) A (2 * c)
  have hH := RationalTail.const_mul_finSum
    (fun j => halfThetaTerm (harmW k) (j + 1))
    (-(Q'.ofNat 8 * harmW k)) (2 * c)
  unfold lowerSixRecoverySparseMode
  dsimp only [A] at hadd hI hH ⊢
  refine Q'.eqv_trans _
    (finSum (fun j =>
        A * integerThetaTerm (harmW k) (j + 1)) (2 * c) +
      finSum (fun j =>
        -(Q'.ofNat 8 *
          (harmW k * halfThetaTerm (harmW k) (j + 1)))) (2 * c)) _
    hadd ?_
  refine Q'.add_eqv_congr' (Q'.eqv_symm hI) ?_
  refine Q'.eqv_trans _
    (finSum (fun j =>
      (-(Q'.ofNat 8 * harmW k)) *
        halfThetaTerm (harmW k) (j + 1)) (2 * c)) _ ?_ ?_
  · apply RationalTail.finSum_eqv_congr
    intro j
    recovery_drop_ring
  · exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hH) (by
      recovery_drop_ring)

theorem lowerSixFixedCenterSparseSlack_eqv_modeSum (k c : Nat) :
    lowerSixFixedCenterSparseSlack k c ≈
      finSum (fun j => lowerSixRecoverySparseMode k (j + 1)) (2 * c) +
        Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 1) := by
  have hsum := lowerSixRecoverySparseModeSum_even_eqv k c
  unfold lowerSixFixedCenterSparseSlack
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsum))
    (Q'.eqv_refl _)

private theorem finSum_sparseModeDrop_eqv (k : Nat) : ∀ N,
    finSum (fun j => lowerSixRecoverySparseModeDrop k (j + 1)) N ≈
      finSum (fun j => lowerSixRecoverySparseMode k (j + 1)) N +
        -finSum (fun j => lowerSixRecoverySparseMode (k + 1) (j + 1)) N
  | 0 => by
      simp only [finSum_zero]
      recovery_drop_ring
  | N + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((finSum (fun j => lowerSixRecoverySparseMode k (j + 1)) N +
            -finSum (fun j =>
              lowerSixRecoverySparseMode (k + 1) (j + 1)) N) +
          lowerSixRecoverySparseModeDrop k (N + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_sparseModeDrop_eqv k N)
      · unfold lowerSixRecoverySparseModeDrop
        recovery_drop_ring

/-- Exact finite one-mode decomposition of the raw fixed-center drop. -/
theorem lowerSixFixedCenterDrop_eqv_modeDrops (k c : Nat) :
    lowerSixFixedCenterDrop k c ≈
      finSum (fun j => lowerSixRecoverySparseModeDrop k (j + 1)) (2 * c) +
        lowerSixRecoveryTerminalDrop k (2 * c) := by
  have hold := lowerSixFixedCenterSparseSlack_eqv_modeSum k c
  have hnew := lowerSixFixedCenterSparseSlack_eqv_modeSum (k + 1) c
  have hsum := finSum_sparseModeDrop_eqv k (2 * c)
  unfold lowerSixFixedCenterDrop lowerSixRecoveryTerminalDrop
  refine Q'.eqv_trans _
    ((finSum (fun j => lowerSixRecoverySparseMode k (j + 1)) (2 * c) +
        Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 1)) +
      -(finSum (fun j =>
          lowerSixRecoverySparseMode (k + 1) (j + 1)) (2 * c) +
        Q'.ofNat 4 * integerThetaTerm
          (harmW (k + 1)) (2 * c + 1))) _
    (Q'.add_eqv_congr' hold (Q'.neg_eqv_congr _ _ hnew)) ?_
  refine Q'.eqv_trans _
    ((finSum (fun j => lowerSixRecoverySparseMode k (j + 1)) (2 * c) +
        -finSum (fun j =>
          lowerSixRecoverySparseMode (k + 1) (j + 1)) (2 * c)) +
      (Q'.ofNat 4 * integerThetaTerm (harmW k) (2 * c + 1) +
        -(Q'.ofNat 4 * integerThetaTerm
          (harmW (k + 1)) (2 * c + 1)))) _
    (by recovery_drop_ring) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsum)

/-- Exact weighted-carrier form of the complete fixed-center drop, including
the adverse terminal boundary term. -/
theorem lowerSixFixedCenterDrop_eqv_weightCarriers (k c : Nat) :
    lowerSixFixedCenterDrop k c ≈
      finSum (fun j =>
        lowerSixRecoveryDropWeight k (j + 1) *
          lowerSixRecoveryModeDropCarrier k (j + 1)) (2 * c) +
        lowerSixRecoveryTerminalDrop k (2 * c) := by
  have hmode := RationalTail.finSum_eqv_congr
    (fun j => lowerSixRecoverySparseModeDrop k (j + 1))
    (fun j => lowerSixRecoveryDropWeight k (j + 1) *
      lowerSixRecoveryModeDropCarrier k (j + 1))
    (fun j => lowerSixRecoverySparseModeDrop_eqv_weightCarrier
      k (j + 1) (by omega)) (2 * c)
  exact Q'.eqv_trans _ _ _
    (lowerSixFixedCenterDrop_eqv_modeDrops k c)
    (Q'.add_eqv_congr_right _ _ _ hmode)

/-- A boundary-payment interface for the compensated-Abel attack.  Once the
weighted carrier sum pays the (possibly adverse) terminal mode, the complete
fixed-center recovery drop is nonnegative. -/
theorem lowerSixFixedCenterDrop_nonnegative_of_weightedCarrierPayment
    {k c : Nat}
    (hpayment :
      -lowerSixRecoveryTerminalDrop k (2 * c) ≤
        finSum (fun j =>
          lowerSixRecoveryDropWeight k (j + 1) *
            lowerSixRecoveryModeDropCarrier k (j + 1)) (2 * c)) :
    (0 : Q') ≤ lowerSixFixedCenterDrop k c := by
  let S := finSum (fun j =>
    lowerSixRecoveryDropWeight k (j + 1) *
      lowerSixRecoveryModeDropCarrier k (j + 1)) (2 * c)
  let T := lowerSixRecoveryTerminalDrop k (2 * c)
  have hdiff : (0 : Q') ≤ S + -(-T) :=
    Q'.sub_nonneg_of_le hpayment
  have hsum : (0 : Q') ≤ S + T :=
    Q'.le_trans' _ _ _ hdiff
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_left S (-(-T)) T (Q'.neg_neg_eqv T)))
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixFixedCenterDrop_eqv_weightCarriers k c)))

/-! ## Kernel-checked fence around a false pointwise route -/

/-- The last positive sparse mode before the first physical sign crossing. -/
theorem lowerSixRecoverySparseModeDrop_48_6_nonnegative :
    (0 : Q') ≤ lowerSixRecoverySparseModeDrop 48 6 := by
  unfold lowerSixRecoverySparseModeDrop lowerSixRecoverySparseMode
    integerThetaTerm halfThetaTerm harmW harmU oneSub unit qpow
  decide

/-- Pointwise nonnegativity already fails at the next mode. -/
theorem lowerSixRecoverySparseModeDrop_48_7_negative :
    lowerSixRecoverySparseModeDrop 48 7 < (0 : Q') := by
  unfold lowerSixRecoverySparseModeDrop lowerSixRecoverySparseMode
    integerThetaTerm halfThetaTerm harmW harmU oneSub unit qpow
  decide

/-- The boundary term is also adverse at the first physical cell. -/
theorem lowerSixRecoveryTerminalDrop_48_20_negative :
    lowerSixRecoveryTerminalDrop 48 20 < (0 : Q') := by
  unfold lowerSixRecoveryTerminalDrop integerThetaTerm harmW harmU oneSub unit qpow
  decide

#print axioms lowerSixFixedCenterSparseSlack_eqv_modeSum
#print axioms lowerSixFixedCenterDrop_eqv_modeDrops
#print axioms lowerSixFixedCenterDrop_eqv_weightCarriers
#print axioms lowerSixRecoverySparseMode_factor
#print axioms lowerSixRecoverySparseMode_eqv_weightSlope
#print axioms lowerSixRecoveryModeSlope_cross_mono
#print axioms lowerSixRecoveryModeSlope_nonnegative_succ
#print axioms lowerSixRecoveryModeSlope_nonpositive_pred
#print axioms lowerSixWeightDriftFactor_succ_eqv
#print axioms lowerSixWeightDriftFactor_zero_eqv
#print axioms lowerSixWeightDriftFactor_shift_eqv_driftSqFactor
#print axioms one_le_lowerSixWeightDriftFactor
#print axioms integerThetaTerm_step_eqv
#print axioms lowerSixRecoverySparseModeDrop_factor
#print axioms lowerSixRecoverySparseModeDrop_eqv_weightCarrier
#print axioms integerThetaTerm_harmonic_pos
#print axioms lowerSixRecoveryDropWeight_pos
#print axioms lowerSixRecoveryTerminalDrop_nonpositive
#print axioms lowerSixRecoverySparseModeDrop_nonnegative_of_carrier
#print axioms lowerSixRecoveryModeDropCarrier_nonnegative_of_modeDrop
#print axioms lowerSixFixedCenterDrop_nonnegative_of_weightedCarrierPayment
#print axioms lowerSixRecoverySparseModeDrop_48_6_nonnegative
#print axioms lowerSixRecoverySparseModeDrop_48_7_negative
#print axioms lowerSixRecoveryTerminalDrop_48_20_negative

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
