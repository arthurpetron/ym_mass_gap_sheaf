/-
Track 11.7-fusion / R4as -- support-truncated centered rectangle residual.

The rectangular centered theorem leaves the fixed row prefix
`r < 4 * 2^k`.  That prefix still contains rows which are identically zero:
an autoconvolution row at channel `t` can be active only when

    r < N + 1 - ceil(t / 2).

This module proves the support cutoff constructively, truncates the common
upper-channel prefix at the successor-channel support, and compiles the
strictly smaller residual to the existing centered physical frontier.  On
the physical cutoff and in the upper strip, the new prefix length `R`
satisfies `2*R <= 7*2^k+1`, improving the former `R <= 4*2^k`.

This remains an implication, not an inhabitance claim.  No `Classical`,
`native_decide`, explicit proof hole, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier

namespace YMGap.Continuum.P2HalfTimeCenteredActivePrefix

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
open YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier
open YMGap.Continuum.P2HalfTimeCenteredProfile
open YMGap.Continuum.P2HalfTimeShiftTail
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact support truncation -/

/-- Number of shift rows which can possibly be active at cutoff `N` and
channel `t`. -/
def cutoffActiveRowCount (N t : Nat) : Nat :=
  N + 1 - ceilHalf t

/-- Every row at or beyond the exact active-row count vanishes. -/
theorem cutoffShiftRow_eqv_zero_of_activeRowCount_le
    (w : Q') (N t r : Nat) (hr : cutoffActiveRowCount N t <= r) :
    cutoffShiftRow w N t r ≈ 0 := by
  unfold cutoffShiftRow
  apply fsum_zero_below
  intro p hp
  unfold cutoffCoeff
  by_cases hpN : p + r < N + 1
  · by_cases hqN : (t - p) + r < N + 1
    · have hceilLower := le_two_ceilHalf t
      have hceilUpper := two_ceilHalf_le_add_one t
      by_cases hc : ceilHalf t <= N + 1
      · exfalso
        unfold cutoffActiveRowCount at hr
        omega
      · exfalso
        unfold cutoffActiveRowCount at hr
        omega
    · rw [if_neg hqN]
      exact Q'.mul_zero_eqv _
  · rw [if_neg hpN]
    exact Q'.zero_mul_eqv _

private theorem fsum_zero_extension_active {f : Nat -> Q'} {n m : Nat}
    (hnm : n <= m) (hz : forall i, n <= i -> f i ≈ 0) :
    fsum f m ≈ fsum f n := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz m hnm))
        (Q'.eqv_of_eq (Q'.add_zero' _))

/-- Any finite row prefix can be truncated at the exact support count. -/
theorem cutoffShiftRows_eqv_activePrefix
    (w : Q') (N t R : Nat) :
    fsum (fun r => cutoffShiftRow w N t r) R ≈
      fsum (fun r => cutoffShiftRow w N t r)
        (Nat.min R (cutoffActiveRowCount N t)) := by
  by_cases hR : R <= cutoffActiveRowCount N t
  · simp only [Nat.min_eq_left hR]
    exact Q'.eqv_refl _
  · have hactive : cutoffActiveRowCount N t <= R := Nat.le_of_not_ge hR
    simp only [Nat.min_eq_right hactive]
    exact fsum_zero_extension_active hactive (fun r hr =>
      cutoffShiftRow_eqv_zero_of_activeRowCount_le w N t r hr)

/-- Every sharply truncated row is nonnegative at a nonnegative weight. -/
theorem cutoffShiftRow_nonneg {w : Q'} (hw : (0 : Q') <= w)
    (N t r : Nat) : (0 : Q') <= cutoffShiftRow w N t r := by
  unfold cutoffShiftRow
  exact fsum_nonneg (fun p => Q'.mul_nonneg _ _
    (cutoffCoeff_nonneg hw N r p)
    (cutoffCoeff_nonneg hw N r (t - p))) (t + 1)

/-! ## Smaller common prefix in the upper physical strip -/

/-- Common upper-channel prefix: the rectangular prefix intersected with the
support of the successor channel. -/
def physicalCenteredActiveRectangleSplitStart (k N s : Nat) : Nat :=
  Nat.min (physicalCenteredRectangleSplitStart k N)
    (cutoffActiveRowCount N (s + 1))

def physicalCenteredActiveRectangleLowShiftSum
    (k N s t : Nat) : Q' :=
  fsum (fun r => cutoffShiftRow (blockWeight k) N t r)
    (physicalCenteredActiveRectangleSplitStart k N s)

/-- The successor-channel rectangular prefix is exactly its active common
prefix; the discarded suffix is identically zero. -/
theorem physicalCenteredRectangleLowShiftSum_succ_eqv_active
    (k N s : Nat) :
    physicalCenteredRectangleLowShiftSum k N (s + 1) ≈
      physicalCenteredActiveRectangleLowShiftSum k N s (s + 1) := by
  unfold physicalCenteredRectangleLowShiftSum
  simpa only [physicalCenteredActiveRectangleLowShiftSum,
    physicalCenteredActiveRectangleSplitStart] using
      cutoffShiftRows_eqv_activePrefix (blockWeight k) N (s + 1)
        (physicalCenteredRectangleSplitStart k N)

/-- At the predecessor channel, the active common prefix is bounded by the
original rectangular prefix; any extra predecessor-only row is nonnegative. -/
theorem physicalCenteredActiveRectangleLowShiftSum_le
    (k N s : Nat) :
    physicalCenteredActiveRectangleLowShiftSum k N s s <=
      physicalCenteredRectangleLowShiftSum k N s := by
  unfold physicalCenteredActiveRectangleLowShiftSum
  unfold physicalCenteredRectangleLowShiftSum
  apply fsum_le_of_le
  · intro r
    exact cutoffShiftRow_nonneg (blockWeight_nonneg k) N s r
  · exact Nat.min_le_left _ _

/-- A half-time inequality on the active common prefix implies the former
rectangular-prefix obligation. -/
theorem physicalCenteredRectangleLow_halfTime_of_active
    (k N s : Nat)
    (hactive :
      dimQ s *
          physicalCenteredActiveRectangleLowShiftSum k N s (s + 1) <=
        qpow (blockWeight k) (s + 2) *
          (dimQ (s + 1) *
            physicalCenteredActiveRectangleLowShiftSum k N s s)) :
    dimQ s * physicalCenteredRectangleLowShiftSum k N (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * physicalCenteredRectangleLowShiftSum k N s) := by
  have eleft := physicalCenteredRectangleLowShiftSum_succ_eqv_active k N s
  have hprefix := physicalCenteredActiveRectangleLowShiftSum_le k N s
  have hdim := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ (s + 1))
    hprefix (dimQ_nonneg (s + 1))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (blockWeight k) (s + 2)) hdim
      (qpow_nonneg (blockWeight k) (blockWeight_nonneg k) (s + 2))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left (dimQ s) _ _ eleft))
    (Q'.le_trans' _ _ _ hactive hscaled)

/-- Quantitative physical shrink in the upper strip.  The former common
prefix had length at most `4*2^k`; support reduces its doubled length to at
most `7*2^k+1`. -/
theorem two_mul_physicalCenteredActiveRectangleSplitStart_le
    (k s : Nat) (hs : 3 * 2 ^ k <= s + 2) :
    2 * physicalCenteredActiveRectangleSplitStart k (blockNcut k) s <=
      7 * 2 ^ k + 1 := by
  let A := 2 ^ k
  let C := ceilHalf (s + 1)
  have hstart :
      physicalCenteredActiveRectangleSplitStart k (blockNcut k) s <=
        cutoffActiveRowCount (blockNcut k) (s + 1) :=
    Nat.min_le_right _ _
  have hcut : blockNcut k + 1 = 5 * A := by
    simpa only [A] using blockNcut_closed k
  have hceil : s + 1 <= 2 * C := by
    simpa only [C] using le_two_ceilHalf (s + 1)
  by_cases hC : C <= 5 * A
  · unfold cutoffActiveRowCount at hstart
    rw [hcut] at hstart
    omega
  · unfold cutoffActiveRowCount at hstart
    rw [hcut] at hstart
    omega

/-! ## Residual and physical-frontier compilers -/

/-- Region-split residual with the upper branch reduced to the exact active
common prefix. -/
structure P2PhysicalCenteredActiveRectangleResidual (k N : Nat) : Type where
  lower : forall s, 1 <= s -> s < 2 * N -> s + 2 < 3 * 2 ^ k ->
    physicalBestLowShiftDebt k N s <= physicalBestHighShiftReserve k N s
  upper : forall s, 1 <= s -> s < 2 * N -> 3 * 2 ^ k <= s + 2 ->
    dimQ s *
        physicalCenteredActiveRectangleLowShiftSum k N s (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) *
          physicalCenteredActiveRectangleLowShiftSum k N s s)

/-- Compile the support-truncated residual to the previous centered rectangle
carrier. -/
def P2PhysicalCenteredActiveRectangleResidual.toRectangle {k N : Nat}
    (T : P2PhysicalCenteredActiveRectangleResidual k N) :
    P2PhysicalCenteredRectangleResidual k N where
  lower := T.lower
  upper := fun s hs hsN hupper =>
    physicalCenteredRectangleLow_halfTime_of_active k N s
      (T.upper s hs hsN hupper)

structure BlockCompatibleP2CenteredActiveRectangleResidualFromFour : Type where
  residual : forall k, 4 <= k ->
    P2PhysicalCenteredActiveRectangleResidual k (blockNcut k)

def BlockCompatibleP2CenteredActiveRectangleResidualFromFour.toRectangle
    (T : BlockCompatibleP2CenteredActiveRectangleResidualFromFour) :
    BlockCompatibleP2CenteredRectangleResidualFromFour where
  residual := fun k hk => (T.residual k hk).toRectangle

/-- The physical frontier with the coefficient input reduced to the
support-truncated centered residual. -/
structure BlockCompatibleP2PhysicalCenteredActiveReserveFrontier : Type where
  coefficient : BlockCompatibleP2CenteredActiveRectangleResidualFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

def BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.toCentered
    (A : BlockCompatibleP2PhysicalCenteredActiveReserveFrontier) :
    BlockCompatibleP2PhysicalCenteredReserveFrontier where
  coefficient := A.coefficient.toRectangle
  theta := A.theta

def BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.toCanonicalFamily
    (A : BlockCompatibleP2PhysicalCenteredActiveReserveFrontier) :
    CanonicalBulkControlFamily :=
  A.toCentered.toCanonicalFamily

theorem BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.pGamma_ge_two
    (A : BlockCompatibleP2PhysicalCenteredActiveReserveFrontier) (k : Nat) :
    2 <= A.toCanonicalFamily.pGamma k :=
  A.toCentered.pGamma_ge_two k

theorem BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.finePin
    (A : BlockCompatibleP2PhysicalCenteredActiveReserveFrontier)
    (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv
      (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control (k + 1)) (mode (k + 1))) :=
  A.toCentered.finePin mode k

theorem BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.imagePin
    (A : BlockCompatibleP2PhysicalCenteredActiveReserveFrontier)
    (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator A.toCanonicalFamily mode))
    (k : Nat) :
    CReal.Equiv
      (B.Φ (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1)))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control k) (mode k)) :=
  A.toCentered.imagePin mode B k

end YMGap.Continuum.P2HalfTimeCenteredActivePrefix

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.cutoffShiftRow_eqv_zero_of_activeRowCount_le
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.cutoffShiftRows_eqv_activePrefix
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.physicalCenteredRectangleLow_halfTime_of_active
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.two_mul_physicalCenteredActiveRectangleSplitStart_le
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.P2PhysicalCenteredActiveRectangleResidual.toRectangle
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.BlockCompatibleP2CenteredActiveRectangleResidualFromFour.toRectangle
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.toCentered
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.pGamma_ge_two
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.finePin
#print axioms YMGap.Continuum.P2HalfTimeCenteredActivePrefix.BlockCompatibleP2PhysicalCenteredActiveReserveFrontier.imagePin
