/-
Track 11.7-fusion / R4at -- support-truncated lower min-tail residual.

The lower branch of the centered physical carrier was still expressed using
the complete prefix below the pointwise-best analytic tail.  Its successor
channel has the same exact support cutoff as the upper rectangular branch.
This module intersects the lower prefix with that support, proves that the
old signed debt is bounded by the new active debt, and compiles the smaller
datum through the existing physical frontier.

For the physical cutoff, throughout the lower strip `s+2 < 3*2^k`, the new
prefix length `R` satisfies the uniform exact bound `4*R <= 15*2^k`.  This is
a proof-about-computation reduction from the former worst width `4*2^k` to
at most `15*2^k/4`.

This remains an implication, not an inhabitance claim.  No `Classical`,
`native_decide`, explicit proof hole, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeCenteredActivePrefix

namespace YMGap.Continuum.P2HalfTimeCenteredActiveResidual

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeCenteredActivePrefix
open YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier
open YMGap.Continuum.P2HalfTimeCenteredProfile
open YMGap.Continuum.P2HalfTimeShiftTail
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## Active lower min-tail prefix -/

/-- The pointwise-best analytic prefix intersected with the exact support of
the successor channel. -/
def physicalBestActiveSplitStart (k N s : Nat) : Nat :=
  Nat.min (physicalBestSplitStart k N s)
    (cutoffActiveRowCount N (s + 1))

def physicalBestActiveLowShiftSum (k N s t : Nat) : Q' :=
  fsum (fun r => cutoffShiftRow (blockWeight k) N t r)
    (physicalBestActiveSplitStart k N s)

/-- The successor part of the old lower prefix is exactly its active
truncation. -/
theorem physicalBestLowShiftSum_succ_eqv_active (k N s : Nat) :
    physicalBestLowShiftSum k N s (s + 1) ≈
      physicalBestActiveLowShiftSum k N s (s + 1) := by
  unfold physicalBestLowShiftSum
  simpa only [physicalBestActiveLowShiftSum, physicalBestActiveSplitStart]
    using cutoffShiftRows_eqv_activePrefix (blockWeight k) N (s + 1)
      (physicalBestSplitStart k N s)

/-- The active predecessor prefix is no larger than the old predecessor
prefix because every discarded row is nonnegative. -/
theorem physicalBestActiveLowShiftSum_le (k N s : Nat) :
    physicalBestActiveLowShiftSum k N s s <=
      physicalBestLowShiftSum k N s s := by
  unfold physicalBestActiveLowShiftSum physicalBestLowShiftSum
  apply fsum_le_of_le
  · intro r
    exact cutoffShiftRow_nonneg (blockWeight_nonneg k) N s r
  · exact Nat.min_le_left _ _

/-- Signed debt of the support-truncated lower prefix. -/
def physicalBestActiveLowShiftDebt (k N s : Nat) : Q' :=
  dimQ s * physicalBestActiveLowShiftSum k N s (s + 1) +
    -(qpow (blockWeight k) (s + 2) *
      (dimQ (s + 1) * physicalBestActiveLowShiftSum k N s s))

/-- Removing successor-zero rows can only increase the displayed debt: the
successor sum is unchanged, while the nonnegative predecessor payment is
possibly shortened.  Thus a certificate for the active debt implies the old
lower debt/reserve certificate. -/
theorem physicalBestLowShiftDebt_le_active (k N s : Nat) :
    physicalBestLowShiftDebt k N s <=
      physicalBestActiveLowShiftDebt k N s := by
  have esucc := physicalBestLowShiftSum_succ_eqv_active k N s
  have hpred := physicalBestActiveLowShiftSum_le k N s
  have hdim := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ (s + 1))
    hpred (dimQ_nonneg (s + 1))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (blockWeight k) (s + 2)) hdim
      (qpow_nonneg (blockWeight k) (blockWeight_nonneg k) (s + 2))
  have hneg := Q'.neg_le_neg hscaled
  have hsucc :
      dimQ s * physicalBestLowShiftSum k N s (s + 1) <=
        dimQ s * physicalBestActiveLowShiftSum k N s (s + 1) :=
    Q'.le_of_eqv (Q'.mul_eqv_congr_left (dimQ s) _ _ esucc)
  simpa only [physicalBestLowShiftDebt, physicalBestActiveLowShiftDebt] using
    Q'.add_le_add hsucc hneg

/-! ## Uniform lower-strip width -/

/-- The support-truncated lower prefix has exact quarter-width bound
`4*R <= 15*2^k`.  It follows by adding the two independent doubled bounds:
the analytic tail gives `2R <= 5*2^k+s+1`, while successor support gives
`2R <= 10*2^k-s-1`. -/
theorem four_mul_physicalBestActiveSplitStart_le
    (k s : Nat) (hs : s + 2 < 3 * 2 ^ k) :
    4 * physicalBestActiveSplitStart k (blockNcut k) s <=
      15 * 2 ^ k := by
  let A := 2 ^ k
  let R := physicalBestActiveSplitStart k (blockNcut k) s
  let C := ceilHalf (s + 1)
  have hRtail : R <= physicalTailStart k s := by
    exact Nat.le_trans (Nat.min_le_left _ _)
      (Nat.le_trans (Nat.min_le_left _ _)
        (Nat.min_le_left _ _))
  have htail := two_ceilHalf_le_add_one (5 * 2 ^ k + s)
  have htwoR : 2 * R <= 5 * A + s + 1 := by
    have hmul := Nat.mul_le_mul_left 2 hRtail
    exact Nat.le_trans hmul (by
      simpa only [physicalTailStart, A] using htail)
  have hRactive : R <= cutoffActiveRowCount (blockNcut k) (s + 1) :=
    Nat.min_le_right _ _
  have hcut : blockNcut k + 1 = 5 * A := by
    simpa only [A] using blockNcut_closed k
  have hceil : s + 1 <= 2 * C := by
    simpa only [C] using le_two_ceilHalf (s + 1)
  by_cases hC : C <= 5 * A
  · unfold cutoffActiveRowCount at hRactive
    rw [hcut] at hRactive
    omega
  · unfold cutoffActiveRowCount at hRactive
    rw [hcut] at hRactive
    omega

/-! ## Residual and physical-frontier compilers -/

/-- Both channel regions now use their exact successor-active prefix. -/
structure P2PhysicalCenteredFullyActiveResidual (k N : Nat) : Type where
  lower : forall s, 1 <= s -> s < 2 * N -> s + 2 < 3 * 2 ^ k ->
    physicalBestActiveLowShiftDebt k N s <=
      physicalBestHighShiftReserve k N s
  upper : forall s, 1 <= s -> s < 2 * N -> 3 * 2 ^ k <= s + 2 ->
    dimQ s *
        physicalCenteredActiveRectangleLowShiftSum k N s (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) *
          physicalCenteredActiveRectangleLowShiftSum k N s s)

def P2PhysicalCenteredFullyActiveResidual.toActiveRectangle {k N : Nat}
    (T : P2PhysicalCenteredFullyActiveResidual k N) :
    P2PhysicalCenteredActiveRectangleResidual k N where
  lower := fun s hs hsN hlower =>
    Q'.le_trans' _ _ _ (physicalBestLowShiftDebt_le_active k N s)
      (T.lower s hs hsN hlower)
  upper := T.upper

structure BlockCompatibleP2CenteredFullyActiveResidualFromFour : Type where
  residual : forall k, 4 <= k ->
    P2PhysicalCenteredFullyActiveResidual k (blockNcut k)

def BlockCompatibleP2CenteredFullyActiveResidualFromFour.toActiveRectangle
    (T : BlockCompatibleP2CenteredFullyActiveResidualFromFour) :
    BlockCompatibleP2CenteredActiveRectangleResidualFromFour where
  residual := fun k hk => (T.residual k hk).toActiveRectangle

structure BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier : Type where
  coefficient : BlockCompatibleP2CenteredFullyActiveResidualFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

def BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.toActive
    (A : BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier) :
    BlockCompatibleP2PhysicalCenteredActiveReserveFrontier where
  coefficient := A.coefficient.toActiveRectangle
  theta := A.theta

def BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.toCanonicalFamily
    (A : BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier) :
    CanonicalBulkControlFamily :=
  A.toActive.toCanonicalFamily

theorem BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.pGamma_ge_two
    (A : BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier)
    (k : Nat) : 2 <= A.toCanonicalFamily.pGamma k :=
  A.toActive.pGamma_ge_two k

theorem BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.finePin
    (A : BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier)
    (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv
      (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control (k + 1)) (mode (k + 1))) :=
  A.toActive.finePin mode k

theorem BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.imagePin
    (A : BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier)
    (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator A.toCanonicalFamily mode))
    (k : Nat) :
    CReal.Equiv
      (B.Φ (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1)))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control k) (mode k)) :=
  A.toActive.imagePin mode B k

end YMGap.Continuum.P2HalfTimeCenteredActiveResidual

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.physicalBestLowShiftSum_succ_eqv_active
#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.physicalBestLowShiftDebt_le_active
#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.four_mul_physicalBestActiveSplitStart_le
#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.P2PhysicalCenteredFullyActiveResidual.toActiveRectangle
#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.BlockCompatibleP2CenteredFullyActiveResidualFromFour.toActiveRectangle
#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.toActive
#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.pGamma_ge_two
#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.finePin
#print axioms YMGap.Continuum.P2HalfTimeCenteredActiveResidual.BlockCompatibleP2PhysicalCenteredFullyActiveReserveFrontier.imagePin
