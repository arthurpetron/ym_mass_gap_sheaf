/-
All physical prefixes of the cubic central-window carrier.

The full block is nonnegative by the endpoint certificate.  A negative cell
can occur only after the cubic slope has become nonnegative, and the carrier
suffix theorem then propagates strict negativity forward.  The generic
terminal-negative combinator therefore turns the full-block certificate into
every-prefix nonnegativity.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicNegativeBranch

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicAllPrefixes

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierSuffix
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFirstBand
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointPhysical
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullPhysicalClosure
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicNegativeBranch
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicTerminalPrefix

local infix:50 " ≈ " => Q'.eqv

/-- Inclusive prefix of the physical cubic mode cells. -/
def thetaCubicModePrefix (k p : Nat) : Q' :=
  fsum (fun j => thetaCubicModeCell k (thetaWindowLeft k + j)) (p + 1)

/-- Every physical cubic mode prefix is nonnegative beyond the first
separately checked square-root band. -/
theorem thetaCubicModePrefix_nonnegative {k p : Nat} (hk : 48 ≤ k)
    (hp : p ≤ thetaWindowCenter k - thetaWindowLeft k) :
    (0 : Q') ≤ thetaCubicModePrefix k p := by
  let f : Nat → Q' :=
    fun j => thetaCubicModeCell k (thetaWindowLeft k + j)
  let L := thetaWindowCenter k - thetaWindowLeft k + 1
  have hleftCenter : thetaWindowLeft k ≤ thetaWindowCenter k := by
    unfold thetaWindowLeft
    exact Nat.div_le_self _ 2
  have htotal : (0 : Q') ≤ fsum f L := by
    have h := thetaCubicFullModeBlock_nonnegative hk
    unfold thetaCubicFullModeBlock thetaCubicModeBlock at h
    exact h
  have hstep : ∀ i, i + 1 < L → f i < (0 : Q') →
      f (i + 1) < (0 : Q') := by
    intro i hi hneg
    let n := thetaWindowLeft k + i
    have hnLeft : thetaWindowLeft k ≤ n := by
      dsimp only [n]
      omega
    have hnCenter : n ≤ thetaWindowCenter k := by
      dsimp only [n, L] at hi ⊢
      omega
    have hnNextCenter : n + 1 ≤ thetaWindowCenter k := by
      dsimp only [n, L] at hi ⊢
      omega
    have hn0 : 1 ≤ n := by
      have hlpos := thetaWindowLeft_pos (show 38 ≤ k by omega)
      dsimp only [n]
      omega
    have hnD : n + 1 ≤ k + 2 :=
      Nat.le_trans hnNextCenter
        (thetaWindowCenter_le_harmonicDen (show 38 ≤ k by omega))
    have hR : (0 : Q') ≤ thetaCubicRightCarrier k n :=
      thetaCubicNegativeCell_rightCarrier_nonnegative hk hnLeft hnCenter hneg
    have hs := thetaCubicModeCell_negative_succ hn0 hnD hR hneg
    simpa only [f, n, Nat.add_assoc] using hs
  have hpL : p + 1 ≤ L := by
    dsimp only [L]
    omega
  exact fsum_prefix_nonnegative_of_terminal_negative f L htotal hstep
    (p + 1) hpL

private theorem cubicCentralCarrier_eq_modeCell (k j : Nat) :
    thetaCubicCentralCarrier k j ≈
      thetaCubicModeCell k (thetaWindowLeft k + j) := by
  let n := thetaWindowLeft k + j
  unfold thetaCubicCentralCarrier thetaCubicModeCell
  dsimp only [n]
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left (sevenDirichletProfile k) _ _
      (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv
        (thetaWindowLeft k + j) (thetaWindowLeft k + j)))

theorem thetaCubicAbelPrefix_eqv_modePrefix (k p : Nat) :
    thetaCubicAbelPrefix k p ≈ thetaCubicModePrefix k p := by
  unfold thetaCubicAbelPrefix thetaCubicModePrefix
    abelPrefix
  exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _
    (cubicCentralCarrier_eq_modeCell k) (p + 1)

/-- Every inclusive cubic Abel prefix is nonnegative at every `k ≥ 48`. -/
theorem thetaCubicAbelPrefix_large_nonnegative {k p : Nat} (hk : 48 ≤ k)
    (hp : p ≤ thetaWindowCenter k - thetaWindowLeft k) :
    (0 : Q') ≤ thetaCubicAbelPrefix k p := by
  exact Q'.le_trans' _ _ _ (thetaCubicModePrefix_nonnegative hk hp)
    (Q'.ge_of_eqv (thetaCubicAbelPrefix_eqv_modePrefix k p))

/-- Complete physical cubic-prefix theorem, combining the exact first-band
audit with the symbolic endpoint/suffix proof. -/
theorem thetaCubicAbelPrefix_all_nonnegative {k p : Nat} (hk : 38 ≤ k)
    (hp : p ≤ thetaWindowCenter k - thetaWindowLeft k) :
    (0 : Q') ≤ thetaCubicAbelPrefix k p := by
  by_cases hk47 : k ≤ 47
  · exact thetaCubicAbelPrefix_firstBand_nonnegative hk hk47 hp
  · exact thetaCubicAbelPrefix_large_nonnegative (by omega) hp

#print axioms thetaCubicModePrefix
#print axioms thetaCubicModePrefix_nonnegative
#print axioms thetaCubicAbelPrefix_eqv_modePrefix
#print axioms thetaCubicAbelPrefix_large_nonnegative
#print axioms thetaCubicAbelPrefix_all_nonnegative

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicAllPrefixes
