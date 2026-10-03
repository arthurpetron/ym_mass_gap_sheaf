/-
# Original cleared Rayleigh cost is a chronological lag difference

The actual half-smoothed test b=T^t(g_n*psi) and vacuum A=g_(n+t)
retain the complete original action. The two window quotients have their
distinct original partitions Z0=ell(A^2) and Z1=ell(A*T A). Multiplying
their difference by Z0*Z1 gives exactly the existing vacuum-subtracted
clearedRayleighCost. The SAME supplied test, and hence any supplied rational
center, is used in both windows. No sign, relative estimate, stationarity,
or limiting/scaling claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWindowPin
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
import YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (massRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWindowPin (normalized_block_window_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
  (rawPair centeredPair own_centered_lag_difference_bounds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass baseLinks kineticWeight spatialWeight terminalMessage

private theorem block_succ (w : Q') (K width t : Nat) (p : RatPoly) :
    originalBlockTransfer w K width (t+1) p =
      transferStep w K width (originalBlockTransfer w K width t p) := by
  simpa only [originalBlockTransfer, iterateStep, transferStep] using
    iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 p

private theorem clear_difference (Z0 Z1 B0 B1 : Q')
    (hZ0 : (0 : Q') < Z0) (hZ1 : (0 : Q') < Z1) :
    Z1*B0 + -(Z0*B1) ≈
      (Z0*Z1) * (B0*Q'.recipPos Z0 hZ0 + -(B1*Q'.recipPos Z1 hZ1)) := by
  let r0 := Q'.recipPos Z0 hZ0
  let r1 := Q'.recipPos Z1 hZ1
  have hregroup : (Z0*Z1)*(B0*r0 + -(B1*r1)) ≈
      (Z0*r0)*(Z1*B0) + -((Z1*r1)*(Z0*B1)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1))
        (.add (.mul (.var 2) (.var 4)) (.neg (.mul (.var 3) (.var 5)))))
      (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.mul (.var 1) (.var 5)) (.mul (.var 0) (.var 3)))))
      (by decide) (fun
        | 0 => Z0 | 1 => Z1 | 2 => B0 | 3 => B1 | 4 => r0 | _ => r1)
  have hcancel : (Z0*r0)*(Z1*B0) + -((Z1*r1)*(Z0*B1)) ≈ Z1*B0 + -(Z0*B1) :=
    Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv Z0 hZ0))
        (Q'.one_mul_eqv _))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv Z1 hZ1))
        (Q'.one_mul_eqv _)))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hregroup hcancel)

/-- Literal vacuum-subtracted original cost, cleared by BOTH chronological
partitions. The arbitrary supported psi is never recentered. -/
theorem clearedRayleighCost_window_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let Z0 := weightedMass w K width (polyMul A A)
    let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
    clearedRayleighCost w K width A b ≈ (Z0*Z1) *
      (windowRatio hw0 hw1 K width hK n (2*t) n
        (polyMul psi (liftBoundary ((2*t)*(N width)) psi)) +
        -(windowRatio hw0 hw1 K width hK n (2*t+1) n
          (polyMul psi (liftBoundary ((2*t+1)*(N width)) psi)))) := by
  let A := terminalMessage w K width (n+t)
  let h := polyMul (terminalMessage w K width n) psi
  let b := originalBlockTransfer w K width t h
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B0 := weightedMass w K width (polyMul b b)
  let B1 := weightedMass w K width (polyMul b (transferStep w K width b))
  have hZ0 : (0 : Q') < Z0 := terminalPair_positive hw0 hw1 K width hK (n+t) (n+t)
  have hZ1 : (0 : Q') < Z1 := by
    dsimp only [Z1, A]
    rw [terminalMessage_next]
    exact terminalPair_positive hw0 hw1 K width hK (n+t) (n+t+1)
  have hzero : B0*Q'.recipPos Z0 hZ0 ≈
      windowRatio hw0 hw1 K width hK n (2*t) n
        (polyMul psi (liftBoundary ((2*t)*(N width)) psi)) := by
    simpa only [Nat.add_zero] using normalized_block_window_pin hw0 hw1 K width hK n t 0 hpsi
  have hone : B1*Q'.recipPos Z1 hZ1 ≈
      windowRatio hw0 hw1 K width hK n (2*t+1) n
        (polyMul psi (liftBoundary ((2*t+1)*(N width)) psi)) := by
    have hnum : B1 ≈ weightedMass w K width
        (polyMul (originalBlockTransfer w K width t h)
          (originalBlockTransfer w K width (t+1) h)) := by
      rw [block_succ w K width t h]
      exact Q'.eqv_refl _
    have hden : Z1 ≈ weightedMass w K width
        (polyMul (terminalMessage w K width (n+t)) (terminalMessage w K width (n+t+1))) := by
      rw [← terminalMessage_next w K width (n+t)]
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _
      (massRatio_congr w K width hZ1
        (terminalPair_positive hw0 hw1 K width hK (n+t) (n+t+1)) hnum hden)
      (normalized_block_window_pin hw0 hw1 K width hK n t 1 hpsi)
  change Z1*B0 + -(Z0*B1) ≈ _
  exact Q'.eqv_trans _ _ _ (clear_difference Z0 Z1 B0 B1 hZ0 hZ1)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' hzero (Q'.neg_eqv_congr _ _ hone)))

/-- BOTH cleared orders for the ACTUAL odd-window mean, retained at both
lags. Only the endpoint-mean mismatch is paid; the raw pair difference
and both original chronological partitions remain literal. -/
theorem own_clearedRayleighCost_raw_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat)
    {f : RatPoly} {C : Q'} (I : Interval (N width) f C) :
    let c := middleRatio hw0 hw1 K width hK (n+1) n f
    let psi := shifted f c
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let Z0 := weightedMass w K width (polyMul A A)
    let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
    let rawDifference := rawPair hw0 hw1 K width hK n (2*t) f +
      -(rawPair hw0 hw1 K width hK n (2*t+1) f)
    let error := mixRate hw0 hw1 width ^ n * ((C+C)*(C+C))
    clearedRayleighCost w K width A b ≤ (Z0*Z1)*(rawDifference+error) ∧
      (Z0*Z1)*rawDifference ≤ clearedRayleighCost w K width A b + (Z0*Z1)*error := by
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  let psi := shifted f c
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let rawDifference := rawPair hw0 hw1 K width hK n (2*t) f +
    -(rawPair hw0 hw1 K width hK n (2*t+1) f)
  let centeredDifference := centeredPair hw0 hw1 K width hK n (2*t) f c +
    -(centeredPair hw0 hw1 K width hK n (2*t+1) f c)
  let error := mixRate hw0 hw1 width ^ n * ((C+C)*(C+C))
  have hZ0 : (0 : Q') < Z0 := terminalPair_positive hw0 hw1 K width hK (n+t) (n+t)
  have hZ1 : (0 : Q') < Z1 := by
    dsimp only [Z1, A]
    rw [terminalMessage_next]
    exact terminalPair_positive hw0 hw1 K width hK (n+t) (n+t+1)
  have hproduct : (0 : Q') ≤ Z0*Z1 :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hZ0) (Q'.le_of_lt hZ1)
  have hpin : clearedRayleighCost w K width A b ≈ (Z0*Z1)*centeredDifference :=
    clearedRayleighCost_window_pin hw0 hw1 K width hK n t (shifted_supported I.support c)
  have hbounds : centeredDifference ≤ rawDifference+error ∧
      rawDifference ≤ centeredDifference+error :=
    own_centered_lag_difference_bounds hw0 hw1 K width hK n (2*t) (2*t+1) I
  have hforward := Q'.mul_le_mul_of_nonneg_left _ _ (Z0*Z1) hbounds.1 hproduct
  have hreverse := Q'.mul_le_mul_of_nonneg_left _ _ (Z0*Z1) hbounds.2 hproduct
  have hsplit : (Z0*Z1)*(centeredDifference+error) ≈
      clearedRayleighCost w K width A b + (Z0*Z1)*error :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_symm hpin) (Q'.eqv_refl _))
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) hforward,
    Q'.le_trans' _ _ _ hreverse (Q'.le_of_eqv hsplit)⟩

#print axioms clearedRayleighCost_window_pin
#print axioms own_clearedRayleighCost_raw_bounds

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighWindow
