/-
# Exact finite padding of the actual observed window

Adjoining one unobserved slice to the right redistributes one transition
from the right boundary into the window. Adjoining one slice to the left
shifts the probe by exactly one source slice and redistributes the same
transition from the left boundary. Both identities compare the SAME full
chronological K/V chain, insertion and positive partition. A zero-transition
window is the existing middle-slice ratio, with its final V retained once.

These are finite redistribution identities, not finite stationarity. Their
consumer is consistency of the independently constructed window time limits.
No cutoff removal, ambient-lattice placement, reflected OS or gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (massRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion (liftBoundary_add)
open YMGap.Continuum.SU2QuaternionHeadWindowContraction (windowMessage_iterate)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

/-- The same literal polynomial has support after adjoining one right slice. -/
theorem windowSupport_right {width L : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    SupportedQuaternionBlocks ((L+1+1)*(N width)) p := by
  intro term ht
  exact Nat.le_trans (hp term ht)
    (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (N width) (Nat.le_succ (L+1))))

/-- Adjoining one left slice shifts every source block, including fringe blocks. -/
theorem windowSupport_left {width L : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    SupportedQuaternionBlocks ((L+1+1)*(N width)) (liftBoundary (N width) p) := by
  simpa only [Nat.add_mul, Nat.one_mul] using lift_supported hp (N width)

/-- Right unit padding changes only the partition of the total transition
count into window and right-boundary lengths. The full partition is unchanged. -/
theorem windowRatio_pad_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    windowRatio hw0 hw1 K width hK m (L+1) n p ≈
      windowRatio hw0 hw1 K width hK m L (n+1) p := by
  have htime : m+(L+1+n) = m+(L+(n+1)) := by omega
  have hnum := window_pairing w K width m (L+1) n (windowSupport_right hp)
  rw [htime] at hnum
  have hden := window_partition_pairing w K width m (L+1) n
  rw [htime] at hden
  exact massRatio_congr w K width
    (terminalPair_positive hw0 hw1 K width hK (m+(L+1)) n)
    (terminalPair_positive hw0 hw1 K width hK (m+L) (n+1))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hnum) (window_pairing w K width m L (n+1) hp))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hden) (window_partition_pairing w K width m L (n+1)))

/-- Left unit padding shifts the insertion by exactly N blocks. It is the
same original chain as the shorter window with one more left-boundary step. -/
theorem windowRatio_pad_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p) :
    windowRatio hw0 hw1 K width hK m (L+1) n (liftBoundary (N width) p) ≈
      windowRatio hw0 hw1 K width hK (m+1) L n p := by
  have htime : m+(L+1+n) = (m+1)+(L+n) := by omega
  have hplace : liftBoundary (m*(N width)) (liftBoundary (N width) p) =
      liftBoundary ((m+1)*(N width)) p := by
    rw [Nat.add_mul, Nat.one_mul, liftBoundary_add]
  have hnum := window_pairing w K width m (L+1) n (windowSupport_left hp)
  rw [htime, hplace] at hnum
  have hden := window_partition_pairing w K width m (L+1) n
  rw [htime] at hden
  exact massRatio_congr w K width
    (terminalPair_positive hw0 hw1 K width hK (m+(L+1)) n)
    (terminalPair_positive hw0 hw1 K width hK ((m+1)+L) n)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hnum) (window_pairing w K width (m+1) L n hp))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hden) (window_partition_pairing w K width (m+1) L n))

/-- A zero-transition window is exactly the existing slice ratio. The
supported-slice guard is retained for its polynomial-functional consumer. -/
theorem windowRatio_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    windowRatio hw0 hw1 K width hK m 0 n p ≈
      middleRatio hw0 hw1 K width hK m n p := by
  have hzero : RatPolyCoeffEqv (observedMessage w K width m 0 p)
      (polyMul (terminalMessage w K width m) p) :=
    windowMessage_iterate (N width) (kineticWeight w K width) (spatialWeight w K width)
      0 (terminalMessage w K width m) p
  exact massRatio_congr w K width
    (terminalPair_positive hw0 hw1 K width hK m n)
    (terminalPair_positive hw0 hw1 K width hK m n)
    (weightedMass_congr w K width (hzero.mul_right (terminalMessage w K width n)))
    (Q'.eqv_refl _)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding.windowSupport_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding.windowSupport_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding.windowRatio_pad_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding.windowRatio_pad_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding.windowRatio_zero
