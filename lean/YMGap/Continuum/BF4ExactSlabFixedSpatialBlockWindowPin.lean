/-
# Original block pairings are chronological endpoint windows

The same supplied signed test is used at both endpoints. In particular a
test shifted by a rational OWN mean keeps that very mean in both copies;
no mean is recomputed at the longer horizon. The block contains the original
kinetic and spatial factors at every step. Its numerator at lag 2t+d and
its original partition are folded separately, including t=d=0.

These finite source pins assert neither stationarity nor a relative-energy
estimate. Consecutive d have different chronological partitions.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWindowPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (iterateStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add terminalPair_total)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (massRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (observedMessage windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks terminalMessage

/-- Both original endpoint insertions retained. This coefficient identity
requires no support or positivity hypothesis on the signed p and q. -/
theorem observedMessage_endpoints (w : Q') (K width n L : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv
      (observedMessage w K width n L (polyMul p (liftBoundary (L*(N width)) q)))
      (polyMul (originalBlockTransfer w K width L
        (polyMul (terminalMessage w K width n) p)) q) := by
  let g := terminalMessage w K width n
  let H := halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) L
  have hsource : RatPolyCoeffEqv
      (polyMul (polyMul g (polyMul p (liftBoundary (L*(N width)) q))) H)
      (polyMul (polyMul (polyMul g p) H) (liftBoundary (L*(N width)) q)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
      (fun
        | 0 => g
        | 1 => p
        | 2 => liftBoundary (L*(N width)) q
        | _ => H)
  have hhead : RatPolyCoeffEqv
      (partialHaarHeads (L*(N width)) (polyMul (polyMul g p) H))
      (originalBlockTransfer w K width L (polyMul g p)) :=
    (partialHaarHeads_congr (L*(N width))
      ((RatPolyCoeffEqv.mul_one (polyMul g p)).mul_right H)).symm.trans
        (windowMessage_one (N width) (kineticWeight w K width) (spatialWeight w K width)
          L (polyMul g p))
  exact (partialHaarHeads_congr (L*(N width)) hsource).trans
    ((partialHaarHeads_mul_lift (L*(N width)) (polyMul (polyMul g p) H) q).trans
      (hhead.mul_right q))

/-- SAME-test block numerator at lag 2t+d, under the original complete V.
The support premise is used only by weighted transfer symmetry. -/
theorem block_window_numerator (w : Q') (K width n t d : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    weightedMass w K width
      (polyMul
        (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi))
        (originalBlockTransfer w K width (t+d) (polyMul (terminalMessage w K width n) psi))) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width n (2*t+d)
          (polyMul psi (liftBoundary ((2*t+d)*(N width)) psi)))
          (terminalMessage w K width n)) := by
  let h := polyMul (terminalMessage w K width n) psi
  have hh : SupportedQuaternionBlocks (N width) h :=
    supported_polyMul (terminalMessage_supported w K width n) hpsi
  have hlate : SupportedQuaternionBlocks (N width)
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) (t+d) h) :=
    iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) (t+d) hh
  have hs := iterateStep_weighted_symmetric w K width t hh hlate
  rw [← iterateStep_add] at hs
  have htime : (t+d)+t=2*t+d := by omega
  rw [htime] at hs
  have hstart : weightedMass w K width
      (polyMul (originalBlockTransfer w K width t h) (originalBlockTransfer w K width (t+d) h)) ≈
      weightedMass w K width (polyMul h (originalBlockTransfer w K width (2*t+d) h)) :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)) hs
  have hwindow : RatPolyCoeffEqv
      (polyMul (observedMessage w K width n (2*t+d)
        (polyMul psi (liftBoundary ((2*t+d)*(N width)) psi))) (terminalMessage w K width n))
      (polyMul h (originalBlockTransfer w K width (2*t+d) h)) :=
    ((observedMessage_endpoints w K width n (2*t+d) psi psi).mul_right
      (terminalMessage w K width n)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 2) (.var 1)) (.var 0)) (by decide)
          (fun
            | 0 => originalBlockTransfer w K width (2*t+d) h
            | 1 => psi
            | _ => terminalMessage w K width n))
  exact Q'.eqv_trans _ _ _ hstart (Q'.eqv_symm (weightedMass_congr w K width hwindow))

/-- The block partition has the SAME total chronological horizon as its
window numerator; d=0 and d=1 retain their distinct original masses. -/
theorem block_window_partition (w : Q') (K width n t d : Nat) :
    weightedMass w K width
      (polyMul (terminalMessage w K width (n+t)) (terminalMessage w K width (n+t+d))) ≈
      weightedMass w K width
        (polyMul (terminalMessage w K width (n+(2*t+d))) (terminalMessage w K width n)) := by
  have hleft := terminalPair_total w K width (n+t) (n+t+d)
  have hright := terminalPair_total w K width (n+(2*t+d)) n
  have htime : (n+t)+(n+t+d)=(n+(2*t+d))+n := by omega
  rw [htime] at hleft
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

/-- Actual normalized original block pairing, with a constructed positive
terminal-pair mass and no center, stationary law, or new comparison input. -/
theorem normalized_block_window_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t d : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    massRatio w K width
      (polyMul
        (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi))
        (originalBlockTransfer w K width (t+d) (polyMul (terminalMessage w K width n) psi)))
      (polyMul (terminalMessage w K width (n+t)) (terminalMessage w K width (n+t+d)))
      (terminalPair_positive hw0 hw1 K width hK (n+t) (n+t+d)) ≈
      windowRatio hw0 hw1 K width hK n (2*t+d) n
        (polyMul psi (liftBoundary ((2*t+d)*(N width)) psi)) :=
  massRatio_congr w K width
    (terminalPair_positive hw0 hw1 K width hK (n+t) (n+t+d))
    (terminalPair_positive hw0 hw1 K width hK (n+(2*t+d)) n)
    (block_window_numerator w K width n t d hpsi)
    (block_window_partition w K width n t d)

#print axioms observedMessage_endpoints
#print axioms block_window_numerator
#print axioms block_window_partition
#print axioms normalized_block_window_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWindowPin
