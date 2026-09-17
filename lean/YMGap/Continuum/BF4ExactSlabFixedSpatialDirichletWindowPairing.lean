/-
# Original terminal edge density is the existing one-step window

The complete terminal factors V*u_n at both endpoints are retained. The
existing exact window-message pairing supplies the lower integration and
its unchanged final spatial weight. Its half-open/full-chain identity
already handles lifted constants; no coefficient equality between a
lifted unit and the unpadded unit is asserted here.

This is an unnormalized finite identity for arbitrary supported edge tests,
not a stationary-vacuum identification or a Poincare estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindowPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (observedMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Every supported two-slice insertion is paired with the SAME original
one-step observed message and the SAME finite terminal message. -/
theorem edge_window_pairing (w : Q') (K width n : Nat) {p : RatPoly}
    (_hp : SupportedQuaternionBlocks (N width+N width) p) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width n)) p) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width n 1 p) (terminalMessage w K width n)) := by
  let g := terminalMessage w K width n
  let V := spatialWeight w K width
  let W := kineticWeight w K width
  let G := liftBoundary (N width) (polyMul V g)
  have h := windowMessage_pairing (N width) W V 1 g p g
  have hcount : (1+1)*(N width) = N width+N width := by omega
  rw [hcount] at h
  have hin : RatPolyCoeffEqv
      (polyMul (edgeDensity w K width g) p)
      (polyMul (polyMul g p) (chain (N width) W V 1 g)) := by
    change RatPolyCoeffEqv
      (polyMul (polyMul (polyMul W (polyMul V g)) G) p)
      (polyMul (polyMul g p) (polyMul W (polyMul V G)))
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.var 4))
      (.mul (.mul (.var 2) (.var 4)) (.mul (.var 0) (.mul (.var 1) (.var 3))))
      (by decide) (fun | 0 => W | 1 => V | 2 => g | 3 => G | _ => p)
  have hout : RatPolyCoeffEqv
      (polyMul (windowMessage (N width) W V 1 g p) (polyMul V g))
      (polyMul V (polyMul (observedMessage w K width n 1 p) g)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => observedMessage w K width n 1 p | 1 => V | _ => g)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hin)
    (Q'.eqv_trans _ _ _ h (haar_of_coeff hout))

end YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindowPairing

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindowPairing.edge_window_pairing
