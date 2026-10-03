/-
# Exact heat defect inside the original half-smoothed block determinant

The block message b=T^t(g_n*psi_n) retains the ORIGINAL depth-n OWN center.
Only its energy term is shifted back to the bare square observable and then
identified with the signed heat defect at depth n+t. Both chronological
partitions, the boundary drift and the complete signed multiplication cost
remain literal. No recentering of b, finite eigenpin or sign is asserted.

Consumer: the combined relative bound s*D <= C*Z1*ell(b*b). That quantitative
estimate on a justified changing family is still unpaid by this identity.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
import YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect

namespace YMGap.Continuum.BF4DyadicWilsonSquareExactBlockHeatDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
  (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
  (clearedRayleighCost boundaryDrift signedMultiplicationCost original_block_rayleigh_split)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse (energy_shifted)
open YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect
  (squareSignedHeatDefect paddedSquare_energy_signedHeatDefect_identity)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight kineticWeight energy
  weightedMass squareSignedHeatDefect oddVariance terminalMessage originalBlockTransfer
  clearedRayleighCost boundaryDrift signedMultiplicationCost middleRatio

/-- Division-free original determinant with BOTH partitions and its entire
signed correction. The two displayed centers are not identified: psi uses
depth n, while the exact heat-defect energy uses the OWN variance at n+t. -/
theorem paddedSquare_exact_block_heatDefect {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (n t scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let g := terminalMessage w K width n
    let c := middleRatio hw0 hw1 K width hK (n+1) n f
    let psi := shifted f c
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul g psi)
    let Z0 := weightedMass w K width (polyMul A A)
    let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
    clearedRayleighCost w K width A b ≈
      (Z0*((1-qpow w (12*side scale))*(Z1*oddVariance hw0 hw1 K width hK (n+t) f)-
        squareSignedHeatDefect hw0 hw1 K width hK (n+t) scale hwidth)+
        boundaryDrift w K width A psi)+signedMultiplicationCost w K width A b psi := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let g := terminalMessage w K width n
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  let psi := shifted f c
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul g psi)
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let a := qpow w (12*side scale)
  let v := oddVariance hw0 hw1 K width hK (n+t) f
  let M := squareSignedHeatDefect hw0 hw1 K width hK (n+t) scale hwidth
  have hf : SupportedQuaternionBlocks (N width) f :=
    sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hg : SupportedQuaternionBlocks (N width) g := terminalMessage_supported w K width n
  have hp : SupportedQuaternionBlocks (N width) psi := shifted_supported hf c
  have hA : originalBlockTransfer w K width t g = A := by
    dsimp only [g, A]
    unfold originalBlockTransfer terminalMessage
    exact (iterateStep_add (N width) (kineticWeight w K width)
      (spatialWeight w K width) n t polyOne).symm
  have hsplit : clearedRayleighCost w K width A b ≈
      (Z0*energy w K width A psi+boundaryDrift w K width A psi)+
        signedMultiplicationCost w K width A b psi := by
    simpa only [hA] using original_block_rayleigh_split w K width t hg hp
  have hshift : energy w K width A psi ≈ energy w K width A f :=
    energy_shifted w K width (terminalMessage_supported w K width (n+t)) hf c
  have hmass : oddMass w K width (n+t) ≈ Z1 := by
    change weightedMass w K width
      (polyMul (terminalMessage w K width (n+t+1)) A) ≈
        weightedMass w K width (polyMul A (transferStep w K width A))
    rw [← terminalMessage_next w K width (n+t)]
    exact weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)
  have hheat : energy w K width A f ≈ (1-a)*(Z1*v)-M :=
    Q'.eqv_trans _ _ _
      (paddedSquare_energy_signedHeatDefect_identity hw0 hw1 K width hK (n+t) scale hwidth)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (1-a) _ _ (Q'.mul_eqv_congr_right _ _ v hmass))
        (Q'.eqv_refl (-M)))
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left Z0 _ _ (Q'.eqv_trans _ _ _ hshift hheat))
        (Q'.eqv_refl (boundaryDrift w K width A psi)))
      (Q'.eqv_refl (signedMultiplicationCost w K width A b psi)))

#print axioms paddedSquare_exact_block_heatDefect

end YMGap.Continuum.BF4DyadicWilsonSquareExactBlockHeatDefect
