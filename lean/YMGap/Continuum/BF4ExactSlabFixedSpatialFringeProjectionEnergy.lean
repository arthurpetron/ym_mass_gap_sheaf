/-
# Exact original temporal energy of the stable fringe extraction

The two constructed finite polynomial pieces use the same spatial
reciprocal, original marginal and original transfer. The fringe piece
has zero mean and weighted transfer, hence its energy is exactly its
squared marginal norm. Orthogonality and transfer symmetry give one
exact energy split, leaving only the actual fringe-independent piece.

This is not a coercivity estimate on that remaining piece. It is not
assumed centered, and no completed gap or physical-time rate is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKernelEnergySplit
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKernelEnergySplit
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow
  (reciprocal reciprocal_supported reciprocal_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm
  (scaled_pieces_orthogonal)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (k : Nat)

/-- The constructed finite fringe piece, with no terminal-depth parameter. -/
def fringePart (f : RatPoly) : RatPoly :=
  polyMul (reciprocal hw0 hw1 K width hK k) (spatialFringeResidual w K width f)

/-- The remaining actual polynomial is independent of every fringe coordinate. -/
def activePart (f : RatPoly) : RatPoly :=
  polyMul (reciprocal hw0 hw1 K width hK k) (spatialFringeMean w K width f)

theorem fringePart_supported {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (fringePart hw0 hw1 K width hK k f) :=
  supported_polyMul (reciprocal_supported hw0 hw1 K width hK k)
    (spatialFringeResidual_supported w K width hf)

theorem activePart_supported {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (activePart hw0 hw1 K width hK k f) :=
  supported_polyMul (reciprocal_supported hw0 hw1 K width hK k)
    (spatialFringeMean_supported w K width hf)

theorem activePart_independent (f : RatPoly) (i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i (activePart hw0 hw1 K width hK k f) :=
  quaternionBlockIndependent_polyMul (reciprocal_independent hw0 hw1 K width hK k i hi)
    (spatialFringeMean_independent w K width f i hi)

/-- The extracted fringe has zero original marginal mean at every depth. -/
theorem fringePart_mean_zero (n : Nat) (f : RatPoly) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (fringePart hw0 hw1 K width hK k f)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).mul_left _))
    (spatialFringeResidual_orthogonal w K width n f (reciprocal hw0 hw1 K width hK k)
      (reciprocal_independent hw0 hw1 K width hK k))

theorem fringePart_transfer_zero (n : Nat) (f p : RatPoly) :
    quaternionHaar (N width) (polyMul p (transferStep w K width
      (polyMul (terminalMessage w K width n) (fringePart hw0 hw1 K width hK k f)))) ≈ 0 :=
  spatialFringeResidual_scaled_transfer_zero w K width n f
    (reciprocal hw0 hw1 K width hK k) p (reciprocal_independent hw0 hw1 K width hK k)

/-- The whole extracted fringe is paid exactly, not by a componentwise cap. -/
theorem fringePart_energy (n : Nat) (f : RatPoly) :
    energy w K width (terminalMessage w K width n) (fringePart hw0 hw1 K width hK k f) ≈
      marginalPair w K width n (fringePart hw0 hw1 K width hK k f) (fringePart hw0 hw1 K width hK k f) :=
  terminal_kernel_energy w K width n (fringePart_transfer_zero hw0 hw1 K width hK k n f)

/-- One exact original-energy identity isolates the remaining active piece.
No mean-zero or coercivity premise is imposed on that active piece. -/
theorem extracted_energy_split (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    energy w K width (terminalMessage w K width n)
      (polyAdd (fringePart hw0 hw1 K width hK k f) (activePart hw0 hw1 K width hK k f)) ≈
      marginalPair w K width n (fringePart hw0 hw1 K width hK k f) (fringePart hw0 hw1 K width hK k f) +
        energy w K width (terminalMessage w K width n) (activePart hw0 hw1 K width hK k f) :=
  terminal_kernel_energy_split w K width n
    (fringePart_supported hw0 hw1 K width hK k hf) (activePart_supported hw0 hw1 K width hK k hf)
    (fringePart_transfer_zero hw0 hw1 K width hK k n f)
    (scaled_pieces_orthogonal w K width n f (reciprocal hw0 hw1 K width hK k)
      (reciprocal_independent hw0 hw1 K width hK k))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.fringePart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.activePart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.fringePart_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.activePart_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.activePart_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.fringePart_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.fringePart_transfer_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.fringePart_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy.extracted_energy_split
