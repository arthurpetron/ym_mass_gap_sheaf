/-
# Centered stable fringe extraction in the same original marginal

For a mean-zero original f, center ONLY the active piece by its actual
nu-mean divided by the positive rational partition. The fringe already
has zero mean and is unchanged. Scalar orthogonal centering cannot
increase either the active norm or the approximation error.

The resulting active piece is both fringe-independent and truly centered
in nu. The exact original-energy split applies to these actual pieces.
No active coercivity premise is assumed or supplied.
-/

import YMGap.Continuum.QuaternionHaarNormalizedCenter
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialEnergyNormBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (mass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKernelEnergySplit (terminal_kernel_energy_split)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection (spatialFringeResidual_orthogonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow (reciprocal reciprocal_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm
  (reciprocal_pieces_norm_le reciprocal_error_norm_le_tolerance relativeApproximationCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionEnergy
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_add)
open YMGap.Continuum.QuaternionHaarNormalizedCenter

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n k : Nat)

/-- Only a positive rational partition is inverted; the original marginal
and the already centered fringe part are unchanged. -/
def centeredActivePart (f : RatPoly) : RatPoly :=
  center (N width) (marginalWeight w K width n) (mass_positive hw0 hw1 K width hK n)
    (activePart hw0 hw1 K width hK k f)

theorem centeredActivePart_supported {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (centeredActivePart hw0 hw1 K width hK n k f) :=
  center_supported (N width) (marginalWeight w K width n) (mass_positive hw0 hw1 K width hK n)
    (activePart_supported hw0 hw1 K width hK k hf)

theorem centeredActivePart_independent (f : RatPoly) (i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i (centeredActivePart hw0 hw1 K width hK n k f) :=
  center_independent (N width) (marginalWeight w K width n) (mass_positive hw0 hw1 K width hK n)
    (activePart_independent hw0 hw1 K width hK k f i hi)

theorem centeredActivePart_mean_zero (f : RatPoly) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (centeredActivePart hw0 hw1 K width hK n k f)) ≈ 0 :=
  center_mean_zero (N width) (marginalWeight w K width n) (mass_positive hw0 hw1 K width hK n)
    (activePart hw0 hw1 K width hK k f)

theorem centered_pieces_orthogonal (f : RatPoly) :
    marginalPair w K width n (fringePart hw0 hw1 K width hK k f)
      (centeredActivePart hw0 hw1 K width hK n k f) ≈ 0 := by
  let J := reciprocal hw0 hw1 K width hK k
  let b := centeredActivePart hw0 hw1 K width hK n k f
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => J | 1 => BF4ExactSlabFixedSpatialFringeProjection.spatialFringeResidual w K width f | _ => b)).mul_left _))
    (spatialFringeResidual_orthogonal w K width n f (polyMul J b)
      (fun i hi => quaternionBlockIndependent_polyMul
        (reciprocal_independent hw0 hw1 K width hK k i hi)
        (centeredActivePart_independent hw0 hw1 K width hK n k f i hi)))

/-- Centering the active piece preserves the joint coefficient-one budget. -/
theorem centered_pieces_norm_le {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    marginalPair w K width n (fringePart hw0 hw1 K width hK k f) (fringePart hw0 hw1 K width hK k f) +
      marginalPair w K width n (centeredActivePart hw0 hw1 K width hK n k f)
        (centeredActivePart hw0 hw1 K width hK n k f) ≤ marginalPair w K width n f f :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_left _ _ _ (center_norm_le (N width) (marginalWeight w K width n)
      (mass_positive hw0 hw1 K width hK n) (activePart hw0 hw1 K width hK k f)))
    (reciprocal_pieces_norm_le hw0 hw1 K width hK n k hf)

/-- With centered input, centering the error changes only the active piece.
There is no rescaling of f or the fringe part. -/
theorem centered_error_pin (f : RatPoly)
    (hmean : quaternionHaar (N width) (polyMul (marginalWeight w K width n) f) ≈ 0) :
    RatPolyCoeffEqv
      (center (N width) (marginalWeight w K width n) (mass_positive hw0 hw1 K width hK n)
        (polyAdd f (polyNeg (polyAdd (fringePart hw0 hw1 K width hK k f) (activePart hw0 hw1 K width hK k f)))))
      (polyAdd f (polyNeg (polyAdd (fringePart hw0 hw1 K width hK k f)
        (centeredActivePart hw0 hw1 K width hK n k f)))) := by
  let r := fringePart hw0 hw1 K width hK k f
  let b := activePart hw0 hw1 K width hK k f
  let nu := marginalWeight w K width n
  have hZ := mass_positive hw0 hw1 K width hK n
  exact (center_add (N width) nu hZ f (polyNeg (polyAdd r b))).trans
    ((center_fixed (N width) nu hZ f hmean).add
      ((center_neg (N width) nu hZ (polyAdd r b)).trans
        (RatPolyCoeffEqv.neg ((center_add (N width) nu hZ r b).trans
          ((center_fixed (N width) nu hZ r (fringePart_mean_zero hw0 hw1 K width hK k n f)).add (.refl _))))))

/-- The same spatial relative modulus survives exact scalar centering,
without a factor two or a depth-dependent loss. -/
theorem centered_error_norm_le_tolerance {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hmean : quaternionHaar (N width) (polyMul (marginalWeight w K width n) f) ≈ 0)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hk : relativeApproximationCutoff hw0 hw1 K width hK epsilon ≤ k) :
    let e := polyAdd f (polyNeg (polyAdd (fringePart hw0 hw1 K width hK k f)
      (centeredActivePart hw0 hw1 K width hK n k f)))
    marginalPair w K width n e e ≤ epsilon*marginalPair w K width n f f := by
  let e := polyAdd f (polyNeg (polyAdd (fringePart hw0 hw1 K width hK k f) (activePart hw0 hw1 K width hK k f)))
  have he := centered_error_pin hw0 hw1 K width hK n k f hmean
  have hn := haar_of_coeff (blocks := N width) ((he.mul he).mul_left (marginalWeight w K width n))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hn)
    (Q'.le_trans' _ _ _ (center_norm_le (N width) (marginalWeight w K width n)
      (mass_positive hw0 hw1 K width hK n) e)
      (reciprocal_error_norm_le_tolerance hw0 hw1 K width hK n k hf epsilon hepsilon hk))

/-- The original energy now isolates a genuinely centered, fringe-independent
active polynomial. Its coercive lower bound remains to be proved. -/
theorem centered_extracted_energy_split {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    energy w K width (terminalMessage w K width n)
      (polyAdd (fringePart hw0 hw1 K width hK k f) (centeredActivePart hw0 hw1 K width hK n k f)) ≈
      marginalPair w K width n (fringePart hw0 hw1 K width hK k f) (fringePart hw0 hw1 K width hK k f) +
        energy w K width (terminalMessage w K width n) (centeredActivePart hw0 hw1 K width hK n k f) :=
  terminal_kernel_energy_split w K width n
    (fringePart_supported hw0 hw1 K width hK k hf) (centeredActivePart_supported hw0 hw1 K width hK n k hf)
    (fringePart_transfer_zero hw0 hw1 K width hK k n f)
    (centered_pieces_orthogonal hw0 hw1 K width hK n k f)

/-- The constructed approximation error is small in the ORIGINAL energy,
using the same relative modulus. This is an upper bound, not coercivity. -/
theorem centered_error_energy_le_tolerance {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hmean : quaternionHaar (N width) (polyMul (marginalWeight w K width n) f) ≈ 0)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hk : relativeApproximationCutoff hw0 hw1 K width hK epsilon ≤ k) :
    let e := polyAdd f (polyNeg (polyAdd (fringePart hw0 hw1 K width hK k f)
      (centeredActivePart hw0 hw1 K width hK n k f)))
    energy w K width (terminalMessage w K width n) e ≤
      (2 : Q')*(epsilon*marginalPair w K width n f f) := by
  let s := polyAdd (fringePart hw0 hw1 K width hK k f)
    (centeredActivePart hw0 hw1 K width hK n k f)
  have hs : SupportedQuaternionBlocks (N width) s :=
    supported_add (fringePart_supported hw0 hw1 K width hK k hf)
      (centeredActivePart_supported hw0 hw1 K width hK n k hf)
  have hneg : SupportedQuaternionBlocks (N width) (polyNeg s) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hs u hu
  exact Q'.le_trans' _ _ _
    (BF4ExactSlabFixedSpatialEnergyNormBound.energy_le_two_norm hw0 hw1 K width hK n
      (supported_add hf hneg))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (centered_error_norm_le_tolerance hw0 hw1 K width hK n k hf hmean epsilon hepsilon hk)
      (by decide : (0 : Q') ≤ (2 : Q')))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centeredActivePart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centeredActivePart_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centeredActivePart_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centeredActivePart_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centered_pieces_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centered_pieces_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centered_error_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centered_error_norm_le_tolerance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centered_extracted_energy_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFringeExtraction.centered_error_energy_le_tolerance
