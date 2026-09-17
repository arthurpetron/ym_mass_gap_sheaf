/-
# The original odd marginal and energy on the active subspace

For supported polynomials independent of all inactive coordinates, exact
face peeling replaces the spatial weight by its active-face product in
the original odd marginal and temporal energy. The terminal messages
remain the original g_n=T^n 1 and g_(n+1); no reduced message sequence,
stationary identification, normalization or coercive bound is introduced.

All identities are finite Haar pairings, not free-polynomial equality of
the original and active spatial actions. No coupling guard is required.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActiveEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (terminal_fringe_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight
  (activeSpatialWeight activeSpatialWeight_supported spatialWeight_haar_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer
  (activeTransfer activeTransfer_supported original_transfer_haar_active)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productMap_independent_of_not_mem)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight activeSpatialWeight weightedMass activeBlocks

/-- The same kinetic kernel still averages every inactive output coordinate. -/
theorem activeTransfer_fringe_independent (w : Q') (K width : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (i : Nat)
    (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i (activeTransfer w K width f) :=
  productMap_independent_of_not_mem (N width) w K (activeBlocks width)
    (activeBlocks_lt width) i (fringeBlocks_lt width i hi)
    ((fringeBlocks_mem_iff width i).mp hi).2 _
    (supported_polyMul (activeSpatialWeight_supported w K width) hf)

/-- Exact original odd-marginal mean, retaining both original terminal messages. -/
theorem marginal_mean_active (w : Q') (K width n : Nat) {b : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hi : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i b) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n) b) ≈
      quaternionHaar (N width)
        (polyMul (polyMul (activeSpatialWeight w K width)
          (polyMul (terminalMessage w K width n) (terminalMessage w K width (n+1)))) b) := by
  let g := terminalMessage w K width n
  let t := terminalMessage w K width (n+1)
  have hq : SupportedQuaternionBlocks (N width) (polyMul (polyMul g t) b) :=
    supported_polyMul (supported_polyMul (terminalMessage_supported w K width n)
      (terminalMessage_supported w K width (n+1))) hb
  have hqi : ∀ i, i ∈ fringeBlocks width →
      QuaternionBlockIndependent i (polyMul (polyMul g t) b) := fun i h =>
    quaternionBlockIndependent_polyMul
      (quaternionBlockIndependent_polyMul (terminal_fringe_independent w K width n i h)
        (terminal_fringe_independent w K width (n+1) i h)) (hi i h)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (((RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) g t).mul_right b).trans
      (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) (polyMul g t) b)))
    (Q'.eqv_trans _ _ _ (spatialWeight_haar_active w K width _ hq hqi)
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (activeSpatialWeight w K width) (polyMul g t) b).symm))

/-- The same reduction for every supported active pair, not only squares. -/
theorem marginal_pair_active (w : Q') (K width n : Nat) {b c : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hi : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i b)
    (hc : SupportedQuaternionBlocks (N width) c)
    (hj : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i c) :
    marginalPair w K width n b c ≈
      quaternionHaar (N width)
        (polyMul (polyMul (activeSpatialWeight w K width)
          (polyMul (terminalMessage w K width n) (terminalMessage w K width (n+1))))
          (polyMul b c)) :=
  marginal_mean_active w K width n (supported_polyMul hb hc)
    (fun i h => quaternionBlockIndependent_polyMul (hi i h) (hj i h))

private theorem weighted_transfer_square_active (w : Q') (K width : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hi : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    weightedMass w K width (polyMul f (transferStep w K width f)) ≈
      quaternionHaar (N width)
        (polyMul (polyMul (activeSpatialWeight w K width) f) (activeTransfer w K width f)) := by
  unfold weightedMass
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) f _).symm)
    (Q'.eqv_trans _ _ _
      (original_transfer_haar_active w K width hf hi
        (supported_polyMul (spatialWeight_supported w K width) hf))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) f _))
        (Q'.eqv_trans _ _ _
          (spatialWeight_haar_active w K width _
            (supported_polyMul hf (activeTransfer_supported w K width hf))
            (fun i h => quaternionBlockIndependent_polyMul (hi i h)
              (activeTransfer_fringe_independent w K width hf i h)))
          (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (activeSpatialWeight w K width) f _).symm))))

/-- The ORIGINAL finite energy written with the exactly integrated spatial action.
The messages are still the original T^n 1, and this identity supplies no gap. -/
theorem energy_active (w : Q') (K width n : Nat) {b : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hi : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i b) :
    energy w K width (terminalMessage w K width n) b ≈
      quaternionHaar (N width)
        (polyMul (polyMul (activeSpatialWeight w K width)
          (polyMul (terminalMessage w K width n) (terminalMessage w K width (n+1))))
          (polyMul b b)) +
      -(quaternionHaar (N width)
        (polyMul (polyMul (activeSpatialWeight w K width) (polyMul (terminalMessage w K width n) b))
          (activeTransfer w K width (polyMul (terminalMessage w K width n) b)))) := by
  have hdiag : weightedMass w K width
      (polyMul (polyMul (terminalMessage w K width n)
        (transferStep w K width (terminalMessage w K width n))) (polyMul b b)) ≈
      marginalPair w K width n b b := by
    rw [terminalMessage_next]
    unfold weightedMass marginalPair marginalWeight
    exact haar_of_coeff
      ((RatPolyCoeffEqv.mul_assoc (spatialWeight w K width)
        (polyMul (terminalMessage w K width n) (terminalMessage w K width (n+1)))
        (polyMul b b)).symm.trans
        ((RatPolyCoeffEqv.mul_assoc (spatialWeight w K width)
          (terminalMessage w K width n) (terminalMessage w K width (n+1))).symm.mul_right (polyMul b b)))
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ hdiag (marginal_pair_active w K width n hb hi hb hi))
    (Q'.neg_eqv_congr _ _ (weighted_transfer_square_active w K width
      (supported_polyMul (terminalMessage_supported w K width n) hb)
      (fun i h => quaternionBlockIndependent_polyMul (terminal_fringe_independent w K width n i h) (hi i h))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialActiveEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveEnergy.activeTransfer_fringe_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveEnergy.marginal_mean_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveEnergy.marginal_pair_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveEnergy.energy_active
