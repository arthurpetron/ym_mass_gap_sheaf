/-
# Original centered transfer quadratic as a finite window covariance

This keeps the complete spatial action, the original odd partition, and the
moving odd-marginal center.  It is a finite identity: no completed-carrier
limit or variance-relative scaling estimate is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferReserve
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindowPairing
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
  (edgeDensity edge_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindowPairing
  (edge_window_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
  (windowRatio observedMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
  (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct
  (centered_product_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_positive marginalMoment_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff lift_supported)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted normalizedMoment)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

/-- The complete spatially weighted centered transfer quadratic divided by
the SAME positive odd partition.  The source and its center are not replaced
by a bare Haar observable. -/
def normalizedCenteredTransferQuadratic {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  let g := terminalMessage w K width n
  let psi := oddCentered hw0 hw1 K width hK n f
  weightedMass w K width
      (polyMul (polyMul g psi) (transferStep w K width (polyMul g psi))) *
    Q'.recipPos (oddMass w K width n)
      (oddMass_positive hw0 hw1 K width hK n)

/-- The normalized quadratic is the literal original one-step window with
the moving odd-marginal center inserted at both endpoints. -/
theorem normalizedCenteredTransferQuadratic_window {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    normalizedCenteredTransferQuadratic hw0 hw1 K width hK n f ≈
      windowRatio hw0 hw1 K width hK n 1 n
        (polyMul (oddCentered hw0 hw1 K width hK n f)
          (liftBoundary (N width) (oddCentered hw0 hw1 K width hK n f))) := by
  let psi := oddCentered hw0 hw1 K width hK n f
  let g := terminalMessage w K width n
  let p := polyMul psi (liftBoundary (N width) psi)
  have hpsi : SupportedQuaternionBlocks (N width) psi :=
    oddCentered_supported hw0 hw1 K width hK n hf
  have hlow : SupportedQuaternionBlocks (N width+N width) psi :=
    support_mono hpsi (by omega)
  have hp : SupportedQuaternionBlocks (N width+N width) p :=
    supported_polyMul hlow (lift_supported hpsi (N width))
  have hnum : weightedMass w K width
      (polyMul (polyMul g psi) (transferStep w K width (polyMul g psi))) ≈
      weightedMass w K width (polyMul (observedMessage w K width n 1 p) g) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (edge_pairing w K width g psi psi))
      (edge_window_pairing w K width n hp)
  change weightedMass w K width
      (polyMul (polyMul g psi) (transferStep w K width (polyMul g psi))) *
        Q'.recipPos (oddMass w K width n)
          (oddMass_positive hw0 hw1 K width hK n) ≈
      weightedMass w K width (polyMul (observedMessage w K width n 1 p) g) *
        Q'.recipPos (oddMass w K width n)
          (oddMass_positive hw0 hw1 K width hK n)
  exact Q'.mul_eqv_congr_right _ _ _ hnum

/-- The moving-center quadratic is a covariance of FIXED original-window
insertions.  Both endpoint means are obtained by the proved one-step window
identities, rather than assumed equal at finite depth. -/
theorem normalizedCenteredTransferQuadratic_covariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    normalizedCenteredTransferQuadratic hw0 hw1 K width hK n f ≈
      windowRatio hw0 hw1 K width hK n 1 n
        (polyMul f (liftBoundary (N width) f)) +
        -(windowRatio hw0 hw1 K width hK n 1 n f *
          windowRatio hw0 hw1 K width hK n 1 n (liftBoundary (N width) f)) := by
  let c := normalizedMoment (N width) (marginalWeight w K width n) f
    (marginalMass_positive hw0 hw1 K width hK n)
  let m := middleRatio hw0 hw1 K width hK (n+1) n f
  have hc : c ≈ m := marginalMoment_pin hw0 hw1 K width hK n f
  have hs : RatPolyCoeffEqv (shifted f c) (shifted f m) := by
    unfold shifted
    exact (RatPolyCoeffEqv.refl _).add
      (RatPolyCoeffEqv.smul_coefficient (Q'.neg_eqv_congr _ _ hc) polyOne)
  have hp : RatPolyCoeffEqv
      (polyMul (shifted f c) (liftBoundary (N width) (shifted f c)))
      (polyMul (shifted f m) (liftBoundary (N width) (shifted f m))) :=
    hs.mul (lift_coeff (N width) hs)
  have hcenter : windowRatio hw0 hw1 K width hK n 1 n
      (polyMul (oddCentered hw0 hw1 K width hK n f)
        (liftBoundary (N width) (oddCentered hw0 hw1 K width hK n f))) ≈
      windowRatio hw0 hw1 K width hK n 1 n
        (polyMul (shifted f m) (liftBoundary (N width) (shifted f m))) := by
    exact windowRatio_congr hw0 hw1 K width hK n 1 n hp
  exact Q'.eqv_trans _ _ _
    (normalizedCenteredTransferQuadratic_window hw0 hw1 K width hK n hf)
    (Q'.eqv_trans _ _ _ hcenter (centered_product_pin hw0 hw1 K width hK n hf))

#print axioms normalizedCenteredTransferQuadratic
#print axioms normalizedCenteredTransferQuadratic_window
#print axioms normalizedCenteredTransferQuadratic_covariance

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferCovariance
