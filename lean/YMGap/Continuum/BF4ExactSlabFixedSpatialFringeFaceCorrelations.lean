/-
# Exact connected-correlation cancellation after a fringe-face insertion

The literal first-transfer identity propagates through every later original
transfer by weighted symmetry. Its Haar-tested equality is never promoted
to coefficient equality. The original finite-window joint and both marginal
ratios have the SAME partition; their connected combination is exactly zero.

All widths, terminal depths and positive separations are included, but only
faces with an inactive fringe link. The fully active bulk interaction is
not estimated. Positivity enters only the existing partition normalization.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceCorrelations

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (iterateStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (observedMessage windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput (inputNumerator inputPartition)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary (inputPartition_terminal_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction (windowMessage windowMessage_iterate)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] weightedMass baseLinks spatialWeight kineticWeight

private theorem weighted_first_pair (w : Q') (K width m : Nat) (hK : 1 ≤ K)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width) (ha : ¬ FullyActive width face)
    (s : RatPoly) (hs : SupportedQuaternionBlocks (N width) s) :
    weightedMass w K width (polyMul s (transferStep w K width
      (polyMul (terminalMessage w K width m) (characterPolynomial (plaquette width face).scalar 1)))) ≈
    coeffW w 1 * weightedMass w K width
      (polyMul s (transferStep w K width (terminalMessage w K width m))) := by
  have h := inactive_fundamental_transfer_pair w K width m hK hf ha
    (polyMul (spatialWeight w K width) s) (supported_polyMul (spatialWeight_supported w K width) hs)
  unfold weightedMass
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
    (Q'.eqv_trans _ _ _ h
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))))

/-- All positive transfer powers retain the same scalar multiple of the
unobserved message, in the original weighted pairing with arbitrary s. -/
theorem inactive_fundamental_iterate_pair (w : Q') (K width m r : Nat) (hK : 1 ≤ K)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width) (ha : ¬ FullyActive width face)
    (s : RatPoly) (hs : SupportedQuaternionBlocks (N width) s) :
    weightedMass w K width (polyMul s
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) (r+1)
        (polyMul (terminalMessage w K width m) (characterPolynomial (plaquette width face).scalar 1)))) ≈
      coeffW w 1 * weightedMass w K width
        (polyMul s (terminalMessage w K width (m+(r+1)))) := by
  let g := terminalMessage w K width m
  let chi := characterPolynomial (plaquette width face).scalar 1
  let S := iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) r s
  have hg := terminalMessage_supported w K width m
  have hc := SU2QuaternionRelativeHeatPairGeometry.character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hS := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) r hs
  have hleft := iterateStep_weighted_symmetric w K width r
    (transferStep_supported w K width (supported_polyMul hg hc)) hs
  have hright := iterateStep_weighted_symmetric w K width r
    (transferStep_supported w K width hg) hs
  have ht : iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) r
      (transferStep w K width g) = terminalMessage w K width (m+(r+1)) :=
    (iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) m (r+1) polyOne).symm
  have hm := weighted_first_pair w K width m hK hf ha S hS
  have hcomm (a b : RatPoly) := weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm a b)
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (hcomm _ _)
      (Q'.eqv_trans _ _ _ hm
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (hcomm _ _) (by rw [← ht]; exact Q'.eqv_symm hright)))))

private theorem iterate_congr (blocks : Nat) (kernel weight : RatPoly) :
    (n : Nat) → {p q : RatPoly} → RatPolyCoeffEqv p q →
      RatPolyCoeffEqv (iterateStep blocks kernel weight n p) (iterateStep blocks kernel weight n q)
  | 0, _, _, h => h
  | n+1, _, _, h => iterate_congr blocks kernel weight n
      (partialHaarHeads_congr blocks ((h.mul_left weight).mul_left kernel))

private theorem separated_pair (w : Q') (K width m r : Nat) (hK : 1 ≤ K)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width) (ha : ¬ FullyActive width face)
    (s : RatPoly) (hs : SupportedQuaternionBlocks (N width) s) :
    weightedMass w K width (polyMul s
      (separatedMessage w K width m 0 (r+1) (characterPolynomial (plaquette width face).scalar 1))) ≈
      coeffW w 1 * weightedMass w K width
        (polyMul s (terminalMessage w K width (m+(r+1)))) := by
  have he := iterate_congr (N width) (kineticWeight w K width) (spatialWeight w K width) (r+1)
    (windowMessage_iterate (N width) (kineticWeight w K width) (spatialWeight w K width) 0
      (terminalMessage w K width m) (characterPolynomial (plaquette width face).scalar 1))
  exact Q'.eqv_trans _ _ _ (weightedMass_congr w K width (he.mul_left s))
    (inactive_fundamental_iterate_pair w K width m r hK hf ha s hs)

private theorem input_numerator_zero (w : Q') (K width n : Nat) (h q : RatPoly) :
    inputNumerator w K width 0 n h q ≈
      weightedMass w K width (polyMul (polyMul (terminalMessage w K width n) q) h) :=
  weightedMass_congr w K width
    (((windowMessage_iterate (N width) (kineticWeight w K width) (spatialWeight w K width) 0 h q).mul_right
      (terminalMessage w K width n)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 2) (.var 1)) (.var 0))
        (by decide) (fun | 0 => h | 1 => q | _ => terminalMessage w K width n)))

/-- Joint numerator factorization before any division, with both original
boundary messages and arbitrary supported right endpoint probe retained. -/
theorem inactive_input_numerator (w : Q') (K width m r n : Nat) (hK : 1 ≤ K)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width) (ha : ¬ FullyActive width face)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    inputNumerator w K width 0 n
      (separatedMessage w K width m 0 (r+1) (characterPolynomial (plaquette width face).scalar 1)) q ≈
      coeffW w 1 * inputNumerator w K width 0 n (terminalMessage w K width (m+(r+1))) q :=
  Q'.eqv_trans _ _ _ (input_numerator_zero w K width n _ q)
    (Q'.eqv_trans _ _ _
      (separated_pair w K width m r hK hf ha (polyMul (terminalMessage w K width n) q)
        (supported_polyMul (terminalMessage_supported w K width n) hq))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (input_numerator_zero w K width n _ q))))

/-- The left numerator is the SAME original partition times the same
fundamental coefficient; it is not normalized by an observed mass. -/
theorem inactive_input_partition (w : Q') (K width m r n : Nat) (hK : 1 ≤ K)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width) (ha : ¬ FullyActive width face) :
    inputPartition w K width 0 n
      (separatedMessage w K width m 0 (r+1) (characterPolynomial (plaquette width face).scalar 1)) ≈
      coeffW w 1 * inputPartition w K width 0 n (terminalMessage w K width (m+(r+1))) :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _
      (separated_pair w K width m r hK hf ha (terminalMessage w K width n)
        (terminalMessage_supported w K width n))
      (Q'.mul_eqv_congr_left _ _ _ (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _))))

/-- Exact connected covariance zero for a literal inactive face and every
supported endpoint probe at every positive gap, in the ORIGINAL window law. -/
theorem window_connected_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (m r n : Nat)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width) (ha : ¬ FullyActive width face)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let chi := characterPolynomial (plaquette width face).scalar 1
    let right := liftBoundary ((r+1)*(N width)) q
    windowRatio hw0 hw1 K width hK m (r+1) n (polyMul chi right) +
      -(windowRatio hw0 hw1 K width hK m (r+1) n chi *
        windowRatio hw0 hw1 K width hK m (r+1) n right) ≈ 0 := by
  let chi := characterPolynomial (plaquette width face).scalar 1
  let u := terminalMessage w K width (m+(r+1))
  let Z := inputPartition w K width 0 n u
  have hZ := inputPartition_terminal_positive hw0 hw1 K width hK 0 n (m+(r+1))
  let zinv := Q'.recipPos Z hZ
  let C := inputNumerator w K width 0 n u q
  let c := coeffW w 1
  have hj := windowRatio_separated_joint hw0 hw1 K width hK m 0 (r+1) 0 n chi q hZ
  have hl := windowRatio_separated_left hw0 hw1 K width hK m 0 (r+1) 0 n chi hZ
  have hr := windowRatio_separated_right hw0 hw1 K width hK m 0 (r+1) 0 n q hZ
  simp only [Nat.zero_add, Nat.add_zero] at hj hl hr
  have hA := inactive_input_numerator w K width m r n hK1 hf ha q hq
  have hB := inactive_input_partition w K width m r n hK1 hf ha
  have hjc : windowRatio hw0 hw1 K width hK m (r+1) n
      (polyMul chi (liftBoundary ((r+1)*(N width)) q)) ≈ c*(C*zinv) :=
    Q'.eqv_trans _ _ _ hj (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ zinv hA) (Q'.mul_assoc_eqv c C zinv))
  have hlc : windowRatio hw0 hw1 K width hK m (r+1) n chi ≈ c :=
    Q'.eqv_trans _ _ _ hl (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ zinv hB) (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv c Z zinv) (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv Z hZ)) (Q'.mul_one_eqv c))))
  have hprod := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hlc)
    (Q'.mul_eqv_congr_left c _ _ hr)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hjc (Q'.neg_eqv_congr _ _ hprod))
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => c*(C*zinv)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceCorrelations

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceCorrelations.inactive_fundamental_iterate_pair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceCorrelations.inactive_input_numerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceCorrelations.inactive_input_partition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceCorrelations.window_connected_zero
