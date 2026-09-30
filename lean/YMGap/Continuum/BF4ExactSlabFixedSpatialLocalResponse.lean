/-
# Width-independent positive one-step response of an active original face

The original endpoint band, exact spectator-modulated dual preimage and
one-edge Haar moments retain the SAME exterior kinetic quadratic. It cancels
against the original odd partition. The displayed floor depends on the nome,
not spatial width, terminal depth or late heat cutoff. No spatial-limit
construction, scaling survival, upper decay estimate or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorPartition
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments
import YMGap.Continuum.RationalCommonQuadraticResponse

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost (inverseRate costCap costCap_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatLocalBand (erasedCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex mem_of_mem_erase)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RationalCommonQuadraticResponse

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage

private theorem haar_smul_left (blocks : Nat) (c : Q') (p q : RatPoly) :
    quaternionHaar blocks (polyMul (polySmul c p) q) ≈
      c * quaternionHaar blocks (polyMul p q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right blocks c q p)
      (Q'.mul_eqv_congr_left c _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm q p))))

/-- Explicit fixed-nome floor; neither volume nor terminal depth occurs. -/
def localResponseFloor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Q' :=
  Q'.divPos (localLower w 4 * localLower w 4)
    (costCap hw0 * (localUpper w 4 * localUpper w 4))
    (Q'.mul_pos (costCap_positive hw0)
      (Q'.mul_pos (localUpper_positive hw0 hw1 4) (localUpper_positive hw0 hw1 4)))

theorem localResponseFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < localResponseFloor hw0 hw1 :=
  Q'.mul_pos (Q'.mul_pos (localLower_positive hw0 hw1 4) (localLower_positive hw0 hw1 4))
    (Q'.recipPos_pos _ _)

/-- The literal original one-step window has a positive floor independent of
width, depth and late cutoff, for any center in the character interval. -/
theorem localResponseFloor_le_window {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat)
    (m : Q') (hm0 : -(2 : Q') ≤ m) (hm1 : m ≤ (2 : Q')) :
    localResponseFloor hw0 hw1 ≤
      windowRatio hw0 hw1 K width hK (n+1) 1 (n+1)
        (polyMul (source width face m) (liftBoundary (N width) (source width face m))) := by
  let A := spectator w K width n (edgesOf face)
  let l : Z4Link := (face.1, (dirsOf face.2).1)
  have hl : l ∈ edgesOf face := by simp [l, edgesOf]
  let i := (baseLinks width).idxOf l
  let ids := eraseIndex i (activeBlocks width)
  let R := productMap (N width) w K ids A
  let h := source width face m
  let d := dualTest hw0 width face m
  let b := polyMul d A
  let u := weightedSource w K width (n+1) h
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width (n+1))
  let Q := quaternionHaar (N width) (polyMul A R)
  let D := kineticPair (N width) w K (activeBlocks width) u b
  let NN := kineticPair (N width) w K (activeBlocks width) u u
  have hA := spectator_supported w K width n (edgesOf face)
  have hAI : ∀ l, l ∈ edgesOf face → QuaternionBlockIndependent ((baseLinks width).idxOf l) A :=
    fun l hl => spectator_independent w K width n (edgesOf face) l hl (face_link_mem_base hf hl)
  have hids : ∀ j, j ∈ ids → j < N width :=
    fun j hj => activeBlocks_lt width j (mem_of_mem_erase i hj)
  have hR : SupportedQuaternionBlocks (N width) R := productMap_supported _ w K ids hids hA
  have hAR := supported_polyMul hA hR
  have hErase := active_erased_spectator width w K i (hactive l hl) A hA (hAI l hl)
  have hARI : QuaternionBlockIndependent i (polyMul A R) :=
    quaternionBlockIndependent_polyMul (hAI l hl) hErase.2
  have hh := source_supported width face m
  have hd := dualTest_supported hw0 width face m
  have hb := supported_polyMul hd hA
  have hu := weightedSource_supported w K width (n+1) hh
  have CA := spectator_certificate hw0 hw1 K width hK n (edgesOf face)
  have CR := erasedCertificate (N width) hw0 hw1 K hK ids hids hA CA
  have hQ : (0 : Q') ≤ Q := (CA.mul CR).haar_nonnegative
  have hpre : SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width) b) (polyMul h R) :=
    (plaquette_spectator_dual_preimage hw0 width face hf hactive K hK1 A hA hAI m).trans
      ((SupportedHaarEqv.refl (N width) h).mul hErase.1
        (productMap_supported _ w K _ (activeBlocks_lt width) hA) hh)
  have hquad : kineticPair (N width) w K (activeBlocks width) A A ≈ Q := hErase.1 A hA
  have hpartition : oddMass w K width (n+1) ≤ (localUpper w 4 * localUpper w 4)*Q :=
    Q'.le_trans' _ _ _ (oddMass_spectator_cap hw0 hw1 K width hK n face)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hquad))
  have hcost : kineticPair (N width) w K (activeBlocks width) b b ≈
      (inverseRate hw0 + m*m)*Q :=
    Q'.eqv_trans _ _ _ (hpre b hb)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => d | 1 => A | 2 => h | _ => R)))
        (dual_source_moment hw0 hf l hl (polyMul A R) hAR hARI m))
  have hdet : D ≈ quaternionHaar (N width) (polyMul a (polyMul (polyMul h h) R)) :=
    Q'.eqv_trans _ _ _ (hpre u hu)
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.var 2) (.var 2)) (.var 3)))
        (by decide) (fun
          | 0 => spatialWeight w K width
          | 1 => terminalMessage w K width (n+1)
          | 2 => h
          | _ => R)))
  have hsize : (edgesOf face).length ≤ 4 := by simp [edgesOf]
  have hband := haar_order
    (endpoint_localLowerCertificate hw0 hw1 K width hK n (edgesOf face) 4 hsize)
    ((Certificate.square h hh).mul CR)
  have hlower : quaternionHaar (N width)
      (polyMul (polySmul (localLower w 4) A) (polyMul (polyMul h h) R)) ≈
      (localLower w 4) * (((1 : Q') + m*m)*Q) :=
    Q'.eqv_trans _ _ _ (haar_smul_left _ _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
          (by decide) (fun | 0 => A | 1 => h | _ => R)))
        (shifted_square_moment hf l hl (polyMul A R) hAR hARI m)))
  have h1 : (1 : Q') ≤ 1+m*m := Q'.add_le_self_of_nonneg 1 _ (SumOfSquares.q_mul_self_nonneg m)
  have hQle : Q ≤ (1+m*m)*Q :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv Q))
      (Q'.mul_le_mul_of_nonneg_right _ _ Q h1 hQ)
  have hD : localLower w 4 * Q ≤ D :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (localLower w 4) hQle
        (Q'.le_of_lt (localLower_positive hw0 hw1 4)))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hlower)
        (Q'.le_trans' _ _ _ hband (Q'.ge_of_eqv hdet)))
  have hsquare : m*m ≤ (2 : Q')*2 :=
    Q'.mul_le_of_bounds (by decide) (by decide) hm0 hm1 hm0 hm1
  have hcostScalar : inverseRate hw0 + m*m ≤ costCap hw0 :=
    Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hsquare (by decide : (2 : Q')*2 ≤ 5))
  have hNN : (0 : Q') ≤ NN :=
    kineticPair_nonnegative _ w (Q'.le_of_lt hw0) K _ (activeBlocks_lt width) u hu
  have hcs : D*D ≤ NN*(costCap hw0*Q) :=
    Q'.le_trans' _ _ _
      (kineticPair_cauchySchwarz _ w (Q'.le_of_lt hw0) K _ (activeBlocks_lt width) u b hu hb)
      (Q'.mul_le_mul_of_nonneg_left _ _ NN
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcost)
          (Q'.mul_le_mul_of_nonneg_right _ _ Q hcostScalar hQ)) hNN)
  have hfinal := common_quadratic_response_ratio (localLower w 4) (localUpper w 4)
    (costCap hw0) (oddMass w K width (n+1)) Q D NN
    (localLower_positive hw0 hw1 4) (localUpper_positive hw0 hw1 4)
    (costCap_positive hw0) (oddMass_positive hw0 hw1 K width hK (n+1))
    hQ hD hpartition hcs
  exact Q'.le_trans' _ _ _ hfinal
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (response_numerator_pin w K width (n+1) hh)))

#print axioms localResponseFloor
#print axioms localResponseFloor_positive
#print axioms localResponseFloor_le_window

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalResponse
