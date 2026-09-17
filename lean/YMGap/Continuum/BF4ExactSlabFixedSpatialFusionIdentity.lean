/-
# Complete heat fusion in the original transferred pair and right window

The source is the full original spatial action times the actual terminal
message. Separating one physical face and applying the finite heat fusion
identity gives an exact signed bulk plus both cutoff-boundary terms.

The determinant uses the SAME original reference message U = T g_m in
every term and the original right-window numerator and partition. There is
no erased partition, independence premise, cutoff floor, or norm estimate.
All statements are coefficient/rational identities, for every rational nome
and every cutoff, including zero. Signed bulk control remains open.
-/

import YMGap.Continuum.SU2QuaternionHeatFusionResidual
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFusionIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap kernelMap_smul)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.SU2QuaternionHeatFusionResidual
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] baseLinks spatialWeight kineticWeight activeBlocks
  terminalMessage inputNumerator inputPartition

private theorem transfer_productMap (w : Q') (K width : Nat) (input : RatPoly) :
    transferStep w K width input = productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) input) := by
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

private theorem originalProbeMessage_pin (w : Q') (K width m : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (probe : RatPoly) :
    RatPolyCoeffEqv
      (transferStep w K width (polyMul (terminalMessage w K width m) probe))
      (remainderMessage w K width m face
        (polyMul (heatPrefix w K (plaquette width face).scalar) probe)) := by
  rw [transfer_productMap]
  exact productMap_congr _ w K _
    (((spatialWeight_split w K width face hf).mul_right _).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
        (by decide) (fun
          | 0 => heatPrefix w K (plaquette width face).scalar
          | 1 => remainingSpatialWeight w K width face
          | 2 => terminalMessage w K width m
          | _ => probe)))

private theorem remainder_add (w : Q') (K width m : Nat) (face : Z4Plaq)
    (p q : RatPoly) :
    RatPolyCoeffEqv (remainderMessage w K width m face (polyAdd p q))
      (polyAdd (remainderMessage w K width m face p)
        (remainderMessage w K width m face q)) :=
  (productMap_congr _ w K _ (RatPolyCoeffEqv.mul_add_right _ p q)).trans
    (productMap_add _ w K _ _ _)

private theorem remainder_smul (w : Q') (K width m : Nat) (face : Z4Plaq)
    (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (remainderMessage w K width m face (polySmul c p))
      (polySmul c (remainderMessage w K width m face p)) :=
  (productMap_congr _ w K _ (RatPolyCoeffEqv.polyMul_smul_right c _ p)).trans
    (kernelMap_smul _ _ c _)

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1))*weight []+0 ≈ ((-c)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl _)

private theorem centered_product (h p : RatPoly) (c : Q') :
    RatPolyCoeffEqv (polyAdd (polyMul h p) (polySmul (-c) h))
      (polyMul (polyAdd p (polyNeg (cap c))) h) := by
  have he := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 1) (.var 2)) (.var 0))
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 0)))
    (by decide) (fun | 0 => h | 1 => p | _ => cap (-c))
  exact ((((RatPolyCoeffEqv.refl p).add (cap_neg c)).mul_right h).trans
    (he.trans ((RatPolyCoeffEqv.refl _).add (cap_mul_left (-c) h)))).symm

/-- The complete fusion residual of the actual first transferred pair.
No other spatial factor or terminal-message dependence is removed. -/
theorem originalFusion_message (w : Q') (K width m : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    RatPolyCoeffEqv
      (polyAdd
        (transferStep w K width (polyMul (terminalMessage w K width m)
          (characterPolynomial (plaquette width face).scalar 1)))
        (polySmul (-coeffW w 1) (transferStep w K width (terminalMessage w K width m))))
      (polyAdd
        (remainderMessage w K width m face (bulkResidual w K (plaquette width face).scalar))
        (remainderMessage w K width m face (boundaryResidual w K (plaquette width face).scalar))) := by
  let x := (plaquette width face).scalar
  let H := heatPrefix w K x
  let p := characterPolynomial x 1
  let c := coeffW w 1
  have hs : RatPolyCoeffEqv (polyAdd (polyMul H p) (polySmul (-c) H))
      (polyAdd (bulkResidual w K x) (boundaryResidual w K x)) :=
    (centered_product H p c).trans (heat_fusion_residual w K x)
  exact ((originalProbeMessage_pin w K width m face hf p).add
    ((originalMessage_pin w K width m face hf).smul (-c))).trans
    (((RatPolyCoeffEqv.refl _).add (remainder_smul w K width m face (-c) H).symm).trans
      ((remainder_add w K width m face (polyMul H p) (polySmul (-c) H)).symm.trans
        ((productMap_congr _ w K _ (hs.mul_left (remainderSource w K width m face))).trans
          (remainder_add w K width m face _ _))))

-- Scalar cancellation is normalized before any original message is substituted.
private theorem determinant_split (A X Y Z B C D E c : Q')
    (hJ : A + (-c)*Y ≈ B+C) (hZ : X + (-c)*Z ≈ D+E) :
    A*Z + -(X*Y) ≈ (B*Z + -(D*Y)) + (C*Z + -(E*Y)) := by
  have he : A*Z + -(X*Y) ≈ (A+(-c)*Y)*Z + -((X+(-c)*Z)*Y) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2))))
      (.add (.mul (.add (.var 0) (.mul (.neg (.var 4)) (.var 2))) (.var 3))
        (.neg (.mul (.add (.var 1) (.mul (.neg (.var 4)) (.var 3))) (.var 2))))
      (by decide) (fun | 0 => A | 1 => X | 2 => Y | 3 => Z | _ => c)
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hJ)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hZ)))
    (poly_identity_of_normal_eq
      (.add (.mul (.add (.var 0) (.var 1)) (.var 4))
        (.neg (.mul (.add (.var 2) (.var 3)) (.var 5))))
      (.add (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 2) (.var 5))))
        (.add (.mul (.var 1) (.var 4)) (.neg (.mul (.var 3) (.var 5)))))
      (by decide) (fun | 0 => B | 1 => C | 2 => D | 3 => E | 4 => Z | _ => Y)))

/-- Exact signed bulk/boundary split in the original right-window determinant.
Every term uses U = T g_m as reference and its SAME original partition Z(U). -/
theorem originalFusion_determinant (w : Q') (K width m L n : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (psi : RatPoly) :
    let U := transferStep w K width (terminalMessage w K width m)
    let F := transferStep w K width (polyMul (terminalMessage w K width m)
      (characterPolynomial (plaquette width face).scalar 1))
    let B := remainderMessage w K width m face (bulkResidual w K (plaquette width face).scalar)
    let E := remainderMessage w K width m face (boundaryResidual w K (plaquette width face).scalar)
    let J := fun h => inputNumerator w K width L n h psi
    let Z := inputPartition w K width L n
    J F * Z U + -(Z F * J U) ≈
      (J B * Z U + -(Z B * J U)) + (J E * Z U + -(Z E * J U)) := by
  let U := transferStep w K width (terminalMessage w K width m)
  let F := transferStep w K width (polyMul (terminalMessage w K width m)
    (characterPolynomial (plaquette width face).scalar 1))
  let B := remainderMessage w K width m face (bulkResidual w K (plaquette width face).scalar)
  let E := remainderMessage w K width m face (boundaryResidual w K (plaquette width face).scalar)
  let J := fun h => inputNumerator w K width L n h psi
  let Z := inputPartition w K width L n
  let c := coeffW w 1
  have hp : RatPolyCoeffEqv (polyAdd F (polySmul (-c) U)) (polyAdd B E) :=
    originalFusion_message w K width m face hf
  have hJ : J F + (-c)*J U ≈ J B+J E :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (inputNumerator_add w K width L n F (polySmul (-c) U) psi)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (inputNumerator_smul w K width L n (-c) U psi))))
      (Q'.eqv_trans _ _ _ (inputNumerator_congr w K width L n hp psi)
        (inputNumerator_add w K width L n B E psi))
  have hZ : Z F + (-c)*Z U ≈ Z B+Z E :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (inputPartition_add w K width L n F (polySmul (-c) U))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (inputPartition_smul w K width L n (-c) U))))
      (Q'.eqv_trans _ _ _ (inputPartition_congr w K width L n hp)
        (inputPartition_add w K width L n B E))
  exact determinant_split (J F) (Z F) (J U) (Z U) (J B) (J E) (Z B) (Z E) c hJ hZ

end YMGap.Continuum.BF4ExactSlabFixedSpatialFusionIdentity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFusionIdentity.originalFusion_message
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFusionIdentity.originalFusion_determinant
