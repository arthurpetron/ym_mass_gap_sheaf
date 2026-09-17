/-
# The full-source fusion boundary under the ORIGINAL right-window partition

The two signed spin-cutoff edge terms are propagated with every remaining
spatial factor and the actual left terminal message. The right test also
retains its original action and terminal. A single-face floor eliminates
the auxiliary erased mass; the result uses the original partition squared.
Only the cutoff artefact is bounded here. The signed bulk harmonic sum,
uniform temporal decay, scaling and continuum mass gap remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSignedInputBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder
import YMGap.Continuum.BF4ExactSlabFixedSpatialFusionIdentity
import YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedInputBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder
open YMGap.Continuum.BF4ExactSlabFixedSpatialFusionIdentity (originalFusion_determinant)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headFloor headFloor_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeatFusionResidual (bulkResidual boundaryResidual)
open YMGap.Continuum.SU2QuaternionHeatFusionBoundaryTail
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks inputNumerator inputPartition transferStep terminalMessage

/-- Exactly the two fusion-boundary terms in the original first message. -/
def boundaryMessage (w : Q') (K width m : Nat) (face : Z4Plaq) : RatPoly :=
  remainderMessage w K width m face (boundaryResidual w K (plaquette width face).scalar)

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem negative_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-c) p) (polyNeg (polySmul c p)) :=
  ((RatPolyCoeffEqv.smul_coefficient
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 c)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv c)))) p).trans
    (RatPolyCoeffEqv.smul_assoc (-1) c p).symm).trans (smul_neg _)

/-- The final coefficient depends on nome, cutoff and probe cap only.
Both boundary depths, width and right-window length are arbitrary. -/
theorem fusionBoundary_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    {p : RatPoly} {c : Q'} (I : Interval ((L+1)*(N width)) p c) :
    let u := transferStep w K width (terminalMessage w K width m)
    let e := boundaryMessage w K width m face
    headFloor w * Q'.abs
      (inputNumerator w K width L n e p * inputPartition w K width L n u +
        -(inputPartition w K width L n e * inputNumerator w K width L n u p)) ≤
      (2*c*boundaryCap w K) *
        (inputPartition w K width L n u * inputPartition w K width L n u) := by
  let B := boundaryInterval (Q'.le_of_lt hw0)
    (.scalar (plaquette_supported width (N width) (Nat.le_refl _) face)
      (plaquette_unit width (N width) (Nat.le_refl _) face)) K
  let g := terminalMessage w K width m
  let u := transferStep w K width g
  let v := erasedMessage w K width m face
  let e := boundaryMessage w K width m face
  have Q : Certificate (N width) (polyAdd (polySmul (boundaryCap w K) v) (polySmul (-1) e)) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (smul_neg _))
      (remainderMessage_upper hw0 hw1 K width hK m face B)
  have F : Certificate (N width) (polyAdd u (polySmul (-(headFloor w)) v)) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (negative_smul _ _))
      (originalMessage_floor hw0 hw1 K width hK m face hf)
  exact inputCovariance_relative_bound hw0 hw1 K width hK L n
    (transferStep_supported w K width (terminalMessage_supported w K width m))
    (erasedMessage_supported w K width m face)
    (remainderMessage_supported w K width m face B.support)
    (transferStep_certificate hw0 hw1 K width hK (terminalMessage_supported w K width m)
      (terminalMessage_certificate hw0 hw1 K width hK m))
    (erasedMessage_certificate hw0 hw1 K width hK m face)
    (remainderMessage_lower hw0 hw1 K width hK m face B) Q F I
    B.nonnegative (Q'.le_of_lt (headFloor_positive hw0 hw1))

private theorem scale_positive (c : Q') (hc : (0 : Q') ≤ c) : (0 : Q') < 2*c+1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 (2*c)
      (Q'.mul_nonneg _ _ (by decide) hc)) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- The denominator 2*c+1 avoids any nonzero-probe-cap assumption. -/
def boundaryTolerance (w c : Q') (hc : (0 : Q') ≤ c) (epsilon : Q') : Q' :=
  (epsilon*headFloor w)*Q'.recipPos (2*c+1) (scale_positive c hc)

/-- Explicit original-partition cutoff; no spatial or temporal parameter occurs. -/
def relativeBoundaryCutoff (w c : Q') (hc : (0 : Q') ≤ c) (epsilon : Q') : Nat :=
  max (headCutoff w) (boundaryCutoff w (boundaryTolerance w c hc epsilon))

private theorem tolerance_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (c : Q') (hc : (0 : Q') ≤ c) (epsilon : Q') (he : (0 : Q') < epsilon) :
    (0 : Q') < boundaryTolerance w c hc epsilon :=
  Q'.mul_pos (Q'.mul_pos he (headFloor_positive hw0 hw1)) (Q'.recipPos_pos _ _)

private theorem tolerance_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (c : Q') (hc : (0 : Q') ≤ c) (epsilon : Q') (he : (0 : Q') < epsilon) :
    (2*c)*boundaryTolerance w c hc epsilon ≤ epsilon*headFloor w := by
  let r := Q'.recipPos (2*c+1) (scale_positive c hc)
  have hr : (2*c)*r ≤ 1 := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ r
      (Q'.add_le_self_of_nonneg (2*c) 1 Q'.zero_le_one)
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))
    (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ _))
  have heq : (2*c)*boundaryTolerance w c hc epsilon ≈
      (epsilon*headFloor w)*((2*c)*r) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => 2*c | 1 => epsilon*headFloor w | _ => r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hr
        (Q'.le_of_lt (Q'.mul_pos he (headFloor_positive hw0 hw1))))
      (Q'.le_of_eqv (Q'.mul_one_eqv _)))

/-- Uniform control relative to the SAME original partition squared.
Messages, reference mass and action may all change with K. No raw
unnormalized limit, signed bulk estimate or temporal decay is inferred. -/
theorem fusionBoundary_small {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (K width m L n : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    {p : RatPoly} {c : Q'} (I : Interval ((L+1)*(N width)) p c)
    (hK : relativeBoundaryCutoff w c I.nonnegative epsilon ≤ K) :
    let u := transferStep w K width (terminalMessage w K width m)
    let e := boundaryMessage w K width m face
    Q'.abs (inputNumerator w K width L n e p * inputPartition w K width L n u +
      -(inputPartition w K width L n e * inputNumerator w K width L n u p)) ≤
      epsilon*(inputPartition w K width L n u * inputPartition w K width L n u) := by
  have hhead : headCutoff w ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  have htail : boundaryCutoff w (boundaryTolerance w c I.nonnegative epsilon) ≤ K :=
    Nat.le_trans (Nat.le_max_right _ _) hK
  let u := transferStep w K width (terminalMessage w K width m)
  let Z := inputPartition w K width L n u
  have hcap := boundaryCap_small hw0 hw1 (boundaryTolerance w c I.nonnegative epsilon)
    (tolerance_positive hw0 hw1 c I.nonnegative epsilon he) K htail
  have hrate : 2*c*boundaryCap w K ≤ epsilon*headFloor w :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (2*c) hcap
        (Q'.mul_nonneg _ _ (by decide) I.nonnegative))
      (tolerance_budget hw0 hw1 c I.nonnegative epsilon he)
  have hbound := fusionBoundary_bound hw0 hw1 K width hhead m L n face hf I
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ (Z*Z) hrate
    (SumOfSquares.q_mul_self_nonneg Z)
  have hp : (epsilon*headFloor w)*(Z*Z) ≈ headFloor w*(epsilon*(Z*Z)) :=
    poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => epsilon | 1 => headFloor w | _ => Z*Z)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ hbound (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hp)))
    (headFloor_positive hw0 hw1)

/-- Direct consumer: the ORIGINAL observed/unobserved first pair differs
from its signed bulk harmonic determinant by at most epsilon*Z_original^2.
The same right window and reference message occur in both terms. -/
theorem originalFusion_bulk_error {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (K width m L n : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    {psi : RatPoly} {c : Q'} (I : Interval ((L+1)*(N width)) psi c)
    (hK : relativeBoundaryCutoff w c I.nonnegative epsilon ≤ K) :
    let U := transferStep w K width (terminalMessage w K width m)
    let F := transferStep w K width (polyMul (terminalMessage w K width m)
      (characterPolynomial (plaquette width face).scalar 1))
    let B := remainderMessage w K width m face (bulkResidual w K (plaquette width face).scalar)
    let J := fun h => inputNumerator w K width L n h psi
    let Z := inputPartition w K width L n
    Q'.abs ((J F*Z U + -(Z F*J U)) + -(J B*Z U + -(Z B*J U))) ≤
      epsilon*(Z U*Z U) := by
  let U := transferStep w K width (terminalMessage w K width m)
  let F := transferStep w K width (polyMul (terminalMessage w K width m)
    (characterPolynomial (plaquette width face).scalar 1))
  let B := remainderMessage w K width m face (bulkResidual w K (plaquette width face).scalar)
  let E := boundaryMessage w K width m face
  let J := fun h => inputNumerator w K width L n h psi
  let Z := inputPartition w K width L n
  have hs : J F*Z U + -(Z F*J U) ≈
      (J B*Z U + -(Z B*J U)) + (J E*Z U + -(Z E*J U)) :=
    originalFusion_determinant w K width m L n face hf psi
  have heq : (J F*Z U + -(Z F*J U)) + -(J B*Z U + -(Z B*J U)) ≈
      J E*Z U + -(Z E*J U) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hs (Q'.eqv_refl _))
      (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
        (.var 1) (by decide)
        (fun | 0 => J B*Z U + -(Z B*J U) | _ => J E*Z U + -(Z E*J U)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr heq))
    (fusionBoundary_small hw0 hw1 epsilon he K width m L n face hf I hK)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary.boundaryMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary.fusionBoundary_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary.boundaryTolerance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary.relativeBoundaryCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary.fusionBoundary_small
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary.originalFusion_bulk_error
