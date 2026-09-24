/-
# Centered angular identity in the SAME original odd-time marginal

The weight is the existing `marginalWeight = V*g_n*g_(n+1)`, not
`(V*g_n)^2`. A selected-link permutation preserves its actual partition
and every original middle moment. The head-linear Ward identity therefore
has the original centered `middleRatio` variance on its right side.

The signed derivative of the COMPLETE marginal remains on the left. No
stationary-message relation, residual sign/size, temporal energy bound,
spatial/spacing estimate or continuum survival is assumed or concluded.
-/

import YMGap.Continuum.QuaternionHaarCenteredLinearWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarCenteredLinearWard

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks terminalMessage

/-- Reindex the existing marginal; do not create an alternative density. -/
def frameWeight (w : Q') (K width n : Nat)
    (swap : QuaternionBlockInvolution (N width)) : RatPoly :=
  reindexQuaternionPolynomial swap (marginalWeight w K width n)

theorem frameMass_pin (w : Q') (K width n : Nat)
    (swap : QuaternionBlockInvolution (N width)) :
    quaternionHaar (N width) (frameWeight w K width n swap) ≈
      oddMass w K width n := by
  refine Q'.eqv_trans _ _ _
    (quaternionHaar_reindex swap _ (marginalWeight_supported w K width n)) ?_
  unfold marginalWeight oddMass weightedMass
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
    (fun | 0 => spatialWeight w K width
         | 1 => terminalMessage w K width n
         | _ => terminalMessage w K width (n+1)))

theorem frameMass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (swap : QuaternionBlockInvolution (N width)) :
    (0 : Q') < quaternionHaar (N width) (frameWeight w K width n swap) :=
  HeatKernelRGStep.lt_of_lt_of_le (oddMass_positive hw0 hw1 K width hK n)
    (Q'.ge_of_eqv (frameMass_pin w K width n swap))

/-- Each frame moment is the pre-existing normalized original chain moment. -/
theorem frameMoment_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (swap : QuaternionBlockInvolution (N width)) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p) :
    normalizedMoment (N width) (frameWeight w K width n swap)
        (reindexQuaternionPolynomial swap p)
        (frameMass_positive hw0 hw1 K width hK n swap) ≈
      middleRatio hw0 hw1 K width hK (n+1) n p := by
  have hnum := quaternionHaar_reindex swap
    (polyMul (marginalWeight w K width n) p)
    (supported_polyMul (marginalWeight_supported w K width n) hp)
  rw [reindexQuaternionPolynomial_mul] at hnum
  have hraw : quaternionHaar (N width) (polyMul (marginalWeight w K width n) p) ≈
      weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width (n+1)) p)
          (terminalMessage w K width n)) := by
    unfold marginalWeight weightedMass
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.var 1))) (by decide)
      (fun | 0 => spatialWeight w K width
           | 1 => terminalMessage w K width n
           | 2 => terminalMessage w K width (n+1)
           | _ => p))
  have hrec := Q'.recipPos_eqv_congr _ _
    (frameMass_positive hw0 hw1 K width hK n swap)
    (oddMass_positive hw0 hw1 K width hK n)
    (frameMass_pin w K width n swap)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ hnum hraw))
    (Q'.mul_eqv_congr_left _ _ _ hrec)

theorem frameVariance_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (swap : QuaternionBlockInvolution (N width)) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p) :
    normalizedVariance (N width) (frameWeight w K width n swap)
        (reindexQuaternionPolynomial swap p)
        (frameMass_positive hw0 hw1 K width hK n swap) ≈
      middleRatio hw0 hw1 K width hK (n+1) n (polyMul p p) +
        -(middleRatio hw0 hw1 K width hK (n+1) n p *
          middleRatio hw0 hw1 K width hK (n+1) n p) := by
  have h1 := frameMoment_pin hw0 hw1 K width hK n swap p hp
  have h2 := frameMoment_pin hw0 hw1 K width hK n swap (polyMul p p)
    (supported_polyMul hp hp)
  rw [reindexQuaternionPolynomial_mul] at h2
  exact Q'.add_eqv_congr' h2 (Q'.neg_eqv_congr _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h1)
      (Q'.mul_eqv_congr_left _ _ _ h1)))

/-- The signed source term and angular energy equal three times the actual
odd partition times the actual original centered variance. -/
theorem frame_centered_ward {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (swap : QuaternionBlockInvolution (N width)) (hN : 0 < N width)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p)
    (hlinear : HasQuaternionBlockDegree 0 1 (reindexQuaternionPolynomial swap p)) :
    let W := frameWeight w K width n swap
    let f := reindexQuaternionPolynomial swap p
    let c := normalizedMoment (N width) W f (frameMass_positive hw0 hw1 K width hK n swap)
    quaternionHaar (N width) (polyMul W (angularSquare f)) +
        centeredLinearWardResidual (N width-1) W f c ≈
      3 * (oddMass w K width n *
        (middleRatio hw0 hw1 K width hK (n+1) n (polyMul p p) +
          -(middleRatio hw0 hw1 K width hK (n+1) n p *
            middleRatio hw0 hw1 K width hK (n+1) n p))) := by
  have hlen : N width-1+1 = N width := Nat.sub_add_cancel hN
  have hZ : (0 : Q') < quaternionHaar (N width-1+1) (frameWeight w K width n swap) := by
    rw [hlen]
    exact frameMass_positive hw0 hw1 K width hK n swap
  have h := centered_linear_ward_own_mean (N width-1) (frameWeight w K width n swap)
    (reindexQuaternionPolynomial swap p) hZ hlinear
  simp only [hlen] at h
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left 3 _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (frameMass_pin w K width n swap))
      (Q'.mul_eqv_congr_left _ _ _ (frameVariance_pin hw0 hw1 K width hK n swap p hp))))

/-- Concrete original plaquette instance: incidence supplies degree one and
the carrier is nonempty by the selected physical link, with no degree input. -/
theorem plaquette_centered_ward {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width)
    {link : Z4Link} (hl : link ∈ edgesOf face) :
    let swap := headSwapBlockInvolution (N width) ((baseLinks width).idxOf link)
      (List.idxOf_lt_length_of_mem (incident_mem_baseLinks hf hl))
    let p := characterPolynomial (plaquette width face).scalar 1
    let W := frameWeight w K width n swap
    let f := reindexQuaternionPolynomial swap p
    let c := normalizedMoment (N width) W f (frameMass_positive hw0 hw1 K width hK n swap)
    quaternionHaar (N width) (polyMul W (angularSquare f)) +
        centeredLinearWardResidual (N width-1) W f c ≈
      3 * (oddMass w K width n *
        (middleRatio hw0 hw1 K width hK (n+1) n (polyMul p p) +
          -(middleRatio hw0 hw1 K width hK (n+1) n p *
            middleRatio hw0 hw1 K width hK (n+1) n p))) := by
  have hlink := incident_mem_baseLinks hf hl
  have hidx := List.idxOf_lt_length_of_mem hlink
  exact frame_centered_ward hw0 hw1 K width hK n
    (headSwapBlockInvolution (N width) ((baseLinks width).idxOf link) hidx)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) hidx)
    (characterPolynomial (plaquette width face).scalar 1)
    (SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1)
    (plaquette_character_head_degree width hf hl)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard.frameMass_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard.frameMass_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard.frameMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard.frameVariance_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard.frame_centered_ward
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard.plaquette_centered_ward
