/-
# Original growing-square energy as a signed heat multiplication defect

The original unprojected endpoint q=V*terminalMessage is retained. Its
active product heat, OWN odd-marginal center, variance and partition are
the same throughout. The signed pairing is computed, not assumed small
or nonnegative. No local band, source independence, channel decomposition,
variance inverse or scaling/survival conclusion is used.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect
import YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse

namespace YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment sourceEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (energy_source_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (oddMoment_unprojected_source centered_unprojected_square energy_shifted)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage sourceCharacter energy

/-- Computed polynomial on the ORIGINAL active heat and unprojected source. -/
def squareHeatMultiplicationDefect (w : Q') (K width depth scale : Nat)
    (hwidth : side scale < width) : RatPoly :=
  multiplicationDefect (N width) w K (activeBlocks width)
    (endpointSource w K width (terminalMessage w K width depth))
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
    (qpow w (12*side scale))

theorem squareHeatMultiplicationDefect_supported (w : Q') (K width depth scale : Nat)
    (hwidth : side scale < width) :
    SupportedQuaternionBlocks (N width)
      (squareHeatMultiplicationDefect w K width depth scale hwidth) :=
  multiplicationDefect_supported (N width) w K (activeBlocks width)
    (activeBlocks_lt width) _ _ _
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
    (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1)

/-- Actual SIGNED Haar pairing at the OWN original marginal center. -/
def squareSignedHeatDefect {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  H width (polyMul
    (polyMul (endpointSource w K width (terminalMessage w K width depth))
      (oddCentered hw0 hw1 K width hK depth f))
    (squareHeatMultiplicationDefect w K width depth scale hwidth))

private theorem shifted_original_mean_zero (blocks : Nat) (W f : RatPoly)
    (hZ : (0 : Q') < quaternionHaar blocks W) :
    quaternionHaar blocks (polyMul W (shifted f (normalizedMoment blocks W f hZ))) ≈ 0 := by
  let m := normalizedMoment blocks W f hZ
  have hm : m*quaternionHaar blocks W ≈ quaternionHaar blocks (polyMul W f) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ hZ)))
        (Q'.mul_one_eqv _))
  have hp := Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right blocks 1 W f)
    (Q'.one_mul_eqv _)
  have hc : quaternionHaar blocks (polyMul W (polySmul (-m) polyOne)) ≈
      -(quaternionHaar blocks (polyMul W f)) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right blocks (-m) W polyOne)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (-m) _ _
        (haar_of_coeff (blocks := blocks) (RatPolyCoeffEqv.mul_one W)))
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.var 1))
            (.neg (.mul (.var 0) (.var 1))) (by decide)
            (fun | 0 => m | _ => quaternionHaar blocks W))
          (Q'.neg_eqv_congr _ _ hm)))
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_add_right blocks W (polySmul 1 f) (polySmul (-m) polyOne))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp hc)
      (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
        (by decide) (fun _ => quaternionHaar blocks (polyMul W f))))

/-- SAME original source first moment at its OWN center; no raw mean is used. -/
theorem paddedSquare_centered_source_firstMoment_zero {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (depth scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    sourceMoment (N width) w K (activeBlocks width)
      (endpointSource w K width (terminalMessage w K width depth))
      (oddCentered hw0 hw1 K width hK depth f) ≈ 0 := by
  dsimp only
  exact Q'.eqv_trans _ _ _
    (oddMoment_unprojected_source w K width depth _).symm
    (shifted_original_mean_zero (N width) (marginalWeight w K width depth) _
      (marginalMass_positive hw0 hw1 K width hK depth))

/-- COMPLETE original energy, without K>=1/K>=2 or a sign assumption. -/
theorem paddedSquare_energy_signedHeatDefect_identity {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (depth scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    energy w K width (terminalMessage w K width depth) f ≈
      (1-qpow w (12*side scale))*(oddMass w K width depth*
        oddVariance hw0 hw1 K width hK depth f)-
      squareSignedHeatDefect hw0 hw1 K width hK depth scale hwidth := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let mu := normalizedMoment (N width) (marginalWeight w K width depth) f
    (marginalMass_positive hw0 hw1 K width hK depth)
  let psi := shifted f mu
  let q := endpointSource w K width (terminalMessage w K width depth)
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have he := Q'.eqv_trans _ _ _
    (energy_shifted w K width (terminalMessage_supported w K width depth) hf mu).symm
    (energy_source_pin w K width (terminalMessage w K width depth) psi)
  have hzero : sourceMoment (N width) w K (activeBlocks width) q psi ≈ 0 :=
    paddedSquare_centered_source_firstMoment_zero hw0 hw1 K width hK depth scale hwidth
  have hc := sourceEnergy_centered_multiplicationDefect (N width) w K
    (activeBlocks width) q f (qpow w (12*side scale)) mu hzero
  have hs := centered_unprojected_square hw0 hw1 K width hK depth hf
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hc
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left (1-qpow w (12*side scale)) _ _ hs)
      (Q'.eqv_refl _)))

attribute [local irreducible] oddMass oddVariance normalizedEnergy squareSignedHeatDefect

/-- Divide only by the SAME positive original partition. This exact identity
retains a favorable or unfavorable signed defect without absolute values. -/
theorem paddedSquare_normalizedEnergy_signedHeatDefect_identity {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (depth scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    normalizedEnergy hw0 hw1 K width hK depth f ≈
      (1-qpow w (12*side scale))*oddVariance hw0 hw1 K width hK depth f-
      squareSignedHeatDefect hw0 hw1 K width hK depth scale hwidth*
        Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let Z := oddMass w K width depth
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK depth)
  let V := oddVariance hw0 hw1 K width hK depth f
  let s := 1-qpow w (12*side scale)
  let M := squareSignedHeatDefect hw0 hw1 K width hK depth scale hwidth
  unfold normalizedEnergy
  change energy w K width (terminalMessage w K width depth) f*r ≈ s*V-M*r
  have he : energy w K width (terminalMessage w K width depth) f ≈ s*(Z*V)-M :=
    paddedSquare_energy_signedHeatDefect_identity hw0 hw1 K width hK depth scale hwidth
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ r he)
    (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.var 3))) (.var 4))
      (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 4)))
        (.neg (.mul (.var 3) (.var 4))))
      (by decide) (fun | 0 => s | 1 => Z | 2 => V | 3 => M | _ => r))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (s*V) _ _
          (Q'.mul_recipPos_eqv Z (oddMass_positive hw0 hw1 K width hK depth)))
          (Q'.mul_one_eqv _)) (Q'.eqv_refl _)))

#print axioms squareHeatMultiplicationDefect
#print axioms squareHeatMultiplicationDefect_supported
#print axioms squareSignedHeatDefect
#print axioms paddedSquare_centered_source_firstMoment_zero
#print axioms paddedSquare_energy_signedHeatDefect_identity
#print axioms paddedSquare_normalizedEnergy_signedHeatDefect_identity

end YMGap.Continuum.BF4DyadicWilsonSquareSignedHeatDefect
