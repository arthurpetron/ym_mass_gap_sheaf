/-
The checked linear local band is transported through the original positive
block transfer. The input is the literal padded Wilson square centered at
its OWN original odd-window mean. The two later chronological partitions
remain distinct in the cleared conclusion. Fixed-nome finite statement only.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalEnergyTransport
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
import YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit

namespace YMGap.Continuum.BF4DyadicWilsonSquareLinearBandTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment shifted shifted_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate
    terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy energy_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive marginalMoment_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (oddMoment_unprojected_source centered_unprojected_square energy_shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
  (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
  (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonEta)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalEnergyTransport
  (original_block_cost_le_initial_energy)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareLinearBandGain
  (linearBandFraction linearBandFraction_positive paddedSquare_energy_linear_band_raw)
open YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain
  (paddedSquare_centered_mass_positive)
open YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit
  (originalOwnBlockCost originalOwnBlockVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (terminalMessage_next)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage energy

private def squareCharacter (scale width : Nat) (hwidth : side scale < width) : RatPoly :=
  sourceCharacter width (paddedSquare scale width hwidth).edges 1

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width n : Nat) (hwidth : side scale < width)

include width n hwidth in
/-- The actual raw energy inequality and strictly positive OWN centered mass
force the computed linear-band residual coefficient to be nonnegative. -/
theorem linearBandResidual_nonnegative :
    (0 : Q') ≤ 1-linearBandFraction hw0 hw1 scale := by
  let K := headCutoff w+(n+1)
  have hK : headCutoff w ≤ K := Nat.le_add_right _ _
  have hK1 : 1 ≤ K := by dsimp [K]; omega
  let f := squareCharacter scale width hwidth
  let g := terminalMessage w K width (n+1)
  let S := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
  let d := 1-linearBandFraction hw0 hw1 scale
  have hE : (0 : Q') ≤ energy w K width g f :=
    energy_nonnegative hw0 hw1 K width hK
      (terminalMessage_supported w K width (n+1))
      (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1)
      (terminalMessage_certificate hw0 hw1 K width hK (n+1))
  have hraw : energy w K width g f ≤ d*S :=
    paddedSquare_energy_linear_band_raw hw0 hw1 K width hK n scale hwidth hK1
  have hS : (0 : Q') < S :=
    paddedSquare_centered_mass_positive hw0 hw1 K width hK n scale hwidth
  have hds : (0 : Q') ≤ d*S := Q'.le_trans' _ _ _ hE hraw
  exact Q'.nonneg_of_mul_pos hS
    (Q'.le_trans' _ _ _ hds (Q'.le_of_eqv (Q'.mul_comm_eqv d S)))

/-- Positivity of the checked linear band fraction gives the upper guard
required by the original local-energy transport theorem. -/
theorem linearBandResidual_le_one :
    1-linearBandFraction hw0 hw1 scale ≤ 1 := by
  let delta := linearBandFraction hw0 hw1 scale
  have hδ : (0 : Q') ≤ delta :=
    Q'.le_of_lt (linearBandFraction_positive hw0 hw1 scale)
  have hp : (1 : Q') + -(1-delta) ≈ delta :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => delta)
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hδ (Q'.ge_of_eqv hp))

/-- The linear raw bound is exactly the initial centered energy hypothesis
for the SAME chronological source g_(n+1) and SAME original weight.
The OWN center is transported coefficientwise from normalizedMoment to the
existing middleRatio; no arbitrary-center assertion is made. -/
theorem paddedSquare_initial_centered_energy :
    let K := headCutoff w+(n+1)
    let hK : headCutoff w ≤ K := Nat.le_add_right _ _
    let f := squareCharacter scale width hwidth
    let c := middleRatio hw0 hw1 K width hK (n+2) (n+1) f
    let psi := shifted f c
    let g := terminalMessage w K width (n+1)
    let d := 1-linearBandFraction hw0 hw1 scale
    energy w K width g psi ≤
      d*weightedMass w K width
        (polyMul (polyMul g (transferStep w K width g)) (polyMul psi psi)) := by
  dsimp only
  let K := headCutoff w+(n+1)
  have hK : headCutoff w ≤ K := Nat.le_add_right _ _
  have hK1 : 1 ≤ K := by dsimp [K]; omega
  let f := squareCharacter scale width hwidth
  let g := terminalMessage w K width (n+1)
  let c := middleRatio hw0 hw1 K width hK (n+2) (n+1) f
  let psi := shifted f c
  let d := 1-linearBandFraction hw0 hw1 scale
  let W := marginalWeight w K width (n+1)
  let c0 := normalizedMoment (N width) W f
    (marginalMass_positive hw0 hw1 K width hK (n+1))
  let psi0 := oddCentered hw0 hw1 K width hK (n+1) f
  let S := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hg := terminalMessage_supported w K width (n+1)
  have hc : c0 ≈ c := by
    simpa only [c0, c, Nat.add_assoc, Nat.reduceAdd] using
      (marginalMoment_pin hw0 hw1 K width hK (n+1) f)
  have hpsi : RatPolyCoeffEqv psi0 psi := by
    change RatPolyCoeffEqv (shifted f c0) (shifted f c)
    unfold shifted
    exact (RatPolyCoeffEqv.refl _).add
      (RatPolyCoeffEqv.smul_coefficient (Q'.neg_eqv_congr _ _ hc) polyOne)
  have hmoment : H width (polyMul W (polyMul psi psi)) ≈ S := by
    have hchange : H width (polyMul W (polyMul psi psi)) ≈
        H width (polyMul W (polyMul psi0 psi0)) :=
      haar_of_coeff ((hpsi.symm.mul hpsi.symm).mul_left W)
    exact Q'.eqv_trans _ _ _ hchange
      (Q'.eqv_trans _ _ _
        (oddMoment_unprojected_source w K width (n+1) (polyMul psi0 psi0))
        (centered_unprojected_square hw0 hw1 K width hK (n+1) hf))
  have hmass : weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) (polyMul psi psi)) ≈ S := by
    have ht : transferStep w K width g = terminalMessage w K width (n+2) := by
      simpa only [g, Nat.add_assoc, Nat.reduceAdd] using
        terminalMessage_next w K width (n+1)
    rw [ht]
    refine Q'.eqv_trans _ _ _ (haar_of_coeff ?_) hmoment
    dsimp only [W, marginalWeight]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (by decide) (fun
        | 0 => spatialWeight w K width
        | 1 => g
        | 2 => terminalMessage w K width (n+2)
        | _ => polyMul psi psi)
  have hE : energy w K width g psi ≈ energy w K width g f :=
    energy_shifted w K width hg hf c
  have hraw : energy w K width g f ≤ d*S :=
    paddedSquare_energy_linear_band_raw hw0 hw1 K width hK n scale hwidth hK1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hE)
    (Q'.le_trans' _ _ _ hraw
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left d _ _ hmass)))

/-- Every later filter length obeys the original cleared block cost, with
its distinct zero-step and one-step chronological partitions. The coefficient
is fixed by the initial literal padded-square band and the existing endpoint
comparison budget; no new analytic input or source positivity is assumed. -/
theorem paddedSquare_linearBand_original_block_cost (t : Nat) :
    let K := headCutoff w+(n+1)
    let hK : headCutoff w ≤ K := Nat.le_add_right _ _
    let f := squareCharacter scale width hwidth
    let c := middleRatio hw0 hw1 K width hK (n+2) (n+1) f
    let psi := shifted f c
    let A := terminalMessage w K width (n+1+t)
    let b := originalBlockTransfer w K width t
      (polyMul (terminalMessage w K width (n+1)) psi)
    let d := 1-linearBandFraction hw0 hw1 scale
    clearedRayleighCost w K width A b ≤
      (d+comparisonEta hw0 hw1 width n)*
        (weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  let K := headCutoff w+(n+1)
  have hK : headCutoff w ≤ K := Nat.le_add_right _ _
  let f := squareCharacter scale width hwidth
  let c := middleRatio hw0 hw1 K width hK (n+2) (n+1) f
  let psi := shifted f c
  let d := 1-linearBandFraction hw0 hw1 scale
  have hp : SupportedQuaternionBlocks (N width) psi :=
    shifted_supported
      (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1) c
  exact original_block_cost_le_initial_energy hw0 hw1 K width hK n t hp
    (linearBandResidual_nonnegative hw0 hw1 scale width n hwidth)
    (linearBandResidual_le_one hw0 hw1 scale)
    (paddedSquare_initial_centered_energy hw0 hw1 scale width n hwidth)

/-- The same checked cleared inequality, divided by the TWO actual positive
chronological masses, controls the EXISTING original OWN cost by its OWN
block variance. No mass is identified with the other, and no norm inverse
is used. -/
theorem paddedSquare_linearBand_originalOwnBlockCost (t : Nat) :
    originalOwnBlockCost hw0 hw1 scale width hwidth (n+1) t ≤
      ((1-linearBandFraction hw0 hw1 scale)+comparisonEta hw0 hw1 width n)*
        originalOwnBlockVariance hw0 hw1 scale width hwidth (n+1) t := by
  let K := headCutoff w+(n+1)
  have hK : headCutoff w ≤ K := Nat.le_add_right _ _
  let f := squareCharacter scale width hwidth
  let c := middleRatio hw0 hw1 K width hK (n+2) (n+1) f
  let psi := shifted f c
  let A := terminalMessage w K width (n+1+t)
  let b := originalBlockTransfer w K width t
    (polyMul (terminalMessage w K width (n+1)) psi)
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  let C := clearedRayleighCost w K width A b
  let coeff := (1-linearBandFraction hw0 hw1 scale)+comparisonEta hw0 hw1 width n
  have hZ0 : (0 : Q') < Z0 :=
    terminalPair_positive hw0 hw1 K width hK (n+1+t) (n+1+t)
  have hZ1 : (0 : Q') < Z1 := by
    change (0 : Q') < weightedMass w K width
      (polyMul (terminalMessage w K width (n+1+t))
        (transferStep w K width (terminalMessage w K width (n+1+t))))
    rw [terminalMessage_next w K width (n+1+t)]
    exact terminalPair_positive hw0 hw1 K width hK (n+1+t) (n+1+t+1)
  let r01 := Q'.recipPos (Z0*Z1) (Q'.mul_pos hZ0 hZ1)
  let r0 := Q'.recipPos Z0 hZ0
  have h01 : (Z0*Z1)*r01 ≈ 1 :=
    Q'.mul_recipPos_eqv (Z0*Z1) (Q'.mul_pos hZ0 hZ1)
  have h0 : Z0*r0 ≈ 1 := Q'.mul_recipPos_eqv Z0 hZ0
  have hZ1r : Z1*r01 ≈ r0 := by
    have hins : Z1*r01 ≈ (Z0*r0)*(Z1*r01) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
        (Q'.mul_eqv_congr_right _ _ _ h0.symm)
    have hreorder : (Z0*r0)*(Z1*r01) ≈ r0*((Z0*Z1)*r01) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.var 1) (.mul (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => Z0 | 1 => r0 | 2 => Z1 | _ => r01)
    exact Q'.eqv_trans _ _ _ hins
      (Q'.eqv_trans _ _ _ hreorder
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left r0 _ _ h01)
          (Q'.mul_one_eqv r0)))
  have hcleared : C ≤ coeff*(Z1*B) :=
    paddedSquare_linearBand_original_block_cost
      hw0 hw1 scale width n hwidth t
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ r01 hcleared
    (Q'.le_of_lt (Q'.recipPos_pos (Z0*Z1) (Q'.mul_pos hZ0 hZ1)))
  have hright : (coeff*(Z1*B))*r01 ≈ coeff*(B*r0) := by
    have hreorder : (coeff*(Z1*B))*r01 ≈ coeff*(B*(Z1*r01)) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
        (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3))))
        (by decide) (fun | 0 => coeff | 1 => Z1 | 2 => B | _ => r01)
    exact Q'.eqv_trans _ _ _ hreorder
      (Q'.mul_eqv_congr_left coeff _ _
        (Q'.mul_eqv_congr_left B _ _ hZ1r))
  change C*r01 ≤ coeff*(B*r0)
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright)

end YMGap.Continuum.BF4DyadicWilsonSquareLinearBandTransport

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandTransport.linearBandResidual_nonnegative
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandTransport.linearBandResidual_le_one
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandTransport.paddedSquare_initial_centered_energy
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandTransport.paddedSquare_linearBand_original_block_cost
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareLinearBandTransport.paddedSquare_linearBand_originalOwnBlockCost
