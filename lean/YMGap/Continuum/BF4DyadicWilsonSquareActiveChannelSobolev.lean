/-
# OWN-centered original Wilson energy in active Sobolev channels

Expand the actual original energy into passive Gram channels before paying
its cubic and omitted-mode errors on the active footprint. The observable in
each channel is centered at the SAME original interacting mean. Its literal
full Casimir, signed curvature, complete angular weight defect and Ward
insertion remain. No channel count, replacement density, global projection
gain identity, numerical dominance or changing-family scaling is asserted.
-/

import YMGap.Continuum.SU2QuaternionPassiveChannelRetainedCasimirSobolev
import YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse

namespace YMGap.Continuum.BF4DyadicWilsonSquareActiveChannelSobolev

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
  (activeSourceSobolevErrorBudget)
open YMGap.Continuum.SU2QuaternionGeneralRetainedCasimir (oneThird)
open YMGap.Continuum.SU2QuaternionPassiveChannelRetainedCasimirSobolev
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource energy_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance normalizedWardResidual marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported oddCentered_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal
  (marginalAngular angularWeightDefect angular_weight_identity)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor (normalizedAngular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare
  (marginalAngular_shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse (energy_shifted)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor (paddedSquare_normalized_ward)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  sourceCharacter oddMass oddVariance

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "q" => projectedEndpointSource w K width (terminalMessage w K width n)
local notation "psi" => oddCentered hw0 hw1 K width hK n f
local notation "Z" => oddMass w K width n
local notation "V" => oddVariance hw0 hw1 K width hK n f

/-- The original q, q*psi and q*psi^2 pay cubic Casimir norms only on the
literal loop footprint; omitted-mode norms remain raw Haar quantities. -/
def activeChannelSobolevBudget : Q' :=
  activeSourceSobolevErrorBudget (N width-1) (observableBlocks scale width hwidth)
    w K q psi

/-- Signed full-Casimir curvature in the exact original passive channels. -/
def activeChannelCurvature : Q' :=
  channelCurvature (N width-1) w K (spectatorBlocks scale width hwidth) q psi

/-- The complete channel square uses Cfull(psi) literally, including its
original mean correction. No eigenidentity with lambda*psi is used. -/
def activeChannelCasimirSquare : Q' :=
  channelCasimirSquare (N width-1) w K (spectatorBlocks scale width hwidth) q psi

/-- Complete numerator debt. The angular defect is marginal minus raw,
so its coefficient is NEGATIVE. The signed curvature and negative square
are retained alongside the actual active Sobolev error. -/
def activeChannelCenteredDebt : Q' :=
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  activeChannelSobolevBudget hw0 hw1 K width hK n scale hwidth -
    (h+t)*angularWeightDefect w K width n psi +
    t*(-activeChannelCurvature hw0 hw1 K width hK n scale hwidth -
      oneThird*activeChannelCasimirSquare hw0 hw1 K width hK n scale hwidth)

/-- Normalize the whole signed numerator by the SAME original partition. -/
def normalizedActiveChannelCenteredDebt : Q' :=
  activeChannelCenteredDebt hw0 hw1 K width hK n scale hwidth *
    Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n)

attribute [local irreducible] activeChannelSobolevBudget activeChannelCurvature
  activeChannelCasimirSquare activeChannelCenteredDebt normalizedActiveChannelCenteredDebt

/-- Original unnormalized energy rebased to its OWN marginal angular cost.
All complete signed debts remain; there is no sufficientCutoff guard. -/
theorem paddedSquare_energy_activeChannel_marginal_bound :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    energy w K width (terminalMessage w K width n) f ≤
      (h+t)*marginalAngular w K width n f +
        activeChannelCenteredDebt hw0 hw1 K width hK n scale hwidth := by
  dsimp only
  unfold activeChannelCenteredDebt
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let a := weightedAngularEnergy (N width-1) q psi
  let d := angularWeightDefect w K width n psi
  let e := activeChannelSobolevBudget hw0 hw1 K width hK n scale hwidth
  let c := activeChannelCurvature hw0 hw1 K width hK n scale hwidth
  let s := activeChannelCasimirSquare hw0 hw1 K width hK n scale hwidth
  let mean := normalizedMoment (N width) (marginalWeight w K width n) f
    (marginalMass_positive hw0 hw1 K width hK n)
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hp := oddCentered_supported hw0 hw1 K width hK n hf
  have hfringe := fun i hi => oddCentered_independent hw0 hw1 K width hK n i
    (paddedSquare_fringe_independent scale width hwidth i hi)
  have hpass := fun i hi => oddCentered_independent hw0 hw1 K width hK n i
    (sourceCharacter_spectator_independent scale width hwidth i hi)
  have hsource := energy_projected_source w K width (terminalMessage w K width n)
    psi (terminalMessage_supported w K width n) hp hfringe
  have hcenter := energy_shifted w K width (terminalMessage_supported w K width n) hf mean
  have hbound := sourceEnergy_le_activeSobolev_retainedCasimir (N width-1)
    (Q'.le_of_lt hw0) hw1 K (spectatorBlocks scale width hwidth)
    (observableBlocks scale width hwidth) (spectatorBlocks_nodup scale width hwidth)
    (by simpa only [hN] using spectatorBlocks_lt scale width hwidth)
    (by simpa only [hN] using observableBlocks_lt scale width hwidth)
    (spectator_not_observable scale width hwidth)
    (by simpa only [hN] using spectator_observable_cover scale width hwidth)
    q psi (by simpa only [hN] using source_supported w K width n)
    (by simpa only [hN] using hp) hpass
  have hraw : energy w K width (terminalMessage w K width n) f ≤
      (h+t)*a+(t*(-c-oneThird*s)+e) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcenter.symm)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource)
        (by simpa only [h, t, a, c, s, e, hN, activeChannelCurvature,
          activeChannelCasimirSquare, activeChannelSobolevBudget] using hbound))
  have hang : a+d ≈ marginalAngular w K width n f :=
    Q'.eqv_trans _ _ _
      (angular_weight_identity w K width n psi hp (baseLinks_positive width) hfringe)
      (marginalAngular_shifted w K width n f mean)
  have hshape : (h+t)*a+(t*(-c-oneThird*s)+e) ≈
      (h+t)*(a+d)+(e-(h+t)*d+t*(-c-oneThird*s)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.add (.var 3) (.var 4)))
      (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.add (.add (.var 4) (.neg (.mul (.var 0) (.var 2)))) (.var 3)))
      (by decide) (fun
        | 0 => h+t
        | 1 => a
        | 2 => d
        | 3 => t*(-c-oneThird*s)
        | _ => e)
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hshape
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hang) (Q'.eqv_refl _))))

/-- Actual ORIGINAL growing-square energy at its OWN mean and variance.
The complete normalized signed debt and original Ward insertion remain.
This finite bound gives no changing-family dominance or continuum result. -/
theorem paddedSquare_energy_activeChannel_sobolev_bound :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    normalizedEnergy hw0 hw1 K width hK n f ≤
      (h+t)*((12*Q'.ofNat (side scale))*V) -
        (h+t)*normalizedWardResidual hw0 hw1 K width hK n f +
        normalizedActiveChannelCenteredDebt hw0 hw1 K width hK n scale hwidth := by
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let A := normalizedAngular hw0 hw1 K width hK n f
  let W := normalizedWardResidual hw0 hw1 K width hK n f
  let D := normalizedActiveChannelCenteredDebt hw0 hw1 K width hK n scale hwidth
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n)
  have hraw := paddedSquare_energy_activeChannel_marginal_bound
    hw0 hw1 K width hK n scale hwidth
  have hnorm := Q'.mul_le_mul_of_nonneg_right _ _ r hraw
    (Q'.le_of_lt (Q'.recipPos_pos Z _))
  have hdist : ((h+t)*marginalAngular w K width n f+
      activeChannelCenteredDebt hw0 hw1 K width hK n scale hwidth)*r ≈
      (h+t)*A+D :=
    by
      unfold D normalizedActiveChannelCenteredDebt
      dsimp only [A, r, normalizedAngular]
      exact Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (Q'.eqv_refl _))
  have hward := paddedSquare_normalized_ward hw0 hw1 K width hK n scale hwidth
  have hjoin : (h+t)*A+D ≈ (h+t)*(A+W)-(h+t)*W+D :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.var 3))
      (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.neg (.mul (.var 0) (.var 2)))) (.var 3))
      (by decide) (fun | 0 => h+t | 1 => A | 2 => W | _ => D)
  exact Q'.le_trans' _ _ _ hnorm (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hdist
    (Q'.eqv_trans _ _ _ hjoin
      (Q'.add_eqv_congr' (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hward) (Q'.eqv_refl _)) (Q'.eqv_refl _)))))

#print axioms activeChannelSobolevBudget
#print axioms activeChannelCurvature
#print axioms activeChannelCasimirSquare
#print axioms activeChannelCenteredDebt
#print axioms normalizedActiveChannelCenteredDebt
#print axioms paddedSquare_energy_activeChannel_marginal_bound
#print axioms paddedSquare_energy_activeChannel_sobolev_bound

end YMGap.Continuum.BF4DyadicWilsonSquareActiveChannelSobolev
