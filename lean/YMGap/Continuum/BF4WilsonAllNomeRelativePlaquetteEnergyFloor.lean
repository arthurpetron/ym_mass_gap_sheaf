/-
# Relative-Ward floor on the literal Wilson plaquette completion

The new finite original-action prediction floor applies only after its
explicit relative-angular cutoff. The pre-existing source-square/window
pin and joint diagonal convergence carry that same scalar to the same
completed physical-time plaquette, with no new analytic premise.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteEnergyFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeEnergyFloor

namespace YMGap.Continuum.BF4WilsonAllNomeRelativePlaquetteEnergyFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeEnergyFloor
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteEnergyFloor
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect)
open YMGap.Continuum.BF4ExactSlabRelativePredictionError (relativePredictionFloor)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.RCSignedPairBudget
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

attribute [local irreducible] baseLinks originalWindowScalar originalJointLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "loop" => plaquetteLoop face hf
local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1

/-- A computed stage threshold, not an eventually-true existential. -/
def relativeStageCutoff (w : Q') : Nat :=
  relativeCutoff w 2048 - headCutoff w

private theorem relative_stage_ready (w : Q') (stage : Nat)
    (hstage : relativeStageCutoff w ≤ stage) :
    relativeCutoff w 2048 ≤ headCutoff w + stage := by
  have hhead := headCutoff_le_relativeCutoff w 2048
  unfold relativeStageCutoff at hstage
  omega

/-- The new relative-score floor holds on each sufficiently late ORIGINAL
diagonal odd window of the same literal plaquette time square. -/
theorem finite_relative_plaquette_increment_floor (stage depth : Nat)
    (hstage : relativeStageCutoff w ≤ stage) :
    relativePredictionFloor w ≤ originalWindowScalar hw0 hw1 1
      (timeSquare loop 1) stage depth depth := by
  let K := headCutoff w + stage
  have hK : headCutoff w ≤ K := Nat.le_add_right _ _
  have hKrel : relativeCutoff w 2048 ≤ K :=
    relative_stage_ready w stage hstage
  have hfloor := plaquette_relative_energy_floor hw0 hw1 K width hKrel depth face hf
  have henergy := normalizedEnergy_window hw0 hw1 K width hK depth
    (SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1)
  have hcongr := windowRatio_congr hw0 hw1 K width hK depth 1 depth
    (source_square_plaquette width face hf)
  have hpin := originalWindowScalar_pin hw0 hw1 1 (timeSquare loop 1)
    (timeSquare_within loop 1) stage depth depth
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ henergy
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hcongr) (Q'.eqv_symm hpin))))

/-- The same completed Wilson time increment inherits the relative floor.
Its cutoff threshold remains explicit and computable. -/
theorem plaquette_relative_timeIncrement_floor :
    leEv (ofQ' (relativePredictionFloor w))
      (timeIncrement hw0 hw1 loop 1) := by
  apply leEv_of_ofQ'_limit_le (convergesTo_const _)
    (originalJoint_diagonal_converges hw0 hw1 1 _ (timeSquare_within loop 1))
  intro epsilon he
  refine ⟨relativeStageCutoff w, fun stage hstage => ?_⟩
  exact Q'.le_trans' _ _ _
    (finite_relative_plaquette_increment_floor hw0 hw1 width face hf
      stage stage hstage)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

/-- Positive one-step defect form of the SAME literal completed plaquette.
The factor one half comes solely from the existing exact time-square pin. -/
theorem plaquette_relative_defect_form_floor :
    RCle (Rq (HalfPow.half * relativePredictionFloor w))
      (B v (defect hw0 hw1 v)) := by
  have h : RCle (Rq (relativePredictionFloor w))
      (Quotient.mk crealSetoid (timeIncrement hw0 hw1 loop 1)) := by
    simpa only [RCle_mk] using
      (plaquette_relative_timeIncrement_floor hw0 hw1 width face hf)
  rw [plaquette_timeIncrement_defect_pin hw0 hw1 width face hf] at h
  have hs := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half) h
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (by decide : Q'.eqv (HalfPow.half * 2) 1),
    RCscale_one] at hs
  have hl : RCscale HalfPow.half (Rq (relativePredictionFloor w)) =
      Rq (HalfPow.half * relativePredictionFloor w) := by
    rw [RCscale_mk]
    exact Quotient.sound
      (CRealAlg.ofQ'_mul HalfPow.half (relativePredictionFloor w)).symm
  rw [hl] at hs
  exact hs

#print axioms relativeStageCutoff
#print axioms finite_relative_plaquette_increment_floor
#print axioms plaquette_relative_timeIncrement_floor
#print axioms plaquette_relative_defect_form_floor

end YMGap.Continuum.BF4WilsonAllNomeRelativePlaquetteEnergyFloor
