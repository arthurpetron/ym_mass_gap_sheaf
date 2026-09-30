/-
# The original plaquette temporal-energy floor on the literal Wilson carrier

The finite adjacent-time square is the same original odd-window observable
whose energy was bounded by the selected-star prediction argument. Its
existing diagonal limit is the literal Wilson time increment. This is a
single-source positive time defect, not a complement-wide spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteEnergyFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
import YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
import YMGap.Continuum.BF4WilsonAllNomeKineticIncrement
import YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
import YMGap.Continuum.BF4WilsonAllNomeLoopTimePin
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteEnergyFloor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteEnergyFloor
open YMGap.Continuum.BF4WilsonAllNomeKineticIncrement
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState timeIncrement_reflected_pin)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks originalWindowScalar originalJointLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "loop" => plaquetteLoop face hf
local notation "x" => loopState loop
local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

private theorem rc_negative_one (a : RC) : RCscale (-1) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

private theorem inner_sub_left (a b d : Completion hw0 hw1 width) :
    B (completedSub hw0 hw1 a b) d = RCsub (B a d) (B b d) := by
  unfold completedSub completedNeg RCsub
  rw [completedInner_add_left, completedInner_smul_left, rc_negative_one]

private theorem inner_sub_right (a b d : Completion hw0 hw1 width) :
    B a (completedSub hw0 hw1 b d) = RCsub (B a b) (B a d) := by
  rw [completedInner_symm hw0 hw1 a, inner_sub_left,
    completedInner_symm hw0 hw1 b a, completedInner_symm hw0 hw1 d a]

private theorem centered_sub_cancel (a b m : CReal) :
    Equiv (sub (sub a m) (sub b m)) (sub a b) :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 2)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => a.approx k | 1 => b.approx k | _ => m.approx k))

/-- The literal time-square source is the same adjacent-slice plaquette jump
whose original-window energy is bounded below. -/
theorem source_square_plaquette :
    RatPolyCoeffEqv (sourcePolynomial (timeSquare loop 1))
      (polyMul (jump width (characterPolynomial (plaquette width face).scalar 1))
        (jump width (characterPolynomial (plaquette width face).scalar 1))) := by
  have hc := sourceCharacter_plaquette width face 1
  have hj : RatPolyCoeffEqv
      (jump width (sourceCharacter width (loop).edges 1))
      (jump width (characterPolynomial (plaquette width face).scalar 1)) := by
    unfold jump
    exact hc.add (RatPolyCoeffEqv.neg (lift_coeff (N width) hc))
  have hs := source_square_pin loop
  change RatPolyCoeffEqv (sourcePolynomial (timeSquare loop 1))
    (polyMul (jump width (sourceCharacter width (loop).edges 1))
      (jump width (sourceCharacter width (loop).edges 1))) at hs
  exact hs.trans (hj.mul hj)

/-- Every original finite diagonal odd window pays the same nome-only cost. -/
theorem finite_plaquette_increment_floor (stage depth : Nat) :
    starRatio w ≤ originalWindowScalar hw0 hw1 1 (timeSquare loop 1)
      stage depth depth := by
  let K := headCutoff w + stage
  have hK : headCutoff w ≤ K := Nat.le_add_right _ _
  have hfloor := plaquette_energy_floor hw0 hw1 K width hK depth face hf
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

/-- The actual completed Wilson time increment of a physical plaquette has
a positive width-independent floor at every fixed strict nome. -/
theorem plaquette_timeIncrement_floor :
    leEv (ofQ' (starRatio w))
      (timeIncrement hw0 hw1 loop 1) := by
  apply leEv_of_ofQ'_limit_le (convergesTo_const _)
    (originalJoint_diagonal_converges hw0 hw1 1 _ (timeSquare_within loop 1))
  intro epsilon he
  refine ⟨0, fun stage _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (finite_plaquette_increment_floor hw0 hw1 width face hf stage stage)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

/-- The original squared increment is exactly twice the completed defect
form of the SAME literal centered plaquette, with no face-span carrier swap. -/
theorem plaquette_timeIncrement_defect_pin :
    Quotient.mk crealSetoid (timeIncrement hw0 hw1 loop 1) =
      RCscale 2 (B v (defect hw0 hw1 v)) := by
  have h0 := plaquetteExcitation_correlator_pin hw0 hw1 width face hf 0
  rw [completedTime_zero] at h0
  have h1 := plaquetteExcitation_correlator_pin hw0 hw1 width face hf 1
  have hc : Equiv
      (sub (centeredTimeMoment hw0 hw1 0 x x)
        (centeredTimeMoment hw0 hw1 1 x x))
      (sub (intrinsicForm hw0 hw1 x x)
        (intrinsicForm hw0 hw1 x (advance 1 x))) := by
    unfold centeredTimeMoment
    rw [advance_zero]
    exact centered_sub_cancel _ _ _
  have ht := (timeIncrement_reflected_pin hw0 hw1 loop 1).trans
    (Pivot2.mul_congr_right hc.symm)
  rw [defect, inner_sub_right, h0, h1, RCsub_mk, RCscale_mk]
  exact Quotient.sound ht

/-- A positive nome-only one-step defect form for the actual completed
physical-time operator, on this one literal plaquette excitation. -/
theorem plaquette_defect_form_floor :
    RCle (Rq (HalfPow.half * starRatio w))
      (B v (defect hw0 hw1 v)) := by
  have h : RCle (Rq (starRatio w))
      (Quotient.mk crealSetoid (timeIncrement hw0 hw1 loop 1)) := by
    simpa only [RCle_mk] using
      (plaquette_timeIncrement_floor hw0 hw1 width face hf)
  rw [plaquette_timeIncrement_defect_pin] at h
  have hs := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half) h
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (by decide : Q'.eqv (HalfPow.half * 2) 1),
    RCscale_one] at hs
  have hl : RCscale HalfPow.half (Rq (starRatio w)) =
      Rq (HalfPow.half * starRatio w) := by
    rw [RCscale_mk]
    exact Quotient.sound (CRealAlg.ofQ'_mul HalfPow.half (starRatio w)).symm
  rw [hl] at hs
  exact hs

#print axioms source_square_plaquette
#print axioms finite_plaquette_increment_floor
#print axioms plaquette_timeIncrement_floor
#print axioms plaquette_timeIncrement_defect_pin
#print axioms plaquette_defect_form_floor

end YMGap.Continuum.BF4WilsonAllNomePlaquetteEnergyFloor
