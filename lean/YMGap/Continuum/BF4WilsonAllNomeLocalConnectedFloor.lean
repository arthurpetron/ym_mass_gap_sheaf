/-
# A width-independent connected response at fixed nome and spatial width

The original finite-action local spectator estimate gives a nome-only
positive constant for every active face.  The existing exact centered-window
identity and joint-limit convergence carry that same constant to the
completed one-step connected response.  No spatial limit is taken here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalResponse
import YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCompletedResponse

namespace YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive (source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost
  (plaquette_middleRatio_bounds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalResponse
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws (jointPairing_symm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm (jointCenteredMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner (completedInner)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime (jointCompletedTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance
open YMGap.Continuum.BF4WilsonAllNomePlaquetteMeanPin
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor
  (connected_diagonal_converges)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] originalWindowScalar originalJointLimit baseLinks

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

include hf

local notation "loop" => plaquetteLoop face hf
local notation "e0" => (WindowExpression.loop 0 loop 1)
local notation "e1" => (WindowExpression.loop 1 loop 1)
local notation "M" => originalJointLimit hw0 hw1 0 e0 (Nat.le_refl 0)

/-- The actual centered original window inherits the four-link nome-only
floor, with its center chosen from the original finite endpoint mean. -/
theorem centered_window_response_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) :
    let m := middleRatio hw0 hw1 K width hK ((n+1)+1) (n+1)
      (characterPolynomial (plaquette width face).scalar 1)
    localResponseFloor hw0 hw1 ≤
      windowRatio hw0 hw1 K width hK (n+1) 1 (n+1)
        (polyMul (source width face m) (liftBoundary (N width) (source width face m))) := by
  have hb := plaquette_middleRatio_bounds hw0 hw1 K width hK ((n+1)+1) (n+1) face
  exact localResponseFloor_le_window hw0 hw1 width face hf hactive K hK hK1 n _ hb.1 hb.2

/-- The same fixed original observables give a uniform finite connected
floor along the existing cutoff/time diagonal. -/
theorem finite_connected_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (j : Nat) (hj : 1 ≤ j) :
    localResponseFloor hw0 hw1 ≤
      originalWindowScalar hw0 hw1 1 (lagExpression loop 1) j j j +
        -(originalWindowScalar hw0 hw1 1 e0 j j j *
          originalWindowScalar hw0 hw1 1 e1 j j j) := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have h0 : RatPolyCoeffEqv (sourcePolynomial e0) f := by
    simpa only [sourcePolynomial, Nat.zero_mul, liftBoundary] using
      sourceCharacter_plaquette width face 1
  have h1 : RatPolyCoeffEqv (sourcePolynomial e1) (liftBoundary (N width) f) := by
    simpa only [sourcePolynomial, Nat.one_mul] using
      lift_coeff (N width) (sourceCharacter_plaquette width face 1)
  have hp : RatPolyCoeffEqv (sourcePolynomial (lagExpression loop 1))
      (polyMul f (liftBoundary (N width) f)) :=
    (h1.mul h0).trans (RatPolyCoeffEqv.mul_comm _ _)
  have p0 := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 1 e0 (Nat.zero_le _) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j 1 j h0)
  have p1 := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 1 e1 (Nat.le_refl _) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j 1 j h1)
  have pp := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 1 (lagExpression loop 1) (lag_within loop 1) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j 1 j hp)
  have he := Q'.add_eqv_congr' pp (Q'.neg_eqv_congr _ _ (qmul p0 p1))
  have h := centered_window_response_floor hw0 hw1 width face hf hactive
    (headCutoff w+j) (Nat.le_add_right _ _) (by omega) (j-1)
  simp only [Nat.sub_add_cancel hj] at h
  have hc := centered_product_pin hw0 hw1 (headCutoff w+j) width
    (Nat.le_add_right _ _) j (plaquette_supported width face)
  exact Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hc) (Q'.ge_of_eqv he))

/-- The two regulator limits preserve the nome-only floor for the same
connected one-step plaquette response, at each fixed spatial width. -/
theorem connected_response_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    leEv (ofQ' (localResponseFloor hw0 hw1))
      (sub (lagMoment hw0 hw1 loop 1) (mul M M)) := by
  apply leEv_of_ofQ'_limit_le (convergesTo_const _)
    (connected_diagonal_converges hw0 hw1 width face hf)
  intro epsilon he
  exact ⟨1, fun j hj => Q'.le_trans' _ _ _
    (finite_connected_floor hw0 hw1 width face hf hactive j hj)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

local notation "x" => faceSpan width face hf
local notation "v" => Subtype.val (faceExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width

/-- The nome-only bound is on the same original centered joint moment. -/
theorem jointCenteredMoment_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    leEv (ofQ' (localResponseFloor hw0 hw1))
      (jointCenteredMoment hw0 hw1 width 1 x x) := by
  have hm := jointPairing_mean hw0 hw1 width face hf
  have hu := (jointPairing_symm hw0 hw1 width (unit width) x).trans hm
  have hp := equiv_sub (jointPairing_lag hw0 hw1 width face hf 1)
    ((mul_congr_left hm).trans (TrigSignedAdd.mul_congr_right hu))
  exact leEv_trans (connected_response_floor hw0 hw1 width face hf hactive)
    (leEv_of_equiv hp.symm)

/-- The same completed plaquette vector has a positive one-step response,
with a constant independent of width at fixed nome. -/
theorem faceExcitation_response_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Quotient.mk crealSetoid (ofQ' (localResponseFloor hw0 hw1)))
      (B v (T 1 v)) := by
  rw [faceExcitation_correlator_pin]
  exact jointCenteredMoment_floor hw0 hw1 width face hf hactive

omit hf
/-- Strict padding supplies activity for a base face. This remains a
fixed-width completed statement, with no spatial-limit comparison. -/
theorem padded_faceExcitation_response_floor {base width : Nat}
    (hwidth : base < width) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let probe := (faceExcitation hw0 hw1 width face
      (spatialFaces_mono (Nat.le_of_lt hwidth) hf)).val
    RCle (Quotient.mk crealSetoid (ofQ' (localResponseFloor hw0 hw1)))
      (completedInner hw0 hw1 width probe (jointCompletedTime hw0 hw1 width 1 probe)) :=
  faceExcitation_response_floor hw0 hw1 width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf)

end YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor

#print axioms YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor.centered_window_response_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor.finite_connected_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor.connected_response_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor.jointCenteredMoment_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor.faceExcitation_response_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomeLocalConnectedFloor.padded_faceExcitation_response_floor
