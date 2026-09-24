/-
# A nonzero plaquette excitation in the SAME all-nome Wilson completion

The actual mean's rational approximations construct the centered vector.
The original local-star scalar floor proves its positive norm, and its time
pairing is the actual connected plaquette moment. The completed strict bound
therefore has a nonzero vector in its existing vacuum-complement domain.

The floor depends on nome. There is no cross-width identification, scaling
survival, physical Hamiltonian, or continuum claim. In particular, positivity
of this fixed-parameter norm is not the missing relative loss estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeCenteredVector
import YMGap.Continuum.BF4WilsonAllNomePlaquetteVariance

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
  (uniformFloor uniformFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws (intrinsicForm_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
open YMGap.Continuum.BF4WilsonAllNomePlaquetteVariance
  (centered_norm_floor centered_response_floor)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "x" => loopState (plaquetteLoop face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Explicit rational centering in the already constructed Wilson carrier. -/
def plaquetteExcitation : VacuumComplement hw0 hw1 (width := width) :=
  centeredExcitation hw0 hw1 x

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)

/-- The same computed positive floor works at every width and face position,
with nome fixed. No identification of the different carriers is asserted. -/
theorem plaquetteExcitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w))) (B v v) := by
  change RCle _ (B (centeredVector hw0 hw1 x) (centeredVector hw0 hw1 x))
  rw [centeredVector_diagonal]
  exact centered_norm_floor hw0 hw1 width face hf

theorem plaquetteExcitation_norm_ne_zero : B v v ≠ RCzero := by
  intro hz
  have h := plaquetteExcitation_norm_floor hw0 hw1 width face hf
  rw [hz] at h
  have hle : starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (starRatio_positive hw0 hw1) hle)

theorem plaquetteExcitation_ne_zero : v ≠ embed hw0 hw1 (zero width) := by
  intro hz
  apply plaquetteExcitation_norm_ne_zero hw0 hw1 width face hf
  rw [hz, completedInner_embed]
  exact Quotient.sound (intrinsicForm_zero_left hw0 hw1 (zero width))

/-- The centered observable and temporal operator are on this SAME carrier. -/
theorem plaquetteExcitation_correlator_pin (n : Nat) :
    B v (T n v) = Quotient.mk crealSetoid (centeredTimeMoment hw0 hw1 n x x) :=
  centeredVector_time_pairing hw0 hw1 n x

/-- The existing universal strict estimate now has an explicit nonzero input. -/
theorem plaquetteExcitation_twoStep_bound :
    RCle (B v (T 2 v))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width))) (B v v)) :=
  vacuumComplement_twoStep_form_gap hw0 hw1 width
    (plaquetteExcitation hw0 hw1 width face hf)

/-- The original connected-response certificate is a positive matrix
coefficient of this SAME completed vector, not an auxiliary detector state. -/
theorem plaquetteExcitation_response_floor
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Quotient.mk crealSetoid (ofQ' (uniformFloor hw0 width))) (B v (T 1 v)) := by
  rw [plaquetteExcitation_correlator_pin]
  exact centered_response_floor hw0 hw1 width face hf hactive

def originFace : Z4Plaq := ((0, 0, 0, 0), .p01)

theorem originFace_mem (width : Nat) : originFace ∈ spatialFaces (width+1) :=
  (spatialFaces_mem_iff (width+1) originFace).mpr
    ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _, Nat.zero_lt_succ _, rfl, by decide⟩

/-- No face-existence assumption: every positive width has a supplied nonzero
state and its explicit quantitative norm lower bound. -/
def nonzeroExcitation (width : Nat) :
    {state : VacuumComplement hw0 hw1 (width := width+1) //
      RCle (Quotient.mk crealSetoid (ofQ' (starRatio w))) (B state.val state.val) ∧
      state.val ≠ embed hw0 hw1 (zero (width+1))} :=
  ⟨plaquetteExcitation hw0 hw1 (width+1) originFace (originFace_mem width),
    plaquetteExcitation_norm_floor hw0 hw1 (width+1) originFace (originFace_mem width),
    plaquetteExcitation_ne_zero hw0 hw1 (width+1) originFace (originFace_mem width)⟩

/-- Strict padding proves the active-link premise for the explicit origin
face. Both the response floor and its positivity are supplied as data. -/
def positiveResponseExcitation (width : Nat) :
    Σ state : VacuumComplement hw0 hw1 (width := width+2),
      {floor : Q' // (0 : Q') < floor ∧
        RCle (Quotient.mk crealSetoid (ofQ' floor)) (B state.val (T 1 state.val))} :=
  ⟨plaquetteExcitation hw0 hw1 (width+2) originFace (originFace_mem (width+1)),
    uniformFloor hw0 (width+2), uniformFloor_positive hw0 hw1 (width+2),
    plaquetteExcitation_response_floor hw0 hw1 (width+2) originFace
      (originFace_mem (width+1))
      (plaquette_active_after_padding (by omega : 1 < width+2) originFace (originFace_mem 0))⟩

#print axioms plaquetteExcitation
#print axioms plaquetteExcitation_norm_floor
#print axioms plaquetteExcitation_norm_ne_zero
#print axioms plaquetteExcitation_ne_zero
#print axioms plaquetteExcitation_correlator_pin
#print axioms plaquetteExcitation_twoStep_bound
#print axioms plaquetteExcitation_response_floor
#print axioms originFace
#print axioms originFace_mem
#print axioms nonzeroExcitation
#print axioms positiveResponseExcitation

end YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
