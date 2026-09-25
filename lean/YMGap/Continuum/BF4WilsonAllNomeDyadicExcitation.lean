/-
# Nonzero growing Wilson-square states on the SAME all-nome completion

Each padded dyadic square has an actual centered vacuum-complement state,
its computed positive norm floor, and SAME-operator connected correlators.
The existing completed strict bound acts on these nonzero states. The floor
is independent of square size and width at fixed nome, not as nome tends
to one. This constructs a finite-parameter family, not a limit of states
in different completions or a continuum survival theorem.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicVariance
import YMGap.Continuum.BF4WilsonAllNomeCompletedGap

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws (intrinsicForm_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
open YMGap.Continuum.BF4WilsonAllNomeDyadicVariance

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

/-- The existing constructive centering supplies this actual subtype state. -/
def dyadicExcitation : VacuumComplement hw0 hw1 (width := width) :=
  centeredExcitation hw0 hw1 (loopState (paddedSquare scale width hwidth))

local notation "v" => Subtype.val (dyadicExcitation hw0 hw1 scale width hwidth)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

theorem dyadicExcitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w))) (B v v) :=
  centeredVector_norm_floor hw0 hw1 scale width hwidth

def dyadicNormCeiling : Q' :=
  centeredNormCeiling hw0 hw1 (loopState (paddedSquare scale width hwidth))

theorem dyadicExcitation_norm_ceiling :
    RCle (B v v)
      (Quotient.mk crealSetoid (ofQ' (dyadicNormCeiling hw0 hw1 scale width hwidth))) := by
  exact centeredVector_norm_ceiling hw0 hw1
    (loopState (paddedSquare scale width hwidth))

theorem dyadicExcitation_norm_ne_zero : B v v ≠ RCzero := by
  intro hz
  have h := dyadicExcitation_norm_floor hw0 hw1 scale width hwidth
  rw [hz] at h
  have hle : starRatio w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (starRatio_positive hw0 hw1) hle)

theorem dyadicExcitation_ne_zero : v ≠ embed hw0 hw1 (zero width) := by
  intro hz
  apply dyadicExcitation_norm_ne_zero hw0 hw1 scale width hwidth
  rw [hz, completedInner_embed]
  exact Quotient.sound (intrinsicForm_zero_left hw0 hw1 (zero width))

/-- The connected scalar and discrete time are those of this SAME state. -/
theorem dyadicExcitation_correlator_pin (n : Nat) :
    B v (T n v) = Quotient.mk crealSetoid
      (centeredTimeMoment hw0 hw1 n (loopState (paddedSquare scale width hwidth))
        (loopState (paddedSquare scale width hwidth))) :=
  centeredVector_time_pairing hw0 hw1 n _

/-- The universal completed bound has the actual growing-square state in
its existing domain; its rate still depends on nome and width. -/
theorem dyadicExcitation_twoStep_bound :
    RCle (B v (T 2 v))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate hw0 hw1 width))) (B v v)) :=
  vacuumComplement_twoStep_form_gap hw0 hw1 width
    (dyadicExcitation hw0 hw1 scale width hwidth)

/-- No existence premise: compute a fitting width, actual state and proof
of nonvanishing for every dyadic square size. No cross-width map is claimed. -/
def nonzeroExcitation (scale : Nat) :
    {state : VacuumComplement hw0 hw1 (width := side scale+1) //
      RCle (Quotient.mk crealSetoid (ofQ' (starRatio w))) (B state.val state.val) ∧
      state.val ≠ embed hw0 hw1 (zero (side scale+1))} :=
  ⟨dyadicExcitation hw0 hw1 scale (side scale+1) (Nat.lt_succ_self _),
    dyadicExcitation_norm_floor hw0 hw1 scale (side scale+1) (Nat.lt_succ_self _),
    dyadicExcitation_ne_zero hw0 hw1 scale (side scale+1) (Nat.lt_succ_self _)⟩

#print axioms dyadicExcitation
#print axioms dyadicExcitation_norm_floor
#print axioms dyadicNormCeiling
#print axioms dyadicExcitation_norm_ceiling
#print axioms dyadicExcitation_norm_ne_zero
#print axioms dyadicExcitation_ne_zero
#print axioms dyadicExcitation_correlator_pin
#print axioms dyadicExcitation_twoStep_bound
#print axioms nonzeroExcitation

end YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation
