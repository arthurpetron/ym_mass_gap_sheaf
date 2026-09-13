/-
# Geometrically translated states in the ORIGINAL thermodynamic completion

Every finite presentation and nonnegative integer lag gives an actual state
in the previously constructed completion. The same-map composition, rebasing,
linear laws and bulk placement pins follow from literal observable geometry.
The original square cap bounds the norm at every lag, with no lag-dependent
loss. Centering has the same cap.

This is a family Presentation -> Completion, not an operator on Completion.
The cap is presentation-dependent, not a bound relative to its OS norm.
Preservation of arbitrary semantic equality and OS null vectors, interacting
time homogeneity and an operator contraction remain separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra
import YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding (bulkAtTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion

local notation "B" => completedInner

def timeState (lag : Nat) (p : Presentation) : Completion := embedObservable (timeObservable lag p)

theorem timeState_pin (lag : Nat) (p : Presentation) :
    timeState lag p = embedPresentation (translate lag p) := rfl

theorem timeState_zero (p : Presentation) : timeState 0 p = embedPresentation p :=
  congrArg embedObservable (timeObservable_zero p)

theorem timeState_comp (s t : Nat) (p : Presentation) :
    timeState t (translate s p) = timeState (s+t) p :=
  congrArg embedObservable (timeObservable_comp s t p)

theorem timeState_rebase (lag : Nat) (p : Presentation) (target : Nat) (hp : p.base ≤ target) :
    timeState lag ⟨target, atBase p target hp⟩ = timeState lag p :=
  congrArg embedObservable (timeObservable_rebase lag p target hp)

theorem timeState_bulk {base : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression base) :
    embedPresentation ⟨base+padding, bulkAtTime padding s e⟩ = timeState s.val ⟨base,e⟩ :=
  congrArg embedObservable (timeObservable_bulk padding s e)

theorem timeState_add (lag : Nat) (p q : Presentation) :
    timeState lag (add p q) = completedAdd (timeState lag p) (timeState lag q) := by
  unfold timeState
  rw [timeObservable_add, completedAdd_embedObservable]

theorem timeState_smul (lag : Nat) (c : Q') (p : Presentation) :
    timeState lag (smul c p) = completedSmul c (timeState lag p) := rfl

/-- Translation of the literal constant expression; not operator stationarity. -/
theorem timeState_one (lag : Nat) : timeState lag one = completedUnit :=
  congrArg embedObservable (timeObservable_one lag)

theorem diagonalCeiling_translate (lag : Nat) (p : Presentation) :
    diagonalCeiling (translate lag p) = diagonalCeiling p :=
  BF4ExactSlabPlaquetteUniformSquareBound.bound_bulkAtTime lag ⟨lag, Nat.lt_succ_self lag⟩ p.expression

/-- Uniform in lag at fixed nome/spacing, with the explicit original polynomial cap. -/
theorem timeState_norm_le (lag : Nat) (p : Presentation) :
    RCle (B (timeState lag p) (timeState lag p))
      (Quotient.mk crealSetoid (ofQ' (diagonalCeiling p))) := by
  rw [timeState_pin, completedInner_embedPresentation]
  change leEv (presentedForm (translate lag p) (translate lag p)) (ofQ' (diagonalCeiling p))
  have h := diagonal_le_ceiling (translate lag p)
  rw [diagonalCeiling_translate] at h
  exact h

def centeredTimeState (lag : Nat) (p : Presentation) : UnitComplement := centeredState (timeState lag p)

theorem centeredTimeState_zero (p : Presentation) :
    centeredTimeState 0 p = centeredState (embedPresentation p) :=
  congrArg centeredState (timeState_zero p)

theorem centeredTimeState_comp (s t : Nat) (p : Presentation) :
    centeredTimeState t (translate s p) = centeredTimeState (s+t) p :=
  congrArg centeredState (timeState_comp s t p)

theorem centeredTimeState_rebase (lag : Nat) (p : Presentation) (target : Nat) (hp : p.base ≤ target) :
    centeredTimeState lag ⟨target, atBase p target hp⟩ = centeredTimeState lag p :=
  congrArg centeredState (timeState_rebase lag p target hp)

theorem centeredTimeState_norm_le (lag : Nat) (p : Presentation) :
    RCle (B (centeredTimeState lag p).val (centeredTimeState lag p).val)
      (Quotient.mk crealSetoid (ofQ' (diagonalCeiling p))) :=
  RCle_trans (center_norm_le (timeState lag p)) (timeState_norm_le lag p)

theorem centeredTimeState_inner (s t : Nat) (p q : Presentation) :
    B (centeredTimeState s p).val (centeredTimeState t q).val =
      RCsub (B (timeState s p) (timeState t q))
        (RCmul (B (timeState s p) completedUnit) (B completedUnit (timeState t q))) :=
  centered_inner (timeState s p) (timeState t q)

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_comp
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_rebase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_bulk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.diagonalCeiling_translate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.timeState_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.centeredTimeState
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.centeredTimeState_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.centeredTimeState_comp
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.centeredTimeState_rebase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.centeredTimeState_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates.centeredTimeState_inner
