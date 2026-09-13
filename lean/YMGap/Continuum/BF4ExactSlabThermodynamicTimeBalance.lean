/-
# Reflected time balance for the SAME original completed-state family

Original spacetime-law invariance and a literal one-step coordinate identity
prove B(Tp,q)=B(p,Tq) for all finite presentations. Common-base compatibility
then removes the shared-base restriction. Composition gives balance at all
lags and identifies every two-time pairing with its same-object sum-lag row.

Original means are unchanged under the existing geometric translation.
Centering therefore has the same balance. The domain is still Presentation:
OS-null descent, an operator on the completion, norm-relative contraction,
strict gap and the continuum construction are not asserted here.
-/

import YMGap.Continuum.BF4ExactSlabSpacetimeTimeInvariance
import YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry
import YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding (bulkAtTime)
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression (fromLower reflectedProduct)
open YMGap.Continuum.BF4ExactSlabSpacetimeTimeInvariance
open YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry
open YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit (lower_limit_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm (formLimit)
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations (timeCovariance)

local notation "B" => completedInner

private theorem realEquiv_of_eq {a b : CReal} (h : a=b) : Equiv a b := by cases h; exact Equiv.refl _

theorem meanLimit_bulkAtTime {base : Nat} (padding : Nat) (lag : Fin (padding+1)) (e : PlaquetteExpression base) :
    Equiv (BF4ExactSlabExpressionThermodynamicLimit.meanLimit (bulkAtTime padding lag e))
      (BF4ExactSlabExpressionThermodynamicLimit.meanLimit e) :=
  (lower_limit_pin (bulkAtTime padding lag e)).symm.trans
    ((realEquiv_of_eq (congrArg BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit
      (fromLower_bulkAtTime padding lag e))).trans
      ((meanLimit_embed (bulkPlacement base padding lag) (fromLower e)).trans (lower_limit_pin e)))

/-- Invariance of the actual original mean, not just the literal constant. -/
theorem value_timeObservable (lag : Nat) (p : Presentation) :
    value (timeObservable lag p) = value (embed p) :=
  Quotient.sound (meanLimit_bulkAtTime lag ⟨lag, Nat.lt_succ_self lag⟩ p.expression)

theorem formLimit_balance {base : Nat} (e f : PlaquetteExpression base) :
    Equiv (formLimit (bulkAtTime 1 ⟨1, by decide⟩ e) (bulkAtTime 1 ⟨0, by decide⟩ f))
      (formLimit (bulkAtTime 1 ⟨0, by decide⟩ e) (bulkAtTime 1 ⟨1, by decide⟩ f)) :=
  (meanLimit_embed (outerLeft base)
    (reflectedProduct (bulkAtTime 1 ⟨1, by decide⟩ e) (bulkAtTime 1 ⟨0, by decide⟩ f))).symm.trans
    ((realEquiv_of_eq (congrArg BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit (reflectedProduct_balance e f))).trans
      (meanLimit_embed (outerRight base)
        (reflectedProduct (bulkAtTime 1 ⟨0, by decide⟩ e) (bulkAtTime 1 ⟨1, by decide⟩ f))))

theorem time_inner_bulk {base : Nat} (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression base) :
    B (timeState s.val ⟨base,e⟩) (timeState t.val ⟨base,f⟩) =
      Quotient.mk crealSetoid (formLimit (bulkAtTime padding s e) (bulkAtTime padding t f)) := by
  have h := (completedInner_embedPresentation ⟨base+padding, bulkAtTime padding s e⟩
    ⟨base+padding, bulkAtTime padding t f⟩).trans (pairing_sameBase (bulkAtTime padding s e) (bulkAtTime padding t f))
  rw [timeState_bulk padding s e, timeState_bulk padding t f] at h
  exact h

theorem one_step_balance_sameBase {base : Nat} (e f : PlaquetteExpression base) :
    B (timeState 1 ⟨base,e⟩) (timeState 0 ⟨base,f⟩) = B (timeState 0 ⟨base,e⟩) (timeState 1 ⟨base,f⟩) :=
  (time_inner_bulk 1 ⟨1, by decide⟩ ⟨0, by decide⟩ e f).trans
    ((Quotient.sound (formLimit_balance e f)).trans (time_inner_bulk 1 ⟨0, by decide⟩ ⟨1, by decide⟩ e f).symm)

/-- Original reflected balance for ALL finite presentations, on the SAME completion. -/
theorem one_step_balance (p q : Presentation) :
    B (timeState 1 p) (timeState 0 q) = B (timeState 0 p) (timeState 1 q) := by
  have h := one_step_balance_sameBase (atBase p (p.base+q.base) (Nat.le_add_right _ _))
    (atBase q (p.base+q.base) (Nat.le_add_left _ _))
  rw [timeState_rebase 1 p, timeState_rebase 0 q, timeState_rebase 0 p, timeState_rebase 1 q] at h
  exact h

theorem time_balance (s t : Nat) (p q : Presentation) :
    B (timeState (s+1) p) (timeState t q) = B (timeState s p) (timeState (t+1) q) := by
  have h := one_step_balance (translate s p) (translate t q)
  rw [timeState_comp, timeState_comp, timeState_comp, timeState_comp] at h
  simpa only [Nat.add_zero] using h

/-- The same-object moment relation; no operator or norm bound is presumed. -/
theorem time_sum : ∀ s t : Nat, ∀ p q : Presentation,
    B (timeState s p) (timeState t q) = B (timeState 0 p) (timeState (s+t) q)
  | 0, t, p, q => by rw [Nat.zero_add]
  | s+1, t, p, q => by
      have h := (time_balance s t p q).trans (time_sum s (t+1) p q)
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem time_unit_right (lag : Nat) (p : Presentation) : B (timeState lag p) completedUnit = value (embed p) := by
  have h := (completedInner_embedObservable (timeObservable lag p) unit).trans
    ((pairing_unit_right_value (timeObservable lag p)).trans (value_timeObservable lag p))
  exact h

theorem time_unit_left (lag : Nat) (p : Presentation) : B completedUnit (timeState lag p) = value (embed p) :=
  (completedInner_symm _ _).trans (time_unit_right lag p)

theorem centered_time_inner (s t : Nat) (p q : Presentation) :
    B (centeredTimeState s p).val (centeredTimeState t q).val =
      RCsub (B (timeState s p) (timeState t q)) (RCmul (value (embed p)) (value (embed q))) := by
  rw [centeredTimeState_inner, time_unit_right, time_unit_left]

theorem timeCovariance_sum (s t : Nat) (p q : Presentation) :
    timeCovariance s t p q = timeCovariance 0 (s+t) p q := by
  unfold timeCovariance
  rw [centered_time_inner, centered_time_inner, time_sum s t p q]

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.meanLimit_bulkAtTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.value_timeObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.formLimit_balance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.time_inner_bulk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.one_step_balance_sameBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.one_step_balance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.time_balance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.time_sum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.time_unit_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.time_unit_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.centered_time_inner
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance.timeCovariance_sum
