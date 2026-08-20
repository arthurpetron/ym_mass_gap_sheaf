/-
M3e -- direction-neutral mass-normalized loss persistence.

The persistence algebra proved in `MassNormalizedGapPersistence` and in its
refinement-oriented companion does not use an exact block-factor relation.
It uses only positive physical spacings, nonnegative rational mass and loss
certificates, and the one-step normalized-loss inequality

  M_k <= M_(k+1) + delta_k / a_(k+1).

This file records precisely that common core.  Coarse-block and refinement
flows map to it, but an analytic AF trajectory may also inhabit it directly
without proving that consecutive spacings have an exact natural-number ratio.
Geometric scale relations remain useful optional data; they are not a premise
of telescoping persistence.

This is constructive reduction machinery only.  It supplies no RG estimate,
summable loss budget, physical separator, continuum limit, or mass-gap proof.
-/

import YMGap.Continuum.MassNormalizedGapPersistence
import YMGap.Continuum.MassNormalizedRefinementPersistence

namespace YMGap.Continuum.MassNormalizedLossPersistence

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow
open YMGap.RG.StableDynamics
open YMGap.Continuum.UnifiedContinuumFloor
open YMGap.Continuum.MassNormalizedGapPersistence
open YMGap.Continuum.MassNormalizedRefinementPersistence

/-- The direction-neutral data actually used by normalized-loss telescoping.
No exact relation between adjacent spacings is assumed. -/
structure MassNormalizedLossFlow where
  spacing : Nat -> Q'
  spacing_pos : forall k, (0 : Q') < spacing k
  mass : Nat -> Q'
  mass_nonnegative : forall k, (0 : Q') <= mass k
  logLoss : Nat -> Q'
  logLoss_nonnegative : forall k, (0 : Q') <= logLoss k
  step : forall k,
    mass k <= mass (k + 1) +
      Q'.divPos (logLoss k) (spacing (k + 1))
        (spacing_pos (k + 1))

namespace MassNormalizedLossFlow

/-- The dimensionful normalized loss charged at one scale transition. -/
def rateLoss (flow : MassNormalizedLossFlow) : QSeq :=
  fun k => Q'.divPos (flow.logLoss k) (flow.spacing (k + 1))
    (flow.spacing_pos (k + 1))

theorem rateLoss_nonnegative (flow : MassNormalizedLossFlow) (k : Nat) :
    (0 : Q') <= flow.rateLoss k := by
  unfold rateLoss Q'.divPos
  exact Q'.mul_nonneg _ _ (flow.logLoss_nonnegative k)
    (Q'.le_of_lt (Q'.recipPos_pos _ (flow.spacing_pos (k + 1))))

theorem step_rateLoss (flow : MassNormalizedLossFlow) (k : Nat) :
    flow.mass k <= flow.mass (k + 1) + flow.rateLoss k :=
  flow.step k

/-- Finite telescoping of the direction-neutral normalized loss. -/
theorem mass_le_mass_add_accumulated_loss (flow : MassNormalizedLossFlow) :
    forall N, flow.mass 0 <= flow.mass N + finSum flow.rateLoss N := by
  intro N
  induction N with
  | zero =>
      show flow.mass 0 <= flow.mass 0 + 0
      rw [Q'.add_zero']
      exact Q'.le_refl' _
  | succ n ih =>
      have hstep := flow.step_rateLoss n
      have hpush : flow.mass n + finSum flow.rateLoss n <=
          (flow.mass (n + 1) + flow.rateLoss n) +
            finSum flow.rateLoss n :=
        Q'.add_le_add_right _ _ _ hstep
      have hchain : flow.mass 0 <=
          (flow.mass (n + 1) + flow.rateLoss n) +
            finSum flow.rateLoss n :=
        Q'.le_trans' _ _ _ ih hpush
      have hreorder :
          ((flow.mass (n + 1) + flow.rateLoss n) +
              finSum flow.rateLoss n).eqv
            (flow.mass (n + 1) +
              (finSum flow.rateLoss n + flow.rateLoss n)) := by
        have hswap :
            ((flow.mass (n + 1) + flow.rateLoss n) +
                finSum flow.rateLoss n).eqv
              (flow.mass (n + 1) +
                (flow.rateLoss n + finSum flow.rateLoss n)) :=
          Q'.add_assoc_eqv _ _ _
        have hcomm :
            (flow.mass (n + 1) +
                (flow.rateLoss n + finSum flow.rateLoss n)).eqv
              (flow.mass (n + 1) +
                (finSum flow.rateLoss n + flow.rateLoss n)) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
        exact Q'.eqv_trans _ _ _ hswap hcomm
      exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv hreorder)

/-- Forget the optional coarse-block factor while preserving all analytic
data definitionally. -/
def ofBlockFlow (flow : MassNormalizedBlockFlow) :
    MassNormalizedLossFlow where
  spacing := flow.spacing
  spacing_pos := flow.spacing_pos
  mass := flow.mass
  mass_nonnegative := flow.mass_nonnegative
  logLoss := flow.logLoss
  logLoss_nonnegative := flow.logLoss_nonnegative
  step := flow.step

/-- Forget the optional refinement factor while preserving all analytic data
definitionally. -/
def ofRefinementFlow (flow : MassNormalizedRefinementFlow) :
    MassNormalizedLossFlow where
  spacing := flow.spacing
  spacing_pos := flow.spacing_pos
  mass := flow.mass
  mass_nonnegative := flow.mass_nonnegative
  logLoss := flow.logLoss
  logLoss_nonnegative := flow.logLoss_nonnegative
  step := flow.step

@[simp] theorem ofBlockFlow_rateLoss
    (flow : MassNormalizedBlockFlow) :
    (ofBlockFlow flow).rateLoss = flow.rateLoss := rfl

@[simp] theorem ofRefinementFlow_rateLoss
    (flow : MassNormalizedRefinementFlow) :
    (ofRefinementFlow flow).rateLoss = flow.rateLoss := rfl

end MassNormalizedLossFlow

/-- Constructive persistence for precisely the direction-neutral loss core. -/
structure MassNormalizedLossPersistence (flow : MassNormalizedLossFlow) where
  lossBudget : SummableDistortion flow.rateLoss
  anchorDominates : lossBudget.cap < flow.mass 0

namespace MassNormalizedLossPersistence

/-- The anchor mass remaining after paying the complete normalized loss. -/
def floorWitness {flow : MassNormalizedLossFlow}
    (persistence : MassNormalizedLossPersistence flow) : Q' :=
  flow.mass 0 + -persistence.lossBudget.cap

theorem floorWitness_pos {flow : MassNormalizedLossFlow}
    (persistence : MassNormalizedLossPersistence flow) :
    (0 : Q') < persistence.floorWitness :=
  qSubPosOfLt persistence.anchorDominates

theorem floorWitness_le_mass {flow : MassNormalizedLossFlow}
    (persistence : MassNormalizedLossPersistence flow) (N : Nat) :
    persistence.floorWitness <= flow.mass N := by
  have htelescope := flow.mass_le_mass_add_accumulated_loss N
  have hcap : flow.mass N + finSum flow.rateLoss N <=
      flow.mass N + persistence.lossBudget.cap :=
    Q'.add_le_add_left _ _ _ (persistence.lossBudget.partialSumBound N)
  have hseed : flow.mass 0 <= flow.mass N + persistence.lossBudget.cap :=
    Q'.le_trans' _ _ _ htelescope hcap
  have hreordered : flow.mass 0 <=
      persistence.lossBudget.cap + flow.mass N :=
    Q'.le_trans' _ _ _ hseed (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  exact Q'.sub_le_of_le_add hreordered

/-- The canonical uniform rational mass floor. -/
def toUniformSpacingFloor {flow : MassNormalizedLossFlow}
    (persistence : MassNormalizedLossPersistence flow) :
    QFloor flow.mass where
  floor := persistence.floorWitness
  floor_pos := persistence.floorWitness_pos
  bound := persistence.floorWitness_le_mass

/-- A coarse-block persistence witness is also a direction-neutral witness. -/
def ofBlockPersistence {flow : MassNormalizedBlockFlow}
    (persistence : MassNormalizedPersistence flow) :
    MassNormalizedLossPersistence
      (MassNormalizedLossFlow.ofBlockFlow flow) where
  lossBudget := persistence.lossBudget
  anchorDominates := persistence.anchorDominates

/-- A refinement persistence witness is also a direction-neutral witness. -/
def ofRefinementPersistence {flow : MassNormalizedRefinementFlow}
    (persistence : MassNormalizedRefinementPersistence flow) :
    MassNormalizedLossPersistence
      (MassNormalizedLossFlow.ofRefinementFlow flow) where
  lossBudget := persistence.lossBudget
  anchorDominates := persistence.anchorDominates

/-- Requested dyadic resolution for the normalized-loss tail. -/
def dyadicResolution (Lambda : Q') (r : Nat) : Q' :=
  half ^ r * Lambda

private theorem half_pow_pos (r : Nat) : (0 : Q') < half ^ r := by
  induction r with
  | zero => decide
  | succ n ih => exact Q'.mul_pos (by decide) ih

theorem dyadicResolution_pos
    (Lambda : Q') (hLambda : (0 : Q') < Lambda) (r : Nat) :
    (0 : Q') < dyadicResolution Lambda r :=
  Q'.mul_pos (half_pow_pos r) hLambda

/-- Explicit scale after which finite normalized-loss tails satisfy the
requested dyadic tolerance. -/
def dyadicModulus {flow : MassNormalizedLossFlow}
    (persistence : MassNormalizedLossPersistence flow)
    (Lambda : Q') (r : Nat) : Nat :=
  persistence.lossBudget.modulus (dyadicResolution Lambda r)

theorem dyadic_tail_bound {flow : MassNormalizedLossFlow}
    (persistence : MassNormalizedLossPersistence flow)
    (Lambda : Q') (hLambda : (0 : Q') < Lambda) (r start : Nat)
    (hstart : persistence.dyadicModulus Lambda r <= start) (length : Nat) :
    finSum (fun j => flow.rateLoss (start + j)) length <=
      dyadicResolution Lambda r :=
  persistence.lossBudget.tailBound (dyadicResolution Lambda r)
    (dyadicResolution_pos Lambda hLambda r) start hstart length

end MassNormalizedLossPersistence

end YMGap.Continuum.MassNormalizedLossPersistence

#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossFlow.rateLoss_nonnegative
#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossFlow.mass_le_mass_add_accumulated_loss
#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossFlow.ofBlockFlow_rateLoss
#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossFlow.ofRefinementFlow_rateLoss
#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossPersistence.floorWitness_pos
#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossPersistence.floorWitness_le_mass
#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossPersistence.ofBlockPersistence
#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossPersistence.ofRefinementPersistence
#print axioms YMGap.Continuum.MassNormalizedLossPersistence.MassNormalizedLossPersistence.dyadic_tail_bound
