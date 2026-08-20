/-
M3b -- mass-normalized persistence on a refinement-indexed spacing trajectory.

`MassNormalizedGapPersistence` records the coarse-blocking convention

  a_(k+1) = b_k a_k.

The AF/Faraut producer in this project is indexed in the opposite direction:
increasing `k` means finer spacing.  This file states that convention literally,

  a_k = b_k a_(k+1),

while retaining the same normalized one-step loss inequality

  M_k <= M_(k+1) + delta_k / a_(k+1).

A summable normalized-loss budget below the anchor again gives a positive
uniform mass floor.  The geometric orientation is now explicit rather than
being hidden in a reindexing convention.  This is reduction machinery only;
no AF trajectory, RG step, or loss budget is inhabited here.
-/

import YMGap.Continuum.MassNormalizedGapPersistence

namespace YMGap.Continuum.MassNormalizedRefinementPersistence

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow
open YMGap.RG.StableDynamics
open YMGap.Continuum.UnifiedContinuumFloor

/-- A refinement-indexed physical spacing and rational mass-rate flow.
`spacing_step` states `a_k = b_k*a_(k+1)`, so increasing indices move toward
finer scales when the refinement factor is greater than one. -/
structure MassNormalizedRefinementFlow where
  spacing : Nat -> Q'
  spacing_pos : forall k, (0 : Q') < spacing k
  refinementFactor : Nat -> Nat
  refinementFactor_pos : forall k, 0 < refinementFactor k
  spacing_step : forall k,
    (spacing k).eqv
      (Q'.ofNat (refinementFactor k) * spacing (k + 1))
  mass : Nat -> Q'
  mass_nonnegative : forall k, (0 : Q') <= mass k
  logLoss : Nat -> Q'
  logLoss_nonnegative : forall k, (0 : Q') <= logLoss k
  step : forall k,
    mass k <= mass (k + 1) +
      Q'.divPos (logLoss k) (spacing (k + 1))
        (spacing_pos (k + 1))

namespace MassNormalizedRefinementFlow

/-- The dimensionful loss rate charged when passing to the next finer scale. -/
def rateLoss (flow : MassNormalizedRefinementFlow) : QSeq :=
  fun k => Q'.divPos (flow.logLoss k) (flow.spacing (k + 1))
    (flow.spacing_pos (k + 1))

theorem rateLoss_nonnegative
    (flow : MassNormalizedRefinementFlow) (k : Nat) :
    (0 : Q') <= flow.rateLoss k := by
  unfold rateLoss Q'.divPos
  exact Q'.mul_nonneg _ _ (flow.logLoss_nonnegative k)
    (Q'.le_of_lt (Q'.recipPos_pos _ (flow.spacing_pos (k + 1))))

theorem step_rateLoss
    (flow : MassNormalizedRefinementFlow) (k : Nat) :
    flow.mass k <= flow.mass (k + 1) + flow.rateLoss k :=
  flow.step k

/-- Finite telescoping along the refinement direction:
`M_0 <= M_N + sum_{k<N} delta_k/a_(k+1)`. -/
theorem mass_le_mass_add_accumulated_loss
    (flow : MassNormalizedRefinementFlow) :
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

end MassNormalizedRefinementFlow

/-- Constructive refinement persistence: the complete normalized loss budget
is strictly smaller than the anchor mass. -/
structure MassNormalizedRefinementPersistence
    (flow : MassNormalizedRefinementFlow) where
  lossBudget : SummableDistortion flow.rateLoss
  anchorDominates : lossBudget.cap < flow.mass 0

namespace MassNormalizedRefinementPersistence

/-- Anchor mass remaining after paying the complete refinement loss budget. -/
def floorWitness {flow : MassNormalizedRefinementFlow}
    (persistence : MassNormalizedRefinementPersistence flow) : Q' :=
  flow.mass 0 + -persistence.lossBudget.cap

theorem floorWitness_pos {flow : MassNormalizedRefinementFlow}
    (persistence : MassNormalizedRefinementPersistence flow) :
    (0 : Q') < persistence.floorWitness :=
  qSubPosOfLt persistence.anchorDominates

theorem floorWitness_le_mass {flow : MassNormalizedRefinementFlow}
    (persistence : MassNormalizedRefinementPersistence flow) (N : Nat) :
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

/-- The refinement persistence certificate as a canonical uniform floor. -/
def toUniformSpacingFloor {flow : MassNormalizedRefinementFlow}
    (persistence : MassNormalizedRefinementPersistence flow) :
    QFloor flow.mass where
  floor := persistence.floorWitness
  floor_pos := persistence.floorWitness_pos
  bound := persistence.floorWitness_le_mass

/-- Requested dyadic resolution for a refinement-loss tail. -/
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

/-- Explicit fine-scale index after which normalized loss tails are below the
requested dyadic resolution. -/
def dyadicModulus {flow : MassNormalizedRefinementFlow}
    (persistence : MassNormalizedRefinementPersistence flow)
    (Lambda : Q') (r : Nat) : Nat :=
  persistence.lossBudget.modulus (dyadicResolution Lambda r)

theorem dyadic_tail_bound {flow : MassNormalizedRefinementFlow}
    (persistence : MassNormalizedRefinementPersistence flow)
    (Lambda : Q') (hLambda : (0 : Q') < Lambda) (r start : Nat)
    (hstart : persistence.dyadicModulus Lambda r <= start) (length : Nat) :
    finSum (fun j => flow.rateLoss (start + j)) length <=
      dyadicResolution Lambda r :=
  persistence.lossBudget.tailBound (dyadicResolution Lambda r)
    (dyadicResolution_pos Lambda hLambda r) start hstart length

end MassNormalizedRefinementPersistence

end YMGap.Continuum.MassNormalizedRefinementPersistence

#print axioms YMGap.Continuum.MassNormalizedRefinementPersistence.MassNormalizedRefinementFlow.rateLoss_nonnegative
#print axioms YMGap.Continuum.MassNormalizedRefinementPersistence.MassNormalizedRefinementFlow.mass_le_mass_add_accumulated_loss
#print axioms YMGap.Continuum.MassNormalizedRefinementPersistence.MassNormalizedRefinementPersistence.floorWitness_pos
#print axioms YMGap.Continuum.MassNormalizedRefinementPersistence.MassNormalizedRefinementPersistence.floorWitness_le_mass
#print axioms YMGap.Continuum.MassNormalizedRefinementPersistence.MassNormalizedRefinementPersistence.toUniformSpacingFloor
#print axioms YMGap.Continuum.MassNormalizedRefinementPersistence.MassNormalizedRefinementPersistence.dyadic_tail_bound
