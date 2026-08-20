/-
Mass-normalized gap persistence under constructive RG loss.

The physical motivation is the exact decay rate

  M(a) = -log(q(a)) / a.

This module does NOT define a logarithm or identify a physical separator.
Instead it isolates the rational persistence theorem needed after an analytic
producer has supplied lower certificates for those rates.  A block step may
lose `delta_k / a_{k+1}`; a constructive summable budget for those normalized
losses, dominated by the anchor mass, gives one positive floor at every scale.

Thus this is a reduction layer, not a solution of the BF4 comparison problem
and not a continuum or Clay-closure claim.
-/

import YMGap.Constructive.CRealMul
import YMGap.Constructive.HalfPow
import YMGap.Constructive.RegularCRealArith
import YMGap.RG.StableDynamics
import YMGap.Continuum.AdditiveErosionAdequacy
import YMGap.Continuum.UnifiedContinuumFloor

namespace YMGap.Continuum.MassNormalizedGapPersistence

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow
open YMGap.RG.StableDynamics
open YMGap.Continuum.UnifiedContinuumFloor

/-- Per-scale physical spacing and mass-rate certificates, together with the
normalized one-step erosion inequality.  `spacing_step` records the physical
block factor even though the persistence proof only needs positivity of the
next spacing. -/
structure MassNormalizedBlockFlow where
  spacing : Nat -> Q'
  spacing_pos : forall k, (0 : Q') < spacing k
  blockFactor : Nat -> Nat
  blockFactor_pos : forall k, 0 < blockFactor k
  spacing_step : forall k,
    (spacing (k + 1)).eqv (Q'.ofNat (blockFactor k) * spacing k)
  mass : Nat -> Q'
  mass_nonnegative : forall k, (0 : Q') <= mass k
  logLoss : Nat -> Q'
  logLoss_nonnegative : forall k, (0 : Q') <= logLoss k
  step : forall k,
    mass k <= mass (k + 1) + Q'.divPos (logLoss k) (spacing (k + 1)) (spacing_pos (k + 1))

namespace MassNormalizedBlockFlow

/-- The dimensionful loss rate charged at one blocking step. -/
def rateLoss (flow : MassNormalizedBlockFlow) : QSeq :=
  fun k => Q'.divPos (flow.logLoss k) (flow.spacing (k + 1)) (flow.spacing_pos (k + 1))

theorem rateLoss_nonnegative (flow : MassNormalizedBlockFlow) (k : Nat) :
    (0 : Q') <= flow.rateLoss k := by
  unfold rateLoss Q'.divPos
  exact Q'.mul_nonneg _ _ (flow.logLoss_nonnegative k)
    (Q'.le_of_lt (Q'.recipPos_pos _ (flow.spacing_pos (k + 1))))

theorem step_rateLoss (flow : MassNormalizedBlockFlow) (k : Nat) :
    flow.mass k <= flow.mass (k + 1) + flow.rateLoss k := by
  exact flow.step k

/-- Finite telescoping of the normalized one-step loss:
`M_0 <= M_N + sum_{k<N} delta_k/a_{k+1}`. -/
theorem mass_le_mass_add_accumulated_loss (flow : MassNormalizedBlockFlow) :
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
          (flow.mass (n + 1) + flow.rateLoss n) + finSum flow.rateLoss n :=
        Q'.add_le_add_right _ _ _ hstep
      have hchain : flow.mass 0 <=
          (flow.mass (n + 1) + flow.rateLoss n) + finSum flow.rateLoss n :=
        Q'.le_trans' _ _ _ ih hpush
      have hreorder :
          ((flow.mass (n + 1) + flow.rateLoss n) + finSum flow.rateLoss n).eqv
            (flow.mass (n + 1) + (finSum flow.rateLoss n + flow.rateLoss n)) := by
        have hswap :
            ((flow.mass (n + 1) + flow.rateLoss n) + finSum flow.rateLoss n).eqv
              (flow.mass (n + 1) + (flow.rateLoss n + finSum flow.rateLoss n)) :=
          Q'.add_assoc_eqv _ _ _
        have hcomm :
            (flow.mass (n + 1) + (flow.rateLoss n + finSum flow.rateLoss n)).eqv
              (flow.mass (n + 1) + (finSum flow.rateLoss n + flow.rateLoss n)) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
        exact Q'.eqv_trans _ _ _ hswap hcomm
      exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv hreorder)

end MassNormalizedBlockFlow

/-- Constructive persistence data: all normalized losses have explicit finite
sum and tail control, and their global cap is strictly below the anchor mass. -/
structure MassNormalizedPersistence (flow : MassNormalizedBlockFlow) where
  lossBudget : SummableDistortion flow.rateLoss
  anchorDominates : lossBudget.cap < flow.mass 0

namespace MassNormalizedPersistence

/-- The remaining mass after paying the complete normalized loss budget. -/
def floorWitness {flow : MassNormalizedBlockFlow}
    (persistence : MassNormalizedPersistence flow) : Q' :=
  flow.mass 0 + -persistence.lossBudget.cap

theorem floorWitness_pos {flow : MassNormalizedBlockFlow}
    (persistence : MassNormalizedPersistence flow) :
    (0 : Q') < persistence.floorWitness := by
  exact qSubPosOfLt persistence.anchorDominates

theorem floorWitness_le_mass {flow : MassNormalizedBlockFlow}
    (persistence : MassNormalizedPersistence flow) (N : Nat) :
    persistence.floorWitness <= flow.mass N := by
  have htelescope := flow.mass_le_mass_add_accumulated_loss N
  have hcap : flow.mass N + finSum flow.rateLoss N <=
      flow.mass N + persistence.lossBudget.cap :=
    Q'.add_le_add_left _ _ _ (persistence.lossBudget.partialSumBound N)
  have hseed : flow.mass 0 <= flow.mass N + persistence.lossBudget.cap :=
    Q'.le_trans' _ _ _ htelescope hcap
  have hreordered : flow.mass 0 <= persistence.lossBudget.cap + flow.mass N :=
    Q'.le_trans' _ _ _ hseed (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  exact Q'.sub_le_of_le_add hreordered

/-- The canonical spacing-uniform floor supplied by the persistence theorem. -/
def toUniformSpacingFloor {flow : MassNormalizedBlockFlow}
    (persistence : MassNormalizedPersistence flow) : QFloor flow.mass where
  floor := persistence.floorWitness
  floor_pos := persistence.floorWitness_pos
  bound := persistence.floorWitness_le_mass

/-- Dyadic requested resolution `2^{-r} Lambda` for the loss tail. -/
def dyadicResolution (Lambda : Q') (r : Nat) : Q' :=
  half ^ r * Lambda

private theorem half_pow_pos (r : Nat) : (0 : Q') < half ^ r := by
  induction r with
  | zero => decide
  | succ n ih =>
      exact Q'.mul_pos (by decide) ih

theorem dyadicResolution_pos (Lambda : Q') (hLambda : (0 : Q') < Lambda)
    (r : Nat) : (0 : Q') < dyadicResolution Lambda r := by
  exact Q'.mul_pos (half_pow_pos r) hLambda

/-- Explicit scale after which every finite normalized-loss tail is below
`2^{-r} Lambda`. -/
def dyadicModulus {flow : MassNormalizedBlockFlow}
    (persistence : MassNormalizedPersistence flow) (Lambda : Q') (r : Nat) : Nat :=
  persistence.lossBudget.modulus (dyadicResolution Lambda r)

theorem dyadic_tail_bound {flow : MassNormalizedBlockFlow}
    (persistence : MassNormalizedPersistence flow)
    (Lambda : Q') (hLambda : (0 : Q') < Lambda) (r start : Nat)
    (hstart : persistence.dyadicModulus Lambda r <= start) (length : Nat) :
    finSum (fun j => flow.rateLoss (start + j)) length <= dyadicResolution Lambda r := by
  exact persistence.lossBudget.tailBound (dyadicResolution Lambda r)
    (dyadicResolution_pos Lambda hLambda r) start hstart length

end MassNormalizedPersistence

end YMGap.Continuum.MassNormalizedGapPersistence

#print axioms YMGap.Continuum.MassNormalizedGapPersistence.MassNormalizedBlockFlow.rateLoss_nonnegative
#print axioms YMGap.Continuum.MassNormalizedGapPersistence.MassNormalizedBlockFlow.mass_le_mass_add_accumulated_loss
#print axioms YMGap.Continuum.MassNormalizedGapPersistence.MassNormalizedPersistence.floorWitness_pos
#print axioms YMGap.Continuum.MassNormalizedGapPersistence.MassNormalizedPersistence.floorWitness_le_mass
#print axioms YMGap.Continuum.MassNormalizedGapPersistence.MassNormalizedPersistence.toUniformSpacingFloor
#print axioms YMGap.Continuum.MassNormalizedGapPersistence.MassNormalizedPersistence.dyadicResolution_pos
#print axioms YMGap.Continuum.MassNormalizedGapPersistence.MassNormalizedPersistence.dyadic_tail_bound
