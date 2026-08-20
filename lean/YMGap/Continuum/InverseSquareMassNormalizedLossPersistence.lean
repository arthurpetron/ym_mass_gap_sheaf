/-
M3j -- constructive inverse-square normalized-loss budget.

Along an asymptotically-free trajectory the natural summable residual is often
inverse-square rather than geometric.  This file adapts the repository's
proved telescoping estimate

  term k <= A/(k+B)^2,  B >= 2

to the exact `SummableDistortion` interface consumed by direction-neutral
mass-normalized persistence.  The cap is `A/(B-1)`, and the modulus is the
explicit inverse-square modulus evaluated at `epsilon.den`.

This removes summability as a separate input once the pointwise quadratic
estimate has been proved.  It does not prove that estimate for the actual
four-dimensional Yang--Mills RG flow.
-/

import YMGap.Continuum.MassNormalizedLossPersistence
import YMGap.Continuum.SummableInverseSquare

namespace YMGap.Continuum.InverseSquareMassNormalizedLossPersistence

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RationalTail
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.SummableInverseSquare
open YMGap.RG.StableDynamics

/-! ## Exact adapter from inverse-square tails to `SummableDistortion` -/

/-- The repository's `tailSum` is exactly `finSum` of the shifted stream. -/
theorem finSum_shift_eq_tailSum (term : Nat -> Q') (start : Nat) :
    forall length : Nat,
      finSum (fun offset => term (start + offset)) length =
        tailSum term start length
  | 0 => rfl
  | length + 1 => by
      show finSum (fun offset => term (start + offset)) length +
          term (start + length) =
        tailSum term start length + term (start + length)
      rw [finSum_shift_eq_tailSum term start length]

/-- The telescoping potential `1/(k+B-1)` decreases with the starting index. -/
theorem pot_antitone (B : Nat) (hB : 2 <= B)
    {earlier later : Nat} (h : earlier <= later) :
    pot B hB later <= pot B hB earlier := by
  unfold pot
  apply unit_antitone <;> omega

/-- Any nonnegative stream pointwise dominated by `A/(k+B)^2` carries the
complete constructive summability certificate required by RG persistence. -/
def inverseSquareBudget
    (term : Nat -> Q')
    (termNonnegative : forall k, (0 : Q') <= term k)
    (B : Nat) (hB : 2 <= B)
    (A : Q') (hA : (0 : Q') <= A)
    (term_le : forall k, term k <= A * invSqTerm B hB k) :
    SummableDistortion term where
  cap := A * pot B hB 0
  capNonnegative := Q'.mul_nonneg _ _ hA (pot_nonneg B hB 0)
  termNonnegative := termNonnegative
  partialSumBound := by
    intro length
    have heq : finSum term length = tailSum term 0 length := by
      simpa only [Nat.zero_add] using
        finSum_shift_eq_tailSum term 0 length
    rw [heq]
    exact summableBound_of_invSq B hB A hA term term_le 0 length
  modulus := fun epsilon => invSqModulus A epsilon.den
  tailBound := by
    intro epsilon hepsilon start hstart length
    rw [finSum_shift_eq_tailSum term start length]
    have hsum : tailSum term start length <= A * pot B hB start :=
      summableBound_of_invSq B hB A hA term term_le start length
    have hpot : pot B hB start <=
        pot B hB (invSqModulus A epsilon.den) :=
      pot_antitone B hB hstart
    have hscaled : A * pot B hB start <=
        A * pot B hB (invSqModulus A epsilon.den) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hpot hA
    have hunit : A * pot B hB (invSqModulus A epsilon.den) <=
        unit (2 ^ epsilon.den) (twoPow_pos epsilon.den) :=
      scaled_pot_le_unit B hB A hA epsilon.den
    have hhalf : unit (2 ^ epsilon.den) (twoPow_pos epsilon.den) <=
        half ^ epsilon.den :=
      Q'.ge_of_eqv (half_pow_eqv_unit epsilon.den)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ hunit
          (Q'.le_trans' _ _ _ hhalf (pow_half_le epsilon hepsilon))))

@[simp] theorem inverseSquareBudget_cap
    (term : Nat -> Q')
    (termNonnegative : forall k, (0 : Q') <= term k)
    (B : Nat) (hB : 2 <= B)
    (A : Q') (hA : (0 : Q') <= A)
    (term_le : forall k, term k <= A * invSqTerm B hB k) :
    (inverseSquareBudget term termNonnegative B hB A hA term_le).cap =
      A * pot B hB 0 := rfl

/-! ## Inverse-square control of normalized physical loss -/

/-- The AF-natural local analytic obligation for a normalized-loss flow. -/
structure InverseSquareRateLossControl
    (flow : MassNormalizedLossFlow) : Type where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  rateLoss_le : forall k : Nat,
    flow.rateLoss k <=
      coefficient * invSqTerm offset offset_at_least_two k

namespace InverseSquareRateLossControl

/-- The local inverse-square estimate constructs the complete loss budget. -/
def lossBudget {flow : MassNormalizedLossFlow}
    (control : InverseSquareRateLossControl flow) :
    SummableDistortion flow.rateLoss :=
  inverseSquareBudget flow.rateLoss flow.rateLoss_nonnegative
    control.offset control.offset_at_least_two
    control.coefficient control.coefficient_nonnegative
    control.rateLoss_le

@[simp] theorem lossBudget_cap {flow : MassNormalizedLossFlow}
    (control : InverseSquareRateLossControl flow) :
    control.lossBudget.cap =
      control.coefficient *
        pot control.offset control.offset_at_least_two 0 := rfl

/-- The anchor inequality against `A/(B-1)` constructs persistence. -/
def persistence {flow : MassNormalizedLossFlow}
    (control : InverseSquareRateLossControl flow)
    (anchorDominates :
      control.coefficient *
          pot control.offset control.offset_at_least_two 0 <
        flow.mass 0) :
    MassNormalizedLossPersistence flow where
  lossBudget := control.lossBudget
  anchorDominates := anchorDominates

@[simp] theorem persistence_floorWitness {flow : MassNormalizedLossFlow}
    (control : InverseSquareRateLossControl flow)
    (anchorDominates :
      control.coefficient *
          pot control.offset control.offset_at_least_two 0 <
        flow.mass 0) :
    (control.persistence anchorDominates).floorWitness =
      flow.mass 0 +
        -(control.coefficient *
          pot control.offset control.offset_at_least_two 0) := rfl

theorem persistent_floor_pos {flow : MassNormalizedLossFlow}
    (control : InverseSquareRateLossControl flow)
    (anchorDominates :
      control.coefficient *
          pot control.offset control.offset_at_least_two 0 <
        flow.mass 0) :
    (0 : Q') < (control.persistence anchorDominates).floorWitness :=
  (control.persistence anchorDominates).floorWitness_pos

theorem persistent_floor_le_mass {flow : MassNormalizedLossFlow}
    (control : InverseSquareRateLossControl flow)
    (anchorDominates :
      control.coefficient *
          pot control.offset control.offset_at_least_two 0 <
        flow.mass 0)
    (k : Nat) :
    (control.persistence anchorDominates).floorWitness <= flow.mass k :=
  (control.persistence anchorDominates).floorWitness_le_mass k

end InverseSquareRateLossControl

end YMGap.Continuum.InverseSquareMassNormalizedLossPersistence

#print axioms YMGap.Continuum.InverseSquareMassNormalizedLossPersistence.finSum_shift_eq_tailSum
#print axioms YMGap.Continuum.InverseSquareMassNormalizedLossPersistence.pot_antitone
#print axioms YMGap.Continuum.InverseSquareMassNormalizedLossPersistence.inverseSquareBudget
#print axioms YMGap.Continuum.InverseSquareMassNormalizedLossPersistence.InverseSquareRateLossControl.lossBudget
#print axioms YMGap.Continuum.InverseSquareMassNormalizedLossPersistence.InverseSquareRateLossControl.persistence
#print axioms YMGap.Continuum.InverseSquareMassNormalizedLossPersistence.InverseSquareRateLossControl.persistent_floor_pos
#print axioms YMGap.Continuum.InverseSquareMassNormalizedLossPersistence.InverseSquareRateLossControl.persistent_floor_le_mass
