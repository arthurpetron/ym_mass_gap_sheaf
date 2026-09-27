/-
# Original conditional-generator square lower bound

The proved actual pair estimate is summed over ordered distinct neighbors.
Both endpoint incidences cost at most 25, and remote terms remain positive.
The resulting H-squared lower bound has no volume or late-cutoff loss.
Its coefficient is positive at the exact small-nome pilot, not on an
asserted continuum scaling trajectory. H is conditional-link dynamics,
not the OS time-transfer operator or physical Hamiltonian.
-/

import YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
import YMGap.Continuum.GNSProjectionNeighborLowerBound
import YMGap.Continuum.BF4ExactSlabConditionalGeneratorMargin

namespace YMGap.Continuum.BF4ExactSlabConditionalGeneratorLowerBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabTwoLinkResidualLowerBound
open YMGap.Continuum.BF4ExactSlabConditionalGeneratorMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.QuaternionHaarCharacterInterval

private instance (extent : Nat) : DecidableEq (PhysicalLink extent) :=
  inferInstanceAs (DecidableEq {i // i ∈
    Z4HalfTimeReflectionGeometry.boundaryCompleteSlabLinks extent})

private theorem filter_mask_length_le {A : Type} (p : A → Prop) [DecidablePred p]
    (q : A → Bool) (xs : List A) :
    (xs.filter (fun i => if p i then false else q i)).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons i rest ih =>
      by_cases hp : p i <;> cases hq : q i <;>
        simp only [List.filter_cons, hp, hq,
          Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

private theorem margin_scale {w : Q'} (hd : heatRemainderBound w < 1) (a : RC) :
    RCadd a (RCneg (RCscale (50 * pairCoefficient hd) a)) =
      RCscale (BF4ExactSlabConditionalGeneratorMargin.margin hd) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.mul (.const 50) (.var 1)) (.var 0))))
      (.mul (.add (.const 1) (.neg (.mul (.const 50) (.var 1)))) (.var 0))
      (by decide) (fun | 0 => A.approx n | _ => pairCoefficient hd)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "E" x => Family.finalEnergy (projections hw0 hw1 K extent hK) (schedule extent) x

include hsmall in
/-- Actual ordered signed-neighbor energy: both endpoint charges are counted. -/
theorem signedNeighborEnergy_lower (x : GNSCompletionSpace F) :
    RCle (RCneg (RCscale (50 * pairCoefficient hd) (E x)))
      (signedNeighborEnergy hw0 hw1 K extent hK x) := by
  have h := (P).neighboringCross_lower adjacent (schedule extent) x 25
    (pairCoefficient hd) (pairCoefficient_nonnegative hw0 hd)
    (fun i _ => by
      change ((schedule extent).filter (fun j => if i = j then false else adjacent i j)).length ≤ 25
      exact Nat.le_trans (filter_mask_length_le _ _ _) (neighborhood_row_count extent i))
    (fun j _ => by
      change ((schedule extent).filter (fun i => if i = j then false else adjacent i j)).length ≤ 25
      exact Nat.le_trans (filter_mask_length_le _ _ _)
        (column_count j (schedule extent) (schedule_nodup extent)))
    (fun i j _ _ _ _ => conditional_residual_pair_lower hw0 hw1 hsmall hd
      K extent hK i.val j.val i.property j.property x)
  have hc : Q'.eqv ((2 : Q') * Q'.ofNat 25 * pairCoefficient hd)
      (50 * pairCoefficient hd) :=
    Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv ((2 : Q') * Q'.ofNat 25) 50)
  rw [RCSignedPairBudget.scale_congr hc] at h
  exact h

include hsmall in
/-- The SAME original H satisfies H-squared >= margin times H in quadratic
form, on all completed vectors. No centered-coercivity input is assumed. -/
theorem conditionalGenerator_square_lower (x : GNSCompletionSpace F) :
    RCle (RCscale (BF4ExactSlabConditionalGeneratorMargin.margin hd) (E x))
      (normSq (conditionalGenerator hw0 hw1 K extent hK x)) := by
  have h := RCadd_le_add (RCle_refl (E x))
    (signedNeighborEnergy_lower hw0 hw1 hsmall hd K extent hK x)
  rw [margin_scale] at h
  exact RCle_trans h (signed_energy_le_generator_square hw0 hw1 K extent hK x)

/-- An actual positive, extent/late-cutoff independent pilot coefficient,
not an assumed analytic margin. This is still a conditional-generator bound. -/
theorem existingNome_generator_square_lower (K extent : Nat)
    (hK : headCutoff nome ≤ K)
    (x : GNSCompletionSpace (fullData (w := nome) (by decide) (by decide) K extent hK)) :
    (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin existingNome_guards.2 ∧
      RCle (RCscale (BF4ExactSlabConditionalGeneratorMargin.margin existingNome_guards.2)
        ((projections (w := nome) (by decide) (by decide) K extent hK).finalEnergy
          (schedule extent) x))
        (normSq (conditionalGenerator (w := nome) (by decide) (by decide) K extent hK x)) :=
  ⟨existingNome_margin_positive, conditionalGenerator_square_lower
    (by decide) (by decide) existingNome_guards.1 existingNome_guards.2 K extent hK x⟩

#print axioms signedNeighborEnergy_lower
#print axioms conditionalGenerator_square_lower
#print axioms existingNome_generator_square_lower

end YMGap.Continuum.BF4ExactSlabConditionalGeneratorLowerBound
