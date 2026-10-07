/-
# REDUCTION: RG-step composition for the Wilson gap frontier

Companion to `audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md`. ADDITIVE.

**REDUCTION ONLY.** No approximate intertwiner `Φ_j` is constructed. Exact Wilson
intertwiners almost certainly do not exist; any honest `ε_j` needs Balaban-style
(or equivalent) quantitative RG estimates. That analytic input is OPEN.

Proved: pure Q' rate algebra (`rFine² ≤ rCoarse+ε ⇒ 1−rFine ≥ (1−rCoarse−ε)/2`);
typed `ApproxRgIntertwiner` (map + open transfer Prop); margin recurrence;
conditional dyadic lower-margin packaging from a margin envelope at seed scale 0.
Not proved: any `Φ_j`, any concrete `ε_j`, unconditional `WilsonAFPaddedGapInput`
on `trAF`, or any AF/continuum claim. SC seeds only scales still in the window.

Optional: `timeRate ≈ 1/4` via `comparison_entropy`.

Constructive; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
import YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate
import YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay
import YMGap.Continuum.BF4ExactSlabDescentDistanceDecay
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Constructive.HalfPow
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.Soundness
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.BF4WilsonAllNomeRGStepComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction
  (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
  (WilsonDynamicFamily WilsonLowerMargin)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.Continuum.BF4ExactSlabDescentDistanceDecay (comparison_entropy)
open YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate
  (allNome_strongCoupling_vacuumSq)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Optional identification `timeRate ≈ 1/4` -/

theorem timeRate_eq_one_fourth :
    timeRate ≈ Q'.mkPos 1 4 (by decide) :=
  comparison_entropy

/-! ## 1. Pure Q' rate algebra -/

/-- Rate-level shadow of one approx intertwiner. **REDUCTION.** -/
def RgRateRelation (rFine rCoarse ε : Q') : Prop :=
  (0 : Q') ≤ rFine ∧ rFine ≤ (1 : Q') ∧
    (0 : Q') ≤ ε ∧ rFine * rFine ≤ rCoarse + ε ∧ rCoarse + ε ≤ (1 : Q')

private theorem two_margin_identity (r : Q') :
    ((1 : Q') - r) + ((1 : Q') - r) + -((1 : Q') - r * r) ≈
      ((1 : Q') - r) * ((1 : Q') - r) :=
  poly_identity_of_normal_eq
    (.add (.add (.add (.const 1) (.neg (.var 0)))
                (.add (.const 1) (.neg (.var 0))))
          (.neg (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))))
    (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
    (by decide)
    (fun | 0 => r | _ => 0)

private theorem half_mul_two_right (a : Q') : half * (a + a) ≈ a := by
  have h2 : half * Q'.ofNat 2 ≈ (1 : Q') := by decide
  have hsum : Q'.ofNat 2 * a ≈ a + a :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ a
        (by decide : Q'.eqv (Q'.ofNat 2) ((1 : Q') + (1 : Q'))))
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv ((1 : Q') + (1 : Q')) a)
        (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv a (1 : Q') (1 : Q'))
          (Q'.add_eqv_congr' (Q'.mul_one_eqv a) (Q'.mul_one_eqv a))))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ (Q'.eqv_symm hsum))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half (Q'.ofNat 2) a))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a h2) (Q'.one_mul_eqv a)))

private theorem add_of_add_neg {A B C : Q'} (h : A + -B ≈ C) : A ≈ C + B := by
  have hz : ((-B) + B) ≈ (0 : Q') := Q'.neg_add_self_eqv B
  have h1 : A ≈ A + ((-B) + B) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left A _ _ hz) (Q'.eqv_of_eq (Q'.add_zero' A)))
  have h2 : A + ((-B) + B) ≈ (A + -B) + B :=
    Q'.eqv_symm (Q'.add_assoc_eqv A (-B) B)
  exact Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.add_eqv_congr_right _ _ B h))

private theorem cancel_add_left {X Y Z : Q'} (h : X + Y ≈ Z) : Y ≈ Z + -X := by
  have h1 : Y ≈ (X + Y) + -X :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv X Y (-X))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left X _ _ (Q'.add_comm_eqv Y (-X)))
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv X (-X) Y))
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ Y
              (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv X (-X)) (Q'.neg_add_self_eqv X)))
            (Q'.eqv_of_eq (Q'.zero_add' Y))))))
  exact Q'.eqv_trans _ _ _ h1 (Q'.add_eqv_congr_right _ _ (-X) h)

/-- `0 ≤ r ≤ 1 ⇒ (1 − r²)/2 ≤ 1 − r`. -/
theorem one_sub_ge_half_one_sub_sq (r : Q')
    (_hr0 : (0 : Q') ≤ r) (hr1 : r ≤ (1 : Q')) :
    half * ((1 : Q') - r * r) ≤ (1 : Q') - r := by
  have hdiff0 : (0 : Q') ≤ (1 : Q') - r := Q'.sub_nonneg_of_le hr1
  have hsq0 : (0 : Q') ≤ ((1 : Q') - r) * ((1 : Q') - r) :=
    Q'.mul_nonneg _ _ hdiff0 hdiff0
  have hA : ((1 : Q') - r) + ((1 : Q') - r) ≈
      ((1 : Q') - r) * ((1 : Q') - r) + ((1 : Q') - r * r) :=
    add_of_add_neg (two_margin_identity r)
  have hhalfA : half * (((1 : Q') - r) + ((1 : Q') - r)) ≈ (1 : Q') - r :=
    half_mul_two_right ((1 : Q') - r)
  have hhalfSplit : half *
      (((1 : Q') - r) * ((1 : Q') - r) + ((1 : Q') - r * r)) ≈
      half * (((1 : Q') - r) * ((1 : Q') - r)) + half * ((1 : Q') - r * r) :=
    Q'.mul_add_eqv half _ _
  have hsum : half * (((1 : Q') - r) * ((1 : Q') - r)) +
      half * ((1 : Q') - r * r) ≈ (1 : Q') - r :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hhalfSplit)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left half _ _ (Q'.eqv_symm hA)) hhalfA)
  have hrearr : half * ((1 : Q') - r * r) ≈
      ((1 : Q') - r) + -(half * (((1 : Q') - r) * ((1 : Q') - r))) :=
    cancel_add_left hsum
  have hnn : (0 : Q') ≤ half * (((1 : Q') - r) * ((1 : Q') - r)) :=
    Q'.mul_nonneg _ _ half_nonneg hsq0
  have hneg : -(half * (((1 : Q') - r) * ((1 : Q') - r))) ≤ (0 : Q') :=
    Q'.neg_le_neg hnn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearr)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_left ((1 : Q') - r) _ _ hneg)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))))

/-- YM Bot: `rFine² ≤ rCoarse + ε` ⇒ `1 − rFine ≥ (1 − rCoarse − ε)/2`. -/
theorem margin_after_rg_step (rFine rCoarse ε : Q')
    (H : RgRateRelation rFine rCoarse ε) :
    half * ((1 : Q') - (rCoarse + ε)) ≤ (1 : Q') - rFine := by
  rcases H with ⟨hr0, hr1, _, hsq, _⟩
  have h1 := one_sub_ge_half_one_sub_sq rFine hr0 hr1
  have hmono : (1 : Q') - (rCoarse + ε) ≤ (1 : Q') - rFine * rFine :=
    Q'.add_le_add_left (1 : Q') _ _ (Q'.neg_le_neg hsq)
  have h2 : half * ((1 : Q') - (rCoarse + ε)) ≤
      half * ((1 : Q') - rFine * rFine) :=
    Q'.mul_le_mul_of_nonneg_left _ _ half hmono half_nonneg
  exact Q'.le_trans' _ _ _ h2 h1

/-! ## 2. Approx RG intertwiner (typed; NOT inhabited) -/

/-- **REDUCTION / OPEN.** Approximate RG step from fine to coarse.
`Φ` is typed but never constructed. `transfersRate` is the rate-level
analytic commitment that intertwining estimates must discharge. -/
structure ApproxRgIntertwiner
    {wF wC : Q'} (hwF0 : (0 : Q') < wF) (hwF1 : wF < (1 : Q'))
    (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q'))
    (widthF widthC : Nat) (ε : Q') where
  Φ :
    VacuumComplement hwF0 hwF1 (width := widthF) →
      VacuumComplement hwC0 hwC1 (width := widthC)
  epsilon_nonneg : (0 : Q') ≤ ε
  transfersRate :
    ∀ rC rF : Q',
      WilsonVacuumSqContraction hwC0 hwC1 widthC rC →
        RgRateRelation rF rC ε →
          WilsonVacuumSqContraction hwF0 hwF1 widthF rF

theorem approxRg_transfers
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {ε : Q'}
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 widthF widthC ε)
    (rC rF : Q')
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC)
    (hr : RgRateRelation rF rC ε) :
    WilsonVacuumSqContraction hwF0 hwF1 widthF rF :=
  H.transfersRate rC rF hc hr

/-! ## 3. Rate chains and one-step margin recurrence -/

def weightedErrorSum (ε : Nat → Q') (j0 n : Nat) : Q' :=
  match n with
  | 0 => 0
  | n'+1 => weightedErrorSum ε j0 n' + Q'.ofNat (2 ^ n') * ε (j0 + n')

def RgErrorSummable (ε : Nat → Q') (j0 : Nat) (S : Q') : Prop :=
  (0 : Q') ≤ S ∧ ∀ n : Nat, weightedErrorSum ε j0 n ≤ S

def RgRateChain (r ε : Nat → Q') (j0 : Nat) : Prop :=
  (∀ j, j0 ≤ j → (0 : Q') ≤ r j) ∧
    (∀ j, j0 ≤ j → r j ≤ (1 : Q')) ∧
      (∀ j, j0 ≤ j → (0 : Q') ≤ ε j) ∧
        (∀ j, j0 ≤ j → r (j + 1) * r (j + 1) ≤ r j + ε j) ∧
          (∀ j, j0 ≤ j → r j + ε j ≤ (1 : Q'))

theorem rgRateChain_step (r ε : Nat → Q') (j0 j : Nat)
    (H : RgRateChain r ε j0) (hj : j0 ≤ j) :
    RgRateRelation (r (j + 1)) (r j) (ε j) :=
  ⟨H.1 _ (Nat.le_trans hj (Nat.le_succ j)),
    H.2.1 _ (Nat.le_trans hj (Nat.le_succ j)),
    H.2.2.1 _ hj, H.2.2.2.1 _ hj, H.2.2.2.2 _ hj⟩

theorem rg_margin_step (r ε : Nat → Q') (j0 j : Nat)
    (H : RgRateChain r ε j0) (hj : j0 ≤ j) :
    half * ((1 : Q') - (r j + ε j)) ≤ (1 : Q') - r (j + 1) :=
  margin_after_rg_step (r (j + 1)) (r j) (ε j) (rgRateChain_step r ε j0 j H hj)

def latticeMarginOf (r : Nat → Q') (j : Nat) : Q' := (1 : Q') - r j

/-! ## 4. Margin envelope ⇒ dyadic lower margin at seed scale 0 -/

/-- Inductive envelope from iterating `rg_margin_step` against a weighted-error
budget. Discharging this for concrete Wilson `ε_j` is OPEN. **REDUCTION.** -/
def RgMarginEnvelope (r ε : Nat → Q') (j0 : Nat) (S : Q') : Prop :=
  RgRateChain r ε j0 ∧ RgErrorSummable ε j0 S ∧
    S < (1 : Q') - r j0 ∧
      ∀ n : Nat, half ^ n * ((1 : Q') - r j0 - S) ≤ latticeMarginOf r (j0 + n)

/-- Seed-scale-0 margin constant: `m = 1 − r_0 − S`. -/
def rgSeedMargin (r : Nat → Q') (S : Q') : Q' := (1 : Q') - r 0 - S

/-- Truncated lower margin from scale `j0` (full `WilsonLowerMargin` = `j0 = 0`
when the family's spacing is dyadic). **REDUCTION.** -/
def WilsonLowerMarginFrom (F : WilsonDynamicFamily) (j0 : Nat) (m : Q') : Prop :=
  (0 : Q') < m ∧
    ∀ j, j0 ≤ j → m * F.transferSpacing.spacing j ≤ (1 : Q') - F.rate j

/-- At seed scale 0, with dyadic spacing `half^j`, an envelope yields a truncated
(and hence full) lower-margin shape with `m = 1 − r_0 − S`.
This is the rate half of a conditional `WilsonAFPaddedGapInput`. **REDUCTION.** -/
theorem rg_envelope_zero_lower_margin
    (F : WilsonDynamicFamily) (ε : Nat → Q') (S : Q')
    (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (H : RgMarginEnvelope F.rate ε 0 S)
    (hm0 : (0 : Q') < rgSeedMargin F.rate S) :
    WilsonLowerMarginFrom F 0 (rgSeedMargin F.rate S) := by
  refine ⟨hm0, ?_⟩
  intro j _
  have henv : half ^ j * rgSeedMargin F.rate S ≤ (1 : Q') - F.rate j := by
    simpa [rgSeedMargin, latticeMarginOf] using H.2.2.2 j
  rw [hsp j]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) henv

/-- Specialisation: envelope at 0 + dyadic spacing ⇒ `WilsonLowerMargin`
when the family's `latticeMargin` is `1 − rate`. **REDUCTION.** -/
theorem rg_envelope_zero_wilsonLowerMargin
    (F : WilsonDynamicFamily) (ε : Nat → Q') (S : Q')
    (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (H : RgMarginEnvelope F.rate ε 0 S)
    (hm0 : (0 : Q') < rgSeedMargin F.rate S) :
    WilsonLowerMargin F (rgSeedMargin F.rate S) := by
  have h := rg_envelope_zero_lower_margin F ε S hsp H hm0
  exact ⟨h.1, fun j => by
    have := h.2 j (Nat.zero_le j)
    simpa only [WilsonDynamicFamily.latticeMargin] using this⟩

/-! ## 5. Strong-coupling seed availability (window only) -/

/-- At the pilot nome `1/1024`, every literal width carries VacSq at `timeRate`.
This may seed an RG chain only while the schedule remains in the small-nome
window; on `trAF`, `w_j → 1` and eventually exits. **REDUCTION / seed.** -/
theorem strongCoupling_seed_at_pilot (width : Nat) :
    WilsonVacuumSqContraction nome_pos nome_lt_one width timeRate :=
  allNome_strongCoupling_vacuumSq nome_pos nome_lt_one
    existingNome_guards.1 existingNome_guards.2 existingNome_entropyRate.2 width

end YMGap.Continuum.BF4WilsonAllNomeRGStepComposition

#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.timeRate_eq_one_fourth
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.one_sub_ge_half_one_sub_sq
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.margin_after_rg_step
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.approxRg_transfers
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_margin_step
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_envelope_zero_lower_margin
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_envelope_zero_wilsonLowerMargin
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.strongCoupling_seed_at_pilot
