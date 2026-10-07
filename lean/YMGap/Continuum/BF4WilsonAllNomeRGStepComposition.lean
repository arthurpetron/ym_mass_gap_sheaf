/-
# REDUCTION: RG-step composition for the Wilson gap frontier

Companion to `audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md`. ADDITIVE.

**REDUCTION ONLY.** No approximate intertwiner `Φ_j` is constructed.

`ApproxRgIntertwiner` (operator-level; rate transfer PROVED):
* coercive lower bound `B_f(x,x) ≤ κ·B_c(Φx,Φx)` with `κ > 0` (prevents `Φ = 0`);
* norm upper bound `B_c(Φx,Φx) ≤ B_f(x,x)` — together ⇒ `κ ≥ 1` on any
  vacuum vector with a positive Q' floor under the fine diagonal;
* `intertwine_twoStep`: `B_f(T_f² x) ≤ κ·B_c(T_c Φx) + (κ·ε)·B_f(x)`
  (two fine steps vs one coarse; B-form, no subtype subtraction).

Proved transfer: coarse VacSq at `rC` ⇒ fine **two-step** factor
`α = κ(rC²+ε)`. Dictionary: VacSq at `rF` implies two-step factor `rF⁴`, so
choosing `rF⁴ = α` gives `r_F⁴ ≤ κ(r_C²+ε)`, lining up with the 8a341453 algebra
`r_{j+1}² ≤ r_j + ε_j` after writing `u_j = r_j²` and absorbing `(κ−1)·r_C²` into
the effective defect `ε' = (κ−1)·r_C² + κ·ε`.

No-go (old one-step shape): an attaining fine Rayleigh `≥ r_C` forces
`r_C ≤ κ(r_C²+ε)`, hence `ε` cannot be tiny when `r_C/κ > r_C²`; weighted
`Σ 2^j ε_j` cannot stay small along AF under persistent attainders.

Also: SC cannot seed `trAF` (`not_heatRatio_le_half_afNome`). Seed = open
intermediate-coupling producer.

Constructive; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
import YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate
import YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay
import YMGap.Continuum.BF4ExactSlabDescentDistanceDecay
import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
import YMGap.Continuum.QuaternionHaarCharacterInterval
import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.HamiltonianScalar
import YMGap.Continuum.ReconstructionCapstone
import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.RCDistBridge
import YMGap.Constructive.HalfPow
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.Soundness
import YMGap.Constructive.AbsQ
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.Sqrt

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
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
  (afNomeSchedule afGap afGap_pos afGap_lt_one)
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRatio)
open YMGap.Continuum.HeatKernelGap (qpow_mono)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Constructive.SumOfSquares (q_mul_self_nonneg)
open YMGap.Continuum.GNSQuotient.GNSData (RCofQ'_le_reflect)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Optional identification `timeRate ≈ 1/4` -/

theorem timeRate_eq_one_fourth :
    timeRate ≈ Q'.mkPos 1 4 (by decide) :=
  comparison_entropy

/-! ## 1. Pure Q' rate algebra -/

/-- Rate-level shadow of one approx intertwiner (κ-free form). **REDUCTION.** -/
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

/-- κ-aware two-step rate relation: `rFine⁴ ≤ κ(rCoarse²+ε)`. -/
def RgRateRelationκ (rFine rCoarse ε κ : Q') : Prop :=
  (0 : Q') ≤ rFine ∧ rFine ≤ (1 : Q') ∧
    (0 : Q') ≤ ε ∧ (0 : Q') < κ ∧
      rFine * rFine * (rFine * rFine) ≤ κ * (rCoarse * rCoarse + ε) ∧
        κ * (rCoarse * rCoarse + ε) ≤ (1 : Q')

/-- Effective additive defect: `κ(r_C²+ε) = r_C² + effectiveRgDefect`. -/
def effectiveRgDefect (κ ε rC : Q') : Q' :=
  (κ + -((1 : Q'))) * (rC * rC) + κ * ε

theorem effectiveRgDefect_nonneg (κ ε rC : Q')
    (hκ : (1 : Q') ≤ κ) (hε : (0 : Q') ≤ ε) :
    (0 : Q') ≤ effectiveRgDefect κ ε rC := by
  have hκ1 : (0 : Q') ≤ κ + -((1 : Q')) := Q'.sub_nonneg_of_le hκ
  have hr2 : (0 : Q') ≤ rC * rC := q_mul_self_nonneg rC
  have hκ0 : (0 : Q') ≤ κ := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q')) hκ
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ hκ1 hr2) (Q'.mul_nonneg _ _ hκ0 hε)

theorem transfer_factor_as_coarse_sq_plus_defect (κ ε rC : Q') :
    κ * (rC * rC + ε) ≈ rC * rC + effectiveRgDefect κ ε rC :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.add (.mul (.var 1) (.var 1)) (.var 2)))
    (.add (.mul (.var 1) (.var 1))
      (.add (.mul (.add (.var 0) (.neg (.const 1))) (.mul (.var 1) (.var 1)))
        (.mul (.var 0) (.var 2))))
    (by decide)
    (fun | 0 => κ | 1 => rC | _ => ε)

/-- From `r⁴ ≤ α ≤ 1` and `0 ≤ r ≤ 1`: `(1−α)/4 ≤ 1−r`. -/
theorem margin_after_rg_step_κ (rFine rCoarse ε κ : Q')
    (H : RgRateRelationκ rFine rCoarse ε κ) :
    half * (half * ((1 : Q') - κ * (rCoarse * rCoarse + ε))) ≤
      (1 : Q') - rFine := by
  rcases H with ⟨hr0, hr1, _, _, hsq, _⟩
  have hu0 : (0 : Q') ≤ rFine * rFine := q_mul_self_nonneg rFine
  have hu1 : rFine * rFine ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ rFine hr1 hr0
    have h' : rFine * (1 : Q') ≤ (1 : Q') :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv rFine)) hr1
    exact Q'.le_trans' _ _ _ h h'
  have h1 : half * ((1 : Q') - κ * (rCoarse * rCoarse + ε)) ≤
      (1 : Q') - rFine * rFine := by
    have hmono : (1 : Q') - κ * (rCoarse * rCoarse + ε) ≤
        (1 : Q') - (rFine * rFine) * (rFine * rFine) :=
      Q'.add_le_add_left (1 : Q') _ _ (Q'.neg_le_neg hsq)
    have hhalf : half * ((1 : Q') - κ * (rCoarse * rCoarse + ε)) ≤
        half * ((1 : Q') - (rFine * rFine) * (rFine * rFine)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ half hmono half_nonneg
    exact Q'.le_trans' _ _ _ hhalf
      (one_sub_ge_half_one_sub_sq (rFine * rFine) hu0 hu1)
  have h2 : half * ((1 : Q') - rFine * rFine) ≤ (1 : Q') - rFine :=
    one_sub_ge_half_one_sub_sq rFine hr0 hr1
  have h3 : half * (half * ((1 : Q') - κ * (rCoarse * rCoarse + ε))) ≤
      half * ((1 : Q') - rFine * rFine) :=
    Q'.mul_le_mul_of_nonneg_left _ _ half h1 half_nonneg
  exact Q'.le_trans' _ _ _ h3 h2

/-! ## 2. Approx RG intertwiner (two-step; rate transfer PROVED) -/

def WilsonVacuumSqFactor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) (α : Q') : Prop :=
  ∀ y : VacuumComplement hw0 hw1 (width := width),
    RCle (completedInner hw0 hw1 (completedTime hw0 hw1 1 y.val)
            (completedTime hw0 hw1 1 y.val))
      (RCscale α (completedInner hw0 hw1 y.val y.val))

def WilsonVacuumSqTwoStepFactor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) (α : Q') : Prop :=
  ∀ y : VacuumComplement hw0 hw1 (width := width),
    RCle (completedInner hw0 hw1 (completedTime hw0 hw1 2 y.val)
            (completedTime hw0 hw1 2 y.val))
      (RCscale α (completedInner hw0 hw1 y.val y.val))

theorem wilsonVacuumSq_of_factor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')} {width : Nat}
    (r α : Q') (h : α ≤ r * r) (H : WilsonVacuumSqFactor hw0 hw1 width α) :
    WilsonVacuumSqContraction hw0 hw1 width r := fun y => by
  have hBf0 : RCnonneg (completedInner hw0 hw1 y.val y.val) :=
    completedInner_nonnegative hw0 hw1 y.val
  exact RCle_trans (H y) (RCscale_mono_scalar h hBf0)

theorem vacuumSq_implies_twoStepFactor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')} {width : Nat}
    (r : Q') (H : WilsonVacuumSqContraction hw0 hw1 width r) :
    WilsonVacuumSqTwoStepFactor hw0 hw1 width (r * r * (r * r)) := by
  intro y
  have h1 := H y
  have hr2 : (0 : Q') ≤ r * r := q_mul_self_nonneg r
  have h2raw := H ⟨completedTime hw0 hw1 1 y.val,
    completedTime_preserves_vacuumComplement hw0 hw1 1 y.val y.property⟩
  have h2' :
      RCle
        (completedInner hw0 hw1 (completedTime hw0 hw1 2 y.val)
          (completedTime hw0 hw1 2 y.val))
        (RCscale (r * r)
          (completedInner hw0 hw1 (completedTime hw0 hw1 1 y.val)
            (completedTime hw0 hw1 1 y.val))) := by
    have h := h2raw
    rw [← completedTime_add hw0 hw1 1 1 y.val] at h
    simpa [Nat.add_comm 1 1] using h
  have hscaled :
      RCle
        (RCscale (r * r)
          (completedInner hw0 hw1 (completedTime hw0 hw1 1 y.val)
            (completedTime hw0 hw1 1 y.val)))
        (RCscale (r * r * (r * r))
          (completedInner hw0 hw1 y.val y.val)) := by
    have h := RCscale_mono hr2 h1
    rw [RCscale_RCscale] at h
    exact h
  exact RCle_trans h2' hscaled

/-- **REDUCTION / OPEN to inhabit.** Two fine steps vs one coarse step. -/
structure ApproxRgIntertwiner
    {wF wC : Q'} (hwF0 : (0 : Q') < wF) (hwF1 : wF < (1 : Q'))
    (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q'))
    (widthF widthC : Nat) (ε κ : Q') where
  Φ :
    VacuumComplement hwF0 hwF1 (width := widthF) →
      VacuumComplement hwC0 hwC1 (width := widthC)
  kappa_pos : (0 : Q') < κ
  epsilon_nonneg : (0 : Q') ≤ ε
  lowerBound :
    ∀ x : VacuumComplement hwF0 hwF1 (width := widthF),
      RCle (completedInner hwF0 hwF1 x.val x.val)
        (RCscale κ (completedInner hwC0 hwC1 (Φ x).val (Φ x).val))
  upperBound :
    ∀ x : VacuumComplement hwF0 hwF1 (width := widthF),
      RCle (completedInner hwC0 hwC1 (Φ x).val (Φ x).val)
        (completedInner hwF0 hwF1 x.val x.val)
  intertwine_twoStep :
    ∀ x : VacuumComplement hwF0 hwF1 (width := widthF),
      RCle
        (completedInner hwF0 hwF1
          (completedTime hwF0 hwF1 2 x.val)
          (completedTime hwF0 hwF1 2 x.val))
        (RCadd
          (RCscale κ
            (completedInner hwC0 hwC1
              (completedTime hwC0 hwC1 1 (Φ x).val)
              (completedTime hwC0 hwC1 1 (Φ x).val)))
          (RCscale (κ * ε) (completedInner hwF0 hwF1 x.val x.val)))

private theorem rc_scale_add_right (s t : Q') (a : RC) :
    RCadd (RCscale s a) (RCscale t a) = RCscale (s + t) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
      (.mul (.add (.var 0) (.var 1)) (.var 2))
      (by decide) (fun | 0 => s | 1 => t | _ => A.approx n)))

private def ratQ (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem RCscale_ratQ (s q : Q') : RCscale s (ratQ q) = ratQ (s * q) :=
  Quotient.sound (CRealAlg.ofQ'_mul s q).symm

theorem approxRg_diagonal_le_kappa_diagonal
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {ε κ : Q'}
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 widthF widthC ε κ)
    (x : VacuumComplement hwF0 hwF1 (width := widthF)) :
    RCle (completedInner hwF0 hwF1 x.val x.val)
      (RCscale κ (completedInner hwF0 hwF1 x.val x.val)) := by
  have hκ0 : (0 : Q') ≤ κ := Q'.le_of_lt H.kappa_pos
  exact RCle_trans (H.lowerBound x) (RCscale_mono hκ0 (H.upperBound x))

private theorem one_le_of_delta_le_kappa_delta {κ δ : Q'}
    (hδ : (0 : Q') < δ) (h : δ ≤ κ * δ) : (1 : Q') ≤ κ := by
  have h' : δ * (1 : Q') ≤ δ * κ := by
    have h2 : δ ≤ δ * κ :=
      Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv κ δ))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv δ)) h2
  exact Q'.le_of_mul_le_mul_left h' hδ

/-- **PROVED.** If some fine vacuum diagonal is pinned to a positive rational
`δ` (floor and cap), lower+upper force `1 ≤ κ`. -/
theorem kappa_ge_one
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {ε κ : Q'}
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 widthF widthC ε κ)
    (x : VacuumComplement hwF0 hwF1 (width := widthF))
    (δ : Q') (hδ : (0 : Q') < δ)
    (hfloor : RCle (ratQ δ) (completedInner hwF0 hwF1 x.val x.val))
    (hcap : RCle (completedInner hwF0 hwF1 x.val x.val) (ratQ δ)) :
    (1 : Q') ≤ κ := by
  have hκ0 : (0 : Q') ≤ κ := Q'.le_of_lt H.kappa_pos
  have hself := approxRg_diagonal_le_kappa_diagonal H x
  have h1 : RCle (ratQ δ) (RCscale κ (completedInner hwF0 hwF1 x.val x.val)) :=
    RCle_trans hfloor hself
  have h2 : RCle (RCscale κ (completedInner hwF0 hwF1 x.val x.val))
      (RCscale κ (ratQ δ)) :=
    RCscale_mono hκ0 hcap
  have h3 : RCle (ratQ δ) (RCscale κ (ratQ δ)) := RCle_trans h1 h2
  rw [RCscale_ratQ] at h3
  have hδκ : δ ≤ κ * δ := RCofQ'_le_reflect h3
  exact one_le_of_delta_le_kappa_delta hδ hδκ

/-- **PROVED.** Coarse VacSq ⇒ fine two-step factor `κ(rC²+ε)`. **REDUCTION.** -/
theorem approxRg_transfers_twoStep_factor
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {ε κ : Q'}
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 widthF widthC ε κ)
    (rC : Q')
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC) :
    WilsonVacuumSqTwoStepFactor hwF0 hwF1 widthF (κ * (rC * rC + ε)) := by
  intro y
  have hκ0 : (0 : Q') ≤ κ := Q'.le_of_lt H.kappa_pos
  have hr2 : (0 : Q') ≤ rC * rC := q_mul_self_nonneg rC
  have hκr : (0 : Q') ≤ κ * (rC * rC) := Q'.mul_nonneg _ _ hκ0 hr2
  have hdef := H.intertwine_twoStep y
  have hcoarse := hc (H.Φ y)
  have hcoarseκ :
      RCle
        (RCscale κ (completedInner hwC0 hwC1
          (completedTime hwC0 hwC1 1 (H.Φ y).val)
          (completedTime hwC0 hwC1 1 (H.Φ y).val)))
        (RCscale κ (RCscale (rC * rC)
          (completedInner hwC0 hwC1 (H.Φ y).val (H.Φ y).val))) :=
    RCscale_mono hκ0 hcoarse
  have hcoarseκ' :
      RCle
        (RCscale κ (completedInner hwC0 hwC1
          (completedTime hwC0 hwC1 1 (H.Φ y).val)
          (completedTime hwC0 hwC1 1 (H.Φ y).val)))
        (RCscale (κ * (rC * rC))
          (completedInner hwC0 hwC1 (H.Φ y).val (H.Φ y).val)) := by
    rw [RCscale_RCscale] at hcoarseκ
    exact hcoarseκ
  have hupκ :
      RCle
        (RCscale (κ * (rC * rC))
          (completedInner hwC0 hwC1 (H.Φ y).val (H.Φ y).val))
        (RCscale (κ * (rC * rC))
          (completedInner hwF0 hwF1 y.val y.val)) :=
    RCscale_mono hκr (H.upperBound y)
  have hleft : RCle
      (RCscale κ (completedInner hwC0 hwC1
        (completedTime hwC0 hwC1 1 (H.Φ y).val)
        (completedTime hwC0 hwC1 1 (H.Φ y).val)))
      (RCscale (κ * (rC * rC)) (completedInner hwF0 hwF1 y.val y.val)) :=
    RCle_trans hcoarseκ' hupκ
  have hsum : RCle
      (RCadd
        (RCscale κ (completedInner hwC0 hwC1
          (completedTime hwC0 hwC1 1 (H.Φ y).val)
          (completedTime hwC0 hwC1 1 (H.Φ y).val)))
        (RCscale (κ * ε) (completedInner hwF0 hwF1 y.val y.val)))
      (RCadd
        (RCscale (κ * (rC * rC)) (completedInner hwF0 hwF1 y.val y.val))
        (RCscale (κ * ε) (completedInner hwF0 hwF1 y.val y.val))) :=
    RCadd_le_add hleft (RCle_refl _)
  have hadd :
      RCadd
        (RCscale (κ * (rC * rC)) (completedInner hwF0 hwF1 y.val y.val))
        (RCscale (κ * ε) (completedInner hwF0 hwF1 y.val y.val)) =
      RCscale (κ * (rC * rC) + κ * ε)
        (completedInner hwF0 hwF1 y.val y.val) :=
    rc_scale_add_right _ _ _
  have hfac : κ * (rC * rC) + κ * ε ≈ κ * (rC * rC + ε) :=
    Q'.eqv_symm (Q'.mul_add_eqv κ (rC * rC) ε)
  have hmid : RCle
      (RCadd
        (RCscale (κ * (rC * rC)) (completedInner hwF0 hwF1 y.val y.val))
        (RCscale (κ * ε) (completedInner hwF0 hwF1 y.val y.val)))
      (RCscale (κ * (rC * rC + ε))
        (completedInner hwF0 hwF1 y.val y.val)) := by
    rw [hadd, scale_congr hfac (completedInner hwF0 hwF1 y.val y.val)]
    exact RCle_refl _
  exact RCle_trans hdef (RCle_trans hsum hmid)


/-- Alias: the proved transfer is the two-step factor `κ(rC²+ε)`.
Choosing `rF` with `rF⁴ = κ(rC²+ε)` matches `vacuumSq_implies_twoStepFactor`.
**REDUCTION.** -/
theorem approxRg_transfers
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {ε κ : Q'}
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 widthF widthC ε κ)
    (rC : Q')
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC) :
    WilsonVacuumSqTwoStepFactor hwF0 hwF1 widthF (κ * (rC * rC + ε)) :=
  approxRg_transfers_twoStep_factor H rC hc

/-! ## 2b. No-go for the old one-step intertwining shape -/

/-- Old one-step defect (obstruction only). -/
def ApproxRgOneStepDefect
    {wF wC : Q'} (hwF0 : (0 : Q') < wF) (hwF1 : wF < (1 : Q'))
    (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q'))
    (widthF widthC : Nat) (ε κ : Q')
    (Φ :
      VacuumComplement hwF0 hwF1 (width := widthF) →
        VacuumComplement hwC0 hwC1 (width := widthC)) : Prop :=
  ∀ x : VacuumComplement hwF0 hwF1 (width := widthF),
    RCle
      (completedInner hwF0 hwF1
        (completedTime hwF0 hwF1 1 x.val)
        (completedTime hwF0 hwF1 1 x.val))
      (RCadd
        (RCscale κ
          (completedInner hwC0 hwC1
            (completedTime hwC0 hwC1 1 (Φ x).val)
            (completedTime hwC0 hwC1 1 (Φ x).val)))
        (RCscale (κ * ε) (completedInner hwF0 hwF1 x.val x.val)))

def VacRayleighAtLeast
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)
    (r : Q') (x : VacuumComplement hw0 hw1 (width := width)) : Prop :=
  RCle (RCscale r (completedInner hw0 hw1 x.val x.val))
    (completedInner hw0 hw1 (completedTime hw0 hw1 1 x.val)
      (completedTime hw0 hw1 1 x.val))

/-- Cancel positive right factor: `a·δ ≤ b·δ` and `0 < δ` ⇒ `a ≤ b`. -/
private theorem mul_le_cancel_pos_right {a b δ : Q'}
    (hδ : (0 : Q') < δ) (h : a * δ ≤ b * δ) : a ≤ b := by
  have h' : δ * a ≤ δ * b :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv δ a))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv b δ)))
  exact Q'.le_of_mul_le_mul_left h' hδ

/-- **No-go.** One-step defect + coarse VacSq + upper + attaining Rayleigh on a
diagonal pinned to `δ > 0` ⇒ `rC ≤ κ(rC²+ε)`. So if `rC/κ > rC²`, then `ε` is
bounded below and `Σ 2^j ε_j` cannot stay small under persistent attainders along AF.
**REDUCTION / obstruction to one-step typing.** -/
theorem oneStep_defect_forces_rate_le_kappa_factor
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {ε κ : Q'}
    (Φ :
      VacuumComplement hwF0 hwF1 (width := widthF) →
        VacuumComplement hwC0 hwC1 (width := widthC))
    (hκ : (0 : Q') < κ) (hε : (0 : Q') ≤ ε)
    (hup :
      ∀ x : VacuumComplement hwF0 hwF1 (width := widthF),
        RCle (completedInner hwC0 hwC1 (Φ x).val (Φ x).val)
          (completedInner hwF0 hwF1 x.val x.val))
    (hdef : ApproxRgOneStepDefect hwF0 hwF1 hwC0 hwC1 widthF widthC ε κ Φ)
    (rC : Q') (hr0 : (0 : Q') ≤ rC)
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC)
    (x : VacuumComplement hwF0 hwF1 (width := widthF))
    (hattain : VacRayleighAtLeast hwF0 hwF1 widthF rC x)
    (δ : Q') (hδ : (0 : Q') < δ)
    (hfloor : RCle (ratQ δ) (completedInner hwF0 hwF1 x.val x.val))
    (hcap : RCle (completedInner hwF0 hwF1 x.val x.val) (ratQ δ)) :
    rC ≤ κ * (rC * rC + ε) := by
  have hκ0 : (0 : Q') ≤ κ := Q'.le_of_lt hκ
  have hr2 : (0 : Q') ≤ rC * rC := q_mul_self_nonneg rC
  have hκr : (0 : Q') ≤ κ * (rC * rC) := Q'.mul_nonneg _ _ hκ0 hr2
  have hα0 : (0 : Q') ≤ κ * (rC * rC + ε) :=
    Q'.mul_nonneg _ _ hκ0 (Q'.zero_le_add _ _ hr2 hε)
  have hdefx := hdef x
  have hcoarse := hc (Φ x)
  have hcoarseκ := RCscale_mono hκ0 hcoarse
  have hcoarseκ' : RCle
      (RCscale κ (completedInner hwC0 hwC1
        (completedTime hwC0 hwC1 1 (Φ x).val)
        (completedTime hwC0 hwC1 1 (Φ x).val)))
      (RCscale (κ * (rC * rC))
        (completedInner hwC0 hwC1 (Φ x).val (Φ x).val)) := by
    rw [RCscale_RCscale] at hcoarseκ
    exact hcoarseκ
  have hleft := RCle_trans hcoarseκ' (RCscale_mono hκr (hup x))
  have hsum := RCadd_le_add hleft
    (RCle_refl (RCscale (κ * ε) (completedInner hwF0 hwF1 x.val x.val)))
  have hadd := rc_scale_add_right (κ * (rC * rC)) (κ * ε)
    (completedInner hwF0 hwF1 x.val x.val)
  have hfac : κ * (rC * rC) + κ * ε ≈ κ * (rC * rC + ε) :=
    Q'.eqv_symm (Q'.mul_add_eqv κ (rC * rC) ε)
  have hmid : RCle
      (RCadd
        (RCscale (κ * (rC * rC)) (completedInner hwF0 hwF1 x.val x.val))
        (RCscale (κ * ε) (completedInner hwF0 hwF1 x.val x.val)))
      (RCscale (κ * (rC * rC + ε))
        (completedInner hwF0 hwF1 x.val x.val)) := by
    rw [hadd, scale_congr hfac (completedInner hwF0 hwF1 x.val x.val)]
    exact RCle_refl _
  have hbound := RCle_trans hdefx (RCle_trans hsum hmid)
  have hL : RCle (RCscale rC (ratQ δ))
      (completedInner hwF0 hwF1 (completedTime hwF0 hwF1 1 x.val)
        (completedTime hwF0 hwF1 1 x.val)) :=
    RCle_trans (RCscale_mono hr0 hfloor) hattain
  have hR : RCle
      (completedInner hwF0 hwF1 (completedTime hwF0 hwF1 1 x.val)
        (completedTime hwF0 hwF1 1 x.val))
      (RCscale (κ * (rC * rC + ε)) (ratQ δ)) :=
    RCle_trans hbound (RCscale_mono hα0 hcap)
  have hchain := RCle_trans hL hR
  rw [RCscale_ratQ, RCscale_ratQ] at hchain
  exact mul_le_cancel_pos_right hδ (RCofQ'_le_reflect hchain)

/-- Corollary form: `rC ≤ κ(rC²+ε)` rearranges to a lower bound on `ε` when
`κ > 0`. Written as `rC ≤ κ·rC² + κ·ε`. **REDUCTION.** -/
theorem oneStep_epsilon_budget_form {rC κ ε : Q'}
    (h : rC ≤ κ * (rC * rC + ε)) :
    rC ≤ κ * (rC * rC) + κ * ε :=
  Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_add_eqv κ (rC * rC) ε))

/-! ## 3. Rate chains and margin recurrence -/

def weightedErrorSum (ε : Nat → Q') (j0 n : Nat) : Q' :=
  match n with
  | 0 => 0
  | n'+1 => weightedErrorSum ε j0 n' + Q'.ofNat (2 ^ n') * ε (j0 + n')

def RgErrorSummable (ε : Nat → Q') (j0 : Nat) (S : Q') : Prop :=
  (0 : Q') ≤ S ∧ ∀ n : Nat, weightedErrorSum ε j0 n ≤ S

/-- Persistent attainders with uniform `c ≤ ε_j` prevent `S < c`. **REDUCTION.** -/
def OneStepAfSumObstruction (ε : Nat → Q') (j0 : Nat) (c S : Q') : Prop :=
  (0 : Q') < c ∧ (∀ j, j0 ≤ j → c ≤ ε j) ∧ RgErrorSummable ε j0 S ∧ ¬ (S < c)

def RgRateChain (r ε : Nat → Q') (j0 : Nat) : Prop :=
  (∀ j, j0 ≤ j → (0 : Q') ≤ r j) ∧
    (∀ j, j0 ≤ j → r j ≤ (1 : Q')) ∧
      (∀ j, j0 ≤ j → (0 : Q') ≤ ε j) ∧
        (∀ j, j0 ≤ j → r (j + 1) * r (j + 1) ≤ r j + ε j) ∧
          (∀ j, j0 ≤ j → r j + ε j ≤ (1 : Q'))

def RgRateChainκ (r ε κ : Nat → Q') (j0 : Nat) : Prop :=
  (∀ j, j0 ≤ j → (0 : Q') ≤ r j) ∧
    (∀ j, j0 ≤ j → r j ≤ (1 : Q')) ∧
      (∀ j, j0 ≤ j → (0 : Q') ≤ ε j) ∧
        (∀ j, j0 ≤ j → (0 : Q') < κ j) ∧
          (∀ j, j0 ≤ j →
            r (j + 1) * r (j + 1) * (r (j + 1) * r (j + 1)) ≤
              κ j * (r j * r j + ε j)) ∧
            (∀ j, j0 ≤ j → κ j * (r j * r j + ε j) ≤ (1 : Q'))

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

theorem rgRateChainκ_step (r ε κ : Nat → Q') (j0 j : Nat)
    (H : RgRateChainκ r ε κ j0) (hj : j0 ≤ j) :
    RgRateRelationκ (r (j + 1)) (r j) (ε j) (κ j) :=
  ⟨H.1 _ (Nat.le_trans hj (Nat.le_succ j)),
    H.2.1 _ (Nat.le_trans hj (Nat.le_succ j)),
    H.2.2.1 _ hj, H.2.2.2.1 _ hj, H.2.2.2.2.1 _ hj, H.2.2.2.2.2 _ hj⟩

theorem rg_margin_step_κ (r ε κ : Nat → Q') (j0 j : Nat)
    (H : RgRateChainκ r ε κ j0) (hj : j0 ≤ j) :
    half * (half * ((1 : Q') - κ j * (r j * r j + ε j))) ≤
      (1 : Q') - r (j + 1) :=
  margin_after_rg_step_κ (r (j + 1)) (r j) (ε j) (κ j)
    (rgRateChainκ_step r ε κ j0 j H hj)

def effectiveDefectSeq (κ ε r : Nat → Q') (j : Nat) : Q' :=
  effectiveRgDefect (κ j) (ε j) (r j)

def latticeMarginOf (r : Nat → Q') (j : Nat) : Q' := (1 : Q') - r j

/-! ## 4. Margin envelope ⇒ dyadic lower margin at seed scale 0 -/

def RgMarginEnvelope (r ε : Nat → Q') (j0 : Nat) (S : Q') : Prop :=
  RgRateChain r ε j0 ∧ RgErrorSummable ε j0 S ∧
    S < (1 : Q') - r j0 ∧
      ∀ n : Nat, half ^ n * ((1 : Q') - r j0 - S) ≤ latticeMarginOf r (j0 + n)

def rgSeedMargin (r : Nat → Q') (S : Q') : Q' := (1 : Q') - r 0 - S

def WilsonLowerMarginFrom (F : WilsonDynamicFamily) (j0 : Nat) (m : Q') : Prop :=
  (0 : Q') < m ∧
    ∀ j, j0 ≤ j → m * F.transferSpacing.spacing j ≤ (1 : Q') - F.rate j

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

/-! ## 5. Strong-coupling seed (pilot only; does NOT apply to trAF) -/

/-- At the pilot nome `1/1024`, every literal width carries VacSq at `timeRate`.
This does **not** seed `trAF` / `afNomeSchedule`: every AF scale fails the
`heatRatio ≤ 1/2` guard (see §6). **REDUCTION / pilot seed only.** -/
theorem strongCoupling_seed_at_pilot (width : Nat) :
    WilsonVacuumSqContraction nome_pos nome_lt_one width timeRate :=
  allNome_strongCoupling_vacuumSq nome_pos nome_lt_one
    existingNome_guards.1 existingNome_guards.2 existingNome_entropyRate.2 width

/-! ## 6. AF schedule is outside the strong-coupling window -/

private theorem lt_of_lt_of_le_q {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hcd : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 had
    have hl : (a.den : Int) * (b.num * (c.den : Int))
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int))
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

private theorem not_lt_of_le_q {a b : Q'} (h : a ≤ b) : ¬ (b < a) := by
  intro hlt
  have : b.num * (b.den : Int) < b.num * (b.den : Int) :=
    lt_of_lt_of_le_q hlt h
  exact (Int.lt_irrefl _) this

private theorem not_le_of_gt_q {a b : Q'} (h : b < a) : ¬ (a ≤ b) :=
  fun hle => absurd h (not_lt_of_le_q hle)

/-- `afGap 0 = 234982/484000 < 1/2`. -/
theorem afGap_zero_lt_half : afGap 0 < half := by
  change (afGap 0).num * (half.den : Int) < half.num * ((afGap 0).den : Int)
  decide

/-- `w_0 = 1 − afGap 0 > 1/2` (cross-multiply form). -/
theorem afNome_zero_gt_half : half < afNomeSchedule.nome 0 := by
  change half.num * ((afNomeSchedule.nome 0).den : Int) <
    (afNomeSchedule.nome 0).num * (half.den : Int)
  decide

/-- Every AF scale has `w_j ≥ w_0 > 1/2`. -/
theorem afNome_ge_zero (j : Nat) : afNomeSchedule.nome 0 ≤ afNomeSchedule.nome j := by
  induction j with
  | zero => exact Q'.le_refl' _
  | succ j ih => exact Q'.le_trans' _ _ _ ih (afNomeSchedule.nome_mono j)

private theorem heatRatio_mono_local {u v : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v) :
    heatRatio u ≤ heatRatio v := by
  unfold heatRatio
  have hp : YMGap.Continuum.RGTransport.qpow u 3 ≤
      YMGap.Continuum.RGTransport.qpow v 3 :=
    qpow_mono hu0 huv 3
  have hleft : (2 : Q') * YMGap.Continuum.RGTransport.qpow u 3 ≤
      2 * YMGap.Continuum.RGTransport.qpow v 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 hp (by decide)
  exact Q'.mul_le_mul_of_nonneg_right _ _ 16 hleft (by decide)

/-- `heatRatio(1/2) = 4 > 1/2`. -/
theorem heatRatio_half_gt_half : half < heatRatio half := by
  unfold heatRatio
  decide

/-- No AF scale satisfies `heatRatio ≤ 1/2`. Hence the three SC guards fail
everywhere on `trAF` / `afNomeSchedule`, and strong coupling cannot seed that
trajectory. The seed remains an **open intermediate-coupling** contraction
producer. -/
theorem not_heatRatio_le_half_afNome (j : Nat) :
    ¬ (heatRatio (afNomeSchedule.nome j) ≤ half) := by
  intro hle
  have hw0 : (0 : Q') ≤ half := half_nonneg
  have hge : half ≤ afNomeSchedule.nome j :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt afNome_zero_gt_half) (afNome_ge_zero j)
  have hmono : heatRatio half ≤ heatRatio (afNomeSchedule.nome j) :=
    heatRatio_mono_local hw0 hge
  have hgt : half < heatRatio half := heatRatio_half_gt_half
  have hcontr : half < heatRatio (afNomeSchedule.nome j) :=
    lt_of_lt_of_le_q hgt hmono
  exact absurd hle (not_le_of_gt_q hcontr)

end YMGap.Continuum.BF4WilsonAllNomeRGStepComposition

#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.timeRate_eq_one_fourth
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.one_sub_ge_half_one_sub_sq
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.margin_after_rg_step
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.margin_after_rg_step_κ
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.transfer_factor_as_coarse_sq_plus_defect
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.effectiveRgDefect_nonneg
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.wilsonVacuumSq_of_factor
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.vacuumSq_implies_twoStepFactor
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.approxRg_transfers_twoStep_factor
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.kappa_ge_one
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.oneStep_defect_forces_rate_le_kappa_factor
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_margin_step
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_margin_step_κ
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_envelope_zero_lower_margin
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_envelope_zero_wilsonLowerMargin
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.strongCoupling_seed_at_pilot
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.afGap_zero_lt_half
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.afNome_zero_gt_half
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.not_heatRatio_le_half_afNome
