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

**Envelope PROVED (no longer assumed).** From `RgRateChainκ`, `Σ 2^k eff_k ≤ S`
(`eff = (κ−1)r² + κε`) and the B04 upper half `m_{j0+n} ≤ U·2^{-n}`:
`2^n·m_{j0+n} ≥ m_{j0} − U² − S/2` (`rgKappa_dyadic_envelope`; absolute
`U = M·2^{-j0}`, c = 1 form `≥ m_{j0} − (M²+S)` in `rgKappa_dyadic_envelope_abs`).
`rg_envelope_zero_lower_margin` / `rg_envelope_zero_wilsonLowerMargin` now go
through the κ chain with seed `m_0 − M² − S/2`. Non-vacuous only when
`m_{j0} > U² + S/2`; since `m_{j0} ≤ U`, this needs `U < 1`, i.e. `j0 > log₂ M`.
Spacing: `exprWilsonFamily` (hence `trAF`) has `spacing j = half^j` by `rfl`.

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
  (WilsonDynamicFamily WilsonLowerMargin WilsonUpperMargin exprWilsonFamily)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory (ExprAnchorTrajectory)
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

/-! ## 3b. PROVED dyadic envelope from the κ chain (REDUCTION)

Step (from `margin_after_rg_step_κ`, with `m_j = 1 − r_j`,
`eff_j = effectiveRgDefect κ_j ε_j r_j = (κ_j−1)r_j² + κ_jε_j`):
`m_{j+1} ≥ m_j/2 − (m_j² + eff_j)/4`
(since `1 − κ(r²+ε) = 1 − r² − eff = 2m − m² − eff`).

Scaled `a_n = 2^n·m_{j0+n}`: `a_{n+1} ≥ a_n − 2^{n−1}m² − 2^{n−1}eff`.
With the relative upper margin `m_{j0+n} ≤ U·2^{-n}` (B04 upper half;
absolute form `U = M·2^{-j0}`): `2^{n−1}m² ≤ U²·2^{-(n+1)}`, so telescoping gives
`a_n ≥ m_{j0} − U²·Σ_{k<n}2^{-(k+1)} − ½·Σ_{k<n}2^k eff_{j0+k}
     ≥ m_{j0} − U² − S/2`.
The quadratic `m²` term genuinely needs the upper margin. -/

theorem two_mul_half_eqv : (2 : Q') * half ≈ (1 : Q') := by decide

theorem ofNat_nonneg_rg (k : Nat) : (0 : Q') ≤ Q'.ofNat k := by
  show (0 : Int) * 1 ≤ (k : Int) * 1
  rw [Int.mul_one, Int.mul_one]
  exact Int.natCast_nonneg k

theorem ofNat_two_pow_succ_eqv (n : Nat) :
    Q'.ofNat (2 ^ (n + 1)) ≈ (2 : Q') * Q'.ofNat (2 ^ n) := by
  show ((2 ^ (n + 1) : Nat) : Int) * 1 = ((2 : Int) * ((2 ^ n : Nat) : Int)) * 1
  rw [Nat.pow_succ, Int.natCast_mul, Int.mul_comm (((2 ^ n : Nat)) : Int)]
  rfl

theorem ofNat_two_pow_mul_half_pow (n : Nat) :
    Q'.ofNat (2 ^ n) * half ^ n ≈ (1 : Q') := by
  induction n with
  | zero => decide
  | succ n ih =>
    have e1 : Q'.ofNat (2 ^ (n + 1)) * half ^ (n + 1) ≈
        ((2 : Q') * Q'.ofNat (2 ^ n)) * (half * half ^ n) :=
      Q'.mul_eqv_congr_right _ _ _ (ofNat_two_pow_succ_eqv n)
    have e2 : ((2 : Q') * Q'.ofNat (2 ^ n)) * (half * half ^ n) ≈
        ((2 : Q') * half) * (Q'.ofNat (2 ^ n) * half ^ n) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide)
        (fun | 0 => (2 : Q') | 1 => Q'.ofNat (2 ^ n) | 2 => half | _ => half ^ n)
    have e3 : ((2 : Q') * half) * (Q'.ofNat (2 ^ n) * half ^ n) ≈
        (1 : Q') * (1 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ two_mul_half_eqv)
        (Q'.mul_eqv_congr_left _ _ _ ih)
    exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2
      (Q'.eqv_trans _ _ _ e3 (by decide)))

/-- `G n = Σ_{k<n} half^{k+1}`. -/
def halfGeomSum : Nat → Q'
  | 0 => 0
  | n + 1 => halfGeomSum n + half ^ (n + 1)

theorem halfGeomSum_add_pow (n : Nat) : halfGeomSum n + half ^ n ≈ (1 : Q') := by
  induction n with
  | zero => decide
  | succ n ih =>
    have e1 : (halfGeomSum n + half ^ (n + 1)) + half ^ (n + 1) ≈
        halfGeomSum n + ((2 : Q') * half) * half ^ n :=
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 2)))
        (.add (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
        (by decide)
        (fun | 0 => halfGeomSum n | 1 => half | _ => half ^ n)
    have e2 : halfGeomSum n + ((2 : Q') * half) * half ^ n ≈
        halfGeomSum n + (1 : Q') * half ^ n :=
      Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ two_mul_half_eqv)
    have e3 : halfGeomSum n + (1 : Q') * half ^ n ≈ halfGeomSum n + half ^ n :=
      poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.const 1) (.var 1)))
        (.add (.var 0) (.var 1))
        (by decide)
        (fun | 0 => halfGeomSum n | _ => half ^ n)
    exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 ih))

theorem halfGeomSum_le_one (n : Nat) : halfGeomSum n ≤ (1 : Q') := by
  have hp : (0 : Q') ≤ half ^ n := Q'.pow_nonneg half half_nonneg n
  have h1 : halfGeomSum n + (0 : Q') ≤ halfGeomSum n + half ^ n :=
    Q'.add_le_add_left _ _ _ hp
  rw [Q'.add_zero'] at h1
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (halfGeomSum_add_pow n))

theorem half_pow_add_eqv (a n : Nat) : half ^ (a + n) ≈ half ^ a * half ^ n := by
  induction n with
  | zero =>
    exact Q'.eqv_symm (Q'.mul_one_eqv (half ^ a))
  | succ n ih =>
    have e1 : half ^ (a + (n + 1)) ≈ half * (half ^ a * half ^ n) :=
      Q'.mul_eqv_congr_left half _ _ ih
    have e2 : half * (half ^ a * half ^ n) ≈ half ^ a * (half * half ^ n) :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide)
        (fun | 0 => half | 1 => half ^ a | _ => half ^ n)
    exact Q'.eqv_trans _ _ _ e1 e2

theorem half_pow_le_one (n : Nat) : half ^ n ≤ (1 : Q') := by
  induction n with
  | zero => exact Q'.le_refl' _
  | succ n ih =>
    have h1 : half * half ^ n ≤ half * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg_left _ _ half ih half_nonneg
    exact Q'.le_trans' _ _ _ h1 (by decide)

/-- If `c ≈ 1` then `c·c·X − c·Y − c·Z ≈ X − Y − Z`. -/
theorem c_one_collapse {c : Q'} (hc : c ≈ (1 : Q')) (X Y Z : Q') :
    c * c * X + -(c * Y) + -(c * Z) ≈ X + -Y + -Z := by
  have e1 : c * c * X + -(c * Y) + -(c * Z) ≈
      (1 : Q') * (1 : Q') * X + -((1 : Q') * Y) + -((1 : Q') * Z) :=
    Q'.add_eqv_congr' (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hc) (Q'.mul_eqv_congr_left _ _ _ hc)))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hc)))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hc))
  have e2 : (1 : Q') * (1 : Q') * X + -((1 : Q') * Y) + -((1 : Q') * Z) ≈
      X + -Y + -Z :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.const 1) (.const 1)) (.var 0))
        (.neg (.mul (.const 1) (.var 1)))) (.neg (.mul (.const 1) (.var 2))))
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
      (by decide)
      (fun | 0 => X | 1 => Y | _ => Z)
  exact Q'.eqv_trans _ _ _ e1 e2

theorem half_le_one_rg : half ≤ (1 : Q') := by decide

/-- Pure algebra of one scaled κ-step. -/
theorem scaled_step_core (t m m' E U hn : Q')
    (hstep : half * (half * (m + m + -(m * m) + -E)) ≤ m')
    (ht0 : (0 : Q') ≤ t) (hm0 : (0 : Q') ≤ m) (hU0 : (0 : Q') ≤ U)
    (hmU : m ≤ U * hn) (hthn : t * hn ≈ (1 : Q')) :
    t * m + -(U * U * (half * hn)) + -(half * (t * E)) ≤ ((2 : Q') * t) * m' := by
  have h2t : (0 : Q') ≤ (2 : Q') * t := Q'.mul_nonneg _ _ (by decide) ht0
  have A1 : ((2 : Q') * t) * (half * (half * (m + m + -(m * m) + -E))) ≤
      ((2 : Q') * t) * m' :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hstep h2t
  have e2 : ((2 : Q') * t) * (half * (half * (m + m + -(m * m) + -E))) ≈
      ((2 : Q') * half) * ((2 : Q') * half) * (t * m) +
        -(((2 : Q') * half) * (half * (t * (m * m)))) +
        -(((2 : Q') * half) * (half * (t * E))) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0))
        (.mul (.var 1) (.mul (.var 1)
          (.add (.add (.add (.var 2) (.var 2)) (.neg (.mul (.var 2) (.var 2))))
            (.neg (.var 3))))))
      (.add (.add
        (.mul (.mul (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 1)))
          (.mul (.var 0) (.var 2)))
        (.neg (.mul (.mul (.const 2) (.var 1))
          (.mul (.var 1) (.mul (.var 0) (.mul (.var 2) (.var 2)))))))
        (.neg (.mul (.mul (.const 2) (.var 1))
          (.mul (.var 1) (.mul (.var 0) (.var 3))))))
      (by decide)
      (fun | 0 => t | 1 => half | 2 => m | _ => E)
  have e3 := c_one_collapse two_mul_half_eqv (t * m)
    (half * (t * (m * m))) (half * (t * E))
  -- bound on the quadratic term
  have b1 : m * m ≤ m * (U * hn) := Q'.mul_le_mul_of_nonneg_left _ _ m hmU hm0
  have b2 : t * (m * m) ≤ t * (m * (U * hn)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ t b1 ht0
  have b3 : t * (m * (U * hn)) ≈ (U * m) * (t * hn) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3)))
      (by decide)
      (fun | 0 => t | 1 => m | 2 => U | _ => hn)
  have b4 : (U * m) * (t * hn) ≈ U * m :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hthn) (Q'.mul_one_eqv _)
  have b5 : U * m ≤ U * (U * hn) := Q'.mul_le_mul_of_nonneg_left _ _ U hmU hU0
  have b25 : t * (m * m) ≤ U * (U * hn) :=
    Q'.le_trans' _ _ _ b2 (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ b3 b4)) b5)
  have b6 : half * (t * (m * m)) ≤ half * (U * (U * hn)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ half b25 half_nonneg
  have b7 : half * (U * (U * hn)) ≈ U * U * (half * hn) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide)
      (fun | 0 => half | 1 => U | _ => hn)
  have B : half * (t * (m * m)) ≤ U * U * (half * hn) :=
    Q'.le_trans' _ _ _ b6 (Q'.le_of_eqv b7)
  have C : t * m + -(U * U * (half * hn)) + -(half * (t * E)) ≤
      t * m + -(half * (t * (m * m))) + -(half * (t * E)) :=
    Q'.add_le_add_right _ _ _ (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg B))
  exact Q'.le_trans' _ _ _ C (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ e2 e3))) A1)

/-- One κ-chain step in scaled form `a_n = 2^n·m_{j0+n}`:
`a_{n+1} ≥ a_n − U²·half^{n+1} − half·2^n·eff_{j0+n}`. **PROVED.** -/
theorem rgKappa_scaled_step
    (r ε κ : Nat → Q') (j0 n : Nat) (U : Q')
    (H : RgRateChainκ r ε κ j0) (hU0 : (0 : Q') ≤ U)
    (hup : latticeMarginOf r (j0 + n) ≤ U * half ^ n) :
    Q'.ofNat (2 ^ n) * latticeMarginOf r (j0 + n) +
        -(U * U * half ^ (n + 1)) +
        -(half * (Q'.ofNat (2 ^ n) * effectiveDefectSeq κ ε r (j0 + n))) ≤
      Q'.ofNat (2 ^ (n + 1)) * latticeMarginOf r (j0 + (n + 1)) := by
  have hj : j0 ≤ j0 + n := Nat.le_add_right j0 n
  have hstep := rg_margin_step_κ r ε κ j0 (j0 + n) H hj
  have hT := transfer_factor_as_coarse_sq_plus_defect
    (κ (j0 + n)) (ε (j0 + n)) (r (j0 + n))
  have hq1 : (1 : Q') - κ (j0 + n) * (r (j0 + n) * r (j0 + n) + ε (j0 + n)) ≈
      (1 : Q') + -(r (j0 + n) * r (j0 + n) + effectiveDefectSeq κ ε r (j0 + n)) :=
    Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hT)
  have hq2 : (1 : Q') + -(r (j0 + n) * r (j0 + n) + effectiveDefectSeq κ ε r (j0 + n)) ≈
      latticeMarginOf r (j0 + n) + latticeMarginOf r (j0 + n) +
        -(latticeMarginOf r (j0 + n) * latticeMarginOf r (j0 + n)) +
        -(effectiveDefectSeq κ ε r (j0 + n)) :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.mul (.var 0) (.var 0)) (.var 1))))
      (.add (.add (.add (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
        (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))))
        (.neg (.var 1)))
      (by decide)
      (fun | 0 => r (j0 + n) | _ => effectiveDefectSeq κ ε r (j0 + n))
  have hstep' : half * (half * (latticeMarginOf r (j0 + n) + latticeMarginOf r (j0 + n) +
        -(latticeMarginOf r (j0 + n) * latticeMarginOf r (j0 + n)) +
        -(effectiveDefectSeq κ ε r (j0 + n)))) ≤ latticeMarginOf r (j0 + (n + 1)) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.eqv_trans _ _ _ hq1 hq2)))))
      hstep
  have hm0 : (0 : Q') ≤ latticeMarginOf r (j0 + n) :=
    Q'.sub_nonneg_of_le (H.2.1 (j0 + n) hj)
  have core := scaled_step_core (Q'.ofNat (2 ^ n)) (latticeMarginOf r (j0 + n))
    (latticeMarginOf r (j0 + (n + 1))) (effectiveDefectSeq κ ε r (j0 + n)) U (half ^ n)
    hstep' (ofNat_nonneg_rg _) hm0 hU0 hup (ofNat_two_pow_mul_half_pow n)
  exact Q'.le_trans' _ _ _ core (Q'.le_of_eqv (Q'.eqv_symm
    (Q'.mul_eqv_congr_right _ _ _ (ofNat_two_pow_succ_eqv n))))

/-- Telescoped invariant. **PROVED.** -/
theorem rgKappa_envelope_invariant
    (r ε κ : Nat → Q') (j0 : Nat) (U : Q')
    (H : RgRateChainκ r ε κ j0) (hU0 : (0 : Q') ≤ U)
    (hup : ∀ n : Nat, latticeMarginOf r (j0 + n) ≤ U * half ^ n) :
    ∀ n : Nat,
      latticeMarginOf r j0 + -(U * U * halfGeomSum n) +
          -(half * weightedErrorSum (effectiveDefectSeq κ ε r) j0 n) ≤
        Q'.ofNat (2 ^ n) * latticeMarginOf r (j0 + n) := by
  intro n
  induction n with
  | zero =>
    exact Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 1)) (.const 0))))
        (.neg (.mul (.var 2) (.const 0))))
      (.mul (.const 1) (.var 0))
      (by decide)
      (fun | 0 => latticeMarginOf r j0 | 1 => U | _ => half))
  | succ n ih =>
    have hs := rgKappa_scaled_step r ε κ j0 n U H hU0 (hup n)
    have hmono :
        latticeMarginOf r j0 + -(U * U * halfGeomSum n) +
            -(half * weightedErrorSum (effectiveDefectSeq κ ε r) j0 n) +
            -(U * U * half ^ (n + 1)) +
            -(half * (Q'.ofNat (2 ^ n) * effectiveDefectSeq κ ε r (j0 + n))) ≤
          Q'.ofNat (2 ^ n) * latticeMarginOf r (j0 + n) +
            -(U * U * half ^ (n + 1)) +
            -(half * (Q'.ofNat (2 ^ n) * effectiveDefectSeq κ ε r (j0 + n))) :=
      Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ ih)
    have hre :
        latticeMarginOf r j0 + -(U * U * halfGeomSum (n + 1)) +
            -(half * weightedErrorSum (effectiveDefectSeq κ ε r) j0 (n + 1)) ≈
        latticeMarginOf r j0 + -(U * U * halfGeomSum n) +
            -(half * weightedErrorSum (effectiveDefectSeq κ ε r) j0 n) +
            -(U * U * half ^ (n + 1)) +
            -(half * (Q'.ofNat (2 ^ n) * effectiveDefectSeq κ ε r (j0 + n))) :=
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 1)) (.add (.var 2) (.var 3)))))
          (.neg (.mul (.var 4) (.add (.var 5) (.var 6)))))
        (.add (.add (.add (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 1)) (.var 2))))
          (.neg (.mul (.var 4) (.var 5)))) (.neg (.mul (.mul (.var 1) (.var 1)) (.var 3))))
          (.neg (.mul (.var 4) (.var 6))))
        (by decide)
        (fun | 0 => latticeMarginOf r j0 | 1 => U | 2 => halfGeomSum n
             | 3 => half ^ (n + 1) | 4 => half
             | 5 => weightedErrorSum (effectiveDefectSeq κ ε r) j0 n
             | _ => Q'.ofNat (2 ^ n) * effectiveDefectSeq κ ε r (j0 + n))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) (Q'.le_trans' _ _ _ hmono hs)

/-- **PROVED dyadic envelope (REDUCTION).** Scaled form, explicit constants:
`2^n·m_{j0+n} ≥ m_{j0} − U² − S/2`, where `U` is the relative upper margin
`m_{j0+n} ≤ U·2^{-n}` (absolute form: `U = M·2^{-j0}`). -/
theorem rgKappa_dyadic_envelope
    (r ε κ : Nat → Q') (j0 : Nat) (S U : Q')
    (H : RgRateChainκ r ε κ j0)
    (hS : RgErrorSummable (effectiveDefectSeq κ ε r) j0 S)
    (hU0 : (0 : Q') ≤ U)
    (hup : ∀ n : Nat, latticeMarginOf r (j0 + n) ≤ U * half ^ n) (n : Nat) :
    latticeMarginOf r j0 + -(U * U) + -(half * S) ≤
      Q'.ofNat (2 ^ n) * latticeMarginOf r (j0 + n) := by
  have hinv := rgKappa_envelope_invariant r ε κ j0 U H hU0 hup n
  have hUU : (0 : Q') ≤ U * U := Q'.mul_nonneg _ _ hU0 hU0
  have hG : U * U * halfGeomSum n ≤ U * U :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (halfGeomSum_le_one n) hUU)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hW : half * weightedErrorSum (effectiveDefectSeq κ ε r) j0 n ≤ half * S :=
    Q'.mul_le_mul_of_nonneg_left _ _ half (hS.2 n) half_nonneg
  have hle : latticeMarginOf r j0 + -(U * U) + -(half * S) ≤
      latticeMarginOf r j0 + -(U * U * halfGeomSum n) +
        -(half * weightedErrorSum (effectiveDefectSeq κ ε r) j0 n) :=
    Q'.add_le_add (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg hG)) (Q'.neg_le_neg hW)
  exact Q'.le_trans' _ _ _ hle hinv

/-- Half-power form: `2^{-n}·(m_{j0} − U² − S/2) ≤ m_{j0+n}`. **PROVED.** -/
theorem rgKappa_dyadic_envelope_halfPow
    (r ε κ : Nat → Q') (j0 : Nat) (S U : Q')
    (H : RgRateChainκ r ε κ j0)
    (hS : RgErrorSummable (effectiveDefectSeq κ ε r) j0 S)
    (hU0 : (0 : Q') ≤ U)
    (hup : ∀ n : Nat, latticeMarginOf r (j0 + n) ≤ U * half ^ n) (n : Nat) :
    half ^ n * (latticeMarginOf r j0 + -(U * U) + -(half * S)) ≤
      latticeMarginOf r (j0 + n) := by
  have h := rgKappa_dyadic_envelope r ε κ j0 S U H hS hU0 hup n
  have hp : (0 : Q') ≤ half ^ n := Q'.pow_nonneg half half_nonneg n
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ _ h hp
  have e : half ^ n * (Q'.ofNat (2 ^ n) * latticeMarginOf r (j0 + n)) ≈
      latticeMarginOf r (j0 + n) := by
    have e1 : half ^ n * (Q'.ofNat (2 ^ n) * latticeMarginOf r (j0 + n)) ≈
        (Q'.ofNat (2 ^ n) * half ^ n) * latticeMarginOf r (j0 + n) :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 1) (.var 0)) (.var 2))
        (by decide)
        (fun | 0 => half ^ n | 1 => Q'.ofNat (2 ^ n) | _ => latticeMarginOf r (j0 + n))
    have e2 : (Q'.ofNat (2 ^ n) * half ^ n) * latticeMarginOf r (j0 + n) ≈
        (1 : Q') * latticeMarginOf r (j0 + n) :=
      Q'.mul_eqv_congr_right _ _ _ (ofNat_two_pow_mul_half_pow n)
    have e3 : (1 : Q') * latticeMarginOf r (j0 + n) ≈ latticeMarginOf r (j0 + n) :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_one_eqv _)
    exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e3)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e)

/-- Absolute-upper-margin form (YM Bot normalisation), constant `c = 1`:
from `m_j ≤ M·2^{-j}` for `j ≥ j0`, `2^n·m_{j0+n} ≥ m_{j0} − (M² + S)`.
Sharp form: `≥ m_{j0} − M²·4^{-j0} − S/2`. **PROVED.** -/
theorem rgKappa_dyadic_envelope_abs
    (r ε κ : Nat → Q') (j0 : Nat) (S M : Q')
    (H : RgRateChainκ r ε κ j0)
    (hS : RgErrorSummable (effectiveDefectSeq κ ε r) j0 S)
    (hM0 : (0 : Q') ≤ M)
    (hup : ∀ n : Nat, latticeMarginOf r (j0 + n) ≤ M * half ^ (j0 + n)) (n : Nat) :
    latticeMarginOf r j0 + -(M * half ^ j0 * (M * half ^ j0)) + -(half * S) ≤
        Q'.ofNat (2 ^ n) * latticeMarginOf r (j0 + n) ∧
      latticeMarginOf r j0 + -(M * M + S) ≤
        Q'.ofNat (2 ^ n) * latticeMarginOf r (j0 + n) := by
  have hp0 : (0 : Q') ≤ half ^ j0 := Q'.pow_nonneg half half_nonneg j0
  have hU0 : (0 : Q') ≤ M * half ^ j0 := Q'.mul_nonneg _ _ hM0 hp0
  have hupU : ∀ n : Nat, latticeMarginOf r (j0 + n) ≤ M * half ^ j0 * half ^ n := by
    intro k
    have e : M * half ^ (j0 + k) ≈ M * half ^ j0 * half ^ k :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (half_pow_add_eqv j0 k))
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (by decide) (fun | 0 => M | 1 => half ^ j0 | _ => half ^ k))
    exact Q'.le_trans' _ _ _ (hup k) (Q'.le_of_eqv e)
  have hsharp := rgKappa_dyadic_envelope r ε κ j0 S (M * half ^ j0) H hS hU0 hupU n
  refine ⟨hsharp, ?_⟩
  -- (M h^j0)^2 ≤ M^2 and half*S ≤ S
  have hS0 : (0 : Q') ≤ S := hS.1
  have hp1 : half ^ j0 ≤ (1 : Q') := half_pow_le_one j0
  have hMh : M * half ^ j0 ≤ M :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ M hp1 hM0)
      (Q'.le_of_eqv (Q'.mul_one_eqv M))
  have hsq1 : M * half ^ j0 * (M * half ^ j0) ≤ M * half ^ j0 * M :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hMh hU0
  have hsq2 : M * half ^ j0 * M ≤ M * M :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ M hMh hM0)
  have hsq : M * half ^ j0 * (M * half ^ j0) ≤ M * M := Q'.le_trans' _ _ _ hsq1 hsq2
  have hhS : half * S ≤ S :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ S (half_le_one_rg) hS0)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_one_eqv S)))
  have hcmp : latticeMarginOf r j0 + -(M * M + S) ≤
      latticeMarginOf r j0 + -(M * half ^ j0 * (M * half ^ j0)) + -(half * S) := by
    have e : latticeMarginOf r j0 + -(M * M + S) ≈
        latticeMarginOf r j0 + -(M * M) + -S :=
      poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.add (.var 1) (.var 2))))
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
        (by decide) (fun | 0 => latticeMarginOf r j0 | 1 => M * M | _ => S)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e)
      (Q'.add_le_add (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg hsq)) (Q'.neg_le_neg hhS))
  exact Q'.le_trans' _ _ _ hcmp hsharp

/-! ## 4. Margin envelope ⇒ dyadic lower margin at seed scale 0 (κ chain) -/

/-- **Legacy (ASSUMED envelope).** The `∀ n` conjunct is an assumption here.
Superseded by `RgMarginEnvelopeκ` + `rgMarginEnvelopeκ_dyadic`, which PROVE the
dyadic bound from `RgRateChainκ` + summable effective defect + upper margin. -/
def RgMarginEnvelope (r ε : Nat → Q') (j0 : Nat) (S : Q') : Prop :=
  RgRateChain r ε j0 ∧ RgErrorSummable ε j0 S ∧
    S < (1 : Q') - r j0 ∧
      ∀ n : Nat, half ^ n * ((1 : Q') - r j0 - S) ≤ latticeMarginOf r (j0 + n)

def rgSeedMargin (r : Nat → Q') (S : Q') : Q' := (1 : Q') - r 0 - S

def WilsonLowerMarginFrom (F : WilsonDynamicFamily) (j0 : Nat) (m : Q') : Prop :=
  (0 : Q') < m ∧
    ∀ j, j0 ≤ j → m * F.transferSpacing.spacing j ≤ (1 : Q') - F.rate j

/-- κ-chain envelope hypotheses: NO assumed `∀ n` lower conjunct.
(1) `RgRateChainκ`; (2) `Σ_{k<n} 2^k eff_{j0+k} ≤ S` for all `n`;
(3) relative upper margin `m_{j0+n} ≤ U·2^{-n}` (B04 upper half). **REDUCTION.** -/
def RgMarginEnvelopeκ (r ε κ : Nat → Q') (j0 : Nat) (S U : Q') : Prop :=
  RgRateChainκ r ε κ j0 ∧ RgErrorSummable (effectiveDefectSeq κ ε r) j0 S ∧
    (0 : Q') ≤ U ∧ ∀ n : Nat, latticeMarginOf r (j0 + n) ≤ U * half ^ n

/-- **PROVED.** The dyadic lower margin follows from the κ-chain hypotheses:
`2^{-n}·(m_{j0} − U² − S/2) ≤ m_{j0+n}`. -/
theorem rgMarginEnvelopeκ_dyadic (r ε κ : Nat → Q') (j0 : Nat) (S U : Q')
    (H : RgMarginEnvelopeκ r ε κ j0 S U) (n : Nat) :
    half ^ n * (latticeMarginOf r j0 + -(U * U) + -(half * S)) ≤
      latticeMarginOf r (j0 + n) :=
  rgKappa_dyadic_envelope_halfPow r ε κ j0 S U H.1 H.2.1 H.2.2.1 H.2.2.2 n

/-- Seed margin of the κ envelope at scale 0: `m_0 − M² − S/2`. -/
def rgSeedMarginκ (r : Nat → Q') (S M : Q') : Q' :=
  latticeMarginOf r 0 + -(M * M) + -(half * S)

/-- B04 upper half on a family with `spacing j = 2^{-j}` gives the relative
upper margin at `j0 = 0` with `U = M`. -/
theorem upperMargin_relative_zero (F : WilsonDynamicFamily) (M : Q')
    (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (hU : WilsonUpperMargin F M) :
    ∀ n : Nat, latticeMarginOf F.rate (0 + n) ≤ M * half ^ n := by
  intro n
  rw [Nat.zero_add]
  have h := hU.2 n
  rw [hsp n] at h
  exact h

/-- **PROVED (REDUCTION), rewired through the κ chain.** `RgRateChainκ` at
`j0 = 0`, summable effective defect `≤ S`, and the B04 upper half
`WilsonUpperMargin F M` give the dyadic lower margin with seed
`m_0 − M² − S/2`, whenever that seed is positive. -/
theorem rg_envelope_zero_lower_margin
    (F : WilsonDynamicFamily) (ε κ : Nat → Q') (S M : Q')
    (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (H : RgRateChainκ F.rate ε κ 0)
    (hS : RgErrorSummable (effectiveDefectSeq κ ε F.rate) 0 S)
    (hU : WilsonUpperMargin F M)
    (hm0 : (0 : Q') < rgSeedMarginκ F.rate S M) :
    WilsonLowerMarginFrom F 0 (rgSeedMarginκ F.rate S M) := by
  refine ⟨hm0, ?_⟩
  intro j _
  have henv := rgKappa_dyadic_envelope_halfPow F.rate ε κ 0 S M H hS
    (Q'.le_of_lt hU.1) (upperMargin_relative_zero F M hsp hU) j
  rw [Nat.zero_add] at henv
  rw [hsp j]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) henv

/-- **PROVED (REDUCTION).** `WilsonLowerMargin` via the κ chain. -/
theorem rg_envelope_zero_wilsonLowerMargin
    (F : WilsonDynamicFamily) (ε κ : Nat → Q') (S M : Q')
    (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (H : RgRateChainκ F.rate ε κ 0)
    (hS : RgErrorSummable (effectiveDefectSeq κ ε F.rate) 0 S)
    (hU : WilsonUpperMargin F M)
    (hm0 : (0 : Q') < rgSeedMarginκ F.rate S M) :
    WilsonLowerMargin F (rgSeedMarginκ F.rate S M) := by
  have h := rg_envelope_zero_lower_margin F ε κ S M hsp H hS hU hm0
  exact ⟨h.1, fun j => by
    have := h.2 j (Nat.zero_le j)
    simpa only [WilsonDynamicFamily.latticeMargin] using this⟩

/-- Spacing consistency: every `exprWilsonFamily` (hence the `trAF` family)
uses `dyadicPhysicalSpacing`, whose spacing is `half ^ j` by definition. -/
theorem exprWilsonFamily_spacing_half_pow (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j)
      (tr.schedule.nome_lt_one j) (tr.width j) (r j)) (j : Nat) :
    (exprWilsonFamily tr r hr0 hr1 Hc).transferSpacing.spacing j = half ^ j := rfl

/-- κ-chain lower margin on `exprWilsonFamily`, spacing discharged by `rfl`. -/
theorem exprWilsonFamily_lowerMargin_of_kappaChain
    (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j)
      (tr.schedule.nome_lt_one j) (tr.width j) (r j))
    (ε κ : Nat → Q') (S M : Q')
    (H : RgRateChainκ r ε κ 0)
    (hS : RgErrorSummable (effectiveDefectSeq κ ε r) 0 S)
    (hU : WilsonUpperMargin (exprWilsonFamily tr r hr0 hr1 Hc) M)
    (hm0 : (0 : Q') < rgSeedMarginκ r S M) :
    WilsonLowerMargin (exprWilsonFamily tr r hr0 hr1 Hc) (rgSeedMarginκ r S M) :=
  rg_envelope_zero_wilsonLowerMargin (exprWilsonFamily tr r hr0 hr1 Hc) ε κ S M
    (exprWilsonFamily_spacing_half_pow tr r hr0 hr1 Hc) H hS hU hm0

/-- Legacy: from the ASSUMED envelope. Kept for reference. -/
theorem rg_envelope_zero_lower_margin_assumed
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
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.halfGeomSum_add_pow
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.ofNat_two_pow_mul_half_pow
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rgKappa_scaled_step
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rgKappa_envelope_invariant
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rgKappa_dyadic_envelope
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rgKappa_dyadic_envelope_halfPow
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rgKappa_dyadic_envelope_abs
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rgMarginEnvelopeκ_dyadic
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_envelope_zero_lower_margin_assumed
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.exprWilsonFamily_lowerMargin_of_kappaChain
