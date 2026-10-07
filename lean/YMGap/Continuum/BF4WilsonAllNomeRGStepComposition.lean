/-
# REDUCTION: RG-step composition for the Wilson gap frontier

Companion to `audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md`. ADDITIVE.

**REDUCTION ONLY.** No approximate intertwiner `Φ_j` is constructed.

Strengthened `ApproxRgIntertwiner` (operator-level; rate transfer PROVED):
* coercive lower bound `B_f(x,x) ≤ κ·B_c(Φx,Φx)` with `κ > 0` (prevents `Φ = 0`);
* norm upper bound `B_c(Φx,Φx) ≤ B_f(x,x)`;
* quadratic-form intertwining defect (one-step VacSq B-form; no vector subtraction
  on the subtype — `Completion` has no packaged `AddCommGroup` here).

Proved: coarse VacSq at `rC` + operator fields ⇒ fine square-factor
`κ(rC²+ε)`, hence VacSq at any `rF` with `κ(rC²+ε) ≤ rF²`. Choosing equality
identifies `r_F² = κ(r_C²+ε)` (YM Bot shape with elementary `r_C²`).

Also: every scale of `afNomeSchedule` / `trAF` fails `heatRatio ≤ 1/2`
(`w_j ≥ w_0 > 1/2`), so strong coupling cannot seed `trAF`. The seed is an open
intermediate-coupling contraction producer.

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
import YMGap.Constructive.HalfPow
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.Soundness
import YMGap.Constructive.AbsQ
import YMGap.Constructive.SumOfSquares

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

/-- κ-aware rate relation: choose `rFine` with `rFine² ≤ κ(rCoarse²+ε)` for margin. -/
def RgRateRelationκ (rFine rCoarse ε κ : Q') : Prop :=
  (0 : Q') ≤ rFine ∧ rFine ≤ (1 : Q') ∧
    (0 : Q') ≤ ε ∧ (0 : Q') < κ ∧
      rFine * rFine ≤ κ * (rCoarse * rCoarse + ε) ∧
        κ * (rCoarse * rCoarse + ε) ≤ (1 : Q')

theorem margin_after_rg_step_κ (rFine rCoarse ε κ : Q')
    (H : RgRateRelationκ rFine rCoarse ε κ) :
    half * ((1 : Q') - κ * (rCoarse * rCoarse + ε)) ≤ (1 : Q') - rFine := by
  rcases H with ⟨hr0, hr1, _, _, hsq, _⟩
  have h1 := one_sub_ge_half_one_sub_sq rFine hr0 hr1
  have hmono : (1 : Q') - κ * (rCoarse * rCoarse + ε) ≤ (1 : Q') - rFine * rFine :=
    Q'.add_le_add_left (1 : Q') _ _ (Q'.neg_le_neg hsq)
  have h2 : half * ((1 : Q') - κ * (rCoarse * rCoarse + ε)) ≤
      half * ((1 : Q') - rFine * rFine) :=
    Q'.mul_le_mul_of_nonneg_left _ _ half hmono half_nonneg
  exact Q'.le_trans' _ _ _ h2 h1

/-! ## 2. Approx RG intertwiner (operator-level; rate transfer PROVED) -/

/-- Square-factor form of VacSq (the `r*r` slot). -/
def WilsonVacuumSqFactor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) (α : Q') : Prop :=
  ∀ y : VacuumComplement hw0 hw1 (width := width),
    RCle (completedInner hw0 hw1 (completedTime hw0 hw1 1 y.val)
            (completedTime hw0 hw1 1 y.val))
      (RCscale α (completedInner hw0 hw1 y.val y.val))

theorem wilsonVacuumSq_of_factor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')} {width : Nat}
    (r α : Q') (h : α ≤ r * r) (H : WilsonVacuumSqFactor hw0 hw1 width α) :
    WilsonVacuumSqContraction hw0 hw1 width r := fun y => by
  have hBf0 : RCnonneg (completedInner hw0 hw1 y.val y.val) :=
    completedInner_nonnegative hw0 hw1 y.val
  exact RCle_trans (H y) (RCscale_mono_scalar h hBf0)

/-- **REDUCTION / OPEN to inhabit.** Operator-level approx RG step.

* `lowerBound`: `B_f(x,x) ≤ κ·B_c(Φx,Φx)` with `κ > 0` — coercive, prevents `Φ = 0`.
* `upperBound`: `B_c(Φx,Φx) ≤ B_f(x,x)`.
* `intertwine_oneStep`: quadratic-form defect
  `B_f(T_f x,T_f x) ≤ κ·B_c(T_c Φx,T_c Φx) + (κ·ε)·B_f(x,x)`
  (B-form shadow of approx intertwining; no vector subtraction on the subtype).

Linearity of `Φ` is not a separate field: the B-form consequences are what the
rate proof uses. -/
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
  intertwine_oneStep :
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

private theorem rc_scale_add_right (s t : Q') (a : RC) :
    RCadd (RCscale s a) (RCscale t a) = RCscale (s + t) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
      (.mul (.add (.var 0) (.var 1)) (.var 2))
      (by decide) (fun | 0 => s | 1 => t | _ => A.approx n)))

/-- **PROVED.** Coarse VacSq at `rC` + operator fields ⇒ fine square-factor
`α = κ(rC²+ε)`. **REDUCTION.** -/
theorem approxRg_transfers_factor
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {ε κ : Q'}
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 widthF widthC ε κ)
    (rC : Q')
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC) :
    WilsonVacuumSqFactor hwF0 hwF1 widthF (κ * (rC * rC + ε)) := by
  intro y
  have hκ0 : (0 : Q') ≤ κ := Q'.le_of_lt H.kappa_pos
  have hr2 : (0 : Q') ≤ rC * rC := q_mul_self_nonneg rC
  have hκr : (0 : Q') ≤ κ * (rC * rC) := Q'.mul_nonneg _ _ hκ0 hr2
  have hdef := H.intertwine_oneStep y
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
  have hup := H.upperBound y
  have hupκ :
      RCle
        (RCscale (κ * (rC * rC))
          (completedInner hwC0 hwC1 (H.Φ y).val (H.Φ y).val))
        (RCscale (κ * (rC * rC))
          (completedInner hwF0 hwF1 y.val y.val)) :=
    RCscale_mono hκr hup
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

/-- **PROVED.** VacSq on fine at any `rF` with `κ(rC²+ε) ≤ rF²`.
Choosing equality gives the identification `r_F² = κ(r_C²+ε)`. **REDUCTION.** -/
theorem approxRg_transfers
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {ε κ : Q'}
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 widthF widthC ε κ)
    (rC rF : Q')
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC)
    (hsq : κ * (rC * rC + ε) ≤ rF * rF) :
    WilsonVacuumSqContraction hwF0 hwF1 widthF rF :=
  wilsonVacuumSq_of_factor rF (κ * (rC * rC + ε)) hsq
    (approxRg_transfers_factor H rC hc)

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

/-- Truncated lower margin from scale `j0`. **REDUCTION.** -/
def WilsonLowerMarginFrom (F : WilsonDynamicFamily) (j0 : Nat) (m : Q') : Prop :=
  (0 : Q') < m ∧
    ∀ j, j0 ≤ j → m * F.transferSpacing.spacing j ≤ (1 : Q') - F.rate j

/-- At seed scale 0, with dyadic spacing `half^j`, an envelope yields a truncated
(and hence full) lower-margin shape with `m = 1 − r_0 − S`. **REDUCTION.** -/
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

/-- Specialisation: envelope at 0 + dyadic spacing ⇒ `WilsonLowerMargin`. **REDUCTION.** -/
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
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.wilsonVacuumSq_of_factor
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.approxRg_transfers_factor
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.approxRg_transfers
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_margin_step
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_envelope_zero_lower_margin
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.rg_envelope_zero_wilsonLowerMargin
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.strongCoupling_seed_at_pilot
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.afGap_zero_lt_half
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.afNome_zero_gt_half
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGStepComposition.not_heatRatio_le_half_afNome
