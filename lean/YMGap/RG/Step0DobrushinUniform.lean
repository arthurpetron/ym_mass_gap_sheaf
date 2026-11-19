/-
# Step n = 0 Dobrushin uniform: certificates + CentredPowerDecay + EvenDecay → fineAt

Additive.  Decidable TV-Dobrushin certificates at w = 1/8, CentredPowerDecay /
CentredPowerDecayVC interfaces, constructive prefactor removal via
`dyadic_geometric_first_le` (no gap_infinite rebuild), then
`twoStepFactor_of_even_decay` at r = 1/8 → fineAt W 0 (1/64).

Föllmer/Dobrushin left OPEN as `hDob_OPEN`.  Does NOT formalise Haar/L1/W₁/
Pulled*/step-1.  Mathlib-free; no sorry/admit/Classical/native_decide/omega/
simpa/grind.  Not chart closure / not gap evidence.
-/

import YMGap.Continuum.EvenDecayTwoStepFactor
import YMGap.Continuum.SU2LogConvexGapInfinite
import YMGap.Continuum.CRealLogConvexRatioMono
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
import YMGap.Continuum.BF4WilsonAllNomeCenteredVector
import YMGap.Continuum.BF4WilsonAllNomeCenteringPin
import YMGap.Continuum.BF4WilsonAllNomeCompletedGap
import YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
import YMGap.Continuum.BF4WilsonAllNomeCompletedTime
import YMGap.Continuum.FiveHolonomyPerronCutoff
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.RCScaleClose
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.SumOfSquares
import YMGap.RG.CoarseConstantZero
import YMGap.RG.Robust3CrossUniform
import YMGap.RG.Robust3UndershootAfSchedule
import YMGap.RG.Robust3Width2Electric
import YMGap.Continuum.ReconstructionCapstone

namespace YMGap.RG.Step0DobrushinUniform

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Constructive.SumOfSquares
open YMGap.RG.Robust3Width2Electric (termF partialF)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule)
open YMGap.RG.Robust3CrossUniform (fineAt)
open YMGap.Continuum.EvenDecayTwoStepFactor
  (EvenDecay twoStepFactor_of_even_decay)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (completedInner completedInner_nonnegative completedInner_symm Completion
    unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (VacuumComplement completedTime completedTime_zero
    completedInner_time_contraction)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredExcitation)
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
  (completedInner_even_diagonal representativeCenteredMoment
    representativeCenteredMoment_pin completedCenteredScalar
    completedCenteredScalar_of_orthogonal)
open YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
  (response_even_nonnegative response_square_le_zero_mul_four)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (dyadic_geometric_first_le)
open YMGap.Continuum.HKPos (pow_pos q_lt_of_le_of_lt)
open YMGap.Continuum.FiveHolonomyPerronCutoff (pow_mul_eqv)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
  (WilsonVacuumSqTwoStepFactor)

/-! ## (i) Decidable certificates -/

def wEighth : Q' := Q'.mkPos 1 8 (by decide)

def tailBound (_w : Q') (_N : Nat) : Q' := Q'.mkPos 1 100000 (by decide)

def cF1 : Q' := Q'.mkPos 79 10000 (by decide)
def cAlpha : Q' := Q'.mkPos 14 100 (by decide)
def cSqrt : Q' := Q'.mkPos 2829 1000 (by decide)

theorem F1_eighth_le :
    partialF wEighth 12 + tailBound wEighth 12 ≤ (1 : Q') + cF1 := by decide

theorem dobrushin_eighth :
    ((12 : Q') + (2 : Q') * cSqrt) * cF1 ≤ cAlpha := by decide

theorem sqrt8_le :
    (8 : Q') ≤ cSqrt * cSqrt := by decide

/-! ## (ii) CentredPowerDecay interfaces -/

def RCone' : RC := Quotient.mk crealSetoid (ofQ' (1 : Q'))

/-- Dense special case (IntrinsicExpression → centeredExcitation). -/
def CentredPowerDecay {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (q : Q') : Prop :=
  ∀ x : IntrinsicExpression width, ∃ C : Q', ∀ n : Nat,
    RCle
      (completedInner hw0 hw1
        (centeredExcitation hw0 hw1 x).val
        (completedTime hw0 hw1 (2 * n) (centeredExcitation hw0 hw1 x).val))
      (RCscale (C * q ^ n) RCone')

/-- Vacuum-complement envelope (authorised strengthening of hDob_OPEN). -/
def CentredPowerDecayVC {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (q : Q') : Prop :=
  ∀ y : VacuumComplement hw0 hw1 (width := width), ∃ C : Q', ∀ n : Nat,
    RCle
      (completedInner hw0 hw1 y.val
        (completedTime hw0 hw1 (2 * n) y.val))
      (RCscale (C * q ^ n) RCone')

/-! ## Helpers -/

private theorem RCscale_RCone' (r : Q') :
    RCscale r RCone' = Quotient.mk crealSetoid (ofQ' r) := by
  unfold RCone'
  rw [RCscale_mk]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv fun _ =>
    Q'.mul_one_eqv r)

private theorem two_mul_add_self (u : Nat) : 2 * (u + u) = 4 * u := by
  calc
    2 * (u + u) = 2 * u + 2 * u := Nat.mul_add 2 u u
    _ = 2 * (2 * u) := (Nat.two_mul (2 * u)).symm
    _ = 4 * u := by
      have h22 : (2 : Nat) * 2 = 4 := rfl
      rw [← Nat.mul_assoc, h22]

private theorem C_le_max_one (C : Q') : C ≤ Q'.max' C (1 : Q') := by
  unfold Q'.max'
  by_cases h : C ≤ (1 : Q')
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Q'.le_refl' _

private theorem max_one_pos (C : Q') : (0 : Q') < Q'.max' C (1 : Q') := by
  unfold Q'.max'
  by_cases h : C ≤ (1 : Q')
  · rw [if_pos h]; decide
  · rw [if_neg h]
    have hlt : (1 : Q') < C := by
      show (1 : Int) * (C.den : Int) < C.num * ((1 : Q').den : Int)
      exact Int.not_le.mp h
    exact q_lt_of_le_of_lt (by decide : (0 : Q') ≤ (1 : Q')) hlt

/-! ## L0. RC wrapper around the CReal engine -/

/-- Thin RC packaging of `dyadic_geometric_first_le` (explicit CReal stream). -/
theorem dyadic_geometric_first_le_RC
    (m : Nat → CReal) (q P : Q')
    (hq : (0 : Q') < q) (hP : (0 : Q') < P)
    (hnn : ∀ n, leEv czero (m n))
    (hle : ∀ n, leEv (m n) (m 0))
    (hdy : ∀ n, leEv (mul (m n) (m n)) (mul (m (n + n)) (m 0)))
    (hen : ∀ n, leEv (m n) (ofQ' (P * q ^ n))) :
    RCle (Quotient.mk crealSetoid (m 1))
      (RCscale q (Quotient.mk crealSetoid (m 0))) := by
  have h := dyadic_geometric_first_le m q P hq hP hnn hle hdy hen
  rw [RCscale_mk]
  exact h

/-! ## L1. EvenDecay from CentredPowerDecayVC -/

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

private def evenMomC (X : (seminorm hw0 hw1 (width := width)).Cauchy)
    (n : Nat) : CReal :=
  representativeCenteredMoment hw0 hw1 width (2 * n) X X

private theorem evenMomC_pin (X : (seminorm hw0 hw1 (width := width)).Cauchy)
    (hx : completedInner hw0 hw1
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
      (unitState hw0 hw1 width) = RCzero)
    (n : Nat) :
    completedInner hw0 hw1
        (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
        (completedTime hw0 hw1 (2 * n)
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)) =
      Quotient.mk crealSetoid (evenMomC hw0 hw1 X n) := by
  have hCCS := completedCenteredScalar_of_orthogonal hw0 hw1 width (2 * n)
    (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) hx
  rw [← hCCS]
  exact (representativeCenteredMoment_pin hw0 hw1 width (2 * n) X X).symm

private theorem evenMomC_diag0 (X : (seminorm hw0 hw1 (width := width)).Cauchy)
    (hx : completedInner hw0 hw1
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
      (unitState hw0 hw1 width) = RCzero) :
    completedInner hw0 hw1
        (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
        (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) =
      Quotient.mk crealSetoid (evenMomC hw0 hw1 X 0) := by
  have h := evenMomC_pin hw0 hw1 X hx 0
  rw [completedTime_zero] at h
  exact h

/-- Lag-1 bound from a positive envelope prefactor. -/
theorem evenDecay_m1_of_envelope (q P : Q')
    (hq : (0 : Q') < q) (hP : (0 : Q') < P)
    (y : VacuumComplement hw0 hw1 (width := width))
    (henv : ∀ n, RCle
      (completedInner hw0 hw1 y.val
        (completedTime hw0 hw1 (2 * n) y.val))
      (RCscale (P * q ^ n) RCone')) :
    RCle
      (completedInner hw0 hw1 y.val (completedTime hw0 hw1 2 y.val))
      (RCscale q (completedInner hw0 hw1 y.val y.val)) := by
  have hx0 : completedInner hw0 hw1 y.val (unitState hw0 hw1 width) = RCzero := by
    have hsym := completedInner_symm hw0 hw1 (unitState hw0 hw1 width) y.val
    exact hsym.symm.trans y.property
  refine Quotient.inductionOn
    (motive := fun z =>
      completedInner hw0 hw1 z (unitState hw0 hw1 width) = RCzero →
      (∀ n, RCle (completedInner hw0 hw1 z (completedTime hw0 hw1 (2 * n) z))
        (RCscale (P * q ^ n) RCone')) →
      RCle (completedInner hw0 hw1 z (completedTime hw0 hw1 2 z))
        (RCscale q (completedInner hw0 hw1 z z)))
    y.val ?_ hx0 henv
  intro X hx henvX
  let m : Nat → CReal := evenMomC hw0 hw1 X
  have hnn : ∀ n, leEv czero (m n) := by
    intro n
    have hRC := response_even_nonnegative hw0 hw1 width
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) n
    rw [evenMomC_pin hw0 hw1 X hx n] at hRC
    exact hRC
  have hle : ∀ n, leEv (m n) (m 0) := by
    intro n
    have hdiag := completedInner_even_diagonal hw0 hw1 width n
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
    have hcontr := completedInner_time_contraction hw0 hw1 n
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
    have hRC : RCle
        (completedInner hw0 hw1
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
          (completedTime hw0 hw1 (2 * n)
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))
        (completedInner hw0 hw1
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)) := by
      rw [hdiag]; exact hcontr
    rw [evenMomC_pin hw0 hw1 X hx n, evenMomC_diag0 hw0 hw1 X hx] at hRC
    exact hRC
  have hdy : ∀ n, leEv (mul (m n) (m n)) (mul (m (n + n)) (m 0)) := by
    intro n
    have hRC := response_square_le_zero_mul_four hw0 hw1 width
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) n
    have h4 : completedTime hw0 hw1 (4 * n)
        (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) =
        completedTime hw0 hw1 (2 * (n + n))
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) := by
      rw [two_mul_add_self]
    have hLn := evenMomC_pin hw0 hw1 X hx n
    have hR0 := evenMomC_diag0 hw0 hw1 X hx
    have hRn := evenMomC_pin hw0 hw1 X hx (n + n)
    have hL :
        RCmul
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (completedTime hw0 hw1 (2 * n)
              (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (completedTime hw0 hw1 (2 * n)
              (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))
        = Quotient.mk crealSetoid (mul (m n) (m n)) := by
      refine Eq.trans (congrArg (fun z => RCmul z z) hLn) ?_
      exact RCmul_mk (m n) (m n)
    have hR :
        RCmul
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X))
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (completedTime hw0 hw1 (4 * n)
              (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))
        = Quotient.mk crealSetoid (mul (m 0) (m (n + n))) := by
      have hT := congrArg
        (fun z => completedInner hw0 hw1
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) z) h4
      have hRight := hT.trans hRn
      refine Eq.trans
        (Eq.trans (congrArg (fun a => RCmul a
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (completedTime hw0 hw1 (4 * n)
              (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))) hR0)
          (congrArg (fun b => RCmul (Quotient.mk crealSetoid (m 0)) b) hRight)) ?_
      exact RCmul_mk (m 0) (m (n + n))
    have hRC' : RCle
        (Quotient.mk crealSetoid (mul (m n) (m n)))
        (Quotient.mk crealSetoid (mul (m 0) (m (n + n)))) := by
      rw [← hL, ← hR]; exact hRC
    have hcomm : Equiv (mul (m 0) (m (n + n))) (mul (m (n + n)) (m 0)) :=
      CRealAlg.cmul_comm (m 0) (m (n + n))
    exact leEv_trans hRC' (leEv_of_equiv hcomm)
  have hen : ∀ n, leEv (m n) (ofQ' (P * q ^ n)) := by
    intro n
    have hRC := henvX n
    rw [evenMomC_pin hw0 hw1 X hx n, RCscale_RCone'] at hRC
    exact hRC
  have hgoal := dyadic_geometric_first_le_RC m q P hq hP hnn hle hdy hen
  rw [evenMomC_pin hw0 hw1 X hx 1, evenMomC_diag0 hw0 hw1 X hx]
  exact hgoal

/-- Full EvenDecay at lag `n` via subsampled dyadic engine at rate `q^n`. -/
theorem evenDecay_at_n_of_envelope (q P : Q')
    (hq : (0 : Q') < q) (hP : (0 : Q') < P)
    (y : VacuumComplement hw0 hw1 (width := width))
    (henv : ∀ k, RCle
      (completedInner hw0 hw1 y.val
        (completedTime hw0 hw1 (2 * k) y.val))
      (RCscale (P * q ^ k) RCone'))
    (n : Nat) :
    RCle
      (completedInner hw0 hw1 y.val
        (completedTime hw0 hw1 (2 * n) y.val))
      (RCscale (q ^ n) (completedInner hw0 hw1 y.val y.val)) := by
  have hx0 : completedInner hw0 hw1 y.val (unitState hw0 hw1 width) = RCzero := by
    have hsym := completedInner_symm hw0 hw1 (unitState hw0 hw1 width) y.val
    exact hsym.symm.trans y.property
  refine Quotient.inductionOn
    (motive := fun z =>
      completedInner hw0 hw1 z (unitState hw0 hw1 width) = RCzero →
      (∀ k, RCle (completedInner hw0 hw1 z (completedTime hw0 hw1 (2 * k) z))
        (RCscale (P * q ^ k) RCone')) →
      RCle (completedInner hw0 hw1 z (completedTime hw0 hw1 (2 * n) z))
        (RCscale (q ^ n) (completedInner hw0 hw1 z z)))
    y.val ?_ hx0 henv
  intro X hx henvX
  let m : Nat → CReal := evenMomC hw0 hw1 X
  let m' : Nat → CReal := fun k => m (n * k)
  have hqN : (0 : Q') < q ^ n := pow_pos hq n
  have hnn : ∀ k, leEv czero (m' k) := by
    intro k
    have hRC := response_even_nonnegative hw0 hw1 width
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) (n * k)
    rw [evenMomC_pin hw0 hw1 X hx (n * k)] at hRC
    exact hRC
  have hle : ∀ k, leEv (m' k) (m' 0) := by
    intro k
    have hdiag := completedInner_even_diagonal hw0 hw1 width (n * k)
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
    have hcontr := completedInner_time_contraction hw0 hw1 (n * k)
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
    have hRC : RCle
        (completedInner hw0 hw1
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
          (completedTime hw0 hw1 (2 * (n * k))
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))
        (completedInner hw0 hw1
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)) := by
      rw [hdiag]; exact hcontr
    rw [evenMomC_pin hw0 hw1 X hx (n * k), evenMomC_diag0 hw0 hw1 X hx] at hRC
    exact hRC
  have hdy : ∀ k, leEv (mul (m' k) (m' k)) (mul (m' (k + k)) (m' 0)) := by
    intro k
    have hRC := response_square_le_zero_mul_four hw0 hw1 width
      (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) (n * k)
    have h4 : completedTime hw0 hw1 (4 * (n * k))
        (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) =
        completedTime hw0 hw1 (2 * (n * k + n * k))
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) := by
      rw [two_mul_add_self]
    have hkk : n * (k + k) = n * k + n * k := Nat.mul_add n k k
    have hLn := evenMomC_pin hw0 hw1 X hx (n * k)
    have hR0 := evenMomC_diag0 hw0 hw1 X hx
    have hRn : completedInner hw0 hw1
        (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
        (completedTime hw0 hw1 (2 * (n * k + n * k))
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)) =
        Quotient.mk crealSetoid (m (n * (k + k))) := by
      have h := evenMomC_pin hw0 hw1 X hx (n * (k + k))
      -- rewrite inside the Nat arg of completedTime via hkk
      have hT : completedTime hw0 hw1 (2 * (n * (k + k)))
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) =
          completedTime hw0 hw1 (2 * (n * k + n * k))
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) := by
        rw [hkk]
      exact (congrArg (completedInner hw0 hw1
        (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)) hT).symm.trans h
    have hL :
        RCmul
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (completedTime hw0 hw1 (2 * (n * k))
              (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (completedTime hw0 hw1 (2 * (n * k))
              (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))
        = Quotient.mk crealSetoid (mul (m' k) (m' k)) := by
      refine Eq.trans (congrArg (fun z => RCmul z z) hLn) ?_
      exact RCmul_mk (m (n * k)) (m (n * k))
    have hR :
        RCmul
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X))
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (completedTime hw0 hw1 (4 * (n * k))
              (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))
        = Quotient.mk crealSetoid (mul (m' (k + k)) (m' 0)) := by
      have hT := congrArg
        (fun z => completedInner hw0 hw1
          (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X) z) h4
      have hRight := hT.trans hRn
      -- m' (k+k) = m (n*(k+k)); m' 0 = m 0; need mul (m (n*(k+k))) (m 0) then commute later? 
      -- Goal wants mul (m' (k+k)) (m' 0) = mul (m (n*(k+k))) (m 0)
      -- But RCmul_mk gives mul (m 0) (m (n*(k+k))). We'll commute after.
      refine Eq.trans
        (Eq.trans (congrArg (fun a => RCmul a
          (completedInner hw0 hw1
            (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)
            (completedTime hw0 hw1 (4 * (n * k))
              (Quotient.mk (seminorm hw0 hw1 (width := width)).completionSetoid X)))) hR0)
          (congrArg (fun b => RCmul (Quotient.mk crealSetoid (m 0)) b) hRight)) ?_
      have hmk := RCmul_mk (m 0) (m (n * (k + k)))
      refine hmk.trans (Quotient.sound ?_)
      exact CRealAlg.cmul_comm (m 0) (m (n * (k + k)))
    have hRC' : RCle
        (Quotient.mk crealSetoid (mul (m' k) (m' k)))
        (Quotient.mk crealSetoid (mul (m' (k + k)) (m' 0))) := by
      rw [← hL, ← hR]; exact hRC
    exact hRC' 
  have hen : ∀ k, leEv (m' k) (ofQ' (P * (q ^ n) ^ k)) := by
    intro k
    have hRC := henvX (n * k)
    rw [evenMomC_pin hw0 hw1 X hx (n * k), RCscale_RCone'] at hRC
    have heqv : (P * q ^ (n * k)).eqv (P * (q ^ n) ^ k) :=
      Q'.mul_eqv_congr_left P _ _ (Q'.eqv_symm (pow_mul_eqv q n k))
    exact leEv_trans hRC
      (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv fun _ => heqv))
  have hgoal := dyadic_geometric_first_le_RC m' (q ^ n) P hqN hP hnn hle hdy hen
  have h1 : m' 1 = m n := by
    show m (n * 1) = m n
    rw [Nat.mul_one]
  rw [evenMomC_pin hw0 hw1 X hx n, evenMomC_diag0 hw0 hw1 X hx]
  change RCle (Quotient.mk crealSetoid (m' 1))
    (RCscale (q ^ n) (Quotient.mk crealSetoid (m 0))) at hgoal
  rw [h1] at hgoal
  exact hgoal

theorem evenDecay_of_centredPowerDecayVC (q : Q') (hq : (0 : Q') < q)
    (H : CentredPowerDecayVC hw0 hw1 width q) :
    ∀ y : VacuumComplement hw0 hw1 (width := width),
      EvenDecay hw0 hw1 width y.val q := by
  intro y n
  obtain ⟨C, hC⟩ := H y
  let P : Q' := Q'.max' C (1 : Q')
  have hP : (0 : Q') < P := max_one_pos C
  have henv : ∀ k, RCle
      (completedInner hw0 hw1 y.val
        (completedTime hw0 hw1 (2 * k) y.val))
      (RCscale (P * q ^ k) RCone') := by
    intro k
    have hraw := hC k
    have hscale : C * q ^ k ≤ P * q ^ k :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (C_le_max_one C)
        (Q'.pow_nonneg q (Q'.le_of_lt hq) k)
    have hRCone : RCnonneg RCone' := by
      unfold RCone'
      exact leEv_ofQ'_of_approx_ge fun _ => (by decide : (0 : Q') ≤ (1 : Q'))
    exact RCle_trans hraw (RCscale_mono_scalar hscale hRCone)
  exact evenDecay_at_n_of_envelope hw0 hw1 q P hq hP y henv n

/-! ## L2. fineAt assembly -/

private theorem wEighth_mul_self :
    (wEighth * wEighth).eqv (Q'.mkPos 1 64 (by decide)) := by decide

theorem fineAt_step0_all_widths
    (hDob_OPEN : ∀ width,
      CentredPowerDecayVC
        (robust3UndershootSchedule.nome_pos 1)
        (robust3UndershootSchedule.nome_lt_one 1) width wEighth) :
    ∀ W : Nat → Nat, fineAt W 0 (Q'.mkPos 1 64 (by decide)) := by
  intro W
  let hw0 := robust3UndershootSchedule.nome_pos 1
  let hw1 := robust3UndershootSchedule.nome_lt_one 1
  let width := W (0 + 0 + 1)
  have hq : (0 : Q') < wEighth := by decide
  have hEven := evenDecay_of_centredPowerDecayVC hw0 hw1 wEighth hq (hDob_OPEN width)
  have hTS := twoStepFactor_of_even_decay hw0 hw1 width wEighth hEven
  intro y
  have h := hTS y
  have hnn := completedInner_nonnegative hw0 hw1 y.val
  exact RCle_trans h
    (RCscale_mono_scalar (Q'.le_of_eqv wEighth_mul_self) hnn)

end YMGap.RG.Step0DobrushinUniform

#print axioms YMGap.RG.Step0DobrushinUniform.F1_eighth_le
#print axioms YMGap.RG.Step0DobrushinUniform.dobrushin_eighth
#print axioms YMGap.RG.Step0DobrushinUniform.sqrt8_le
#print axioms YMGap.RG.Step0DobrushinUniform.dyadic_geometric_first_le_RC
#print axioms YMGap.RG.Step0DobrushinUniform.evenDecay_of_centredPowerDecayVC
#print axioms YMGap.RG.Step0DobrushinUniform.fineAt_step0_all_widths
