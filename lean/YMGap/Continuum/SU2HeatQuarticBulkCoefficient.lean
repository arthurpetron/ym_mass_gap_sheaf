/-
# Original untruncated SU(2) quartic bulk coefficient

This file joins the five ACTUAL `BondMovingStep.coeffW` values at labels
`k,...,k+4` to the scalar polynomial certificate in
`SU2HeatQuarticCoefficientMajorant`.  It does not expand a finite character
prefix: the eventual low-spin consumer still needs `k+4 <= K`, and the
moving high-spin tail and finite boundary are separate.
-/

import YMGap.Continuum.SU2HeatQuarticCoefficientMajorant
import YMGap.Continuum.SU2HeatQuarticNomeBudget
import YMGap.Continuum.SU2HeatFusionCoefficientPositive

namespace YMGap.Continuum.SU2HeatQuarticBulkCoefficient

set_option autoImplicit false
set_option maxRecDepth 2048

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport (c4 dimQ)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)
open YMGap.Continuum.FiveHolonomyPerronCutoff (pow_mul_eqv)
open YMGap.Continuum.SU2HeatQuarticCoefficientMajorant
open YMGap.Continuum.SU2HeatQuarticNomeBudget

local infix:50 " ≈ " => Q'.eqv

/-- The untruncated five-term second-fusion coefficient at spin `k+2`. -/
def quarticBulkCoeff (w : Q') (k : Nat) : Q' :=
  ((6 * coeffW w (k+2) +
      -(4 * (coeffW w (k+1) + coeffW w (k+3)))) +
    coeffW w k) + coeffW w (k+4)

private theorem ringQpow_eqv_pow (x : Q') :
    ∀ m, RingNormaliser.qpow x m ≈ x ^ m
  | 0 => Q'.eqv_refl 1
  | m + 1 => by
      have ih := ringQpow_eqv_pow x m
      show RingNormaliser.qpow x m * x ≈ x * x ^ m
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x ih)
        (Q'.mul_comm_eqv (x ^ m) x)

private theorem power_repack (w : Q') (base gap m r : Nat) :
    w ^ base *
      (RingNormaliser.qpow (w ^ gap) m *
        RingNormaliser.qpow (w ^ 2) r) ≈
      w ^ (base + gap*m + 2*r) := by
  have hm : RingNormaliser.qpow (w ^ gap) m ≈ w ^ (gap*m) :=
    Q'.eqv_trans _ _ _ (ringQpow_eqv_pow _ m) (pow_mul_eqv w gap m)
  have hr : RingNormaliser.qpow (w ^ 2) r ≈ w ^ (2*r) :=
    Q'.eqv_trans _ _ _ (ringQpow_eqv_pow _ r) (pow_mul_eqv w 2 r)
  calc
    w ^ base * (RingNormaliser.qpow (w ^ gap) m *
        RingNormaliser.qpow (w ^ 2) r)
        ≈ w ^ base * (w ^ (gap*m) * w ^ (2*r)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ hm)
            (Q'.mul_eqv_congr_left _ _ _ hr))
    _ ≈ (w ^ base * w ^ (gap*m)) * w ^ (2*r) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    _ ≈ w ^ (base + gap*m) * w ^ (2*r) :=
      Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (Q'.pow_add_eqv w base (gap*m)))
    _ ≈ w ^ ((base + gap*m) + 2*r) :=
      Q'.eqv_symm (Q'.pow_add_eqv w (base + gap*m) (2*r))

private theorem coeffW_repack (w : Q') (s base gap m r : Nat)
    (he : c4 s = base + gap*m + 2*r) :
    coeffW w s ≈
      Q'.ofNat (s+1) *
        (w ^ base *
          (RingNormaliser.qpow (w ^ gap) m *
            RingNormaliser.qpow (w ^ 2) r)) := by
  have hnative : coeffW w s ≈ Q'.ofNat (s+1) * w ^ (c4 s) := by
    unfold coeffW dimQ
    exact Q'.mul_eqv_congr_left _ _ _ (qpow_eqv_pow w (c4 s))
  rw [he] at hnative
  exact Q'.eqv_trans _ _ _ hnative
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (power_repack w base gap m r)))

private theorem exponent_shift (k s m r : Nat)
    (hs : (s = 0 ∧ m = 0 ∧ r = 0) ∨
      (s = 1 ∧ m = 1 ∧ r = 0) ∨
      (s = 2 ∧ m = 2 ∧ r = 1) ∨
      (s = 3 ∧ m = 3 ∧ r = 3) ∨
      (s = 4 ∧ m = 4 ∧ r = 6)) :
    c4 (k+s) = k*(k+2) + (2*k+3)*m + 2*r := by
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp only [c4, Nat.mul_add, Nat.add_mul] <;> omega

private theorem dim_shift (k s : Nat) :
    Q'.ofNat ((k+s)+1) ≈ Q'.ofNat (k+1) + Q'.ofNat s := by
  have he : (k+s)+1 = (k+1)+s := by omega
  rw [he]
  exact Q'.ofNat_add_eqv (k+1) s

private abbrev PE := RingNormaliser.PolyExpr

private def pieceExpr (s m r : Nat) : PE :=
  .mul (.add (.var 0) (.const s))
    (.mul (.var 1) (.mul (.pow (.var 2) m) (.pow (.var 3) r)))

private def bulkExpr : PE :=
  .add
    (.add
      (.add
        (.mul (.const 6) (pieceExpr 2 2 1))
        (.neg (.mul (.const 4)
          (.add (pieceExpr 1 1 0) (pieceExpr 3 3 3)))))
      (pieceExpr 0 0 0))
    (pieceExpr 4 4 6)

private def pExprShifted : PE := Id.run do
  let p : PE := .var 0
  let f : PE := .var 1
  let a : PE := .var 2
  let v : PE := .var 3
  let n := .add p (.const 2)
  let raw := .add
    (.add
      (.add
        (.add (.add n (.neg (.const 2)))
          (.neg (.mul (.const 4)
            (.mul (.add n (.neg (.const 1))) a))))
        (.mul (.const 6) (.mul n (.mul (.pow a 2) v))))
      (.neg (.mul (.const 4)
        (.mul (.add n (.const 1)) (.mul (.pow a 3) (.pow v 3))))))
    (.mul (.add n (.const 2)) (.mul (.pow a 4) (.pow v 6)))
  return .mul f raw

private def exprEnv (p f a v : Q') : Nat → Q'
  | 0 => p
  | 1 => f
  | 2 => a
  | _ => v

private theorem shifted_identity (p f a v : Q') :
    eval (exprEnv p f a v) bulkExpr ≈
      eval (exprEnv p f a v) pExprShifted :=
  poly_identity_of_normal_eq bulkExpr pExprShifted
    (by decide) (exprEnv p f a v)

private theorem shifted_factor (p f a v : Q') :
    eval (exprEnv p f a v) bulkExpr ≈
      f * quarticP (p+2) a v := by
  have hi := shifted_identity p f a v
  have hp := quarticP_formula (p+2) a v
  exact Q'.eqv_trans _ _ _ hi
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hp))

private theorem quarticP_congr_n {n n' a v : Q'} (hn : n ≈ n') :
    quarticP n a v ≈ quarticP n' a v := by
  -- The reflected polynomial is congruent in its first environment entry.
  have eval_congr : ∀ e : PE, ∀ ρ σ : Nat → Q',
      (∀ i, ρ i ≈ σ i) → eval ρ e ≈ eval σ e := by
    intro e
    induction e with
    | const c =>
        intro ρ σ _
        exact Q'.eqv_refl _
    | var i =>
        intro ρ σ h
        exact h i
    | add e₁ e₂ ih₁ ih₂ =>
        intro ρ σ h
        exact Q'.add_eqv_congr' (ih₁ ρ σ h) (ih₂ ρ σ h)
    | mul e₁ e₂ ih₁ ih₂ =>
        intro ρ σ h
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (ih₁ ρ σ h))
          (Q'.mul_eqv_congr_left _ _ _ (ih₂ ρ σ h))
    | neg e ih =>
        intro ρ σ h
        exact Q'.neg_eqv_congr _ _ (ih ρ σ h)
    | pow e k ih =>
        intro ρ σ h
        exact RingNormaliser.qpow_eqv_congr (ih ρ σ h) k
  unfold quarticP
  apply eval_congr
  intro i
  cases i with
  | zero => exact hn
  | succ i =>
      cases i with
      | zero => exact Q'.eqv_refl a
      | succ _ => exact Q'.eqv_refl v

/-- The five ACTUAL heat coefficients factor through the previously proved
scalar quartic polynomial.  No finite character cutoff is used here. -/
theorem quarticBulkCoeff_factor (w : Q') (k : Nat) :
    quarticBulkCoeff w k ≈
      w ^ (k*(k+2)) *
        quarticP (Q'.ofNat (k+3)) (w ^ (2*k+3)) (w ^ 2) := by
  let p := Q'.ofNat (k+1)
  let f := w ^ (k*(k+2))
  let a := w ^ (2*k+3)
  let v := w ^ 2
  have h0 := coeffW_repack w k (k*(k+2)) (2*k+3) 0 0
    (exponent_shift k 0 0 0 (Or.inl ⟨rfl, rfl, rfl⟩))
  have h1 := coeffW_repack w (k+1) (k*(k+2)) (2*k+3) 1 0
    (exponent_shift k 1 1 0 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have h2 := coeffW_repack w (k+2) (k*(k+2)) (2*k+3) 2 1
    (exponent_shift k 2 2 1 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  have h3 := coeffW_repack w (k+3) (k*(k+2)) (2*k+3) 3 3
    (exponent_shift k 3 3 3 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))
  have h4 := coeffW_repack w (k+4) (k*(k+2)) (2*k+3) 4 6
    (exponent_shift k 4 4 6 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))
  have hd0 := dim_shift k 0
  have hd1 := dim_shift k 1
  have hd2 := dim_shift k 2
  have hd3 := dim_shift k 3
  have hd4 := dim_shift k 4
  have hs0 : coeffW w k ≈ eval (exprEnv p f a v) (pieceExpr 0 0 0) := by
    exact Q'.eqv_trans _ _ _ h0
      (Q'.mul_eqv_congr_right _ _ _ hd0)
  have hs1 : coeffW w (k+1) ≈ eval (exprEnv p f a v) (pieceExpr 1 1 0) := by
    exact Q'.eqv_trans _ _ _ h1
      (Q'.mul_eqv_congr_right _ _ _ hd1)
  have hs2 : coeffW w (k+2) ≈ eval (exprEnv p f a v) (pieceExpr 2 2 1) := by
    exact Q'.eqv_trans _ _ _ h2
      (Q'.mul_eqv_congr_right _ _ _ hd2)
  have hs3 : coeffW w (k+3) ≈ eval (exprEnv p f a v) (pieceExpr 3 3 3) := by
    exact Q'.eqv_trans _ _ _ h3
      (Q'.mul_eqv_congr_right _ _ _ hd3)
  have hs4 : coeffW w (k+4) ≈ eval (exprEnv p f a v) (pieceExpr 4 4 6) := by
    exact Q'.eqv_trans _ _ _ h4
      (Q'.mul_eqv_congr_right _ _ _ hd4)
  have hbulk : quarticBulkCoeff w k ≈ eval (exprEnv p f a v) bulkExpr := by
    unfold quarticBulkCoeff bulkExpr
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hs2)
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.add_eqv_congr' hs1 hs3))))
        hs0) hs4
  have hnat : p + 2 ≈ Q'.ofNat (k+3) := by
    have he : (k+1)+2 = k+3 := by omega
    exact Q'.eqv_symm (by simpa only [he] using
      (Q'.ofNat_add_eqv (k+1) 2))
  exact Q'.eqv_trans _ _ _ hbulk
    (Q'.eqv_trans _ _ _ (shifted_factor p f a v)
      (Q'.mul_eqv_congr_left _ _ _
        (quarticP_congr_n hnat)))

/-- The original untruncated coefficient inherits the scalar box majorant.
The finite `K` expansion and moving-tail payment are not asserted. -/
theorem quarticBulkCoeff_le_majorant {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (k : Nat) :
    quarticBulkCoeff w k ≤
      w ^ (k*(k+2)) *
        quarticMajorant (Q'.ofNat (k+3))
          (w ^ (2*k+3)) (w ^ 2) := by
  have ha0 : (0 : Q') ≤ w ^ (2*k+3) := Q'.pow_nonneg w hw0 _
  have ha1 : w ^ (2*k+3) ≤ (1 : Q') :=
    YMGap.Continuum.HKPos.pow_le_one hw0 hw1 _
  have hv0 : (0 : Q') ≤ w ^ 2 := Q'.pow_nonneg w hw0 _
  have hv1 : w ^ 2 ≤ (1 : Q') :=
    YMGap.Continuum.HKPos.pow_le_one hw0 hw1 _
  have hn : (0 : Q') ≤ Q'.ofNat (k+3) :=
    YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _
  have hf : (0 : Q') ≤ w ^ (k*(k+2)) := Q'.pow_nonneg w hw0 _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (quarticBulkCoeff_factor w k))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (quarticP_le_majorant hn ha0 ha1 hv0 hv1) hf)

/-- Explicit nome-defect budget for the ACTUAL five-coefficient combination.
It is still an untruncated scalar coefficient, with no finite `K`. -/
theorem quarticBulkCoeff_le_nome_budget {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (k : Nat) :
    quarticBulkCoeff w k ≤
      w ^ (k*(k+2)) * budget (Q'.ofNat (k+3)) (1 + -w) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (quarticBulkCoeff_factor w k))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (nome_polynomial_le_budget hw0 hw1 k)
      (Q'.pow_nonneg w hw0 _))

/-- The center spin coefficient has precisely the heat factor required to
turn the bulk nome budget into a relative one. -/
theorem coeffW_center_factor (w : Q') (k : Nat) :
    coeffW w (k+2) ≈
      Q'.ofNat (k+3) *
        (w ^ (k*(k+2)) * w ^ (4*k+8)) := by
  have he : c4 (k+2) = k*(k+2) + (4*k+8) := by
    simp only [c4, Nat.mul_add, Nat.add_mul]
    omega
  unfold coeffW dimQ
  rw [show (k+2)+1 = k+3 by omega]
  have hp : w ^ (c4 (k+2)) ≈
      w ^ (k*(k+2)) * w ^ (4*k+8) := by
    rw [he]
    exact Q'.pow_add_eqv w (k*(k+2)) (4*k+8)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qpow_eqv_pow w (c4 (k+2))))
    (Q'.mul_eqv_congr_left _ _ _ hp)

/-- Coefficient multiplying the original `coeffW w (k+2)` under the explicit
half-guard.  It carries exactly two and four nome defects. -/
def relativeBudget (n h : Q') : Q' :=
  32*((n*n)*(n*n))*((h*h)*(h*h)) + 296*(h*h)

private theorem budget_doubling_identity (g f n h : Q') :
    (2*g) * (f * budget n h) ≈
      relativeBudget n h * (n * (f*g)) := by
  unfold budget relativeBudget
  exact poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.var 0))
      (.mul (.var 1)
        (.add
          (.mul (.mul (.mul (.const 16) (.var 2))
            (.mul (.mul (.var 2) (.var 2)) (.mul (.var 2) (.var 2))))
            (.mul (.mul (.var 3) (.var 3)) (.mul (.var 3) (.var 3))))
          (.mul (.mul (.const 148) (.var 2))
            (.mul (.var 3) (.var 3))))))
    (.mul
      (.add
        (.mul (.mul (.const 32)
          (.mul (.mul (.var 2) (.var 2)) (.mul (.var 2) (.var 2))))
          (.mul (.mul (.var 3) (.var 3)) (.mul (.var 3) (.var 3))))
        (.mul (.const 296) (.mul (.var 3) (.var 3))))
      (.mul (.var 2) (.mul (.var 1) (.var 0))))
    (by decide) (fun | 0 => g | 1 => f | 2 => n | _ => h)

private theorem budget_nonnegative {n h : Q'}
    (hn : (0 : Q') ≤ n) (hh : (0 : Q') ≤ h) :
    (0 : Q') ≤ budget n h := by
  have hn2 : (0 : Q') ≤ n*n := Q'.mul_nonneg _ _ hn hn
  have hh2 : (0 : Q') ≤ h*h := Q'.mul_nonneg _ _ hh hh
  have hn4 : (0 : Q') ≤ (n*n)*(n*n) := Q'.mul_nonneg _ _ hn2 hn2
  have hh4 : (0 : Q') ≤ (h*h)*(h*h) := Q'.mul_nonneg _ _ hh2 hh2
  unfold budget
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hn) hn4) hh4)
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) hn) hh2)

/-- Relative low-spin scalar control under the named half-guard.  The guard
is not asserted for every spin or every nome, and this theorem does not
assemble a finite character expansion. -/
theorem quarticBulkCoeff_le_relative {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (k : Nat)
    (hhalf : (1 : Q') ≤ 2 * w ^ (4*k+8)) :
    quarticBulkCoeff w k ≤
      relativeBudget (Q'.ofNat (k+3)) (1 + -w) * coeffW w (k+2) := by
  let n := Q'.ofNat (k+3)
  let h := (1 : Q') + -w
  let f := w ^ (k*(k+2))
  let g := w ^ (4*k+8)
  have hn : (0 : Q') ≤ n := Q'.ofNat_nonneg _
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le hw1
  have hf : (0 : Q') ≤ f := Q'.pow_nonneg w hw0 _
  have hfb : (0 : Q') ≤ f * budget n h :=
    Q'.mul_nonneg _ _ hf (budget_nonnegative hn hh)
  have hg : f * budget n h ≤ (2*g) * (f * budget n h) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hhalf hfb)
  have hcenter := coeffW_center_factor w k
  have hbudget : (2*g) * (f * budget n h) ≈
      relativeBudget n h * coeffW w (k+2) :=
    Q'.eqv_trans _ _ _ (budget_doubling_identity g f n h)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hcenter))
  exact Q'.le_trans' _ _ _ (quarticBulkCoeff_le_nome_budget hw0 hw1 k)
    (Q'.le_trans' _ _ _ hg (Q'.le_of_eqv hbudget))

end YMGap.Continuum.SU2HeatQuarticBulkCoefficient

#print axioms YMGap.Continuum.SU2HeatQuarticBulkCoefficient.quarticBulkCoeff_factor
#print axioms YMGap.Continuum.SU2HeatQuarticBulkCoefficient.quarticBulkCoeff_le_majorant
#print axioms YMGap.Continuum.SU2HeatQuarticBulkCoefficient.quarticBulkCoeff_le_nome_budget
#print axioms YMGap.Continuum.SU2HeatQuarticBulkCoefficient.coeffW_center_factor
#print axioms YMGap.Continuum.SU2HeatQuarticBulkCoefficient.budget_doubling_identity
#print axioms YMGap.Continuum.SU2HeatQuarticBulkCoefficient.quarticBulkCoeff_le_relative
