/-
# Obstruction to the coarse dyadic rational loss budget

The rationalized survival interface is useful only if its explicit budget can
hold.  The current cubic certificate cannot satisfy that budget when paired
with the coarse `starRatio` floor: the loss coefficient is at least 384 while
the admissible relative coefficient is at most 2.  This compares certificate
numbers only; it is not a lower bound on the actual completed loss.
-/

import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicRationalBudgetObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusteringImpliesGap
  (lt_of_lt_of_le mul_lt_mul_of_pos_right lt_irrefl')
open YMGap.Constructive.SU3CharFactor (ofNat_mul_eqv)

local infix:50 " ≈ " => Q'.eqv

def dyadicSide (scale : Nat) : Nat := 2 ^ scale

def dyadicLossBoundFormula (w : Q') (scale : Nat) : Q' :=
  (384 : Q') * (Q'.ofNat (dyadicSide scale) *
    (Q'.ofNat (dyadicSide scale) * Q'.ofNat (dyadicSide scale))) * (1 + -w)

/-- Type-level data for the proposed coarse rational survival budget.  The
fields are intentionally witnesses, so its emptiness is a constructive
obstruction rather than a negated existence claim with hidden choice. -/
structure CoarseBudgetData (w : Q') (scale : Nat) where
  rho : Q'
  delta : Q'
  theta : Q'
  rho_defect : rho ≤ 1 + -w
  delta_nonnegative : (0 : Q') ≤ delta
  theta_nonnegative : (0 : Q') ≤ theta
  fraction_budget : delta + theta ≤ (1 : Q')
  loss_budget : dyadicLossBoundFormula w scale ≤ (2*delta) * rho

variable {w : Q'} (scale : Nat)

theorem no_rational_loss_budget
    (rho delta theta : Q')
    (hd : (0 : Q') < 1 + -w)
    (hdelta : (0 : Q') ≤ delta)
    (htheta : (0 : Q') ≤ theta)
    (hbudget : delta + theta ≤ (1 : Q'))
    (hstarDefect : rho ≤ 1 + -w)
    (hbudgetLoss : dyadicLossBoundFormula w scale ≤
      (2*delta) * rho) : False := by
  let L := dyadicSide scale
  let d : Q' := 1 + -w
  have hd' : (0 : Q') < d := by
    simpa only [d] using hd
  have hd0 : (0 : Q') ≤ d := Q'.le_of_lt hd
  have hdelta_one : delta ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg delta theta htheta) hbudget
  have hcoef_delta : (2*delta : Q') ≤ 2 := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hdelta_one (by decide)
  have hstar : rho ≤ d := by
    simpa only [d] using hstarDefect
  have hnonneg_two_delta : (0 : Q') ≤ 2*delta :=
    Q'.mul_nonneg (2 : Q') delta (by decide) hdelta
  have hright_one : (2*delta) * rho ≤
      (2*delta) * d :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hstar hnonneg_two_delta
  have hright_two : (2*delta) * d ≤ 2*d :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcoef_delta hd0
  have hupper : (2*delta) * rho ≤ 2*d :=
    Q'.le_trans' _ _ _ hright_one hright_two
  have hLpos : 0 < L := by
    exact Nat.pow_pos (by decide)
  have hL1 : 1 ≤ L := hLpos
  have hLsq : L ≤ L*L := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left L hL1
  have hLcube : L ≤ L*(L*L) :=
    Nat.le_trans hLsq (Nat.mul_le_mul_left L hLsq)
  have hprod : 1 ≤ L*(L*L) := Nat.le_trans hL1 hLcube
  have h384prod : 384 ≤ 384*(L*(L*L)) :=
    Nat.mul_le_mul_left 384 hprod
  have h2lt384 : (2 : Q') < 384 := by decide
  have h384le : (384 : Q') ≤ Q'.ofNat (384*(L*(L*L))) :=
    CReal.ofNat_le_ofNat h384prod
  have h2ltNat : (2 : Q') < Q'.ofNat (384*(L*(L*L))) :=
    lt_of_lt_of_le h2lt384 h384le
  have hright : Q'.ofNat (384*(L*(L*L))) ≈
      (384 : Q') * (Q'.ofNat L * (Q'.ofNat L * Q'.ofNat L)) := by
    exact Q'.eqv_trans _ _ _ (ofNat_mul_eqv 384 (L*(L*L)))
      (Q'.mul_eqv_congr_left (384 : Q') _ _
        (Q'.eqv_trans _ _ _ (ofNat_mul_eqv L (L*L))
          (Q'.mul_eqv_congr_left (Q'.ofNat L) _ _
            (ofNat_mul_eqv L L))))
  have hcoef : (2 : Q') <
      (384 : Q') * (Q'.ofNat L * (Q'.ofNat L * Q'.ofNat L)) :=
    lt_of_lt_of_le h2ltNat (Q'.le_of_eqv hright)
  have hstrict : 2*d <
      ((384 : Q') * (Q'.ofNat L * (Q'.ofNat L * Q'.ofNat L))) * d :=
    mul_lt_mul_of_pos_right hd' hcoef
  have hstrictLoss : 2*d < dyadicLossBoundFormula w scale := by
    simpa only [dyadicLossBoundFormula, L, d] using hstrict
  have hleLoss : dyadicLossBoundFormula w scale ≤ 2*d :=
    Q'.le_trans' _ _ _ hbudgetLoss hupper
  exact lt_irrefl' _ (lt_of_lt_of_le hstrictLoss hleLoss)

theorem coarse_budget_data_empty
    (h : (0 : Q') < 1 + -w) :
    CoarseBudgetData w scale → False := by
  intro data
  exact no_rational_loss_budget (w := w) scale data.rho data.delta data.theta h
    data.delta_nonnegative data.theta_nonnegative data.fraction_budget
    data.rho_defect data.loss_budget

#print axioms no_rational_loss_budget
#print axioms coarse_budget_data_empty

end YMGap.Continuum.BF4WilsonAllNomeDyadicRationalBudgetObstruction
