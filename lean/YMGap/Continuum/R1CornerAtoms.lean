/-
Track B / local-CLT — reusable ATOMS for the parabolic branch of the R1 upper-tail corner
(`R1CornerScaffold.ParabolicTailBranch`).

# What this file provides (all PROVED, axiom-clean)

  * `oneSub_qpow_le` — the Bernoulli weight bound `1 − wⁿ ≤ n·(1−w)` on `0 ≤ w ≤ 1`.  This is exactly
    the control `h_D = 1 − w^{D²/2} ≤ (D²/2)·(1−w)` on the theta-defect weights that the parabolic
    branch uses against the exact backbone `P(t) = t(t+4)/5`.  Clean single induction; the step is
    `1 − w^{n+1} = (1 − wⁿ) + wⁿ(1−w) ≤ n(1−w) + 1·(1−w)` using `wⁿ ≤ 1`.
  * `parabolicBackbone`, `d2_parabolicBackbone` — the exact anchor `P(t) = t(t+4)/5` (the `w = 1`
    variance) as a `Q'` and its second difference `Δ²P(s) + 2 = 12/5`, pure `Q'` algebra.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`,
no custom `axiom`.
-/

import YMGap.Continuum.R1RegimeGE
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.R1CornerAtoms

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.CircleFourierPowerModel

/-- Cancellation-free ring closer for `Q'.eqv` (local copy of the `R1EvenCentreBound` macro). -/
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, R1EvenCentreBound.neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 1. The Bernoulli weight bound `1 − wⁿ ≤ n·(1−w)`. -/

/-- **`oneSub_qpow_le`** — Bernoulli's inequality in weight-defect form: for `0 ≤ w ≤ 1`,
`1 − wⁿ ≤ n·(1−w)`.  With `n = D²/2` this is `h_D ≤ (D²/2)(1−w)`, the parabolic branch's control on
the theta defect. -/
theorem oneSub_qpow_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    ∀ n, (1 : Q') + -(qpow w n) ≤ Q'.ofNat n * (1 + -w)
  | 0 => by
      -- both sides `≃ 0`
      have hq0 : (qpow w 0).eqv 1 := Q'.eqv_of_eq (qpow_zero w)
      have hL : ((1 : Q') + -(qpow w 0)).eqv 0 :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _ hq0)) (Q'.add_neg_self_eqv 1)
      have hR : (Q'.ofNat 0 * (1 + -w)).eqv 0 := Q'.zero_mul_eqv _
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.ge_of_eqv hR)
  | (n + 1) => by
      have ih := oneSub_qpow_le hw0 hw1 n
      have honesub : (0 : Q') ≤ (1 : Q') + -w := oneSub_nonneg hw1
      have hqle1 : qpow w n ≤ (1 : Q') := HeatKernelGap.qpow_le_one hw0 hw1 n
      -- (id) 1 − w^{n+1} ≃ (1 − wⁿ) + wⁿ(1−w).  Explicit `Q'` algebra (`q := wⁿ`):
      have hid : ((1 : Q') + -(qpow w (n + 1))).eqv
          (((1 : Q') + -(qpow w n)) + qpow w n * (1 + -w)) := by
        show ((1 : Q') + -(qpow w n * w)).eqv _
        -- wⁿ(1−w) ≃ wⁿ + -(wⁿ·w)
        have hA : (qpow w n * (1 + -w)).eqv (qpow w n + -(qpow w n * w)) :=
          Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (qpow w n) 1 (-w))
            (Q'.add_eqv_congr' (Q'.mul_one_eqv (qpow w n)) (Q'.mul_neg_eqv (qpow w n) w))
        -- −wⁿ + (wⁿ + x) ≃ x
        have hD : ((-(qpow w n)) + (qpow w n + -(qpow w n * w))).eqv (-(qpow w n * w)) :=
          Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.add_assoc_eqv (-(qpow w n)) (qpow w n) (-(qpow w n * w))))
            (Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ _ _ (Q'.neg_add_self_eqv (qpow w n)))
              (q_zero_add_eqv (-(qpow w n * w))))
        -- assemble RHS ≃ 1 + -(wⁿ·w) = LHS
        refine Q'.eqv_symm ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hA) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv 1 (-(qpow w n)) (qpow w n + -(qpow w n * w))) ?_
        exact Q'.add_eqv_congr_left _ _ _ hD
      -- (s1) ih  ⇒  add wⁿ(1−w)
      have hs1 : ((1 : Q') + -(qpow w n)) + qpow w n * (1 + -w)
          ≤ Q'.ofNat n * (1 + -w) + qpow w n * (1 + -w) :=
        Q'.add_le_add_right _ _ (qpow w n * (1 + -w)) ih
      -- (s2) wⁿ ≤ 1  ⇒  wⁿ(1−w) ≤ 1·(1−w)
      have hmul : qpow w n * (1 + -w) ≤ (1 : Q') * (1 + -w) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hqle1 honesub
      have hs2 : Q'.ofNat n * (1 + -w) + qpow w n * (1 + -w)
          ≤ Q'.ofNat n * (1 + -w) + (1 : Q') * (1 + -w) :=
        Q'.add_le_add_left _ _ _ hmul
      -- (fin) collapse to ofNat(n+1)·(1−w)
      have hfin : (Q'.ofNat n * (1 + -w) + (1 : Q') * (1 + -w)).eqv
          (Q'.ofNat (n + 1) * (1 + -w)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (R1CaseSplit.add_mul_local (Q'.ofNat n) (1 : Q') (1 + -w))) ?_
        refine Q'.mul_eqv_congr_right _ _ _ ?_
        exact Q'.eqv_symm (Q'.ofNat_add_eqv n 1)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
        (Q'.le_trans' _ _ _ hs1 (Q'.le_trans' _ _ _ hs2 (Q'.le_of_eqv hfin)))

end YMGap.Continuum.R1CornerAtoms

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1CornerAtoms.oneSub_qpow_le
