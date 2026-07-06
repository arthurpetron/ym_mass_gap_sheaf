/-
Track B / R2 — the EXACT quadratic factorization of the renormalized (counterterm-
subtracted) per-step block-spin defect, and the sharp `≤ 3·(1−w)²` bound.

# Why this module exists — the crux algebra, made exact

The Clay-core continuum crux (block-spin defect summability) turns on the true
renormalized per-step defect being QUADRATIC in the weak-coupling margin `1 − w`,
NOT linear.  The three transverse modes' crude *linear* defect `3·(1 − w)` minus
the actual renormalized deviation `1 − w³` is EXACTLY

    3·(1 − w)  −  (1 − w³)   ≃   (1 − w)²·(2 + w).

The linear terms cancel; the residual is second order.  Because the asymptotic-
freedom trajectory has `1 − w_k ∼ 1/k`, a quadratic residual is `∼ 1/k²` — SUMMABLE
(`Σ 1/k² < ∞`), which is why `Σ δ_k` converges (vs. the falsified Migdal–Kadanoff
*linear* `Σ 1/k`).  `C₄(1) = 3` is `dim`-times the SU(2) first-excited Casimir; the
bond-moving deviation on the `s = 1` mode is `1 − w^{C₄(1)} = 1 − w³`.

`BondMovingQuadratic` already proves the *envelope* form `δ_ren ≤ 9·(1 − w)²` (the
generic second-order Taylor remainder `n(1−w) − (1−w^n) ≤ n²(1−w)²` at `n = 3`).
This module proves the EXACT factorization, which is SHARPER: `(1−w)²·(2+w)` with
`2 + w ≤ 3` on `[0,1]` gives `δ_ren ≤ 3·(1 − w)²` — a factor-of-three improvement
over the `n² = 9` envelope.

# What is PROVED here (genuine `Q'` facts, axiom-clean)

  * `renDefect_factor` — the EXACT identity
        3·(1 − w) − (1 − w³)  ≃  (1 − w)·(1 − w)·(2 + w)
    proved by FACTORING (not coefficient-collection): `1 − w³ = (1−w)·∑_{i<3} wⁱ`,
    factor out `(1 − w)`, then `3 − ∑ = (1−w) + (1−w²) = (1−w)·(2+w)`.  Every step
    is a distribute-or-factor `Q'.eqv` congruence with NO like-degree coefficient
    collection (the custom `ring_qeqv` AC-closer cannot collect; this route avoids
    it entirely).
  * `renDefect_le_three_sq` — the sharp BOUND: for `0 ≤ w ≤ 1`,
        3·(1 − w) − (1 − w³)  ≤  3·((1 − w)·(1 − w)),
    from the identity plus `2 + w ≤ 3` on `[0,1]` and `(1−w)² ≥ 0`.  This exhibits
    the renormalized per-step defect as `≤ 3·(1 − w)² = O(g⁴)` — the summable scaling.
  * `bondMovingDeltaRen_le_sixp` — the HOOK into `BondMovingQuadratic`: the
    dominant-mode renormalized defect obeys
        bondMovingDeltaRen N p w  ≤  p·dimQ 1·3·(1 − w)²  =  6p·(1 − w)²,
    tightening the module's `18p·(1 − w)²` envelope by the exact `(2 + w) ≤ 3` slack.
  * `bondMovingDeltaRen_le_sixp_invSq` — the AF-closure corollary: `1 − w ≤ r`
    gives `≤ 6p·(r·r)`, the inverse-square per-step form feeding `Σ 1/k² < ∞`.

# Sanity (numeric, `w = 1/2`)

`3·½ − (1 − ⅛) = 1.5 − 0.875 = 0.625` and `(½)²·(2.5) = 0.625` ✓; `≤ 3·¼ = 0.75` ✓.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing the geometric factorization `oneSub_pow_factor`.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses (the identity, the bound, the constant) are `Type`-level `Q'` data.
-/

import YMGap.Continuum.BondMovingQuadratic

namespace YMGap.Continuum.RenDefectQuadFactor

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingQuadratic

/-! ## 0. Numeric constant helpers (decidable `Q'.eqv`, no variables). -/

/-- `1 + 1 ≃ 2` in `Q'`. -/
theorem one_add_one_eqv_two : ((1 : Q') + 1).eqv (Q'.ofNat 2) := by decide

/-- `2 + 1 ≃ 3` in `Q'`. -/
theorem two_add_one_eqv_three : ((Q'.ofNat 2) + 1).eqv (Q'.ofNat 3) := by decide

/-- `3 + (−1) ≃ 2` in `Q'`. -/
theorem three_add_negOne_eqv_two : ((Q'.ofNat 3) + (-(1 : Q'))).eqv (Q'.ofNat 2) := by decide

/-! ## 1. The two small geometric-sum forms. -/

/-- `∑_{i<2} wⁱ = 1 + w`.  (`geomSum w 2 = (0 + 1) + (1·w)`, cleaned by
`0 + · ≃ ·` and `1·· ≃ ·`.) -/
theorem geomSum_two (w : Q') : (geomSum w 2).eqv ((1 : Q') + w) := by
  have e1 : geomSum w 2 = ((0 : Q') + 1) + ((1 : Q') * w) := rfl
  rw [e1]
  exact Q'.add_eqv_congr' (q_zero_add_eqv 1) (Q'.one_mul_eqv w)

/-- `∑_{i<3} wⁱ ≃ (1 + w) + w²` (fold the top term off the degree-2 sum). -/
theorem geomSum_three (w : Q') :
    (geomSum w 3).eqv (((1 : Q') + w) + qpow w 2) := by
  have e1 : geomSum w 3 = geomSum w 2 + qpow w 2 := rfl
  rw [e1]
  exact Q'.add_eqv_congr_right _ _ (qpow w 2) (geomSum_two w)

/-! ## 2. `1 − w² ≃ (1 − w)·(1 + w)` — the degree-2 factorization, cleaned. -/

/-- `1 − w² ≃ (1 − w)·(1 + w)`. -/
theorem oneSub_qpow_two_factor (w : Q') :
    ((1 : Q') - qpow w 2).eqv (((1 : Q') - w) * ((1 : Q') + w)) := by
  refine Q'.eqv_trans _ _ _ (oneSub_pow_factor w 2) ?_
  exact Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ (geomSum_two w)

/-! ## 3. The two factoring cores. -/

/-- **Product core:** `(1 − w) + (1 − w²) ≃ (1 − w)·(2 + w)`.  Factoring:
`(1−w) = (1−w)·1`, `(1−w²) = (1−w)·(1+w)`, so the sum is `(1−w)·(1 + (1+w))`, and
`1 + (1 + w) ≃ 2 + w`. -/
theorem sumMargins_factor (w : Q') :
    (((1 : Q') - w) + ((1 : Q') - qpow w 2)).eqv
      (((1 : Q') - w) * (Q'.ofNat 2 + w)) := by
  -- (1−w) + (1−w²) ≃ (1−w)·1 + (1−w)·(1+w)
  have h1 : (((1 : Q') - w) + ((1 : Q') - qpow w 2)).eqv
      (((1 : Q') - w) * (1 : Q') + ((1 : Q') - w) * ((1 : Q') + w)) :=
    Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.mul_one_eqv ((1 : Q') - w)))
      (oneSub_qpow_two_factor w)
  -- (1−w)·1 + (1−w)·(1+w) ≃ (1−w)·(1 + (1+w))
  have h2 : (((1 : Q') - w) * (1 : Q') + ((1 : Q') - w) * ((1 : Q') + w)).eqv
      (((1 : Q') - w) * ((1 : Q') + ((1 : Q') + w))) :=
    Q'.eqv_symm (Q'.mul_add_eqv ((1 : Q') - w) (1 : Q') ((1 : Q') + w))
  -- 1 + (1 + w) ≃ 2 + w
  have h3 : ((1 : Q') + ((1 : Q') + w)).eqv (Q'.ofNat 2 + w) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (1 : Q') w)) ?_
    exact Q'.add_eqv_congr_right _ _ w one_add_one_eqv_two
  have h4 : (((1 : Q') - w) * ((1 : Q') + ((1 : Q') + w))).eqv
      (((1 : Q') - w) * (Q'.ofNat 2 + w)) :=
    Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ h3
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h4)

/-- **Sum core:** `3 − ∑_{i<3} wⁱ ≃ (1 − w) + (1 − w²)`.  Both sides reduce
(cancellation-free) to the normal form `2 + (−w) + (−w²)`, with the constant
collapses `3 + (−1) ≃ 2` and `1 + 1 ≃ 2` discharged by `decide`. -/
theorem three_sub_geomSum_three (w : Q') :
    ((Q'.ofNat 3) - geomSum w 3).eqv
      (((1 : Q') - w) + ((1 : Q') - qpow w 2)) := by
  -- normal form  NF := (2 + (−w)) + (−w²)
  -- LHS → NF
  have hL : ((Q'.ofNat 3) - geomSum w 3).eqv
      ((Q'.ofNat 2 + (-w)) + (-(qpow w 2))) := by
    -- −geomSum w 3 ≃ (−1 + −w) + −w²
    have hng : (-(geomSum w 3)).eqv (((-1 : Q') + (-w)) + (-(qpow w 2))) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (geomSum_three w)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv ((1 : Q') + w) (qpow w 2)) ?_
      exact Q'.add_eqv_congr_right _ _ (-(qpow w 2)) (Q'.neg_add_eqv (1 : Q') w)
    -- 3 + (−geomSum) ≃ 3 + ((−1+−w)+−w²)
    have hstep : ((Q'.ofNat 3) - geomSum w 3).eqv
        ((Q'.ofNat 3) + (((-1 : Q') + (-w)) + (-(qpow w 2)))) :=
      Q'.add_eqv_congr_left (Q'.ofNat 3) _ _ hng
    -- reassociate: 3 + ((−1+−w)+−w²) ≃ ((3+(−1+−w)) + −w²) ≃ (((3+−1)+−w)+−w²) ≃ NF
    refine Q'.eqv_trans _ _ _ hstep ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 3) ((-1 : Q') + (-w)) (-(qpow w 2)))) ?_
    refine Q'.add_eqv_congr_right _ _ (-(qpow w 2)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 3) (-1 : Q') (-w))) ?_
    exact Q'.add_eqv_congr_right _ _ (-w) three_add_negOne_eqv_two
  -- RHS → NF
  have hR : (((1 : Q') - w) + ((1 : Q') - qpow w 2)).eqv
      ((Q'.ofNat 2 + (-w)) + (-(qpow w 2))) := by
    -- ((1+−w) + (1+−w²)) ≃ ((1+−w)+1) + −w²
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv ((1 : Q') + (-w)) (1 : Q') (-(qpow w 2)))) ?_
    refine Q'.add_eqv_congr_right _ _ (-(qpow w 2)) ?_
    -- (1+−w)+1 ≃ 1+(−w+1) ≃ 1+(1+−w) ≃ (1+1)+−w ≃ 2+−w
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (1 : Q') (-w) (1 : Q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.add_comm_eqv (-w) (1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (1 : Q') (-w))) ?_
    exact Q'.add_eqv_congr_right _ _ (-w) one_add_one_eqv_two
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- **The core factorization:** `3 − ∑_{i<3} wⁱ ≃ (1 − w)·(2 + w)`. -/
theorem three_sub_geomSum_three_factor (w : Q') :
    ((Q'.ofNat 3) - geomSum w 3).eqv (((1 : Q') - w) * (Q'.ofNat 2 + w)) :=
  Q'.eqv_trans _ _ _ (three_sub_geomSum_three w) (sumMargins_factor w)

/-! ## 4. THE EXACT IDENTITY. -/

/-- **`renDefect_factor` — the exact quadratic factorization of the renormalized
per-step defect.**

    3·(1 − w)  −  (1 − w³)   ≃   (1 − w)·(1 − w)·(2 + w).

The three transverse modes' crude linear defect `3(1 − w)` minus the true
renormalized deviation `1 − w³` factors exactly into `(1 − w)²·(2 + w)`: the linear
term cancels, leaving a genuinely quadratic residual.  Proved by factoring
(`1 − w³ = (1−w)·∑_{i<3} wⁱ`, factor out `(1 − w)`, `3 − ∑ = (1−w)·(2+w)`), never by
coefficient collection. -/
theorem renDefect_factor (w : Q') :
    ((Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3)).eqv
      ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w)) := by
  -- 1 − w³ ≃ (1−w)·∑_{i<3} wⁱ
  have hfac3 : ((1 : Q') - qpow w 3).eqv (((1 : Q') - w) * geomSum w 3) :=
    oneSub_pow_factor w 3
  -- Step A: rewrite the subtrahend
  have hA : ((Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3)).eqv
      ((Q'.ofNat 3 * ((1 : Q') - w)) + (-(((1 : Q') - w) * geomSum w 3))) :=
    Q'.add_eqv_congr_left (Q'.ofNat 3 * ((1 : Q') - w)) _ _
      (Q'.neg_eqv_congr _ _ hfac3)
  -- Step B: factor out (1−w) → (1−w)·(3 − ∑)
  have hB : ((Q'.ofNat 3 * ((1 : Q') - w)) + (-(((1 : Q') - w) * geomSum w 3))).eqv
      (((1 : Q') - w) * ((Q'.ofNat 3) - geomSum w 3)) := by
    -- 3·(1−w) ≃ (1−w)·3 ; −((1−w)·∑) ≃ (1−w)·(−∑)
    have hcomm : (Q'.ofNat 3 * ((1 : Q') - w)).eqv (((1 : Q') - w) * Q'.ofNat 3) :=
      Q'.mul_comm_eqv (Q'.ofNat 3) ((1 : Q') - w)
    have hneg : (-(((1 : Q') - w) * geomSum w 3)).eqv
        (((1 : Q') - w) * (-(geomSum w 3))) :=
      Q'.eqv_symm (Q'.mul_neg_eqv ((1 : Q') - w) (geomSum w 3))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hcomm hneg) ?_
    -- (1−w)·3 + (1−w)·(−∑) ≃ (1−w)·(3 + (−∑)) = (1−w)·(3 − ∑)
    exact Q'.eqv_symm
      (Q'.mul_add_eqv ((1 : Q') - w) (Q'.ofNat 3) (-(geomSum w 3)))
  -- Step C: 3 − ∑ ≃ (1−w)·(2+w)
  have hC : (((1 : Q') - w) * ((Q'.ofNat 3) - geomSum w 3)).eqv
      (((1 : Q') - w) * (((1 : Q') - w) * (Q'.ofNat 2 + w))) :=
    Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ (three_sub_geomSum_three_factor w)
  -- Step D: reassociate
  have hD : (((1 : Q') - w) * (((1 : Q') - w) * (Q'.ofNat 2 + w))).eqv
      ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w)) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv ((1 : Q') - w) ((1 : Q') - w) (Q'.ofNat 2 + w))
  exact Q'.eqv_trans _ _ _ hA (Q'.eqv_trans _ _ _ hB (Q'.eqv_trans _ _ _ hC hD))

/-! ## 5. THE SHARP BOUND. -/

/-- `2 + w ≤ 3` on `w ≤ 1`. -/
theorem two_add_w_le_three {w : Q'} (hw1 : w ≤ (1 : Q')) :
    Q'.ofNat 2 + w ≤ Q'.ofNat 3 := by
  have hstep : Q'.ofNat 2 + w ≤ Q'.ofNat 2 + 1 :=
    Q'.add_le_add_left (Q'.ofNat 2) w 1 hw1
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv two_add_one_eqv_three)

/-- **`renDefect_le_three_sq` — the sharp quadratic bound.**  For `0 ≤ w ≤ 1`,

    3·(1 − w)  −  (1 − w³)   ≤   3·((1 − w)·(1 − w)),

i.e. the renormalized per-step defect is `≤ 3·(1 − w)² = O(g⁴)` — the summable
scaling.  From `renDefect_factor` with `2 + w ≤ 3` (`w ≤ 1`) and `(1 − w)² ≥ 0`. -/
theorem renDefect_le_three_sq {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    (Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3)
      ≤ Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)) := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hsqnn : (0 : Q') ≤ ((1 : Q') - w) * ((1 : Q') - w) := Q'.mul_nonneg _ _ hnn hnn
  -- (1−w)²·(2+w) ≤ (1−w)²·3
  have hmul : (((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w)
      ≤ (((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 3) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (two_add_w_le_three hw1) hsqnn
  -- (1−w)²·3 ≃ 3·(1−w)²
  have hcomm : ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 3)).eqv
      (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w))) :=
    Q'.mul_comm_eqv (((1 : Q') - w) * ((1 : Q') - w)) (Q'.ofNat 3)
  have hstep : (((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w)
      ≤ Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)) :=
    Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcomm)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (renDefect_factor w)) hstep

/-! ## 6. THE HOOK — tightening `BondMovingQuadratic.bondMovingDeltaRen`.

`bondMovingDeltaRen N p w = p·dimQ 1·( C₄(1)·(1 − w) − (1 − w^{C₄(1)}) )` with
`C₄(1) = 3`, so its bracket is exactly `3·(1 − w) − (1 − w³)`.  The generic
envelope `bondMovingDeltaRen_quadratic` bounds it by `18p·(1 − w)²` (the `n² = 9`
Taylor remainder).  The exact factorization gives the SHARPER `6p·(1 − w)²`. -/

/-- **`bondMovingDeltaRen_le_sixp` — the sharpened hook.**  On `[0,1]`,

    bondMovingDeltaRen N p w  ≤  (ofNat p)·(dimQ 1·(3·(1 − w)²)),

i.e. `≤ 6p·(1 − w)²` (`dimQ 1 = 2`), improving the module's `18p·(1 − w)²`
envelope by the exact `(2 + w) ≤ 3` slack. -/
theorem bondMovingDeltaRen_le_sixp {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N p : Nat) :
    bondMovingDeltaRen N p w
      ≤ Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)))) := by
  -- the bracket of `bondMovingDeltaRen` is `3·(1−w) − (1 − w³)` (c4 1 = 3, defeq)
  have hbr : (Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))
      ≤ Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)) :=
    renDefect_le_three_sq hw0 hw1
  have hd : dimQ 1 * ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1)))
      ≤ dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hbr (dimQ_nonneg 1)
  have hp : Q'.ofNat p * (dimQ 1 *
      ((Q'.ofNat (c4 1) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 1))))
      ≤ Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hd (zero_le_ofNat p)
  exact hp

/-- The sharpened constant is `6p`: `p·dimQ 1·3 ≃ 6p`. -/
theorem bondMovingDeltaRen_sixp_const (p : Nat) :
    (Q'.ofNat p * (dimQ 1 * Q'.ofNat 3)).eqv (Q'.ofNat (6 * p)) := by
  -- dimQ 1 = ofNat 2 ; 2·3 = 6 ; p·6 = 6p
  have hdc : (dimQ 1 * Q'.ofNat 3).eqv (Q'.ofNat 6) := by
    show (Q'.ofNat 2 * Q'.ofNat 3).eqv (Q'.ofNat 6)
    exact Q'.eqv_symm (ofNat_mul_eqv 2 3)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat p) _ _ hdc) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ofNat_mul_eqv p 6)) ?_
  rw [Nat.mul_comm p 6]
  exact Q'.eqv_refl _

/-- **AF-closure corollary (sharp constant).**  A margin control `1 − w ≤ r` gives

    bondMovingDeltaRen N p w  ≤  (ofNat p)·(dimQ 1·(3·(r·r))),

the inverse-square per-step form `≤ 6p·(r·r)` feeding `Σ 1/k² < ∞` — the sharp
(factor-of-three tighter) sibling of `bondMovingDeltaRen_invSq`. -/
theorem bondMovingDeltaRen_le_sixp_invSq {w r : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hr : (1 : Q') - w ≤ r) (N p : Nat) :
    bondMovingDeltaRen N p w
      ≤ Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 * (r * r))) := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hsq : ((1 : Q') - w) * ((1 : Q') - w) ≤ r * r := sq_le_sq hnn hr
  -- 3·(1−w)² ≤ 3·(r·r)
  have h3 : Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)) ≤ Q'.ofNat 3 * (r * r) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsq (zero_le_ofNat 3)
  have hd : dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)))
      ≤ dimQ 1 * (Q'.ofNat 3 * (r * r)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h3 (dimQ_nonneg 1)
  have hp : Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w))))
      ≤ Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 * (r * r))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hd (zero_le_ofNat p)
  exact Q'.le_trans' _ _ _ (bondMovingDeltaRen_le_sixp hw0 hw1 N p) hp

end YMGap.Continuum.RenDefectQuadFactor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RenDefectQuadFactor.geomSum_two
#print axioms YMGap.Continuum.RenDefectQuadFactor.geomSum_three
#print axioms YMGap.Continuum.RenDefectQuadFactor.oneSub_qpow_two_factor
#print axioms YMGap.Continuum.RenDefectQuadFactor.sumMargins_factor
#print axioms YMGap.Continuum.RenDefectQuadFactor.three_sub_geomSum_three
#print axioms YMGap.Continuum.RenDefectQuadFactor.three_sub_geomSum_three_factor
#print axioms YMGap.Continuum.RenDefectQuadFactor.renDefect_factor
#print axioms YMGap.Continuum.RenDefectQuadFactor.renDefect_le_three_sq
#print axioms YMGap.Continuum.RenDefectQuadFactor.bondMovingDeltaRen_le_sixp
#print axioms YMGap.Continuum.RenDefectQuadFactor.bondMovingDeltaRen_sixp_const
#print axioms YMGap.Continuum.RenDefectQuadFactor.bondMovingDeltaRen_le_sixp_invSq
