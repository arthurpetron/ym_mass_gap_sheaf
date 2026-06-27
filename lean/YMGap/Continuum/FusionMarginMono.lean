/-
Track B / R2 — DISCHARGING the single named residual `FusionMarginTailMonotone`
of `NormExcitedDrift`, making the dominant-mode `RGCoeffStep` floor UNCONDITIONAL
within its inherited scope.

# What this module proves — and the honest scope (read first)

The companion module assembled a CONCRETE dominant-mode `RGCoeffStep` whose
`physMargin k = 1 − E_k/Z'_k` is the GENUINE fusion-derived, vacuum-normalized gap
margin (real `fusionProduct`/`divPos`), and reduced its single open field
`normExcitedDrift` to ONE crisp obligation:

    FusionMarginTailMonotone : ∀ k, physMargin k ≤ physMargin (k+1),

the tail monotonicity of that genuine margin.  THIS module DISCHARGES that
obligation: `fusionMarginTailMonotone : FusionMarginTailMonotone` is a FULL
inhabitant (no further residual), and hence
`dominantMode_continuum_floor_unconditional` is the now-UNCONDITIONAL dominant-mode
continuum floor on the genuine fusion margin.

# The math (constructive, no calculus)

With `c = c₁ k = coeffW (wSeq k) 1 = 2·(wSeq k)³`, the genuine margin is
`physMargin k = 1 − E_k/Z'_k` with `E_k ≃ c + c` and `Z'_k ≃ 1 + c·c`, so it equals
the rational map `g(c) = (1 − c)²/(1 + c²)`.  This `g` is INCREASING for `c ≥ 1`,
equivalently the normalized excited coefficient `nE(c) = 2c/(1 + c²)` is DECREASING
for `c ≥ 1`.  The constructive engine is the single-product difference identity

    c·(1 + c'²) − c'·(1 + c²)  =  (c' − c)·(c·c' − 1)          (`diff_identity`)

whose RHS is a product of two NONNEGATIVE factors when `1 ≤ c ≤ c'`
(`c' − c ≥ 0`, `c·c' − 1 ≥ 0`), so the numerator difference is `≥ 0`, i.e.
`c'·(1 + c²) ≤ c·(1 + c'²)` (`crossNum_le`).  Cross-multiplying through the two
positive denominators `Z'` (the `divPos` cross-monotonicity `divPos_le_divPos_of_cross`)
turns this into `nE(c') ≤ nE(c)` (`normalizedExcited_antitone`), hence
`physMargin k ≤ physMargin (k+1)` (`fusionMarginTailMonotone`).

The three monotone inputs along the canonical AF trajectory are PROVED here:
`wSeq` is increasing (`wSeq_mono`, from `invSucc` antitone), `c₁ = 2w³` is increasing
(`c1_mono`, the genuine cube-monotonicity `coeffW_one_mono`), and `1 ≤ c₁ k` on the
whole tail (`c1_ge_one`, from the decide-checked anchor `1 ≤ c₁ 0` plus monotonicity).

# Honest scope caveat (do NOT overclaim a physical gap)

Closing this residual makes the dominant-mode floor UNCONDITIONAL, BUT the closure is
via TAIL monotonicity PAST the `c₁ = 1` crossing: it floors only the weak-coupling
tail and SIDESTEPS the intermediate-coupling region (`w ≈ 0.794`, where `c₁ = 1`) at
which the genuine margin dips to ZERO (the companion module's structural finding).
So this does NOT resolve the physical-gap identification across the whole RG flow.
The genuine open obstruction remains: the intermediate-coupling "middle", the `N = 1`
truncation (only the `s = 1` fusion separator is kept), the full-mode (all `s`) margin,
and the genuine 4D AF trajectory.  This module does NOT prove 4D Yang–Mills.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`divPos` arithmetic + the proved fusion/cube-monotonicity machinery;
`decide` only on the concrete-index anchor `1 ≤ c₁ 0` (concrete rationals).  Every
symbolic-`k` fact is a real proof, NOT `decide`.  All load-bearing declarations are
gated below; permitted output is `propext` / `Quot.sound` only.
-/

import YMGap.Continuum.NormExcitedDrift
import YMGap.Continuum.UniformCouplingGap

namespace YMGap.Continuum.FusionMarginMono

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.NormExcitedDrift
open YMGap.Continuum.DominantModeRecursion
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingGap

/-! ## 0. The single-product difference identity (the algebraic crux)

`c·(1 + c'·c') − c'·(1 + c·c)  ≃  (c' − c)·(c·c' − 1)`.  A fixed bivariate polynomial
identity, proved by chaining the `Q'` distributive/commutative `eqv`-lemmas (the
variables `c, c'` are abstract, so no decision procedure is used). -/
theorem diff_identity (c c' : Q') :
    ((c * (1 + c' * c') + -(c' * (1 + c * c)))).eqv
      ((c' + (-c)) * (c * c' + (-1))) := by
  -- monomial reconciliations: c·(c'·c') ≃ c'·(c·c') and c'·(c·c) ≃ c·(c·c')
  have hM1 : (c * (c' * c')).eqv (c' * (c * c')) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c c' c')) ?_
    exact Q'.mul_comm_eqv (c * c') c'
  have hM2 : (c' * (c * c)).eqv (c * (c * c')) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv c' (c * c)) ?_
    exact Q'.mul_assoc_eqv c c c'
  -- LHS ≃ (c + c'·(c·c')) + ((-c') + -(c·(c·c')))
  have hL : ((c * (1 + c' * c') + -(c' * (1 + c * c)))).eqv
      ((c + c' * (c * c')) + ((-c') + -(c * (c * c')))) := by
    have hLa : (c * (1 + c' * c')).eqv (c + c' * (c * c')) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c 1 (c' * c'))
        (q_add_congr (Q'.mul_one_eqv c) hM1)
    have hLb : (-(c' * (1 + c * c))).eqv ((-c') + -(c * (c * c'))) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv c' 1 (c * c))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (c' * 1) (c' * (c * c))) ?_
      exact q_add_congr (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv c'))
        (Q'.neg_eqv_congr _ _ hM2)
    exact q_add_congr hLa hLb
  -- RHS ≃ (c'·(c·c') + (-c')) + (-(c·(c·c')) + c)
  have hR : ((c' + (-c)) * (c * c' + (-1))).eqv
      ((c' * (c * c') + (-c')) + (-(c * (c * c')) + c)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv c' (-c) (c * c' + (-1))) ?_
    refine q_add_congr ?_ ?_
    · refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c' (c * c') (-1)) ?_
      refine q_add_congr (Q'.eqv_refl _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv c' 1) ?_
      exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv c')
    · refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-c) (c * c') (-1)) ?_
      refine q_add_congr ?_ ?_
      · exact Q'.neg_mul_eqv c (c * c')
      · refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (-c) 1) ?_
        refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (-c))) ?_
        exact Q'.neg_neg_eqv c
  -- reconcile the two canonical sums by interchange/commutativity
  refine Q'.eqv_trans _ _ _ hL ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR)
  refine Q'.eqv_trans _ _ _ (q_interchange c (c' * (c * c')) (-c') (-(c * (c * c')))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (c + -c') (c' * (c * c') + -(c * (c * c')))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ (c + -c') (-c' + c) (Q'.add_comm_eqv c (-c'))) ?_
  exact q_interchange (c' * (c * c')) (-(c * (c * c'))) (-c') c

/-! ## 1. The numerator inequality `c'·(1 + c²) ≤ c·(1 + c'²)` for `1 ≤ c ≤ c'`

From `diff_identity`, the difference equals `(c' − c)·(c·c' − 1)`, a product of two
nonnegative factors. -/

/-- For `1 ≤ c ≤ c'`, `c'·(1 + c·c) ≤ c·(1 + c'·c')`.  The difference equals
`(c' − c)·(c·c' − 1) ≥ 0` (`diff_identity` + `mul_nonneg`). -/
theorem crossNum_le {c c' : Q'} (hc : (1 : Q') ≤ c) (hcc' : c ≤ c') :
    c' * (1 + c * c) ≤ c * (1 + c' * c') := by
  -- 0 ≤ c' − c
  have hsub1 : (0 : Q') ≤ c' + (-c) := by
    have := Q'.add_le_add_right c c' (-c) hcc'
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv c)) this
  -- 0 ≤ c·c' − 1.  First 1 ≤ c·c' (from 1 = 1·1 ≤ c·c').
  have hc0 : (0 : Q') ≤ c := Q'.le_trans' _ _ _ (by decide : (0:Q') ≤ (1:Q')) hc
  have hc'0 : (0 : Q') ≤ c' := Q'.le_trans' _ _ _ hc0 hcc'
  have h1cc' : (1 : Q') ≤ c * c' := by
    -- 1 = 1·1 ≤ c·1 ≤ c·c'
    have ha : (1 : Q') * 1 ≤ c * 1 := Q'.mul_le_mul_of_nonneg_right _ _ _ hc (by decide)
    have hb : c * 1 ≤ c * c' :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_trans' _ _ _ hc hcc') hc0
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ ha hb)
    exact Q'.ge_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv 1))
  have hsub2 : (0 : Q') ≤ c * c' + (-1) := by
    have := Q'.add_le_add_right 1 (c * c') (-1) h1cc'
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv 1)) this
  -- product ≥ 0
  have hprod : (0 : Q') ≤ (c' + (-c)) * (c * c' + (-1)) :=
    Q'.mul_nonneg _ _ hsub1 hsub2
  -- transport through diff_identity: 0 ≤ c·(1+c'²) − c'·(1+c²)
  have hdiff : (0 : Q') ≤ c * (1 + c' * c') + -(c' * (1 + c * c)) :=
    Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv (diff_identity c c'))
  exact Q'.le_of_sub_nonneg hdiff

/-! ## 2. The `divPos` cross-monotonicity (`p·q' ≤ p'·q → p/q ≤ p'/q'`) -/

/-- If `p·q' ≤ p'·q` (cross-multiplication) with `q, q' > 0`, then
`divPos p q ≤ divPos p' q'`.  Multiply the cross inequality by `1/q' ≥ 0` and collapse
`p·q'·(1/q') ≃ p`, `p'·q·(1/q') ≃ (p'/q')·q`, then apply `divPos_le_of_le_mul`. -/
theorem divPos_le_divPos_of_cross (p q p' q' : Q')
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q') (hcross : p * q' ≤ p' * q) :
    Q'.divPos p q hq ≤ Q'.divPos p' q' hq' := by
  refine Q'.divPos_le_of_le_mul p q hq ?_
  have hr : (0 : Q') ≤ Q'.recipPos q' hq' := Q'.le_of_lt (Q'.recipPos_pos q' hq')
  have hstep : (p * q') * Q'.recipPos q' hq' ≤ (p' * q) * Q'.recipPos q' hq' :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcross hr
  have hLe : ((p * q') * Q'.recipPos q' hq').eqv p := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p q' (Q'.recipPos q' hq')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p _ _ (Q'.mul_recipPos_eqv q' hq')) ?_
    exact Q'.mul_one_eqv p
  have hRe : ((p' * q) * Q'.recipPos q' hq').eqv (Q'.divPos p' q' hq' * q) := by
    show ((p' * q) * Q'.recipPos q' hq').eqv ((p' * Q'.recipPos q' hq') * q)
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p' q (Q'.recipPos q' hq')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p' _ _ (Q'.mul_comm_eqv q (Q'.recipPos q' hq'))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv p' (Q'.recipPos q' hq') q)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLe)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hRe))

/-! ## 3. The trajectory monotonicity inputs (proved, not assumed)

`wSeq` increasing, `c₁ = 2w³` increasing, `1 ≤ c₁ k` on the whole tail. -/

/-- The trajectory weight is monotone non-decreasing in the index: `wSeq j ≤ wSeq k`
for `j ≤ k`.  `wSeq k = 1 − invSucc (cutoff + k)`, and `invSucc` is antitone
(`ExpNeg.invSucc_le_of_le`). -/
theorem wSeq_mono {j k : Nat} (h : j ≤ k) : wSeq j ≤ wSeq k := by
  show afr.w (cutoff + j) ≤ afr.w (cutoff + k)
  show (1 - Q'.invSucc (cutoff + j)) ≤ (1 - Q'.invSucc (cutoff + k))
  show (1 + -Q'.invSucc (cutoff + j)) ≤ (1 + -Q'.invSucc (cutoff + k))
  refine Q'.add_le_add_left _ _ _ ?_
  exact Q'.neg_le_neg (ExpNeg.invSucc_le_of_le (by omega : cutoff + j ≤ cutoff + k))

/-- The anchor `1 ≤ c₁ 0 = coeffW (wSeq 0) 1`.  At the concrete cutoff index this is
a concrete rational (`c₁ ≈ 1.96 > 1`); `decide`-checked. -/
theorem c1_0_ge_one : (1 : Q') ≤ coeffW (wSeq 0) 1 := by
  show (1 : Q') ≤ coeffW (afr.w (cutoff + 0)) 1
  unfold afr cutoff pMult
  decide

/-- `1 ≤ c₁ k` for ALL tail scales `k` (symbolic).  From the anchor `1 ≤ c₁ 0` and
the cube-monotonicity `coeffW_one_mono` applied to `wSeq 0 ≤ wSeq k`. -/
theorem c1_ge_one (k : Nat) : (1 : Q') ≤ coeffW (wSeq k) 1 :=
  Q'.le_trans' _ _ _ c1_0_ge_one
    (coeffW_one_mono (wSeq_nonneg 0) (wSeq_mono (Nat.zero_le k)))

/-- `c₁ k ≤ c₁ (k+1)`: the leading coefficient `c₁ = 2w³` is increasing in the index
(genuine cube-monotonicity `coeffW_one_mono` along the increasing weight). -/
theorem c1_mono (k : Nat) : coeffW (wSeq k) 1 ≤ coeffW (wSeq (k + 1)) 1 :=
  coeffW_one_mono (wSeq_nonneg k) (wSeq_mono (Nat.le_succ k))

/-! ## 4. The doubled cross inequality and `normalizedExcited` antitone -/

/-- `(c'+c')·(1 + c·c) ≤ (c+c)·(1 + c'·c')` from the single `crossNum_le` by doubling
both sides (`(x+x) = x + x`, then `add_le_add` chained). -/
theorem crossNum_doubled {c c' : Q'} (hc : (1 : Q') ≤ c) (hcc' : c ≤ c') :
    (c' + c') * (1 + c * c) ≤ (c + c) * (1 + c' * c') := by
  have hbase : c' * (1 + c * c) ≤ c * (1 + c' * c') := crossNum_le hc hcc'
  -- (c'+c')·Z = c'·Z + c'·Z, (c+c)·Z' = c·Z' + c·Z'
  have hLe : ((c' + c') * (1 + c * c)).eqv (c' * (1 + c * c) + c' * (1 + c * c)) :=
    Q'.add_mul_eqv c' c' (1 + c * c)
  have hRe : ((c + c) * (1 + c' * c')).eqv (c * (1 + c' * c') + c * (1 + c' * c')) :=
    Q'.add_mul_eqv c c (1 + c' * c')
  -- c'·Z + c'·Z ≤ c·Z' + c'·Z ≤ c·Z' + c·Z'
  have hstep1 : c' * (1 + c * c) + c' * (1 + c * c)
      ≤ c * (1 + c' * c') + c' * (1 + c * c) :=
    Q'.add_le_add_right _ _ _ hbase
  have hstep2 : c * (1 + c' * c') + c' * (1 + c * c)
      ≤ c * (1 + c' * c') + c * (1 + c' * c') :=
    Q'.add_le_add_left _ _ _ hbase
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLe) ?_
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hstep1 hstep2) (Q'.ge_of_eqv hRe)

/-- **The normalized excited coefficient is antitone on the tail:**
`normalizedExcited (k+1) ≤ normalizedExcited k`.  Via the `divPos` cross-monotonicity
fed by the doubled numerator inequality, transported through the fusion `eqv`-forms
`E_j ≃ c_j + c_j`, `Z'_j ≃ 1 + c_j·c_j`. -/
theorem normalizedExcited_antitone (k : Nat) :
    normalizedExcited (k + 1) ≤ normalizedExcited k := by
  -- abbreviations (local `let`s, not `set`, to stay in the Mathlib-free tactic set):
  --   c = c₁ k, c' = c₁ (k+1)
  -- the cross inequality at the genuine fusion quantities:
  --   E_{k+1} · Z'_k ≤ E_k · Z'_{k+1}
  have hcross :
      fusionProduct 1 (coeffW (wSeq (k + 1))) (coeffW (wSeq (k + 1))) 1 * ZprimeSeq k
        ≤ fusionProduct 1 (coeffW (wSeq k)) (coeffW (wSeq k)) 1 * ZprimeSeq (k + 1) := by
    -- transport the doubled numeric inequality through the eqv-forms.
    -- E_{k+1} ≃ c'+c', Z'_k ≃ 1+c·c, E_k ≃ c+c, Z'_{k+1} ≃ 1+c'·c'.
    have hE' : (fusionProduct 1 (coeffW (wSeq (k + 1))) (coeffW (wSeq (k + 1))) 1).eqv
        (coeffW (wSeq (k + 1)) 1 + coeffW (wSeq (k + 1)) 1) := fusionExcited_eqv (wSeq (k + 1))
    have hZk : (ZprimeSeq k).eqv (1 + coeffW (wSeq k) 1 * coeffW (wSeq k) 1) :=
      fusionTrivial_eqv (wSeq k)
    have hE : (fusionProduct 1 (coeffW (wSeq k)) (coeffW (wSeq k)) 1).eqv
        (coeffW (wSeq k) 1 + coeffW (wSeq k) 1) := fusionExcited_eqv (wSeq k)
    have hZk' : (ZprimeSeq (k + 1)).eqv
        (1 + coeffW (wSeq (k + 1)) 1 * coeffW (wSeq (k + 1)) 1) :=
      fusionTrivial_eqv (wSeq (k + 1))
    -- LHS ≃ (c'+c')·(1+c·c), RHS ≃ (c+c)·(1+c'·c')
    have hLeqv :
        (fusionProduct 1 (coeffW (wSeq (k + 1))) (coeffW (wSeq (k + 1))) 1
            * ZprimeSeq k).eqv
          ((coeffW (wSeq (k + 1)) 1 + coeffW (wSeq (k + 1)) 1)
            * (1 + coeffW (wSeq k) 1 * coeffW (wSeq k) 1)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hE')
        (Q'.mul_eqv_congr_left _ _ _ hZk)
    have hReqv :
        (fusionProduct 1 (coeffW (wSeq k)) (coeffW (wSeq k)) 1
            * ZprimeSeq (k + 1)).eqv
          ((coeffW (wSeq k) 1 + coeffW (wSeq k) 1)
            * (1 + coeffW (wSeq (k + 1)) 1 * coeffW (wSeq (k + 1)) 1)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hE)
        (Q'.mul_eqv_congr_left _ _ _ hZk')
    -- numeric inequality (1 ≤ c, c ≤ c')
    have hnum :
        (coeffW (wSeq (k + 1)) 1 + coeffW (wSeq (k + 1)) 1)
            * (1 + coeffW (wSeq k) 1 * coeffW (wSeq k) 1)
          ≤ (coeffW (wSeq k) 1 + coeffW (wSeq k) 1)
            * (1 + coeffW (wSeq (k + 1)) 1 * coeffW (wSeq (k + 1)) 1) :=
      crossNum_doubled (c1_ge_one k) (c1_mono k)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeqv)
      (Q'.le_trans' _ _ _ hnum (Q'.ge_of_eqv hReqv))
  -- feed into the divPos cross-monotonicity (denominators Z'_k, Z'_{k+1} > 0)
  exact divPos_le_divPos_of_cross
    (fusionProduct 1 (coeffW (wSeq (k + 1))) (coeffW (wSeq (k + 1))) 1) (ZprimeSeq (k + 1))
    (fusionProduct 1 (coeffW (wSeq k)) (coeffW (wSeq k)) 1) (ZprimeSeq k)
    (ZprimeSeq_pos (k + 1)) (ZprimeSeq_pos k) hcross

/-! ## 5. THE RESIDUAL, DISCHARGED — `physMargin` is tail-monotone -/

/-- **`physMargin k ≤ physMargin (k+1)`** (the residual's content).  Since
`physMargin = 1 − normalizedExcited` and `normalizedExcited` is antitone on the tail,
the margin is monotone non-decreasing. -/
theorem physMargin_mono (k : Nat) : physMargin k ≤ physMargin (k + 1) := by
  -- 1 − nE(k) ≤ 1 − nE(k+1)  ⟸  nE(k+1) ≤ nE(k)
  show (1 : Q') - normalizedExcited k ≤ 1 - normalizedExcited (k + 1)
  show (1 : Q') + -(normalizedExcited k) ≤ 1 + -(normalizedExcited (k + 1))
  refine Q'.add_le_add_left _ _ _ ?_
  exact Q'.neg_le_neg (normalizedExcited_antitone k)

/-- **THE RESIDUAL, DISCHARGED.**  `FusionMarginTailMonotone` is FULLY inhabited:
the genuine fusion-derived gap margin is monotone non-decreasing on the tail. -/
def fusionMarginTailMonotone : FusionMarginTailMonotone where
  mono := physMargin_mono

/-! ## 6. The now-UNCONDITIONAL dominant-mode continuum floor -/

/-- **THE UNCONDITIONAL DOMINANT-MODE CONTINUUM FLOOR.**  Feeding the discharged
residual `fusionMarginTailMonotone` into the companion module's assembled
`RGCoeffStep`, the genuine fusion-derived margin has a uniform positive floor at every
tail scale — with NO remaining residual hypothesis (within the inherited `N = 1`,
tail-only scope; see the scope caveat at the top of this module). -/
theorem dominantMode_continuum_floor_unconditional :
    (0 : Q') < (dominantRGCoeffStep fusionMarginTailMonotone).prodFloor
      ∧ ∀ k : Nat,
          (dominantRGCoeffStep fusionMarginTailMonotone).prodFloor
            ≤ (dominantRGCoeffStep fusionMarginTailMonotone).physMargin k :=
  dominantMode_continuum_floor fusionMarginTailMonotone

/-- The genuine fusion margin is strictly positive at every tail scale —
UNCONDITIONALLY (the residual is discharged). -/
theorem dominantMode_physMargin_pos_unconditional (k : Nat) :
    (0 : Q') < (dominantRGCoeffStep fusionMarginTailMonotone).physMargin k :=
  dominantMode_physMargin_pos fusionMarginTailMonotone k

end YMGap.Continuum.FusionMarginMono

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionMarginMono.diff_identity
#print axioms YMGap.Continuum.FusionMarginMono.crossNum_le
#print axioms YMGap.Continuum.FusionMarginMono.divPos_le_divPos_of_cross
#print axioms YMGap.Continuum.FusionMarginMono.wSeq_mono
#print axioms YMGap.Continuum.FusionMarginMono.c1_0_ge_one
#print axioms YMGap.Continuum.FusionMarginMono.c1_ge_one
#print axioms YMGap.Continuum.FusionMarginMono.c1_mono
#print axioms YMGap.Continuum.FusionMarginMono.crossNum_doubled
#print axioms YMGap.Continuum.FusionMarginMono.normalizedExcited_antitone
#print axioms YMGap.Continuum.FusionMarginMono.physMargin_mono
#print axioms YMGap.Continuum.FusionMarginMono.fusionMarginTailMonotone
#print axioms YMGap.Continuum.FusionMarginMono.dominantMode_continuum_floor_unconditional
#print axioms YMGap.Continuum.FusionMarginMono.dominantMode_physMargin_pos_unconditional
