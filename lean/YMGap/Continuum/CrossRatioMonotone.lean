/-
Track A / R2 (track: 1-crossratio) — the GENERIC two-value total-positivity engine that
discharges the entire `w ↔ wH` cross-multiplication of a `A(w)·M(wH) ≤ A(wH)·M(w)` monotone-ratio
statement, collapsing it to ONE coefficient-array MLR / TP₂ condition.

# What this module adds (all axiom-clean)

The residual `FiniteSMarginWorstcase.CrossRatioMonotone w` asks, per mode, for the cross-multiplied
increasing-ratio inequality `A_s(w)·M_s(wH) ≤ A_s(wH)·M_s(w)` on `0 ≤ w ≤ wH`, where `A_s`, `M_s`
are honest nonneg-coefficient polynomials in `w`.  Put on a common exponent grid
`A(x) = Σ_j a_j x^{e_j}`, `M(x) = Σ_k m_k x^{e_k}` with `a_j, m_k ≥ 0`, the exact
antisymmetrization identity is

    A(w)·M(wH) − A(wH)·M(w)
      = ½ · Σ_{j,k} (a_j m_k − a_k m_j)·(w^{e_j}wH^{e_k} − wH^{e_j}w^{e_k}),

and for `0 ≤ w ≤ wH` each symmetrized pair term has a definite sign controlled by ONE monotone-
likelihood-ratio (MLR / TP₂) condition on the coefficient arrays:

    (MLR)   e_k < e_j  ⟹  a_k · m_j ≤ a_j · m_k.

This module PROVES that generic engine.

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `qpow_cross_le` — the per-pair mixed-monomial lemma: for `q ≤ p` and `0 ≤ w ≤ wH`,
        w^p · wH^q ≤ w^q · wH^p
    (factor the common `w^q·wH^q ≥ 0`, reduce to `w^{p−q} ≤ wH^{p−q}` = `qpow_mono`).
  * `crossPair_core` — the pure `Q'` two-value antisymmetrization identity: the symmetrized pair
    `crT(j,k) + crT(k,j)` equals `(a_j m_k − a_k m_j)·(wH^{e_j}w^{e_k} − w^{e_j}wH^{e_k})`
    (the two-value analog of the Andréief `swap_core`).
  * `crossTerm_nonneg` — each symmetrized pair is `≥ 0` under (MLR), by trichotomy on `e_j`,`e_k`
    (`qpow_cross_le` supplies the monomial sign; MLR the coefficient sign).
  * `crossTP2` — THE ENGINE.  `fsum_mul_fsum` opens both products, `fsum_swap` antisymmetrizes,
    each pair is `≥ 0`, the factor-2 cancels: the whole `w ↔ wH` cross-multiplication follows
    from (MLR) alone (no per-coefficient positivity is even needed).

# The honest wall

`crossTP2` (+`qpow_cross_le`) discharges the entire two-parameter `w/wH` cross-multiplication and
leaves exactly the coefficient-array MLR / TP₂ inequality `(MLR)`, packaged as the `Type`-level
`ArrayMLR`.  For the actual `A_s = acN(s+1,s)·acN(s+1,s+2)` (antidiagonal split) versus
`M_s = acN(s+1,s+1)²` (diagonal split) arrays this is "convolution preserves TP₂/log-concavity"
for the windowed theta weight — the same uniform-in-`s` theta / local-CLT wall already named
`WindowedGaussianEnvelope` / `WHAllSMargin`.  The proved per-mode atom `coeffW_superLogConcave_wsq`
supplies each MLR *step*; the uniform array closure remains NAMED-OPEN (never `sorry`).  So this is
the correctly-located reduction of `CrossRatioMonotone`, not an escape from the wall.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `fsum`/`qpow` finite-sum + power algebra, `Nat.lt_trichotomy`
on exponents, and `omega` on one index identity.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.AutoconvGershgorin
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.FiniteSMarginWorstcase

namespace YMGap.Continuum.CrossRatioMonotone

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundF
open YMGap.Continuum.AutoconvGershgorin

/-! ## 0. Small sign helper -/

/-- **`flip_nonneg`** — from `x ≤ y` conclude `0 ≤ −(x + −y)` (i.e. `x + −y ≤ 0`).
`0 ≤ y + −x` (`sub_nonneg_of_le`) and `−(x + −y) ≃ y + −x` (`neg_defect_comm`). -/
private theorem flip_nonneg {x y : Q'} (h : x ≤ y) : (0 : Q') ≤ -(x + -y) :=
  Q'.le_trans' 0 (y + -x) (-(x + -y)) (Q'.sub_nonneg_of_le h)
    (Q'.le_of_eqv (Q'.eqv_symm (neg_defect_comm x y)))

/-! ## 1. The per-pair mixed-monomial lemma (Statement 2) -/

/-- **`qpow_cross_le`** — the sharp mixed-monomial inequality.  For `0 ≤ w ≤ wH` and `q ≤ p`,

    w^p · wH^q ≤ w^q · wH^p.

`w^p ≃ w^q·w^{p−q}`, `wH^p ≃ wH^q·wH^{p−q}` (`qpow_add`); factor the common nonnegative
`w^q·wH^q` and reduce to `w^{p−q} ≤ wH^{p−q}` (`qpow_mono`). -/
theorem qpow_cross_le {w wH : Q'} (hw0 : (0 : Q') ≤ w) (hwle : w ≤ wH) {p q : Nat} (hpq : q ≤ p) :
    qpow w p * qpow wH q ≤ qpow w q * qpow wH p := by
  have hwH : (0 : Q') ≤ wH := Q'.le_trans' 0 w wH hw0 hwle
  have hd : q + (p - q) = p := by omega
  have e1 : (qpow w p).eqv (qpow w q * qpow w (p - q)) := by
    have h := qpow_add w q (p - q); rw [hd] at h; exact h
  have e2 : (qpow wH p).eqv (qpow wH q * qpow wH (p - q)) := by
    have h := qpow_add wH q (p - q); rw [hd] at h; exact h
  have hL : (qpow w p * qpow wH q).eqv ((qpow w q * qpow wH q) * qpow w (p - q)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (qpow wH q) e1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (qpow w q) (qpow w (p - q)) (qpow wH q)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (qpow w q) _ _ (Q'.mul_comm_eqv (qpow w (p - q)) (qpow wH q))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (qpow w q) (qpow wH q) (qpow w (p - q)))
  have hR : (qpow w q * qpow wH p).eqv ((qpow w q * qpow wH q) * qpow wH (p - q)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (qpow w q) _ _ e2) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (qpow w q) (qpow wH q) (qpow wH (p - q)))
  have hC : (0 : Q') ≤ qpow w q * qpow wH q :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 q) (qpow_nonneg wH hwH q)
  have hmono : qpow w (p - q) ≤ qpow wH (p - q) := qpow_mono hw0 hwle (p - q)
  have hprod : (qpow w q * qpow wH q) * qpow w (p - q)
      ≤ (qpow w q * qpow wH q) * qpow wH (p - q) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmono hC
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv hR))

/-! ## 2. The two-value antisymmetrization identity -/

/-- **`crossPair_core`** — the pure `Q'` two-value Andréief identity (the two-value analog of
`swap_core`): the symmetrized pair

    ((aj·wHj)·(mk·wk) − (aj·wj)·(mk·wHk)) + ((ak·wHk)·(mj·wj) − (ak·wk)·(mj·wHj))

equals `(aj·mk − ak·mj)·(wHj·wk − wj·wHk)`.  Pure distributivity (`mul_swap4`, `mul_add`/`add_mul`,
the neg combinators) after re-associating each monomial to `(coeff)·(monomial)`. -/
theorem crossPair_core (aj ak mj mk wj wHj wk wHk : Q') :
    ((((aj * wHj) * (mk * wk)) + -((aj * wj) * (mk * wHk)))
      + (((ak * wHk) * (mj * wj)) + -((ak * wk) * (mj * wHj)))).eqv
      (((aj * mk) + -(ak * mj)) * ((wHj * wk) + -(wj * wHk))) := by
  have h1 : ((aj * wHj) * (mk * wk)).eqv ((aj * mk) * (wHj * wk)) := mul_swap4 aj wHj mk wk
  have h2 : (-((aj * wj) * (mk * wHk))).eqv (-((aj * mk) * (wj * wHk))) :=
    Q'.neg_eqv_congr _ _ (mul_swap4 aj wj mk wHk)
  have h3 : ((ak * wHk) * (mj * wj)).eqv ((ak * mj) * (wj * wHk)) :=
    Q'.eqv_trans _ _ _ (mul_swap4 ak wHk mj wj)
      (Q'.mul_eqv_congr_left (ak * mj) (wHk * wj) (wj * wHk) (Q'.mul_comm_eqv wHk wj))
  have h4 : (-((ak * wk) * (mj * wHj))).eqv (-((ak * mj) * (wHj * wk))) :=
    Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _ _ _ (mul_swap4 ak wk mj wHj)
        (Q'.mul_eqv_congr_left (ak * mj) (wk * wHj) (wHj * wk) (Q'.mul_comm_eqv wk wHj)))
  have hLHS :
      ((((aj * wHj) * (mk * wk)) + -((aj * wj) * (mk * wHk)))
        + (((ak * wHk) * (mj * wj)) + -((ak * wk) * (mj * wHj)))).eqv
        ((((aj * mk) * (wHj * wk)) + -((aj * mk) * (wj * wHk)))
          + (((ak * mj) * (wj * wHk)) + -((ak * mj) * (wHj * wk)))) :=
    Q'.add_eqv_congr' (Q'.add_eqv_congr' h1 h2) (Q'.add_eqv_congr' h3 h4)
  have hSwapPair :
      ((((aj * mk) * (wHj * wk)) + -((aj * mk) * (wj * wHk)))
          + (((ak * mj) * (wj * wHk)) + -((ak * mj) * (wHj * wk)))).eqv
        ((((aj * mk) * (wHj * wk)) + -((aj * mk) * (wj * wHk)))
          + (-((ak * mj) * (wHj * wk)) + ((ak * mj) * (wj * wHk)))) :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.add_comm_eqv ((ak * mj) * (wj * wHk)) (-((ak * mj) * (wHj * wk))))
  have hRHS :
      (((aj * mk) + -(ak * mj)) * ((wHj * wk) + -(wj * wHk))).eqv
        ((((aj * mk) * (wHj * wk)) + -((aj * mk) * (wj * wHk)))
          + (-((ak * mj) * (wHj * wk)) + ((ak * mj) * (wj * wHk)))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (aj * mk) (-(ak * mj)) ((wHj * wk) + -(wj * wHk))) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (aj * mk) (wHj * wk) (-(wj * wHk))) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (aj * mk) (wj * wHk))
    · refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (-(ak * mj)) (wHj * wk) (-(wj * wHk))) ?_
      exact Q'.add_eqv_congr'
        (Q'.neg_mul_eqv (ak * mj) (wHj * wk))
        (neg_mul_neg_eqv (ak * mj) (wj * wHk))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ hLHS hSwapPair) (Q'.eqv_symm hRHS)

/-! ## 3. The per-pair sign lemma (the MLR consumer) -/

/-- **`crossTerm_nonneg`** — the symmetrized pair coefficient/monomial product is `≥ 0`.  For
sequences `a, m ≥ 0`-free (positivity NOT needed) but with (MLR)
`e_k < e_j ⟹ a_k·m_j ≤ a_j·m_k`, on `0 ≤ w ≤ wH`,

    0 ≤ (a_j·m_k − a_k·m_j)·(wH^{e_j}·w^{e_k} − w^{e_j}·wH^{e_k}).

By trichotomy on `e_j`, `e_k`: `qpow_cross_le` fixes the monomial factor's sign and MLR the
coefficient factor's sign, so both factors share sign in each branch (and the middle branch is a
`0` monomial factor). -/
theorem crossTerm_nonneg {a m : Nat → Q'} {e : Nat → Nat} {w wH : Q'}
    (hw0 : (0 : Q') ≤ w) (hwle : w ≤ wH)
    (hMLR : ∀ j k, e k < e j → a k * m j ≤ a j * m k) (j k : Nat) :
    (0 : Q') ≤ (a j * m k + -(a k * m j))
      * (qpow wH (e j) * qpow w (e k) + -(qpow w (e j) * qpow wH (e k))) := by
  rcases Nat.lt_trichotomy (e j) (e k) with hlt | heq | hgt
  · -- e j < e k : both factors ≤ 0, product ≥ 0
    have h1 : a j * m k ≤ a k * m j := hMLR k j hlt
    have hnegG1 : (0 : Q') ≤ -(a j * m k + -(a k * m j)) := flip_nonneg h1
    have hcross := qpow_cross_le hw0 hwle (Nat.le_of_lt hlt)
    have hXY : qpow wH (e j) * qpow w (e k) ≤ qpow w (e j) * qpow wH (e k) :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_comm_eqv (qpow wH (e j)) (qpow w (e k)))) hcross
    have hnegG2 : (0 : Q') ≤ -(qpow wH (e j) * qpow w (e k) + -(qpow w (e j) * qpow wH (e k))) :=
      flip_nonneg hXY
    have hprod : (0 : Q') ≤ (-(a j * m k + -(a k * m j)))
        * (-(qpow wH (e j) * qpow w (e k) + -(qpow w (e j) * qpow wH (e k)))) :=
      Q'.mul_nonneg _ _ hnegG1 hnegG2
    exact Q'.le_trans' _ _ _ hprod
      (Q'.le_of_eqv (neg_mul_neg_eqv (a j * m k + -(a k * m j))
        (qpow wH (e j) * qpow w (e k) + -(qpow w (e j) * qpow wH (e k)))))
  · -- e j = e k : the monomial factor ≃ 0
    have hcomm : (qpow wH (e j) * qpow w (e k)).eqv (qpow w (e j) * qpow wH (e k)) := by
      rw [heq]
      exact Q'.mul_comm_eqv (qpow wH (e k)) (qpow w (e k))
    have hG2 : (qpow wH (e j) * qpow w (e k) + -(qpow w (e j) * qpow wH (e k))).eqv 0 := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hcomm) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv (qpow w (e j) * qpow wH (e k)) (-(qpow w (e j) * qpow wH (e k)))) ?_
      exact Q'.neg_add_self_eqv (qpow w (e j) * qpow wH (e k))
    have hzero : ((a j * m k + -(a k * m j))
        * (qpow wH (e j) * qpow w (e k) + -(qpow w (e j) * qpow wH (e k)))).eqv 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hG2) (q_mul_zero (a j * m k + -(a k * m j)))
    exact Q'.ge_of_eqv hzero
  · -- e k < e j : both factors ≥ 0, product ≥ 0
    have h1 : a k * m j ≤ a j * m k := hMLR j k hgt
    have hposG1 : (0 : Q') ≤ a j * m k + -(a k * m j) := Q'.sub_nonneg_of_le h1
    have hcross := qpow_cross_le hw0 hwle (Nat.le_of_lt hgt)
    have hYX : qpow w (e j) * qpow wH (e k) ≤ qpow wH (e j) * qpow w (e k) :=
      Q'.le_trans' _ _ _ hcross
        (Q'.le_of_eqv (Q'.mul_comm_eqv (qpow w (e k)) (qpow wH (e j))))
    have hposG2 : (0 : Q') ≤ qpow wH (e j) * qpow w (e k) + -(qpow w (e j) * qpow wH (e k)) :=
      Q'.sub_nonneg_of_le hYX
    exact Q'.mul_nonneg _ _ hposG1 hposG2

/-! ## 4. The generic engine `crossTP2` (Statement 1) -/

/-- **`crossTP2` — THE ENGINE.**  For nonnegative coefficient arrays `a, m` on a common exponent
grid `e`, on `0 ≤ w ≤ wH`, the (MLR) condition `e_k < e_j ⟹ a_k·m_j ≤ a_j·m_k` implies the
cross-multiplied increasing-ratio inequality

    (Σ_j a_j w^{e_j})·(Σ_k m_k wH^{e_k}) ≤ (Σ_j a_j wH^{e_j})·(Σ_k m_k w^{e_k}).

`fsum_mul_fsum` opens both products into a double sum, `fsum_swap` antisymmetrizes `(j,k)↔(k,j)`,
`crossPair_core` turns each symmetrized pair into a coefficient·monomial product, `crossTerm_nonneg`
signs it under (MLR), and the factor-2 cancels (`ofNat_two_mul_eqv` + `le_of_mul_le_mul_left_pos`).
Notably the per-coefficient positivity `ha`/`hm` is not even used — the antisymmetrization needs
only (MLR). -/
theorem crossTP2 {a m : Nat → Q'} {e : Nat → Nat} {w wH : Q'} (L : Nat)
    (ha : ∀ j, (0 : Q') ≤ a j) (hm : ∀ k, (0 : Q') ≤ m k)
    (hw0 : (0 : Q') ≤ w) (hwle : w ≤ wH)
    (hMLR : ∀ j k, e k < e j → a k * m j ≤ a j * m k) :
    (fsum (fun j => a j * qpow w (e j)) L) * (fsum (fun k => m k * qpow wH (e k)) L)
      ≤ (fsum (fun j => a j * qpow wH (e j)) L) * (fsum (fun k => m k * qpow w (e k)) L) := by
  have hCD := fsum_mul_fsum (fun i => a i * qpow wH (e i)) (fun j => m j * qpow w (e j)) L L
  have hAB := fsum_mul_fsum (fun i => a i * qpow w (e i)) (fun j => m j * qpow wH (e j)) L L
  -- hDsum : D ≃ Σ_i Σ_j crT i j
  have hDsum :
      ((fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
        + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L)).eqv
        (fsum (fun i => fsum (fun j =>
          (a i * qpow wH (e i)) * (m j * qpow w (e j))
            + -((a i * qpow w (e i)) * (m j * qpow wH (e j)))) L) L) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hCD (Q'.neg_eqv_congr _ _ hAB)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (q2_neg (fun i j => (a i * qpow w (e i)) * (m j * qpow wH (e j))) L)) ?_
    exact q2_add (fun i j => (a i * qpow wH (e i)) * (m j * qpow w (e j)))
      (fun i j => -((a i * qpow w (e i)) * (m j * qpow wH (e j)))) L
  -- hDsum' : D ≃ Σ_i Σ_j crT j i (index swap)
  have hDsum' :
      ((fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
        + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L)).eqv
        (fsum (fun j => fsum (fun i =>
          (a i * qpow wH (e i)) * (m j * qpow w (e j))
            + -((a i * qpow w (e i)) * (m j * qpow wH (e j)))) L) L) :=
    Q'.eqv_trans _ _ _ hDsum
      (fsum_swap (fun i j =>
        (a i * qpow wH (e i)) * (m j * qpow w (e j))
          + -((a i * qpow w (e i)) * (m j * qpow wH (e j)))) L L)
  -- hDDsum : D + D ≃ Σ_i Σ_j (crT i j + crT j i)
  have hDDsum :
      (((fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
          + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L))
        + ((fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
          + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L))).eqv
        (fsum (fun i => fsum (fun j =>
          ((a i * qpow wH (e i)) * (m j * qpow w (e j))
            + -((a i * qpow w (e i)) * (m j * qpow wH (e j))))
          + ((a j * qpow wH (e j)) * (m i * qpow w (e i))
            + -((a j * qpow w (e j)) * (m i * qpow wH (e i))))) L) L) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hDsum hDsum')
      (q2_add
        (fun i j => (a i * qpow wH (e i)) * (m j * qpow w (e j))
          + -((a i * qpow w (e i)) * (m j * qpow wH (e j))))
        (fun i j => (a j * qpow wH (e j)) * (m i * qpow w (e i))
          + -((a j * qpow w (e j)) * (m i * qpow wH (e i)))) L)
  -- each symmetrized pair ≥ 0
  have hpair : ∀ i j, (0 : Q') ≤
      ((a i * qpow wH (e i)) * (m j * qpow w (e j))
        + -((a i * qpow w (e i)) * (m j * qpow wH (e j))))
      + ((a j * qpow wH (e j)) * (m i * qpow w (e i))
        + -((a j * qpow w (e j)) * (m i * qpow wH (e i)))) := by
    intro i j
    refine Q'.le_trans' _ _ _ (crossTerm_nonneg hw0 hwle hMLR i j) ?_
    exact Q'.ge_of_eqv
      (crossPair_core (a i) (a j) (m i) (m j)
        (qpow w (e i)) (qpow wH (e i)) (qpow w (e j)) (qpow wH (e j)))
  have hSumNN : (0 : Q') ≤ fsum (fun i => fsum (fun j =>
      ((a i * qpow wH (e i)) * (m j * qpow w (e j))
        + -((a i * qpow w (e i)) * (m j * qpow wH (e j))))
      + ((a j * qpow wH (e j)) * (m i * qpow w (e i))
        + -((a j * qpow w (e j)) * (m i * qpow wH (e i))))) L) L :=
    fsum_nonneg (fun i => fsum_nonneg (fun j => hpair i j) L) L
  -- 0 ≤ D + D
  have hDDnn : (0 : Q') ≤
      ((fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
          + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L))
        + ((fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
          + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L)) :=
    Q'.le_trans' _ _ _ hSumNN (Q'.ge_of_eqv hDDsum)
  -- halve: 0 ≤ D
  have hDnn : (0 : Q') ≤
      (fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
        + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L) := by
    have h2D : (0 : Q') ≤ Q'.ofNat 2 *
        ((fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
          + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L)) :=
      Q'.le_trans' _ _ _ hDDnn (Q'.le_of_eqv (Q'.eqv_symm (ofNat_two_mul_eqv _)))
    have h20 : Q'.ofNat 2 * (0 : Q') ≤ Q'.ofNat 2 *
        ((fsum (fun j => a j * qpow wH (e j)) L * fsum (fun k => m k * qpow w (e k)) L)
          + -(fsum (fun j => a j * qpow w (e j)) L * fsum (fun k => m k * qpow wH (e k)) L)) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (q_mul_zero (Q'.ofNat 2))) h2D
    exact le_of_mul_le_mul_left_pos (show (0 : Q') < Q'.ofNat 2 by decide) h20
  exact Q'.le_of_sub_nonneg hDnn

/-! ## 5. The named residual and its consumer -/

/-- **`ArrayMLR` — THE SOLE NAMED RESIDUAL.**  The coefficient-array monotone-likelihood-ratio /
TP₂ condition: the coefficient ratio `a_•/m_•` is monotone in the exponent, i.e.

    (MLR)   e_k < e_j  ⟹  a_k · m_j ≤ a_j · m_k.

For the actual `A_s`/`M_s` arrays (antidiagonal split dominated by the diagonal split in the
TP₂ sense) this is "convolution preserves TP₂/log-concavity" for the windowed theta weight — the
uniform-in-`s` theta / local-CLT wall.  NAMED-OPEN (never `sorry`): this module does NOT inhabit it
for the actual arrays. -/
structure ArrayMLR (a m : Nat → Q') (e : Nat → Nat) : Type where
  /-- The monotone-likelihood-ratio inequality on the coefficient arrays. -/
  mlr : ∀ j k, e k < e j → a k * m j ≤ a j * m k

/-- **`crossTP2_of_arrayMLR` — the reduction.**  An `ArrayMLR` witness discharges the entire
`w ↔ wH` cross-multiplication of the monotone-ratio statement (this is `crossTP2` fed the packaged
residual). -/
theorem crossTP2_of_arrayMLR {a m : Nat → Q'} {e : Nat → Nat} {w wH : Q'} (L : Nat)
    (ha : ∀ j, (0 : Q') ≤ a j) (hm : ∀ k, (0 : Q') ≤ m k)
    (hw0 : (0 : Q') ≤ w) (hwle : w ≤ wH) (H : ArrayMLR a m e) :
    (fsum (fun j => a j * qpow w (e j)) L) * (fsum (fun k => m k * qpow wH (e k)) L)
      ≤ (fsum (fun j => a j * qpow wH (e j)) L) * (fsum (fun k => m k * qpow w (e k)) L) :=
  crossTP2 L ha hm hw0 hwle H.mlr

/-! ## 6. PROVED vs. NAMED-open (honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `qpow_cross_le` — the per-pair mixed-monomial inequality.
  * `crossPair_core` — the pure `Q'` two-value antisymmetrization identity.
  * `crossTerm_nonneg` — each symmetrized pair is `≥ 0` under (MLR).
  * `crossTP2` / `crossTP2_of_arrayMLR` — the generic engine discharging the full `w ↔ wH`
    cross-multiplication, reducing it to (MLR).

NAMED OPEN (Type-level structure, never `sorry`):
  * `ArrayMLR` — the coefficient-array MLR / TP₂ inequality.  For the actual antidiagonal-vs-diagonal
    `A_s`/`M_s` arrays this is the uniform-in-`s` theta / local-CLT wall (`WindowedGaussianEnvelope`
    / `WHAllSMargin`).  The per-mode step is the proved `coeffW_superLogConcave_wsq`; the uniform
    array closure remains open.

HONEST VERDICT.  `crossTP2` collapses the two-parameter `w/wH` cross-multiplication of
`CrossRatioMonotone` to the single named coefficient-array TP₂ residual `ArrayMLR`, mirroring how
`cancel3` discharges the scalar margin.  It is the correctly-located reduction of the residual, not
an escape from the wall; it does NOT prove the uniform array closure, and it is NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.CrossRatioMonotone

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CrossRatioMonotone.qpow_cross_le
#print axioms YMGap.Continuum.CrossRatioMonotone.crossPair_core
#print axioms YMGap.Continuum.CrossRatioMonotone.crossTerm_nonneg
#print axioms YMGap.Continuum.CrossRatioMonotone.crossTP2
#print axioms YMGap.Continuum.CrossRatioMonotone.crossTP2_of_arrayMLR
