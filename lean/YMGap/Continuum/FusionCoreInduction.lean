/-
Track B / R2 — the `N`-INDUCTION of the heat-kernel box log-concavity core
`FusionConvLogConcaveCore`, with the degree-2 (`N = 2`) truncation inhabited and the
genuine inductive step `core N → core (N+1)` REDUCED to a single finite per-step
cross-term inequality `CoreStep N` (NOT the opaque local-CLT).

# What this module adds (honest scope, read first)

The sibling `SelfFusionLogConcave` proves the box-level core
`FusionConvLogConcaveCore N w` and inhabits it ONLY at `N = 1` (with a constructive
refutation of any unconditional `∀ s, w∈[0,1]` claim).  This module pushes that data:

  * THE `N = 2` CLOSED BOX SUMS (proved, symbolic `w`).  `boxSum2_zero … boxSum2_four`
    give the EXACT closed `Q'` values of the degree-2 box double sums in
    `c₁ = coeffW w 1`, `c₂ = coeffW w 2`; `boxSum2_tail` kills the modes `s ≥ 5`.

  * THE `s = 2` CHANNEL LOG-CONCAVITY (proved, symbolic).  `polyI2` is the pure-`Q'`
    inequality `((c₂+c₂)+(c₁²+c₂²))·c₂² ≤ (c₁c₂+c₁c₂)²` under strong coupling
    (`c₂ ≤ c₁²`, `c₁² ≤ 1`) — the genuine `s = 2` box log-concavity at `N = 2`.

  * THE `N = 2` CORE, INHABITED.  `core_N2_half` inhabits `FusionConvLogConcaveCore 2`
    UNCONDITIONALLY at the concrete strong-coupling value `w = 1/2` (every channel by a
    closed `Q'` computation; the `s ≥ 3` tail by `boxSum2_tail`), and
    `s1Dom_N2_half` wires it through to `S1Dominance 2 (1/2) 2`.  The symbolic
    strong-coupling family is reduced to exactly the two residual channel inequalities
    by `fusionConvLogConcaveCore_N2_of_channels` (the `s = 2` channel is already
    discharged by `polyI2`; only the `s = 0`/`s = 1` channels remain).

  * THE INDUCTIVE STEP (proved reduction).  `boxSum_succ_decomp` is the additive
    decomposition `boxSum (N+1) ≃ boxSum N + Δ`; `CoreStep N` is the single per-step
    CROSS-TERM inequality; and `fusionConvLogConcaveCore_succ_of_coreStep` PROVES
    `core N → CoreStep N → core (N+1)`.  So the general-`N` core is reduced to the
    UNIFORM-in-`N` residual `CoreStep` — a clean finite Casimir-controlled inequality,
    far sharper than the opaque `(r,d)` local-CLT.

# NAMED OPEN (honest)

  * The two `s = 0`/`s = 1` channel log-concavity inequalities at general symbolic `w`
    (`fusionConvLogConcaveCore_N2_of_channels`'s hypotheses `hI0`, `hI1`) — degree-8
    pure-`Q'` polynomial inequalities in `(c₁,c₂)`, the direct analogues of the proved
    `polyI2`.  They HOLD (witnessed unconditionally at `w = 1/2` by `core_N2_half`);
    only their symbolic-`w` proofs are deferred.
  * `CoreStep N` for general `N` — the uniform per-step cross-term inequality.

This is NOT a 4D Yang–Mills mass gap; it is the honest `N`-induction of one structural
box-level log-concavity core, with `N = 1, 2` inhabited and the inductive step reduced
to a single named finite inequality.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, the proved `fsum` algebra, and
`decide` only on closed concrete-rational / finite-index facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  Witnesses are `Type`-level.
-/

import YMGap.Continuum.SelfFusionLogConcave
import YMGap.Continuum.FusionLogConcave
import YMGap.Continuum.CubeRatioBounds

namespace YMGap.Continuum.FusionCoreInduction

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.CubeRatioBounds

/-! ## 0. Local algebra helpers -/

/-- `(a·b)·(a·b) ≃ (a·a)·(b·b)`. -/
private theorem prodsq (a b : Q') : ((a * b) * (a * b)).eqv ((a * a) * (b * b)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (a * b)) ?_
  have inner : (b * (a * b)).eqv (a * (b * b)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b a b)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (b * a) (a * b) b (Q'.mul_comm_eqv b a)) ?_
    exact Q'.mul_assoc_eqv a b b
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ inner) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a a (b * b))

/-- `1 · (1 · x) ≃ x`. -/
private theorem oo1 (x : Q') : ((1 : Q') * ((1 : Q') * x)).eqv x :=
  Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((1 : Q') * x)) (Q'.one_mul_eqv x)

/-- `1 · (x · 1) ≃ x`. -/
private theorem oo2 (x : Q') : ((1 : Q') * (x * (1 : Q'))).eqv x :=
  Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (x * (1 : Q'))) (Q'.mul_one_eqv x)

/-- `((x + 0) + 0) ≃ x`. -/
private theorem dropBC (x : Q') : (((x + (0 : Q')) + (0 : Q'))).eqv x :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (x + 0) x 0 (q_add_zero_eqv x)) (q_add_zero_eqv x)

/-- `((0 + x) + 0) ≃ x`. -/
private theorem dropAC (x : Q') : ((((0 : Q') + x) + (0 : Q'))).eqv x :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (0 + x) x 0 (q_zero_add_eqv x)) (q_add_zero_eqv x)

/-- `((0 + 0) + x) ≃ x`. -/
private theorem dropAB (x : Q') : ((((0 : Q') + (0 : Q')) + x)).eqv x :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (0 + 0) 0 x (q_zero_add_eqv 0)) (q_zero_add_eqv x)

/-- `((x + 0) + y) ≃ x + y`. -/
private theorem dropB_mid (x y : Q') : (((x + (0 : Q')) + y)).eqv (x + y) :=
  Q'.add_eqv_congr_right (x + 0) x y (q_add_zero_eqv x)

/-- **Generic 3-term row collapse.** -/
private theorem rowClean {A B C vA vB vC : Q'}
    (hA : A.eqv vA) (hB : B.eqv vB) (hC : C.eqv vC) :
    ((((0 : Q') + A) + B) + C).eqv ((vA + vB) + vC) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.add_eqv_congr_left 0 A vA hA) hB) hC)
    (Q'.add_eqv_congr_right ((0 + vA) + vB) (vA + vB) vC
      (Q'.add_eqv_congr_right (0 + vA) vA vB (q_zero_add_eqv vA)))

/-! ## 1. The degree-2 closed box sums (symbolic `w`) -/

/-- **`boxSum w 2 0 ≃ (1 + c₁·c₁) + c₂·c₂`.** -/
theorem boxSum2_zero (w : Q') :
    (boxSum w 2 0).eqv ((1 + coeffW w 1 * coeffW w 1) + coeffW w 2 * coeffW w 2) := by
  unfold boxSum
  simp only [fsum]
  have e00 : fusionInd 0 0 0 = (1 : Q') := by decide
  have e01 : fusionInd 0 1 0 = (0 : Q') := by decide
  have e02 : fusionInd 0 2 0 = (0 : Q') := by decide
  have e10 : fusionInd 1 0 0 = (0 : Q') := by decide
  have e11 : fusionInd 1 1 0 = (1 : Q') := by decide
  have e12 : fusionInd 1 2 0 = (0 : Q') := by decide
  have e20 : fusionInd 2 0 0 = (0 : Q') := by decide
  have e21 : fusionInd 2 1 0 = (0 : Q') := by decide
  have e22 : fusionInd 2 2 0 = (1 : Q') := by decide
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, coeffW_zero]
  refine Q'.eqv_trans _ _ _
    (rowClean
      (Q'.eqv_trans _ _ _ (rowClean (oo1 (1 : Q')) (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _))
        (dropBC (1 : Q')))
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.one_mul_eqv (coeffW w 1 * coeffW w 1))
          (Q'.zero_mul_eqv _))
        (dropAC (coeffW w 1 * coeffW w 1)))
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _)
          (Q'.one_mul_eqv (coeffW w 2 * coeffW w 2)))
        (dropAB (coeffW w 2 * coeffW w 2))))
    ?_
  exact Q'.eqv_refl _

/-- **`boxSum w 2 1 ≃ (c₁ + c₁) + (c₁·c₂ + c₁·c₂)`.** -/
theorem boxSum2_one (w : Q') :
    (boxSum w 2 1).eqv ((coeffW w 1 + coeffW w 1)
      + (coeffW w 1 * coeffW w 2 + coeffW w 1 * coeffW w 2)) := by
  unfold boxSum
  simp only [fsum]
  have e00 : fusionInd 0 0 1 = (0 : Q') := by decide
  have e01 : fusionInd 0 1 1 = (1 : Q') := by decide
  have e02 : fusionInd 0 2 1 = (0 : Q') := by decide
  have e10 : fusionInd 1 0 1 = (1 : Q') := by decide
  have e11 : fusionInd 1 1 1 = (0 : Q') := by decide
  have e12 : fusionInd 1 2 1 = (1 : Q') := by decide
  have e20 : fusionInd 2 0 1 = (0 : Q') := by decide
  have e21 : fusionInd 2 1 1 = (1 : Q') := by decide
  have e22 : fusionInd 2 2 1 = (0 : Q') := by decide
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, coeffW_zero]
  refine Q'.eqv_trans _ _ _
    (rowClean
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (oo1 (coeffW w 1)) (Q'.zero_mul_eqv _))
        (dropAC (coeffW w 1)))
      (Q'.eqv_trans _ _ _
        (rowClean (oo2 (coeffW w 1)) (Q'.zero_mul_eqv _)
          (Q'.one_mul_eqv (coeffW w 1 * coeffW w 2)))
        (dropB_mid (coeffW w 1) (coeffW w 1 * coeffW w 2)))
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.one_mul_eqv (coeffW w 2 * coeffW w 1))
          (Q'.zero_mul_eqv _))
        (dropAC (coeffW w 2 * coeffW w 1))))
    ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ (coeffW w 2 * coeffW w 1) (coeffW w 1 * coeffW w 2)
      (Q'.mul_comm_eqv (coeffW w 2) (coeffW w 1))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ ((coeffW w 1 + coeffW w 1) + coeffW w 1 * coeffW w 2)
      (coeffW w 1 * coeffW w 2)
      (Q'.eqv_symm
        (Q'.add_assoc_eqv (coeffW w 1) (coeffW w 1) (coeffW w 1 * coeffW w 2)))) ?_
  exact Q'.add_assoc_eqv (coeffW w 1 + coeffW w 1) (coeffW w 1 * coeffW w 2)
    (coeffW w 1 * coeffW w 2)

/-- **`boxSum w 2 2 ≃ (c₂ + c₂) + (c₁·c₁ + c₂·c₂)`.** -/
theorem boxSum2_two (w : Q') :
    (boxSum w 2 2).eqv ((coeffW w 2 + coeffW w 2)
      + (coeffW w 1 * coeffW w 1 + coeffW w 2 * coeffW w 2)) := by
  unfold boxSum
  simp only [fsum]
  have e00 : fusionInd 0 0 2 = (0 : Q') := by decide
  have e01 : fusionInd 0 1 2 = (0 : Q') := by decide
  have e02 : fusionInd 0 2 2 = (1 : Q') := by decide
  have e10 : fusionInd 1 0 2 = (0 : Q') := by decide
  have e11 : fusionInd 1 1 2 = (1 : Q') := by decide
  have e12 : fusionInd 1 2 2 = (0 : Q') := by decide
  have e20 : fusionInd 2 0 2 = (1 : Q') := by decide
  have e21 : fusionInd 2 1 2 = (0 : Q') := by decide
  have e22 : fusionInd 2 2 2 = (1 : Q') := by decide
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, coeffW_zero]
  refine Q'.eqv_trans _ _ _
    (rowClean
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _) (oo1 (coeffW w 2)))
        (dropAB (coeffW w 2)))
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.one_mul_eqv (coeffW w 1 * coeffW w 1))
          (Q'.zero_mul_eqv _))
        (dropAC (coeffW w 1 * coeffW w 1)))
      (Q'.eqv_trans _ _ _
        (rowClean (oo2 (coeffW w 2)) (Q'.zero_mul_eqv _)
          (Q'.one_mul_eqv (coeffW w 2 * coeffW w 2)))
        (dropB_mid (coeffW w 2) (coeffW w 2 * coeffW w 2))))
    ?_
  exact Q'.add_swap_inner (coeffW w 2) (coeffW w 1 * coeffW w 1) (coeffW w 2)
    (coeffW w 2 * coeffW w 2)

/-- **`boxSum w 2 3 ≃ c₁·c₂ + c₁·c₂`.** -/
theorem boxSum2_three (w : Q') :
    (boxSum w 2 3).eqv (coeffW w 1 * coeffW w 2 + coeffW w 1 * coeffW w 2) := by
  unfold boxSum
  simp only [fsum]
  have e00 : fusionInd 0 0 3 = (0 : Q') := by decide
  have e01 : fusionInd 0 1 3 = (0 : Q') := by decide
  have e02 : fusionInd 0 2 3 = (0 : Q') := by decide
  have e10 : fusionInd 1 0 3 = (0 : Q') := by decide
  have e11 : fusionInd 1 1 3 = (0 : Q') := by decide
  have e12 : fusionInd 1 2 3 = (1 : Q') := by decide
  have e20 : fusionInd 2 0 3 = (0 : Q') := by decide
  have e21 : fusionInd 2 1 3 = (1 : Q') := by decide
  have e22 : fusionInd 2 2 3 = (0 : Q') := by decide
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, coeffW_zero]
  refine Q'.eqv_trans _ _ _
    (rowClean
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _))
        (dropAB (0 : Q')))
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _)
          (Q'.one_mul_eqv (coeffW w 1 * coeffW w 2)))
        (dropAB (coeffW w 1 * coeffW w 2)))
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.one_mul_eqv (coeffW w 2 * coeffW w 1))
          (Q'.zero_mul_eqv _))
        (dropAC (coeffW w 2 * coeffW w 1))))
    ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ (coeffW w 1 * coeffW w 2) (coeffW w 2 * coeffW w 1)
      (q_zero_add_eqv (coeffW w 1 * coeffW w 2))) ?_
  exact Q'.add_eqv_congr_left (coeffW w 1 * coeffW w 2) (coeffW w 2 * coeffW w 1)
    (coeffW w 1 * coeffW w 2) (Q'.mul_comm_eqv (coeffW w 2) (coeffW w 1))

/-- **`boxSum w 2 4 ≃ c₂·c₂`.** -/
theorem boxSum2_four (w : Q') :
    (boxSum w 2 4).eqv (coeffW w 2 * coeffW w 2) := by
  unfold boxSum
  simp only [fsum]
  have e00 : fusionInd 0 0 4 = (0 : Q') := by decide
  have e01 : fusionInd 0 1 4 = (0 : Q') := by decide
  have e02 : fusionInd 0 2 4 = (0 : Q') := by decide
  have e10 : fusionInd 1 0 4 = (0 : Q') := by decide
  have e11 : fusionInd 1 1 4 = (0 : Q') := by decide
  have e12 : fusionInd 1 2 4 = (0 : Q') := by decide
  have e20 : fusionInd 2 0 4 = (0 : Q') := by decide
  have e21 : fusionInd 2 1 4 = (0 : Q') := by decide
  have e22 : fusionInd 2 2 4 = (1 : Q') := by decide
  rw [e00, e01, e02, e10, e11, e12, e20, e21, e22, coeffW_zero]
  refine Q'.eqv_trans _ _ _
    (rowClean
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _))
        (dropAB (0 : Q')))
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _))
        (dropAB (0 : Q')))
      (Q'.eqv_trans _ _ _
        (rowClean (Q'.zero_mul_eqv _) (Q'.zero_mul_eqv _)
          (Q'.one_mul_eqv (coeffW w 2 * coeffW w 2)))
        (dropAB (coeffW w 2 * coeffW w 2))))
    ?_
  exact dropAB (coeffW w 2 * coeffW w 2)

/-- **`boxSum w 2 (k+5) ≃ 0`** — no `(a,b)≤2` reaches mode `s = k+5` (`a+b ≤ 4`). -/
theorem boxSum2_tail (w : Q') (k : Nat) :
    (boxSum w 2 (k + 5)).eqv 0 := by
  unfold boxSum
  refine fsum_zero_below (2 + 1) (fun a ha => ?_)
  refine fsum_zero_below (2 + 1) (fun b hb => ?_)
  have hind : fusionInd a b (k + 5) = (0 : Q') := by
    unfold fusionInd
    have hok : fusionOK a b (k + 5) = false := by
      rw [fusionOK_eq_false_iff]
      rintro ⟨_, h2, _⟩
      omega
    rw [hok]; rfl
  rw [hind]; exact Q'.zero_mul_eqv _

/-! ## 2. The `s = 2` channel log-concavity (symbolic, strong coupling) -/

/-- **`polyI2` — the `s = 2` box log-concavity (PROVED).**  In `x = c₁`, `y = c₂`:
`((y+y)+(x²+y²))·y² ≤ (xy+xy)²` from `y ≤ x²` and `x² ≤ 1`.  (`B₂·B₄ ≤ B₃²`.) -/
theorem polyI2 (x y : Q') (hx0 : (0 : Q') ≤ x) (hy0 : (0 : Q') ≤ y)
    (hyx : y ≤ x * x) (hx1 : x * x ≤ (1 : Q')) :
    ((y + y) + (x * x + y * y)) * (y * y)
      ≤ (x * y + x * y) * (x * y + x * y) := by
  have hxxnn : (0 : Q') ≤ x * x := Q'.mul_nonneg _ _ hx0 hx0
  have hyynn : (0 : Q') ≤ y * y := Q'.mul_nonneg _ _ hy0 hy0
  have hyyxx : y * y ≤ x * x := by
    have a1 : y * y ≤ (x * x) * y := Q'.mul_le_mul_of_nonneg_right y (x * x) y hyx hy0
    have a2 : (x * x) * y ≤ (x * x) * (x * x) :=
      Q'.mul_le_mul_of_nonneg_left y (x * x) (x * x) hyx hxxnn
    have a3 : (x * x) * (x * x) ≤ (x * x) * 1 :=
      Q'.mul_le_mul_of_nonneg_left (x * x) 1 (x * x) hx1 hxxnn
    exact Q'.le_trans' _ _ _ a1 (Q'.le_trans' _ _ _ a2
      (Q'.le_trans' _ _ _ a3 (Q'.le_of_eqv (Q'.mul_one_eqv (x * x)))))
  have hB2D : (y + y) + (x * x + y * y) ≤ (x * x + x * x) + (x * x + x * x) :=
    Q'.add_le_add (Q'.add_le_add hyx hyx) (Q'.add_le_add (Q'.le_refl' (x * x)) hyyxx)
  have hstep : ((y + y) + (x * x + y * y)) * (y * y)
      ≤ ((x * x + x * x) + (x * x + x * x)) * (y * y) :=
    Q'.mul_le_mul_of_nonneg_right _ _ (y * y) hB2D hyynn
  have hDexp : (((x * x + x * x) + (x * x + x * x)) * (y * y)).eqv
      ((((x * x) * (y * y)) + ((x * x) * (y * y)))
        + (((x * x) * (y * y)) + ((x * x) * (y * y)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x * x + x * x) (x * x + x * x) (y * y))
      (Q'.add_eqv_congr' (Q'.add_mul_eqv (x * x) (x * x) (y * y))
        (Q'.add_mul_eqv (x * x) (x * x) (y * y)))
  have hhalf : ((x * y) * (x * y + x * y)).eqv
      (((x * x) * (y * y)) + ((x * x) * (y * y))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (x * y) (x * y) (x * y))
      (Q'.add_eqv_congr' (prodsq x y) (prodsq x y))
  have hRexp : ((x * y + x * y) * (x * y + x * y)).eqv
      ((((x * x) * (y * y)) + ((x * x) * (y * y)))
        + (((x * x) * (y * y)) + ((x * x) * (y * y)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (x * y) (x * y) (x * y + x * y))
      (Q'.add_eqv_congr' hhalf hhalf)
  exact Q'.le_trans' _ _ _ hstep
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hDexp) (Q'.ge_of_eqv hRexp))

/-! ## 3. Strong-coupling hypothesis discharge + box-sum positivity -/

/-- `c₂ ≤ c₁·c₁` (coeffW log-concavity at `s = 0`). -/
theorem coeffW2_le_sq {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    coeffW w 2 ≤ coeffW w 1 * coeffW w 1 := by
  have h := FusionResidualBound.coeffW_logConcave hw0 hw1 0
  rw [coeffW_zero] at h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW w 2))) h

/-- `c₁·c₁ ≤ 1` for `0 ≤ w ≤ 1/2`. -/
theorem coeffW1_sq_le_one {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw12 : w ≤ Q'.mkPos 1 2 (by decide)) :
    coeffW w 1 * coeffW w 1 ≤ (1 : Q') := by
  have hle : coeffW w 1 ≤ (1 : Q') := coeffW1_le_one_of_strong hw0 hw12
  have hnn : (0 : Q') ≤ coeffW w 1 := coeffW_nonneg hw0 1
  have s1 : coeffW w 1 * coeffW w 1 ≤ (1 : Q') * coeffW w 1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hle hnn
  have s2 : (1 : Q') * coeffW w 1 ≤ (1 : Q') * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hle (by decide)
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ s2 (by decide))

/-- The truncated box sum is nonnegative for `0 ≤ w`. -/
theorem boxSum_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N s : Nat) :
    (0 : Q') ≤ boxSum w N s := by
  unfold boxSum
  refine fsum_nonneg (fun a => ?_) (N + 1)
  refine fsum_nonneg (fun b => ?_) (N + 1)
  exact Q'.mul_nonneg _ _ (fusionInd_nonneg a b s)
    (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 a) (coeffW_nonneg hw0 b))

/-! ## 4. The `N = 2` core — concrete (`w = 1/2`) and symbolic (channel-reduced) -/

/-- The degenerate tail of `cauchyBinet` at `N = 2`: for `s = k+3`,
`boxSum w 2 (s+2) ≃ 0`, so the cross-product is `≤` any square. -/
private theorem cauchyBinet_tail {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    boxSum w 2 (k + 3) * boxSum w 2 (k + 3 + 2)
      ≤ boxSum w 2 (k + 3 + 1) * boxSum w 2 (k + 3 + 1) := by
  have hz : (boxSum w 2 (k + 3 + 2)).eqv 0 := boxSum2_tail w k
  have hLHS0 : (boxSum w 2 (k + 3) * boxSum w 2 (k + 3 + 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (q_mul_zero _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS0)
    (Q'.mul_nonneg _ _ (boxSum_nonneg hw0 2 (k + 3 + 1)) (boxSum_nonneg hw0 2 (k + 3 + 1)))

/-- **`core_N2_half` — the `N = 2` box-level core, inhabited UNCONDITIONALLY at the
concrete strong-coupling value `w = 1/2`.**  Every channel `s = 0,1,2` is a closed
`Q'` computation (`decide`); the modes `s ≥ 3` are degenerate (`boxSum2_tail`). -/
def core_N2_half :
    FusionConvLogConcaveCore 2 (Q'.mkPos 1 2 (by decide)) (by decide) (by decide) where
  strongCoupling := by decide
  cauchyBinet := by
    intro s
    match s with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | (k + 3) => exact cauchyBinet_tail (by decide) k

/-- The first-excited edge at `w = 1/2` (`decide`). -/
theorem edge_half :
    bondMovedCoeff 2 (Q'.mkPos 1 2 (by decide)) 2 2
      ≤ bondMovedCoeff 2 (Q'.mkPos 1 2 (by decide)) 2 1 := by decide

/-- **`s1Dom_N2_half` — `S1Dominance 2 (1/2) 2`, wired from `core_N2_half`.** -/
def s1Dom_N2_half :
    YMGap.Continuum.S1Dominance.S1Dominance 2 (Q'.mkPos 1 2 (by decide)) 2 :=
  YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2 (by decide) core_N2_half edge_half

/-- **`fusionConvLogConcaveCore_N2_of_channels` — the SYMBOLIC `N = 2` core, reduced to
the two residual channel inequalities.**  For `0 < w ≤ 1/2`, given the `s = 0` channel
inequality `hI0` (`B₀·B₂ ≤ B₁²`) and the `s = 1` channel inequality `hI1`
(`B₁·B₃ ≤ B₂²`) in closed box-value form, the box-level core holds at `N = 2`: the
`s = 2` channel is discharged by `polyI2`, the strong-coupling hypotheses by
`coeffW2_le_sq`/`coeffW1_sq_le_one`, and the tail by `boxSum2_tail`. -/
def fusionConvLogConcaveCore_N2_of_channels {w : Q'} (hw : (0 : Q') < w)
    (hw12 : w ≤ Q'.mkPos 1 2 (by decide))
    (hI0 : ((1 + coeffW w 1 * coeffW w 1) + coeffW w 2 * coeffW w 2)
        * ((coeffW w 2 + coeffW w 2) + (coeffW w 1 * coeffW w 1 + coeffW w 2 * coeffW w 2))
      ≤ ((coeffW w 1 + coeffW w 1) + (coeffW w 1 * coeffW w 2 + coeffW w 1 * coeffW w 2))
        * ((coeffW w 1 + coeffW w 1) + (coeffW w 1 * coeffW w 2 + coeffW w 1 * coeffW w 2)))
    (hI1 : ((coeffW w 1 + coeffW w 1) + (coeffW w 1 * coeffW w 2 + coeffW w 1 * coeffW w 2))
        * (coeffW w 1 * coeffW w 2 + coeffW w 1 * coeffW w 2)
      ≤ ((coeffW w 2 + coeffW w 2) + (coeffW w 1 * coeffW w 1 + coeffW w 2 * coeffW w 2))
        * ((coeffW w 2 + coeffW w 2) + (coeffW w 1 * coeffW w 1 + coeffW w 2 * coeffW w 2))) :
    FusionConvLogConcaveCore 2 w (Q'.le_of_lt hw)
      (Q'.le_trans' w (Q'.mkPos 1 2 (by decide)) 1 hw12 (by decide)) where
  strongCoupling :=
    Q'.le_trans' _ _ _ (coeffW1_sq_le_one (Q'.le_of_lt hw) hw12) (by decide)
  cauchyBinet := by
    have hw0 : (0 : Q') ≤ w := Q'.le_of_lt hw
    have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw12 (by decide)
    have hc1nn : (0 : Q') ≤ coeffW w 1 := coeffW_nonneg hw0 1
    have hc2nn : (0 : Q') ≤ coeffW w 2 := coeffW_nonneg hw0 2
    have hyx : coeffW w 2 ≤ coeffW w 1 * coeffW w 1 := coeffW2_le_sq hw0 hw1
    have hx1 : coeffW w 1 * coeffW w 1 ≤ (1 : Q') := coeffW1_sq_le_one hw0 hw12
    intro s
    match s with
    | 0 =>
      show boxSum w 2 0 * boxSum w 2 2 ≤ boxSum w 2 1 * boxSum w 2 1
      have hL : (boxSum w 2 0 * boxSum w 2 2).eqv _ :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (boxSum2_zero w))
          (Q'.mul_eqv_congr_left _ _ _ (boxSum2_two w))
      have hR : (boxSum w 2 1 * boxSum w 2 1).eqv _ :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (boxSum2_one w))
          (Q'.mul_eqv_congr_left _ _ _ (boxSum2_one w))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.le_trans' _ _ _ hI0 (Q'.ge_of_eqv hR))
    | 1 =>
      show boxSum w 2 1 * boxSum w 2 3 ≤ boxSum w 2 2 * boxSum w 2 2
      have hL : (boxSum w 2 1 * boxSum w 2 3).eqv _ :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (boxSum2_one w))
          (Q'.mul_eqv_congr_left _ _ _ (boxSum2_three w))
      have hR : (boxSum w 2 2 * boxSum w 2 2).eqv _ :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (boxSum2_two w))
          (Q'.mul_eqv_congr_left _ _ _ (boxSum2_two w))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.le_trans' _ _ _ hI1 (Q'.ge_of_eqv hR))
    | 2 =>
      show boxSum w 2 2 * boxSum w 2 4 ≤ boxSum w 2 3 * boxSum w 2 3
      have hL : (boxSum w 2 2 * boxSum w 2 4).eqv _ :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (boxSum2_two w))
          (Q'.mul_eqv_congr_left _ _ _ (boxSum2_four w))
      have hR : (boxSum w 2 3 * boxSum w 2 3).eqv _ :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (boxSum2_three w))
          (Q'.mul_eqv_congr_left _ _ _ (boxSum2_three w))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
        (Q'.le_trans' _ _ _ (polyI2 (coeffW w 1) (coeffW w 2) hc1nn hc2nn hyx hx1)
          (Q'.ge_of_eqv hR))
    | (k + 3) => exact cauchyBinet_tail hw0 k

/-! ## 5. The `N`-induction: additive decomposition + the per-step `CoreStep` -/

/-- The new top-mode contribution to `boxSum` when the truncation grows `N → N+1`. -/
def boxSumDelta (w : Q') (N s : Nat) : Q' :=
  fsum (fun a => fusionInd a (N + 1) s * (coeffW w a * coeffW w (N + 1))) (N + 1)
    + (fsum (fun b => fusionInd (N + 1) b s * (coeffW w (N + 1) * coeffW w b)) (N + 1)
       + fusionInd (N + 1) (N + 1) s * (coeffW w (N + 1) * coeffW w (N + 1)))

/-- **Additive decomposition** `boxSum w (N+1) s ≃ boxSum w N s + boxSumDelta w N s`. -/
theorem boxSum_succ_decomp (w : Q') (N s : Nat) :
    (boxSum w (N + 1) s).eqv (boxSum w N s + boxSumDelta w N s) := by
  unfold boxSum boxSumDelta
  have key :
      fsum (fun a => fsum (fun b => fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1 + 1))
          (N + 1 + 1)
        = fsum (fun a =>
              fsum (fun b => fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)
              + fusionInd a (N + 1) s * (coeffW w a * coeffW w (N + 1))) (N + 1)
          + (fsum (fun b => fusionInd (N + 1) b s * (coeffW w (N + 1) * coeffW w b)) (N + 1)
             + fusionInd (N + 1) (N + 1) s * (coeffW w (N + 1) * coeffW w (N + 1))) := rfl
  rw [key]
  have hadd :
      (fsum (fun a =>
          fsum (fun b => fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)
          + fusionInd a (N + 1) s * (coeffW w a * coeffW w (N + 1))) (N + 1)).eqv
        (fsum (fun a => fsum (fun b => fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)
          + fsum (fun a => fusionInd a (N + 1) s * (coeffW w a * coeffW w (N + 1))) (N + 1)) :=
    fsum_add (fun a => fsum (fun b => fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1))
      (fun a => fusionInd a (N + 1) s * (coeffW w a * coeffW w (N + 1))) (N + 1)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hadd) ?_
  exact Q'.add_assoc_eqv _ _ _

/-- `boxSumDelta ≥ 0` for `0 ≤ w`. -/
theorem boxSumDelta_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (N s : Nat) :
    (0 : Q') ≤ boxSumDelta w N s := by
  unfold boxSumDelta
  refine Q'.zero_le_add _ _ ?_ (Q'.zero_le_add _ _ ?_ ?_)
  · refine fsum_nonneg (fun a => ?_) (N + 1)
    exact Q'.mul_nonneg _ _ (fusionInd_nonneg _ _ _)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw _) (coeffW_nonneg hw _))
  · refine fsum_nonneg (fun b => ?_) (N + 1)
    exact Q'.mul_nonneg _ _ (fusionInd_nonneg _ _ _)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw _) (coeffW_nonneg hw _))
  · exact Q'.mul_nonneg _ _ (fusionInd_nonneg _ _ _)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw _) (coeffW_nonneg hw _))

/-- **The per-step CROSS-TERM obligation** (the sharp uniform-in-`N` residual).
With `A=boxSum N s`, `B=boxSum N (s+1)`, `C=boxSum N (s+2)`, `a=Δ s`, `b=Δ (s+1)`,
`c=Δ (s+2)`, the step needs `A·c + (a·C + a·c) ≤ (B·b + B·b) + b·b`. -/
structure CoreStep (N : Nat) (w : Q') : Type where
  step : ∀ s,
    boxSum w N s * boxSumDelta w N (s + 2)
        + (boxSumDelta w N s * boxSum w N (s + 2)
           + boxSumDelta w N s * boxSumDelta w N (s + 2))
      ≤ (boxSum w N (s + 1) * boxSumDelta w N (s + 1)
         + boxSum w N (s + 1) * boxSumDelta w N (s + 1))
        + boxSumDelta w N (s + 1) * boxSumDelta w N (s + 1)

/-- `(A+a)·(C+c) ≃ A·C + (A·c + (a·C + a·c))`. -/
private theorem prod_split (A a C c : Q') :
    ((A + a) * (C + c)).eqv (A * C + (A * c + (a * C + a * c))) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv A a (C + c)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_add_eqv A C c) (Q'.mul_add_eqv a C c)) ?_
  exact Q'.add_assoc_eqv (A * C) (A * c) (a * C + a * c)

/-- `(B+b)·(B+b) ≃ B·B + ((B·b + B·b) + b·b)`. -/
private theorem sq_split (B b : Q') :
    ((B + b) * (B + b)).eqv (B * B + ((B * b + B * b) + b * b)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv B b (B + b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_add_eqv B B b) (Q'.mul_add_eqv b B b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ (b * b) (Q'.mul_comm_eqv b B))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (B * B) (B * b) (B * b + b * b)) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv (B * b) (B * b) (b * b))

/-- **THE INDUCTIVE STEP (PROVED reduction).**  `core N → CoreStep N → core (N+1)`.
The additive decomposition turns level-`(N+1)` `cauchyBinet` `(A+a)(C+c) ≤ (B+b)²`
into `A·C + cross ≤ B·B + cross'`; level-`N` gives `A·C ≤ B·B` and `CoreStep` gives
`cross ≤ cross'`. -/
def fusionConvLogConcaveCore_succ_of_coreStep {N : Nat} {w : Q'}
    {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (core : FusionConvLogConcaveCore N w hw0 hw1) (cs : CoreStep N w) :
    FusionConvLogConcaveCore (N + 1) w hw0 hw1 where
  strongCoupling := core.strongCoupling
  cauchyBinet := fun s => by
    have hLs : (boxSum w (N + 1) s).eqv (boxSum w N s + boxSumDelta w N s) :=
      boxSum_succ_decomp w N s
    have hLs2 : (boxSum w (N + 1) (s + 2)).eqv
        (boxSum w N (s + 2) + boxSumDelta w N (s + 2)) := boxSum_succ_decomp w N (s + 2)
    have hLs1 : (boxSum w (N + 1) (s + 1)).eqv
        (boxSum w N (s + 1) + boxSumDelta w N (s + 1)) := boxSum_succ_decomp w N (s + 1)
    have hL : (boxSum w (N + 1) s * boxSum w (N + 1) (s + 2)).eqv
        ((boxSum w N s + boxSumDelta w N s) * (boxSum w N (s + 2) + boxSumDelta w N (s + 2))) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hLs)
        (Q'.mul_eqv_congr_left _ _ _ hLs2)
    have hR : (boxSum w (N + 1) (s + 1) * boxSum w (N + 1) (s + 1)).eqv
        ((boxSum w N (s + 1) + boxSumDelta w N (s + 1))
          * (boxSum w N (s + 1) + boxSumDelta w N (s + 1))) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hLs1)
        (Q'.mul_eqv_congr_left _ _ _ hLs1)
    have hAC : boxSum w N s * boxSum w N (s + 2)
        ≤ boxSum w N (s + 1) * boxSum w N (s + 1) := core.cauchyBinet s
    have hcs : boxSum w N s * boxSumDelta w N (s + 2)
          + (boxSumDelta w N s * boxSum w N (s + 2)
             + boxSumDelta w N s * boxSumDelta w N (s + 2))
        ≤ (boxSum w N (s + 1) * boxSumDelta w N (s + 1)
           + boxSum w N (s + 1) * boxSumDelta w N (s + 1))
          + boxSumDelta w N (s + 1) * boxSumDelta w N (s + 1) := cs.step s
    have hmid : boxSum w N s * boxSum w N (s + 2)
          + (boxSum w N s * boxSumDelta w N (s + 2)
             + (boxSumDelta w N s * boxSum w N (s + 2)
                + boxSumDelta w N s * boxSumDelta w N (s + 2)))
        ≤ boxSum w N (s + 1) * boxSum w N (s + 1)
          + ((boxSum w N (s + 1) * boxSumDelta w N (s + 1)
              + boxSum w N (s + 1) * boxSumDelta w N (s + 1))
             + boxSumDelta w N (s + 1) * boxSumDelta w N (s + 1)) := Q'.add_le_add hAC hcs
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (prod_split (boxSum w N s) (boxSumDelta w N s)
        (boxSum w N (s + 2)) (boxSumDelta w N (s + 2)))) ?_
    refine Q'.le_trans' _ _ _ hmid ?_
    refine Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (sq_split (boxSum w N (s + 1)) (boxSumDelta w N (s + 1)))) ?_
    exact Q'.ge_of_eqv hR

/-! ## 6. Doc-section — PROVED vs NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `boxSum2_zero … boxSum2_four`, `boxSum2_tail` — the closed `N = 2` box sums.
  * `polyI2` — the `s = 2` channel box log-concavity (symbolic, strong coupling).
  * `coeffW2_le_sq`, `coeffW1_sq_le_one`, `boxSum_nonneg` — the strong-coupling
    discharge and box-sum positivity.
  * `core_N2_half`, `edge_half`, `s1Dom_N2_half` — the `N = 2` core INHABITED
    unconditionally at `w = 1/2`, and wired to `S1Dominance 2 (1/2) 2`.
  * `fusionConvLogConcaveCore_N2_of_channels` — the SYMBOLIC strong-coupling `N = 2`
    core reduced to exactly the two residual channel inequalities (`s = 2` discharged
    by `polyI2`).
  * `boxSum_succ_decomp`, `boxSumDelta_nonneg`, `CoreStep`,
    `fusionConvLogConcaveCore_succ_of_coreStep` — the additive decomposition and the
    PROVED inductive step `core N → CoreStep N → core (N+1)`.

NAMED OPEN:
  * The symbolic `s = 0`/`s = 1` channel inequalities (`hI0`, `hI1`) — degree-8
    pure-`Q'` inequalities in `(c₁,c₂)`, the analogues of the proved `polyI2`; they
    HOLD (witnessed at `w = 1/2` by `core_N2_half`), only their symbolic proofs deferred.
  * `CoreStep N` for general `N` — the uniform per-step cross-term inequality, the
    sharp residual to which the whole `N`-induction is reduced.

HONEST VERDICT.  The box core is now inhabited at `N = 2` (unconditionally at `w = 1/2`,
and symbolically modulo two named channel inequalities), and the general-`N` induction
is reduced — with a PROVED inductive step — to the single uniform finite inequality
`CoreStep`.  This is a structural advance on one box-level log-concavity sub-fact; it is
NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreInduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreInduction.boxSum2_zero
#print axioms YMGap.Continuum.FusionCoreInduction.boxSum2_one
#print axioms YMGap.Continuum.FusionCoreInduction.boxSum2_two
#print axioms YMGap.Continuum.FusionCoreInduction.boxSum2_three
#print axioms YMGap.Continuum.FusionCoreInduction.boxSum2_four
#print axioms YMGap.Continuum.FusionCoreInduction.boxSum2_tail
#print axioms YMGap.Continuum.FusionCoreInduction.polyI2
#print axioms YMGap.Continuum.FusionCoreInduction.coeffW2_le_sq
#print axioms YMGap.Continuum.FusionCoreInduction.coeffW1_sq_le_one
#print axioms YMGap.Continuum.FusionCoreInduction.boxSum_nonneg
#print axioms YMGap.Continuum.FusionCoreInduction.core_N2_half
#print axioms YMGap.Continuum.FusionCoreInduction.s1Dom_N2_half
#print axioms YMGap.Continuum.FusionCoreInduction.fusionConvLogConcaveCore_N2_of_channels
#print axioms YMGap.Continuum.FusionCoreInduction.boxSum_succ_decomp
#print axioms YMGap.Continuum.FusionCoreInduction.boxSumDelta_nonneg
#print axioms YMGap.Continuum.FusionCoreInduction.fusionConvLogConcaveCore_succ_of_coreStep
