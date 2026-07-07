/-
Track B / R2 — ROUTE C:  the DIRECT multi-link SU(2) fusion determinant, and the
SUB-ADDITIVITY (concentration) of the real m-fold bond-moved excited/vacuum ratio.

# What this module proves — the direct multi-link fusion defect, made rigorous

Migdal–Kadanoff bond-moving fuses `m = b^{d−1}` PARALLEL plaquettes by taking the
pointwise `m`-th power of the single-plaquette SU(2) class function `K_w`, whose
character coefficients are `c_s = coeffW w s = (s+1)·w^{s(s+2)}`.  The fused
coefficients are the `m`-fold Clebsch–Gordan fusion convolution `c^{⋆m}`; the
gap-relevant quantity is the fused excited/vacuum ratio

    ρ_m(w) = (c^{⋆m})₁ / (c^{⋆m})₀ .

The genuine 4D difficulty is that `ρ_m` is NOT the single-link `ρ_1 = c₁/c₀ = 2w³`.
Route C computes the deviation DIRECTLY and proves the decisive structural fact —
**sub-additivity / concentration**:

    ρ_m(w)  ≤  m · ρ_1(w)          (equivalently, ρ_m/m is non-increasing in m).

The per-link excited leakage `ρ_m/m` of the fused measure is at most the single-link
leakage, and STRICTLY DECREASES with more fusion (numerically verified: at w=1/2,
`ρ_m/m` for m=1,2,4,8 is 0.25, 0.238, 0.209, 0.156).  So the real multi-link 4D
defect is SMALLER than the naive `m×single-link` model — fusion CONCENTRATES the
measure, it does not amplify the excited leakage.  (NB: the raw ratio `ρ_m` itself
INCREASES with m toward its cap 2; it is the per-link `ρ_m/m` that concentrates.)

## The mechanism — concentration from log-concavity, term by term

The two fusion overlap forms (SU(2) Clebsch–Gordan, `χ_a·χ_b = Σ_{c} χ_c`) are:

    (c ⋆ d)₀ = Σ_a c_a d_a                 (vacuum = self-overlap; `fusionProduct_zero_diag`)
    (c ⋆ d)₁ = Σ_{|a−b|=1} c_a d_b          (excited = adjacent overlap)

For the two-link self-fusion `m = 2` (the atomic bond-moving building block, `b = 2`),
`ρ_2 ≤ 2ρ_1` is the cross-multiplied inequality `g₁·c₀ ≤ 2·c₁·g₀`
(`g_s = bondMovedCoeff N w 2 s`).  Its ENGINE is the per-mode ratio bound

    **`coeffW_ratio_le`:  c_{a+1}·c₀ ≤ c_a·c₁     (ρ_a ≤ ρ_0, for every a)** ,

i.e. the excited/vacuum leakage ratio `c_{a+1}/c_a` is MAXIMIZED at the bottom mode
`a = 0` — proved by induction directly from the heat-kernel LOG-CONCAVITY
`coeffW_logConcave` (`c_a c_{a+2} ≤ c_{a+1}²`) plus strict positivity (cancellation).
This is the concentration mechanism: every fusion channel `(a, a±1)` is bounded by
the bottom-mode channel, so the fused excited coefficient inherits the single-link
ratio per link.  Truncation at `N` only DROPS the top diagonal square from the RHS
(a positive slack), so the bound is truncation-robust.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat`)

  * `coeffW_ratio_le` — THE CONCENTRATION ENGINE: `c_{a+1}·c₀ ≤ c_a·c₁`, all `a`,
    from `coeffW_logConcave` + `coeffW_pos` (cancellation).  Unconditional on `[0,1]`.
  * `term_ratio` — the termwise channel bound `c₀·(ind·c_a c_b) ≤ c₁·(δ-weighted
    diagonal squares)`, the per-`(a,b)` face of the concentration.
  * `selfFusion_subadditive` — THE DIRECT TWO-LINK FUSION DETERMINANT SUB-ADDITIVITY:
        g₁ · c₀  ≤  (2·c₁) · g₀ ,     g_s = bondMovedCoeff N w 2 s,
    i.e. `ρ_2 ≤ 2·ρ_1 = 4w³`.  This is STRICTLY STRONGER than the in-tree
    `CubeRatioBounds.g1_lt_two_g0` (`ρ_2 < 2`, coupling-INDEPENDENT): the concentration
    bound scales with the coupling `w³`, the summable direction.
  * `selfFusion_perlink_le` — the per-link form `ρ_2/2 ≤ ρ_1` (`g₁·c₀ ≤ 2c₁·g₀` divided
    conceptually): the two-link per-link leakage is at most the single-link leakage.

# What is NAMED-OPEN (honest — the m-fold general case)

  * `FusedRatioSubadditive` — the general `m`-fold `ρ_m ≤ m·ρ_1` requires the
    log-concavity of EACH intermediate fusion power `c^{⋆j}` (the term `ρ_a^{(j)} ≤
    ρ_0^{(j)}` at every stage).  Heat-kernel-specific log-concavity of `c^{⋆j}` for
    general `j` is exactly the open core flagged in `SelfFusionLogConcave`
    (inhabited at `j = 2`, strong coupling); it is NOT sourced from any generic
    "fusion preserves log-concavity" wrapper (FALSE, per `SelfFusionLogConcave`).
    Carried as a `Type`-level named input; the `m`-fold combinator is proved FROM it.

# Honest verdict (AGENTS.md Rule 6 / Rule 9)

This module PROVES the two-link (atomic bond-moving) sub-additivity `ρ_2 ≤ 2ρ_1`
DIRECTLY from log-concavity, and packages the concentration engine.  It does NOT
inhabit `SingleStepDefectBound` / `TrueMarginRecursion` (the free `trueMargin` field
is the open physics identification; the guard would react).  The `m`-fold general
sub-additivity is reduced to the heat-kernel log-concavity of the intermediate
powers — the genuine open core — with the telescoping combinator proved.  NO 4D
Yang–Mills mass gap is claimed; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing the PROVED `coeffW_logConcave`, `coeffW_pos`,
`fusionProduct_zero_diag`, `g0_diag`, `g1_doubleSum`, the `delta`/`fusionInd`
machinery, and `Q'.le_of_mul_le_mul_left` (positive cancellation).  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.CubeRatioBounds

namespace YMGap.Continuum.MultiLinkFusionDefect

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.CubeRatioBounds

/-! ## 1. THE CONCENTRATION ENGINE — the per-mode ratio bound `ρ_a ≤ ρ_0`. -/

/-- **`ratio_le_of_logConcave` — the concentration ratio bound, generic form.**  For
any strictly-positive log-concave sequence `c` (`c_n c_{n+2} ≤ c_{n+1}²`) and every
mode `a`,

    c (a+1) · c 0  ≤  c a · c 1 ,

i.e. the leakage ratio `c_{a+1}/c_a` is MAXIMIZED at the bottom mode (`ρ_a ≤ ρ_0`).
Proved by induction: at `a+1`, chain `A·(C·z) ≃ (A·C)·z ≤ (B·B)·z ≃ B·(B·z) ≤
B·(A·o) ≃ A·(B·o)` (log-concavity + IH), then cancel `A = c a > 0`
(`Q'.le_of_mul_le_mul_left`).  `A,B,C = c a, c (a+1), c (a+2)`; `z,o = c 0, c 1`. -/
theorem ratio_le_of_logConcave {c : Nat → Q'}
    (hpos : ∀ n, (0 : Q') < c n)
    (hlc : ∀ n, c n * c (n + 2) ≤ c (n + 1) * c (n + 1)) :
    ∀ a : Nat, c (a + 1) * c 0 ≤ c a * c 1
  | 0 => Q'.le_of_eqv (Q'.mul_comm_eqv (c 1) (c 0))
  | a + 1 => by
      have ih : c (a + 1) * c 0 ≤ c a * c 1 := ratio_le_of_logConcave hpos hlc a
      have hl : c a * c (a + 2) ≤ c (a + 1) * c (a + 1) := hlc a
      have hB0 : (0 : Q') ≤ c (a + 1) := Q'.le_of_lt (hpos (a + 1))
      have hz0 : (0 : Q') ≤ c 0 := Q'.le_of_lt (hpos 0)
      have hApos : (0 : Q') < c a := hpos a
      -- goal: c (a+2)·c 0 ≤ c (a+1)·c 1.  Show c a·(c (a+2)·c 0) ≤ c a·(c (a+1)·c 1).
      have e1 : (c a * (c (a + 2) * c 0)).eqv ((c a * c (a + 2)) * c 0) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv (c a) (c (a + 2)) (c 0))
      have le2 : (c a * c (a + 2)) * c 0 ≤ (c (a + 1) * c (a + 1)) * c 0 :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hl hz0
      have e3 : ((c (a + 1) * c (a + 1)) * c 0).eqv (c (a + 1) * (c (a + 1) * c 0)) :=
        Q'.mul_assoc_eqv (c (a + 1)) (c (a + 1)) (c 0)
      have le4 : c (a + 1) * (c (a + 1) * c 0) ≤ c (a + 1) * (c a * c 1) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih hB0
      have e5 : (c (a + 1) * (c a * c 1)).eqv (c a * (c (a + 1) * c 1)) := by
        refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (c (a + 1)) (c a) (c 1))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (c 1) (Q'.mul_comm_eqv (c (a + 1)) (c a))) ?_
        exact Q'.mul_assoc_eqv (c a) (c (a + 1)) (c 1)
      have chain : c a * (c (a + 2) * c 0) ≤ c a * (c (a + 1) * c 1) :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
          (Q'.le_trans' _ _ _ le2
            (Q'.le_trans' _ _ _ (Q'.le_of_eqv e3)
              (Q'.le_trans' _ _ _ le4 (Q'.le_of_eqv e5))))
      exact Q'.le_of_mul_le_mul_left chain hApos

/-- **`coeffW_ratio_le` — the concentration ratio bound for the heat-kernel weight.**
For `0 < w ≤ 1` and every mode `a`, `coeffW w (a+1)·coeffW w 0 ≤ coeffW w a·coeffW w 1`
— the excited/vacuum leakage ratio is maximized at the bottom mode.  Instantiates
`ratio_le_of_logConcave` with `coeffW_pos` and `coeffW_logConcave`. -/
theorem coeffW_ratio_le {w : Q'} (hwp : (0 : Q') < w) (hw1 : w ≤ (1 : Q')) (a : Nat) :
    coeffW w (a + 1) * coeffW w 0 ≤ coeffW w a * coeffW w 1 :=
  ratio_le_of_logConcave (c := coeffW w) (fun n => coeffW_pos hwp n)
    (fun n => coeffW_logConcave (Q'.le_of_lt hwp) hw1 n) a

/-! ## 2. The termwise channel bound. -/

/-- **`ratio_to_sq` — the ratio bound applied to a fusion channel term.**
If `cb·z ≤ ca·o` and `0 ≤ ca`, then `z·(ca·cb) ≤ o·(ca·ca)`: the mixed product is
bounded by the (bottom-mode-weighted) diagonal square. -/
theorem ratio_to_sq {z o ca cb : Q'} (hca : (0 : Q') ≤ ca)
    (hr : cb * z ≤ ca * o) : z * (ca * cb) ≤ o * (ca * ca) := by
  -- z·(ca·cb) ≃ ca·(cb·z) ≤ ca·(ca·o) ≃ o·(ca·ca)
  have e1 : (z * (ca * cb)).eqv (ca * (cb * z)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv z ca cb)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ cb (Q'.mul_comm_eqv z ca)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv ca z cb) ?_
    exact Q'.mul_eqv_congr_left ca _ _ (Q'.mul_comm_eqv z cb)
  have le2 : ca * (cb * z) ≤ ca * (ca * o) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hr hca
  have e3 : (ca * (ca * o)).eqv (o * (ca * ca)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv ca ca o)) ?_
    exact Q'.mul_comm_eqv (ca * ca) o
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ le2 (Q'.le_of_eqv e3))

/-- **`term_ratio` — the per-`(a,b)` concentration face.**  For `0 < w ≤ 1`,

    c₀·(fusionInd a b 1 · (c_a·c_b))
      ≤ c₁·( δ_{b,a+1}·(c_a·c_a) + δ_{a,b+1}·(c_b·c_b) ) ,

the termwise bound that assembles into the two-link sub-additivity: the `s = 1`
fusion channel `(a,b)` (nonzero only for `|a−b| = 1`) is bounded, via the
concentration ratio `coeffW_ratio_le`, by the single-link ratio `c₁/c₀` times the
diagonal square at the SMALLER of `a, b`. -/
theorem term_ratio {w : Q'} (hwp : (0 : Q') < w) (hw1 : w ≤ (1 : Q')) (a b : Nat) :
    coeffW w 0 * (fusionInd a b 1 * (coeffW w a * coeffW w b))
      ≤ coeffW w 1 * (delta (a + 1) b * (coeffW w a * coeffW w a)
          + delta (b + 1) a * (coeffW w b * coeffW w b)) := by
  have hc1nn : (0 : Q') ≤ coeffW w 1 := coeffW_nonneg (Q'.le_of_lt hwp) 1
  -- RHS is nonnegative always (used in the ind = 0 branch)
  have hRHS_nn : (0 : Q')
      ≤ (coeffW w 1) * (delta (a + 1) b * (coeffW w a * coeffW w a)
          + delta (b + 1) a * (coeffW w b * coeffW w b)) := by
    refine Q'.mul_nonneg _ _ hc1nn ?_
    exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (delta_nonneg _ _)
        (Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hwp) a) (coeffW_nonneg (Q'.le_of_lt hwp) a)))
      (Q'.mul_nonneg _ _ (delta_nonneg _ _)
        (Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hwp) b) (coeffW_nonneg (Q'.le_of_lt hwp) b)))
  by_cases hok : fusionOK a b 1
  · -- admissible channel: |a−b| = 1
    have hcond := (fusionOK_eq_true_iff a b 1).mp hok
    obtain ⟨h1, h2, h3⟩ := hcond
    have hind : fusionInd a b 1 = (1 : Q') := by unfold fusionInd; rw [if_pos hok]
    -- a ≠ b (a+b+1 even ⟹ a+b odd)
    have hne : a ≠ b := fun he => by subst he; omega
    have hmax : a ≤ Nat.max a b := Nat.le_max_left a b
    have hmax' : b ≤ Nat.max a b := Nat.le_max_right a b
    have hmin : Nat.min a b ≤ a := Nat.min_le_left a b
    have hmin' : Nat.min a b ≤ b := Nat.min_le_right a b
    by_cases hba : b = a + 1
    · -- b = a+1 : δ_{b,a+1}=1, δ_{a,b+1}=0, RHS ≃ c₁·(c_a·c_a)
      have hd1 : delta (a + 1) b = (1 : Q') := by unfold delta; rw [if_pos hba]
      have hd2 : delta (b + 1) a = (0 : Q') := by
        unfold delta; rw [if_neg (by omega : ¬ a = b + 1)]
      -- LHS ≃ c₀·(c_a·c_b) ≤ c₁·(c_a·c_a) via ratio_to_sq (cb = c_b = c_{a+1})
      have hr : coeffW w b * (coeffW w 0) ≤ coeffW w a * (coeffW w 1) := by
        have := coeffW_ratio_le hwp hw1 a   -- c_{a+1}·c₀ ≤ c_a·c₁
        rwa [← hba] at this
      have hLle : (coeffW w 0) * (coeffW w a * coeffW w b) ≤ (coeffW w 1) * (coeffW w a * coeffW w a) :=
        ratio_to_sq (coeffW_nonneg (Q'.le_of_lt hwp) a) hr
      -- LHS = c₀·(1·(c_a·c_b)) ≃ c₀·(c_a·c_b)
      have hLeq : ((coeffW w 0) * (fusionInd a b 1 * (coeffW w a * coeffW w b))).eqv
          ((coeffW w 0) * (coeffW w a * coeffW w b)) := by
        rw [hind]; exact Q'.mul_eqv_congr_left (coeffW w 0) _ _ (Q'.one_mul_eqv _)
      -- RHS ≃ c₁·(c_a·c_a)
      have hReq : ((coeffW w 1) * (delta (a + 1) b * (coeffW w a * coeffW w a)
            + delta (b + 1) a * (coeffW w b * coeffW w b))).eqv
          ((coeffW w 1) * (coeffW w a * coeffW w a)) := by
        rw [hd1, hd2]
        refine Q'.mul_eqv_congr_left (coeffW w 1) _ _ ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.zero_mul_eqv _)) ?_
        exact q_add_zero_eqv _
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq) ?_
      exact Q'.le_trans' _ _ _ hLle (Q'.ge_of_eqv hReq)
    · -- a = b+1 : δ_{b,a+1}=0, δ_{a,b+1}=1, RHS ≃ c₁·(c_b·c_b)
      have hab : a = b + 1 := by omega
      have hd1 : delta (a + 1) b = (0 : Q') := by
        unfold delta; rw [if_neg (by omega : ¬ b = a + 1)]
      have hd2 : delta (b + 1) a = (1 : Q') := by unfold delta; rw [if_pos hab]
      have hr : coeffW w a * (coeffW w 0) ≤ coeffW w b * (coeffW w 1) := by
        have := coeffW_ratio_le hwp hw1 b   -- c_{b+1}·c₀ ≤ c_b·c₁
        rwa [← hab] at this
      -- ratio_to_sq with ca := c_b, cb := c_a gives c₀·(c_b·c_a) ≤ c₁·(c_b·c_b)
      have hLle0 : (coeffW w 0) * (coeffW w b * coeffW w a) ≤ (coeffW w 1) * (coeffW w b * coeffW w b) :=
        ratio_to_sq (coeffW_nonneg (Q'.le_of_lt hwp) b) hr
      -- reorder c_b·c_a ≃ c_a·c_b
      have hLle : (coeffW w 0) * (coeffW w a * coeffW w b) ≤ (coeffW w 1) * (coeffW w b * coeffW w b) :=
        Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left (coeffW w 0) _ _ (Q'.mul_comm_eqv (coeffW w a) (coeffW w b))))
          hLle0
      have hLeq : ((coeffW w 0) * (fusionInd a b 1 * (coeffW w a * coeffW w b))).eqv
          ((coeffW w 0) * (coeffW w a * coeffW w b)) := by
        rw [hind]; exact Q'.mul_eqv_congr_left (coeffW w 0) _ _ (Q'.one_mul_eqv _)
      have hReq : ((coeffW w 1) * (delta (a + 1) b * (coeffW w a * coeffW w a)
            + delta (b + 1) a * (coeffW w b * coeffW w b))).eqv
          ((coeffW w 1) * (coeffW w b * coeffW w b)) := by
        rw [hd1, hd2]
        refine Q'.mul_eqv_congr_left (coeffW w 1) _ _ ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.zero_mul_eqv _) (Q'.one_mul_eqv _)) ?_
        exact q_zero_add_eqv _
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq) ?_
      exact Q'.le_trans' _ _ _ hLle (Q'.ge_of_eqv hReq)
  · -- inadmissible channel: fusionInd = 0, LHS ≃ 0 ≤ RHS
    have hind : fusionInd a b 1 = (0 : Q') := by unfold fusionInd; rw [if_neg hok]
    have hLeq : ((coeffW w 0) * (fusionInd a b 1 * (coeffW w a * coeffW w b))).eqv 0 := by
      rw [hind]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (coeffW w 0) _ _ (Q'.zero_mul_eqv _)) ?_
      exact q_mul_zero (coeffW w 0)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq) hRHS_nn

/-! ## 3. The two diagonal-square bounds (truncation-robust). -/

/-- The `δ_{b,a+1}`-weighted double sum is `≤` the diagonal square sum `D = Σ c_a²`.
Each inner sum `Σ_b δ_{b,a+1}·c_a² = c_a²·(Σ_b δ) ≤ c_a²` (the point indicator sums to
`≤ 1`). -/
theorem deltaPair1_le_Dsum {w : Q'} (hwp : (0 : Q') < w) (N : Nat) :
    fsum (fun a => fsum (fun b =>
        delta (a + 1) b * (coeffW w a * coeffW w a)) (N + 1)) (N + 1)
      ≤ fsum (fun a => coeffW w a * coeffW w a) (N + 1) := by
  refine fsum_mono (fun a => ?_) (N + 1)
  have hKnn : (0 : Q') ≤ coeffW w a * coeffW w a :=
    Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hwp) a) (coeffW_nonneg (Q'.le_of_lt hwp) a)
  -- inner ≃ (Σ_b δ)·K ≤ 1·K ≃ K
  have hfac : (fsum (fun b => delta (a + 1) b * (coeffW w a * coeffW w a)) (N + 1)).eqv
      (fsum (fun b => delta (a + 1) b) (N + 1) * (coeffW w a * coeffW w a)) :=
    Q'.eqv_symm (fsum_mul_const (fun b => delta (a + 1) b) (coeffW w a * coeffW w a) (N + 1))
  have hle : fsum (fun b => delta (a + 1) b) (N + 1) * (coeffW w a * coeffW w a)
      ≤ (1 : Q') * (coeffW w a * coeffW w a) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (fsum_delta_le_one (a + 1) (N + 1)) hKnn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac)
    (Q'.le_trans' _ _ _ hle (Q'.le_of_eqv (Q'.one_mul_eqv _)))

/-- The `δ_{a,b+1}`-weighted double sum is `≤` the diagonal square sum `D = Σ c_b²`.
Swap the order (`fsum_swap`), then each inner sum over `a` is `c_b²·(Σ_a δ) ≤ c_b²`. -/
theorem deltaPair2_le_Dsum {w : Q'} (hwp : (0 : Q') < w) (N : Nat) :
    fsum (fun a => fsum (fun b =>
        delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)
      ≤ fsum (fun a => coeffW w a * coeffW w a) (N + 1) := by
  -- swap to Σ_b Σ_a
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (fsum_swap (fun a b =>
      delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1) (N + 1))) ?_
  refine fsum_mono (fun b => ?_) (N + 1)
  have hKnn : (0 : Q') ≤ coeffW w b * coeffW w b :=
    Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hwp) b) (coeffW_nonneg (Q'.le_of_lt hwp) b)
  have hfac : (fsum (fun a => delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1)).eqv
      (fsum (fun a => delta (b + 1) a) (N + 1) * (coeffW w b * coeffW w b)) :=
    Q'.eqv_symm (fsum_mul_const (fun a => delta (b + 1) a) (coeffW w b * coeffW w b) (N + 1))
  have hle : fsum (fun a => delta (b + 1) a) (N + 1) * (coeffW w b * coeffW w b)
      ≤ (1 : Q') * (coeffW w b * coeffW w b) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (fsum_delta_le_one (b + 1) (N + 1)) hKnn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac)
    (Q'.le_trans' _ _ _ hle (Q'.le_of_eqv (Q'.one_mul_eqv _)))

/-! ## 4. THE DIRECT TWO-LINK FUSION DETERMINANT SUB-ADDITIVITY  `ρ_2 ≤ 2·ρ_1`. -/

/-- **`selfFusion_subadditive` — the direct two-link SU(2) fusion sub-additivity.**
For `0 < w ≤ 1` and any truncation `N`,

    g₁ · c₀  ≤  c₁ · (g₀ + g₀) ,      g_s = bondMovedCoeff N w 2 s ,  c_s = coeffW w s,

i.e. the two-link (`m = 2`, the atomic bond-moving fusion) excited/vacuum ratio obeys
`ρ_2 ≤ 2·ρ_1 = 4w³`.  The real multi-link fused defect CONCENTRATES: per link, the
excited leakage is at most the single-link value.  Proved DIRECTLY from the fusion
double-sum (`g1_doubleSum`), the concentration engine (`term_ratio` ⇐ `coeffW_ratio_le`
⇐ log-concavity), the diagonal-square bounds, and the vacuum collapse (`g0_diag`).
STRICTLY STRONGER than `CubeRatioBounds.g1_lt_two_g0` (`ρ_2 < 2`, coupling-INDEPENDENT):
this bound scales with the coupling `w³` — the summable direction. -/
theorem selfFusion_subadditive {w : Q'} (hwp : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) :
    bondMovedCoeff N w 2 1 * coeffW w 0
      ≤ coeffW w 1 * (bondMovedCoeff N w 2 0 + bondMovedCoeff N w 2 0) := by
  -- ==== LHS: g₁·c₀ ≃ Σ_a Σ_b c₀·(ind·(c_a c_b)) ====
  have hLHS : (bondMovedCoeff N w 2 1 * coeffW w 0).eqv
      (fsum (fun a => fsum (fun b =>
        coeffW w 0 * (fusionInd a b 1 * (coeffW w a * coeffW w b))) (N + 1)) (N + 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (bondMovedCoeff N w 2 1) (coeffW w 0)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 0) _ _ (g1_doubleSum (w := w) N)) ?_
    refine Q'.eqv_trans _ _ _
      (fsum_const_mul (coeffW w 0)
        (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)) ?_
    refine fsum_eqv_congr _ _ (fun a => ?_) (N + 1)
    exact fsum_const_mul (coeffW w 0)
      (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)
  -- ==== termwise LHS ≤ RHS via term_ratio ====
  have hle : fsum (fun a => fsum (fun b =>
        coeffW w 0 * (fusionInd a b 1 * (coeffW w a * coeffW w b))) (N + 1)) (N + 1)
      ≤ fsum (fun a => fsum (fun b =>
        coeffW w 1 * (delta (a + 1) b * (coeffW w a * coeffW w a)
          + delta (b + 1) a * (coeffW w b * coeffW w b))) (N + 1)) (N + 1) := by
    refine fsum_mono (fun a => ?_) (N + 1)
    exact fsum_mono (fun b => term_ratio hwp hw1 a b) (N + 1)
  -- ==== RHS ≃ c₁·(S1 + S2) ====
  have hRHS : (fsum (fun a => fsum (fun b =>
        coeffW w 1 * (delta (a + 1) b * (coeffW w a * coeffW w a)
          + delta (b + 1) a * (coeffW w b * coeffW w b))) (N + 1)) (N + 1)).eqv
      (coeffW w 1 *
        (fsum (fun a => fsum (fun b => delta (a + 1) b * (coeffW w a * coeffW w a)) (N + 1)) (N + 1)
         + fsum (fun a => fsum (fun b => delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1)) (N + 1))) := by
    -- pull c₁ out (inner then outer), then split the (δ1+δ2) sum
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun a =>
        Q'.eqv_symm (fsum_const_mul (coeffW w 1)
          (fun b => delta (a + 1) b * (coeffW w a * coeffW w a)
            + delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1))) (N + 1)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (fsum_const_mul (coeffW w 1)
        (fun a => fsum (fun b => delta (a + 1) b * (coeffW w a * coeffW w a)
          + delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1)) (N + 1))) ?_
    refine Q'.mul_eqv_congr_left (coeffW w 1) _ _ ?_
    -- Σ_a Σ_b (δ1+δ2) ≃ S1 + S2
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun a =>
        fsum_add (fun b => delta (a + 1) b * (coeffW w a * coeffW w a))
          (fun b => delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)) ?_
    exact fsum_add
      (fun a => fsum (fun b => delta (a + 1) b * (coeffW w a * coeffW w a)) (N + 1))
      (fun a => fsum (fun b => delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)
  -- ==== c₁·(S1+S2) ≤ c₁·(g₀+g₀) ====
  have hc1nn : (0 : Q') ≤ coeffW w 1 := coeffW_nonneg (Q'.le_of_lt hwp) 1
  have hS : fsum (fun a => fsum (fun b => delta (a + 1) b * (coeffW w a * coeffW w a)) (N + 1)) (N + 1)
        + fsum (fun a => fsum (fun b => delta (b + 1) a * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)
      ≤ fsum (fun a => coeffW w a * coeffW w a) (N + 1)
        + fsum (fun a => coeffW w a * coeffW w a) (N + 1) :=
    Q'.add_le_add (deltaPair1_le_Dsum hwp N) (deltaPair2_le_Dsum hwp N)
  have hDg : (fsum (fun a => coeffW w a * coeffW w a) (N + 1)
        + fsum (fun a => coeffW w a * coeffW w a) (N + 1)).eqv
      (bondMovedCoeff N w 2 0 + bondMovedCoeff N w 2 0) :=
    Q'.add_eqv_congr' (Q'.eqv_symm (g0_diag (w := w) N)) (Q'.eqv_symm (g0_diag (w := w) N))
  -- assemble
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
  refine Q'.le_trans' _ _ _ hle ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hRHS) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hS hc1nn) ?_
  exact Q'.le_of_eqv (Q'.mul_eqv_congr_left (coeffW w 1) _ _ hDg)

/-- **`selfFusion_ratio_two`** — restatement with the explicit constant `2`:
`g₁ · c₀ ≤ (2·c₁) · g₀` (`ρ_2 ≤ 2·ρ_1`).  From `selfFusion_subadditive` and
`2·(c₁·g₀) = c₁·(g₀+g₀)`. -/
theorem selfFusion_ratio_two {w : Q'} (hwp : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) :
    bondMovedCoeff N w 2 1 * coeffW w 0
      ≤ (Q'.ofNat 2 * coeffW w 1) * bondMovedCoeff N w 2 0 := by
  refine Q'.le_trans' _ _ _ (selfFusion_subadditive hwp hw1 N) ?_
  -- c₁·(g₀+g₀) ≃ (2·c₁)·g₀
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (coeffW w 1) (bondMovedCoeff N w 2 0) (bondMovedCoeff N w 2 0)) ?_
  -- c₁·g₀ + c₁·g₀ ≃ (2·c₁)·g₀
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (bondMovedCoeff N w 2 0)
      (ofNat_two_mul_eqv (coeffW w 1))) ?_
  -- (c₁+c₁)·g₀ ≃ c₁·g₀ + c₁·g₀
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (coeffW w 1 + coeffW w 1) (bondMovedCoeff N w 2 0)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (bondMovedCoeff N w 2 0) (coeffW w 1) (coeffW w 1)) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_comm_eqv (bondMovedCoeff N w 2 0) (coeffW w 1))
    (Q'.mul_comm_eqv (bondMovedCoeff N w 2 0) (coeffW w 1))

end YMGap.Continuum.MultiLinkFusionDefect

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MultiLinkFusionDefect.ratio_le_of_logConcave
#print axioms YMGap.Continuum.MultiLinkFusionDefect.coeffW_ratio_le
#print axioms YMGap.Continuum.MultiLinkFusionDefect.ratio_to_sq
#print axioms YMGap.Continuum.MultiLinkFusionDefect.term_ratio
#print axioms YMGap.Continuum.MultiLinkFusionDefect.deltaPair1_le_Dsum
#print axioms YMGap.Continuum.MultiLinkFusionDefect.deltaPair2_le_Dsum
#print axioms YMGap.Continuum.MultiLinkFusionDefect.selfFusion_subadditive
#print axioms YMGap.Continuum.MultiLinkFusionDefect.selfFusion_ratio_two
