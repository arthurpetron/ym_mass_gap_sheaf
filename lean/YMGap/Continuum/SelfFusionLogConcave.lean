/-
Track B / R2 — LOG-CONCAVITY of the `p = 2` SU(2) self-fusion coefficient
`g_s = bondMovedCoeff N w 2 s` in the mode index `s`.

# Why this module exists — a structural guardrail on the self-fusion tower

The matched-retune crossover analysis of the `p = 2` self-fusion coefficient
`g_s = bondMovedCoeff N w 2 s` rests on the qualitative shape of the sequence
`s ↦ g_s`.  A clean structural sub-fact about that shape is LOG-CONCAVITY in `s`:
writing `Δ² log g` for the second difference of `log g`, `Δ² log g_s < 0`, i.e. the
cross-multiplied pure-`Q'` inequality

    g_{s+1} · g_{s+1}  ≥  g_s · g_{s+2}.

This is the discrete Pólya-frequency-2 / unimodality property at the level of the
FUSED tower (not the input heat-kernel coefficients).  It is the natural lift of the
input log-concavity `coeffW(s+1)² ≥ coeffW(s)·coeffW(s+2)`
(`FusionResidualBound.coeffW_logConcave`) through the Clebsch–Gordan self-fusion
convolution.  Log-concavity is preserved under (ordinary) convolution by a classical
Cauchy–Binet / AM-GM-over-pairs argument; the SU(2) fusion is a triangle+parity
restricted convolution, so the same preservation is expected — but it is a genuine
finite combinatorial inequality about the truncated Clebsch box double sums, weaker
than (and not implying) the sharp local-CLT dominance the engine ultimately needs.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat` arithmetic)

THE FUSED-TOWER POSITIVITY (proved):
  * `bondMovedCoeff_p2_pos` — `g_s > 0` for `0 < w` and EVERY mode `s` (not only the
    vacuum): the self-fusion of the strictly-positive `coeffW` is strictly positive
    on its non-empty Clebsch channel `(a,b) = (s,0)` (resp. `(0,s)`), which always
    lies in the truncation when `s ≤ N`.  Vacuum case re-exports
    `bondMovedCoeff_zero_pos`.

THE BOX CROSS-DIFFERENCE (proved):
  * `logConcaveCross` — the cross-difference `g_{s+1}·g_{s+1} − g_s·g_{s+2}` whose
    NONNEGATIVITY is exactly the cross-multiplied log-concavity.
  * `logConcaveCross_eq_boxDiff` — rewriting that cross-difference through the PROVED
    closed Clebsch double-sum form `bondMovedCoeff_p2_doubleSum`, so the obligation
    is a PURE-`Q'` finite-sum inequality on the box products `coeffW a · coeffW b`.

THE REDUCTION (proved):
  * `bondMovedCoeff_logConcave_of_core` — **the cross-multiplied log-concavity**
    `g_{s+1}·g_{s+1} ≥ g_s·g_{s+2}` FOLLOWS from the single named pure-`Q'`
    Cauchy–Binet core (`FusionConvLogConcaveCore` below), by transporting the box
    cross-difference and using `Q'.sub_nonneg_of_le`.  The reduction is sorry-free.

# NAMED OPEN — the single tightest pure-`Q'` residual (NOT inhabited)

  * `FusionConvLogConcaveCore` — the Cauchy–Binet positivity of the box
    cross-difference: the finite double-double sum
        (∑_{a,b} I_{s+1}(a,b)·c_a c_b)·(∑_{a',b'} I_{s+1}(a',b')·c_{a'} c_{b'})
          −  (∑_{a,b} I_s(a,b)·c_a c_b)·(∑_{a',b'} I_{s+2}(a',b')·c_{a'} c_{b'})  ≥ 0,
    with `c = coeffW w` (LOG-CONCAVE, `coeffW_logConcave`) and `I = fusionInd` the
    Clebsch indicator.  This is the classical convolution-log-concavity inequality
    specialized to the SU(2) triangle+parity-restricted convolution: a finite
    rational inequality (symmetrize the four-index sum into pairs and match each
    `(c_a c_{b'} − c_{a'} c_b)`-type AM-GM term across the `s ↔ s+2` index shift).
    It is NAMED precisely as a `Type`-level obligation — NOT an oracle, NOT a `sorry`,
    NOT a `C₄²` envelope.  It is NOT inhabited here.

# Honest verdict and scope

This module DEFINES the fused-tower log-concavity cross-difference, proves the FUSED
vacuum/general positivity, rewrites the cross-difference into the PROVED closed
Clebsch box double-sum form, and proves the REDUCTION of the cross-multiplied
log-concavity `g_{s+1}² ≥ g_s·g_{s+2}` to the single named pure-`Q'` Cauchy–Binet
core.  It does NOT inhabit that core: the finite combinatorial
convolution-log-concavity inequality for the truncated triangle+parity Clebsch
convolution is the remaining (classically-true, finite-rational) content, named
honestly.  Log-concavity is a STRUCTURAL sub-fact — necessary, NOT sufficient, for
the sharp dominance local CLT — and this is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Nat`/`Q'` facts, the
proved closed double-sum form, and reused order/`fsum` lemmas.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide` (only `decide` on decidable
facts), no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionRDFactor

namespace YMGap.Continuum.SelfFusionLogConcave

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionRDFactor

/-! ## 1. The fused-tower coefficient is strictly positive at EVERY mode

The vacuum case `g_0 > 0` is `bondMovedCoeff_zero_pos`.  For a general mode `s` within
the truncation (`s ≤ N`) the self-fusion has the non-empty Clebsch channel
`(a,b) = (s,0)`: `χ_s ∈ χ_s·χ_0` (the unit fuses trivially), so the `(s,0)` summand of
the diagonal double sum is `fusionInd s 0 s · (coeffW w s · coeffW w 0) =
1·(coeffW w s · 1) > 0`, and every other summand is nonnegative. -/

/-- `fusionOK s 0 s = true` (the `χ_s ∈ χ_s·χ_0` channel: `|s−0| = s ≤ s ≤ s+0`,
`s+0+s = 2s` even). -/
theorem fusionOK_self_zero (s : Nat) : fusionOK s 0 s = true := by
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max s 0 = s := Nat.max_eq_left (Nat.zero_le s)
  have hmin : Nat.min s 0 = 0 := Nat.min_eq_right (Nat.zero_le s)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  -- (s + 0 + s) % 2 = (2s) % 2 = 0
  have : s + 0 + s = 2 * s := by omega
  rw [this, Nat.mul_comm 2 s, Nat.mul_mod_left]

/-- `fusionInd s 0 s = 1`. -/
theorem fusionInd_self_zero (s : Nat) : fusionInd s 0 s = (1 : Q') := by
  unfold fusionInd
  rw [fusionOK_self_zero s]; rfl

/-- **The `(s,0)` channel summand of `g_s` is strictly positive** for `0 < w`:
`fusionInd s 0 s · (coeffW w s · coeffW w 0) = coeffW w s > 0`. -/
theorem box_channel_pos {w : Q'} (hw : (0 : Q') < w) (s : Nat) :
    (0 : Q') < fusionInd s 0 s * (coeffW w s * coeffW w 0) := by
  rw [fusionInd_self_zero s, coeffW_zero w]
  -- 1 · (coeffW w s · 1) > 0
  have hcs : (0 : Q') < coeffW w s := coeffW_pos hw s
  refine Q'.mul_pos (by decide : (0 : Q') < (1 : Q')) ?_
  exact Q'.mul_pos hcs (by decide : (0 : Q') < (1 : Q'))

/-- **FUSED-TOWER POSITIVITY — every mode within the truncation.**  For `0 < w` and
`s ≤ N`, the `p = 2` self-fusion coefficient is strictly positive:

    bondMovedCoeff N w 2 s  >  0.

PROOF.  Through the closed double-sum form
`g_s ≃ ∑_{a≤N} ∑_{b≤N} fusionInd a b s · (coeffW w a · coeffW w b)`
(`bondMovedCoeff_p2_doubleSum`), the `(a,b) = (s,0)` summand is `coeffW w s > 0`
(`box_channel_pos`); every other summand is nonnegative.  Two nested
single-term-`≤`-sum extractions (`fsum_term_le_of_nonneg`) bound the diagonal channel
below the full sum, and `s ≤ N` keeps it in range. -/
theorem bondMovedCoeff_p2_pos {w : Q'} (hw : (0 : Q') < w) {N s : Nat} (hsN : s ≤ N) :
    (0 : Q') < bondMovedCoeff N w 2 s := by
  -- transport positivity across the double-sum form
  refine lt_of_lt_of_le ?_ (Q'.ge_of_eqv (bondMovedCoeff_p2_doubleSum N s))
  -- each outer term is nonneg
  have houter_nn : ∀ a, (0 : Q')
      ≤ fsum (fun b => fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1) := by
    intro a
    refine fsum_nonneg (fun b => ?_) (N + 1)
    exact Q'.mul_nonneg _ _ (fusionInd_nonneg a b s)
      (Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hw) a)
        (coeffW_nonneg (Q'.le_of_lt hw) b))
  -- the a = s outer term ≤ whole outer sum
  have has : fsum (fun b => fusionInd s b s * (coeffW w s * coeffW w b)) (N + 1)
      ≤ fsum (fun a => fsum (fun b =>
          fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) (N + 1) :=
    fsum_term_le_of_nonneg houter_nn s (N + 1) (Nat.lt_succ_of_le hsN)
  refine lt_of_lt_of_le ?_ has
  -- inside a = s: the b = 0 summand > 0 (box_channel_pos), others nonneg
  have hinner_nn : ∀ b, (0 : Q') ≤ fusionInd s b s * (coeffW w s * coeffW w b) := by
    intro b
    exact Q'.mul_nonneg _ _ (fusionInd_nonneg s b s)
      (Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hw) s)
        (coeffW_nonneg (Q'.le_of_lt hw) b))
  have hb0 : fusionInd s 0 s * (coeffW w s * coeffW w 0)
      ≤ fsum (fun b => fusionInd s b s * (coeffW w s * coeffW w b)) (N + 1) :=
    fsum_term_le_of_nonneg hinner_nn 0 (N + 1) (Nat.succ_pos N)
  exact lt_of_lt_of_le (box_channel_pos hw s) hb0

/-! ## 2. The log-concavity cross-difference and its box form

The cross-multiplied log-concavity `g_{s+1}·g_{s+1} ≥ g_s·g_{s+2}` is the
NONNEGATIVITY of the cross-difference `g_{s+1}·g_{s+1} − g_s·g_{s+2}`.  We rewrite each
of the four `g`-factors through the PROVED closed Clebsch double-sum form, reducing the
obligation to a pure-`Q'` finite-sum inequality on the box products. -/

/-- The Clebsch box double sum of `g_s` (the proved closed form's right-hand side):
`boxSum w N s = ∑_{a≤N} ∑_{b≤N} fusionInd a b s · (coeffW w a · coeffW w b)`. -/
def boxSum (w : Q') (N s : Nat) : Q' :=
  fsum (fun a => fsum (fun b =>
    fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)

/-- `g_s ≃ boxSum w N s` (re-export of `bondMovedCoeff_p2_doubleSum`). -/
theorem bondMovedCoeff_eq_boxSum {w : Q'} (N s : Nat) :
    (bondMovedCoeff N w 2 s).eqv (boxSum w N s) :=
  bondMovedCoeff_p2_doubleSum N s

/-- **The log-concavity cross-difference** `g_{s+1}·g_{s+1} − g_s·g_{s+2}` (in `+ -`
form).  Its nonnegativity is exactly the cross-multiplied log-concavity. -/
def logConcaveCross (N : Nat) (w : Q') (s : Nat) : Q' :=
  bondMovedCoeff N w 2 (s + 1) * bondMovedCoeff N w 2 (s + 1)
    + -(bondMovedCoeff N w 2 s * bondMovedCoeff N w 2 (s + 2))

/-- **The cross-difference in box form.**  `logConcaveCross N w s` equals (as `eqv`)
the pure-`Q'` box cross-difference

    boxSum(s+1)·boxSum(s+1)  −  boxSum(s)·boxSum(s+2),

obtained by replacing each `g`-factor with its closed Clebsch double sum
(`bondMovedCoeff_eq_boxSum`) via `Q'.mul_eqv_congr`/`add` congruences. -/
theorem logConcaveCross_eq_boxDiff {w : Q'} (N s : Nat) :
    (logConcaveCross N w s).eqv
      (boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2))) := by
  unfold logConcaveCross
  refine Q'.add_eqv_congr' ?_ ?_
  · -- g_{s+1}·g_{s+1} ≃ boxSum(s+1)·boxSum(s+1)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (bondMovedCoeff_eq_boxSum N (s + 1))) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (bondMovedCoeff_eq_boxSum N (s + 1))
  · -- -(g_s·g_{s+2}) ≃ -(boxSum(s)·boxSum(s+2))
    refine Q'.neg_eqv_congr _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (bondMovedCoeff_eq_boxSum N s)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (bondMovedCoeff_eq_boxSum N (s + 2))

/-! ## 3. The single named pure-`Q'` Cauchy–Binet core (NOT inhabited)

With the cross-difference reduced to box form, the ENTIRE remaining content of the
fused-tower log-concavity is the Cauchy–Binet positivity of the box cross-difference:
a finite double-double sum over `(a,b)` and `(a',b')` of the Clebsch indicators against
the LOG-CONCAVE `coeffW` products.  We name it precisely as a `Type`-level obligation —
a `Q'` finite-sum inequality, NOT an oracle, NOT a `sorry`. -/

/-- **THE SINGLE NAMED RESIDUAL — Cauchy–Binet positivity of the box cross-difference.**
For the log-concave heat-kernel coefficients `c = coeffW w` (`0 ≤ w ≤ 1`,
`coeffW_logConcave`) and the Clebsch indicator `fusionInd`, the closed box double sums
satisfy

    boxSum(s+1) · boxSum(s+1)  ≥  boxSum(s) · boxSum(s+2).

This is the classical convolution-log-concavity inequality (the input `coeffW` is
log-concave; convolution preserves log-concavity) specialized to the SU(2)
triangle+parity-restricted Clebsch convolution, truncated at degree `N`.  It is a
finite rational inequality: symmetrize the four-index sum into pairs and match each
`(c_a c_{b'} − c_{a'} c_b)`-type AM-GM term across the `s ↔ s+2` index shift, using
`coeffW_logConcave` / `coeffW_ratio_mono`.  NAMED precisely; NOT inhabited here. -/
structure FusionConvLogConcaveCore (N : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) : Type where
  /-- **The OPEN content** — the box cross-difference is nonnegative, for every mode. -/
  cauchyBinet : ∀ s,
    boxSum w N s * boxSum w N (s + 2) ≤ boxSum w N (s + 1) * boxSum w N (s + 1)

/-! ## 4. The reduction — log-concavity from the named core (sorry-free) -/

/-- **THE FUSED-TOWER LOG-CONCAVITY (reduced to the named core).**  Given a
`FusionConvLogConcaveCore` witness, the `p = 2` self-fusion coefficient is LOG-CONCAVE
in the mode index `s`:

    bondMovedCoeff N w 2 (s+1) · bondMovedCoeff N w 2 (s+1)
      ≥  bondMovedCoeff N w 2 s · bondMovedCoeff N w 2 (s+2).

PROOF.  Transport each `g`-factor to its closed Clebsch box double sum
(`bondMovedCoeff_eq_boxSum`), reducing the cross-multiplied inequality to the box
cross-difference, which is the `cauchyBinet` field.  The reduction is sorry-free; the
ONLY open content is the named Cauchy–Binet core. -/
theorem bondMovedCoeff_logConcave_of_core {N : Nat} {w : Q'}
    {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (core : FusionConvLogConcaveCore N w hw0 hw1) (s : Nat) :
    bondMovedCoeff N w 2 s * bondMovedCoeff N w 2 (s + 2)
      ≤ bondMovedCoeff N w 2 (s + 1) * bondMovedCoeff N w 2 (s + 1) := by
  -- LHS ≃ boxSum(s)·boxSum(s+2) ; RHS ≃ boxSum(s+1)·boxSum(s+1)
  have hL : (bondMovedCoeff N w 2 s * bondMovedCoeff N w 2 (s + 2)).eqv
      (boxSum w N s * boxSum w N (s + 2)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (bondMovedCoeff_eq_boxSum N s))
      (Q'.mul_eqv_congr_left _ _ _ (bondMovedCoeff_eq_boxSum N (s + 2)))
  have hR : (boxSum w N (s + 1) * boxSum w N (s + 1)).eqv
      (bondMovedCoeff N w 2 (s + 1) * bondMovedCoeff N w 2 (s + 1)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (bondMovedCoeff_eq_boxSum N (s + 1))))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (bondMovedCoeff_eq_boxSum N (s + 1))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ (core.cauchyBinet s) (Q'.le_of_eqv hR))

/-- **The cross-difference is nonnegative (reduced to the named core).**  Equivalent
restatement of `bondMovedCoeff_logConcave_of_core` as `0 ≤ logConcaveCross N w s`. -/
theorem logConcaveCross_nonneg_of_core {N : Nat} {w : Q'}
    {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (core : FusionConvLogConcaveCore N w hw0 hw1) (s : Nat) :
    (0 : Q') ≤ logConcaveCross N w s := by
  -- 0 ≤ box cross-difference (sub_nonneg_of_le on the cauchyBinet ≤), transported back
  have hbox : (0 : Q') ≤
      boxSum w N (s + 1) * boxSum w N (s + 1) + -(boxSum w N s * boxSum w N (s + 2)) :=
    Q'.sub_nonneg_of_le (core.cauchyBinet s)
  exact Q'.le_trans' _ _ _ hbox (Q'.ge_of_eqv (logConcaveCross_eq_boxDiff N s))

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, pure `Q'`/`Nat`):
  * `fusionOK_self_zero` / `fusionInd_self_zero` / `box_channel_pos` — the non-empty
    `(s,0)` Clebsch channel carries strictly-positive mass.
  * `bondMovedCoeff_p2_pos` — FUSED-TOWER POSITIVITY at EVERY mode `s ≤ N`
    (`g_s > 0`), not only the vacuum.
  * `logConcaveCross` / `logConcaveCross_eq_boxDiff` — the log-concavity
    cross-difference and its rewrite into the PROVED closed Clebsch box double-sum
    form (a pure-`Q'` finite-sum object).
  * `bondMovedCoeff_logConcave_of_core` — **THE REDUCTION**: the cross-multiplied
    log-concavity `g_{s+1}² ≥ g_s·g_{s+2}` from the single named Cauchy–Binet core,
    sorry-free; and `logConcaveCross_nonneg_of_core` (the cross-difference form).

NAMED OPEN (NOT inhabited) — the single tightest pure-`Q'` residual:
  * `FusionConvLogConcaveCore` — the Cauchy–Binet positivity of the box
    cross-difference `boxSum(s+1)² ≥ boxSum(s)·boxSum(s+2)` for the LOG-CONCAVE
    `coeffW` against the Clebsch indicator, truncated at `N`.  This is the classical
    convolution-log-concavity inequality specialized to the SU(2) triangle+parity
    Clebsch convolution — a finite rational inequality, NAMED precisely, NOT an
    oracle, NOT a `sorry`, NOT a `C₄²` envelope, NOT inhabited here.

HONEST VERDICT.  This proves the FUSED-tower positivity at every mode and the
sorry-free REDUCTION of the fused-tower log-concavity `g_{s+1}² ≥ g_s·g_{s+2}` to the
single named pure-`Q'` Cauchy–Binet core (the box cross-difference positivity for the
log-concave input).  It does NOT inhabit that core — the finite combinatorial
convolution-log-concavity inequality for the truncated triangle+parity Clebsch
convolution is the remaining (classically-true, finite-rational) content, named
honestly.  Log-concavity is a STRUCTURAL sub-fact: necessary, NOT sufficient, for the
sharp dominance local CLT.  This is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.SelfFusionLogConcave

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SelfFusionLogConcave.fusionOK_self_zero
#print axioms YMGap.Continuum.SelfFusionLogConcave.fusionInd_self_zero
#print axioms YMGap.Continuum.SelfFusionLogConcave.box_channel_pos
#print axioms YMGap.Continuum.SelfFusionLogConcave.bondMovedCoeff_p2_pos
#print axioms YMGap.Continuum.SelfFusionLogConcave.bondMovedCoeff_eq_boxSum
#print axioms YMGap.Continuum.SelfFusionLogConcave.logConcaveCross_eq_boxDiff
#print axioms YMGap.Continuum.SelfFusionLogConcave.bondMovedCoeff_logConcave_of_core
#print axioms YMGap.Continuum.SelfFusionLogConcave.logConcaveCross_nonneg_of_core
