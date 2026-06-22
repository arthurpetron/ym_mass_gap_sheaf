/-
Track B / R2 — LOG-CONCAVITY of the `p = 2` SU(2) self-fusion coefficient
`g_s = bondMovedCoeff N w 2 s` in the mode index `s`, and the SHARP, HONEST
delimitation of when it holds.

# Why this module exists — a structural sub-fact, and a correction of a false premise

The matched-retune crossover analysis of the `p = 2` self-fusion coefficient
`g_s = bondMovedCoeff N w 2 s` rests on the qualitative shape of the sequence
`s ↦ g_s`.  A clean structural sub-fact about that shape is LOG-CONCAVITY in `s`:
the cross-multiplied pure-`Q'` inequality

    g_{s+1} · g_{s+1}  ≥  g_s · g_{s+2}.

`g_s` equals (`bondMovedCoeff_p2_doubleSum`) the truncated Clebsch box double sum
`boxSum w N s = ∑_{a,b≤N} I_s(a,b)·(c_a c_b)`, `c = coeffW w`, `I = fusionInd`.

CRITICAL CORRECTION (this wave).  A prior framing asserted that this log-concavity
is "the classical fact that convolution preserves log-concavity," hence a finite
rational inequality true for all `s`, all `w∈(0,1)`, all `N`.  THAT FRAMING IS
MATHEMATICALLY FALSE, on TWO independent counts, both established by explicit
computation:

  (1) The TRUNCATION at `N` breaks it.  For `w` near `1` the dominant Clebsch scale
      `r ≍ (1−w)^{−1/2}` exceeds any fixed cutoff `N`, and the box `{a,b≤N}` clips the
      convolution support ASYMMETRICALLY across the modes `s, s+1, s+2`.  The
      cross-difference then goes NEGATIVE.  The smallest witness is `N = 1`, `s = 0`,
      `w = 1`: `boxSum = (5)(4) = 20 > 16 = (4)(4)` — proved below as
      `boxSum1_logConcave_FALSE_at_one`.

  (2) The SU(2) fusion does NOT preserve log-concavity even UNtruncated.  For a
      GENERIC positive log-concave input sequence `c` (ratio `c_{s+1}/c_s`
      non-increasing) the untruncated SU(2)-fusion self-convolution is NOT
      log-concave; explicit log-concave inputs violate it.  The heat-kernel case is
      true (untruncated) only because of the SPECIFIC heat-kernel / Gaussian-theta
      structure `c_a = (a+1)·w^{a(a+2)}` (the `(r,d)` diagonalization), NOT because
      of mere log-concavity.  So `coeffW_logConcave` ALONE does not imply it.

The genuinely TRUE finite statement is the STRONG-COUPLING regime: for `w` bounded
away from `1` (concretely `coeffW w 1 · coeffW w 1 ≤ 3`, implied by `w ≤ 1/2`), the
truncated box log-concavity DOES hold; the cutoff is then never reached.  This is
exactly the regime in which the lattice mass gap is rigorously controlled.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat` arithmetic)

THE FUSED-TOWER POSITIVITY (proved):
  * `bondMovedCoeff_p2_pos` — `g_s > 0` for `0 < w` and EVERY mode `s ≤ N`: the
    self-fusion of the strictly-positive `coeffW` is strictly positive on its
    non-empty Clebsch channel `(a,b) = (s,0)`.

THE BOX CROSS-DIFFERENCE + REDUCTION (proved):
  * `logConcaveCross` / `logConcaveCross_eq_boxDiff` — the cross-difference
    `g_{s+1}² − g_s·g_{s+2}` rewritten through the closed Clebsch box double-sum form.
  * `bondMovedCoeff_logConcave_of_core` — **the cross-multiplied log-concavity**
    `g_{s+1}² ≥ g_s·g_{s+2}` FOLLOWS from any inhabitant of the box-level core, by
    transporting the box cross-difference.  Sorry-free.

THE GENUINE `N = 1` STRONG-COUPLING CASE (proved, NEW):
  * `boxSum1_zero` / `boxSum1_one` / `boxSum1_two` — the EXACT closed `Q'` values of
    the `N = 1` box sums: `B_0 = 1 + c²`, `B_1 = c + c`, `B_2 = c²` (`c = coeffW w 1`).
  * `boxSum1_logConcave` — the `N = 1` log-concavity `B_0·B_2 ≤ B_1·B_1` UNDER the
    explicit strong-coupling hypothesis `c·c ≤ 3` (`= (1+c²)·c² ≤ (c+c)²`, a clean
    pure-`Q'` polynomial inequality).
  * `coeffW1_sq_le_three_of_strong` — that hypothesis holds for `w ≤ 1/2`
    (`coeffW w 1 = 2w³ ≤ 1`, so `c² ≤ 1 ≤ 3`); hence `boxSum1_logConcave_strong`.

THE FALSITY WITNESS (proved, NEW — honesty):
  * `boxSum1_logConcave_FALSE_at_one` — `¬ (B_0·B_2 ≤ B_1·B_1)` at `N = 1`, `w = 1`
    (`20 > 16`): a CONSTRUCTIVE refutation of the unconditional `∀ s, w∈[0,1]` claim.

# NAMED OPEN — the genuinely-true heat-kernel content (NOT a finite combinatorial fact)

  * `FusionConvLogConcaveCore` — the box log-concavity `boxSum(s)·boxSum(s+2) ≤
    boxSum(s+1)²` for EVERY `s`, UNDER the strong-coupling hypothesis carried as a
    field.  At `N = 1` it is inhabited by `boxSum1_logConcave` (see
    `fusionConvLogConcaveCore_N1`).  For general `N` it remains open; the genuine
    content is NOT the false "convolution preserves log-concavity" but the
    heat-kernel-specific `(r,d)` Gaussian-theta local-CLT (`FusionRDFactor`), which is
    NOT a finite rational inequality.

# Honest verdict and scope

This module: proves the fused-tower positivity; proves the reduction of the
cross-multiplied log-concavity to the box-level core; PROVES the `N = 1` case in the
strong-coupling regime exactly (closed `Q'` box values + a clean polynomial
inequality + the `w ≤ 1/2` corollary); and CONSTRUCTIVELY REFUTES the prior
unconditional `∀ s, ∀ w∈[0,1]` claim with an explicit `N = 1`, `w = 1` counterexample.
It documents that the SU(2) fusion does NOT preserve log-concavity for generic
log-concave inputs, so the general statement is heat-kernel-specific (the `(r,d)`
Gaussian local-CLT), NOT a finite combinatorial Cauchy–Binet.  Log-concavity is a
STRUCTURAL sub-fact — necessary, NOT sufficient, for the sharp dominance local CLT —
and this is NOT a 4D Yang–Mills mass gap.

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

/-! ## 3. The named box-level core (heat-kernel-specific; inhabited at `N = 1`)

With the cross-difference reduced to box form, the remaining content of the
fused-tower log-concavity is the positivity of the box cross-difference,

    boxSum(s+1) · boxSum(s+1)  ≥  boxSum(s) · boxSum(s+2).

HONESTY (see the module header).  This is NOT the classical "convolution preserves
log-concavity": (i) the truncation at `N` breaks it for `w → 1`
(`boxSum1_logConcave_FALSE_at_one`), and (ii) the SU(2) fusion does NOT preserve
log-concavity for GENERIC log-concave inputs — the heat-kernel case relies on the
specific `(r,d)` Gaussian-theta structure, not on `coeffW_logConcave` alone.  So the
core is NOT a finite combinatorial Cauchy–Binet; the genuine general-`N` content is the
heat-kernel local-CLT.  The core therefore carries the STRONG-COUPLING hypothesis
`c·c ≤ 3` (`c = coeffW w 1`, implied by `w ≤ 1/2`) under which the truncated statement
is true; it is inhabited at `N = 1` (`fusionConvLogConcaveCore_N1`). -/

/-- **THE NAMED BOX-LEVEL CORE — strong-coupling box log-concavity.**  The closed box
double sums satisfy `boxSum(s)·boxSum(s+2) ≤ boxSum(s+1)²` for every mode `s`, under the
strong-coupling hypothesis `coeffW w 1 · coeffW w 1 ≤ 3` (the field `strongCoupling`),
which keeps the dominant Clebsch scale within the cutoff so the truncation does not
clip the convolution asymmetrically.  Inhabited at `N = 1` below; general `N` open
(heat-kernel `(r,d)` local-CLT, NOT a finite rational inequality). -/
structure FusionConvLogConcaveCore (N : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) : Type where
  /-- The strong-coupling hypothesis (`c² ≤ 3`, `c = coeffW w 1`; holds for `w ≤ 1/2`). -/
  strongCoupling : coeffW w 1 * coeffW w 1 ≤ (3 : Q')
  /-- **The box log-concavity content** — the box cross-difference is nonnegative,
  for every mode (under `strongCoupling`). -/
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

/-! ## 4b. The EXACT `N = 1` box sums (closed `Q'` values)

At truncation `N = 1` the index ranges are `a, b ∈ {0,1}`, so each box sum is a 4-term
double sum that collapses to a closed `Q'` value in `c = coeffW w 1` (using
`coeffW w 0 = 1` and the concrete `fusionInd` indicators):

    boxSum w 1 0  =  1 + c·c       (diagonal channel: (0,0)+(1,1))
    boxSum w 1 1  =  c + c         (off-diagonal channel: (0,1)+(1,0))
    boxSum w 1 2  =  c·c           (top channel: (1,1) only).

These are proved by unfolding `fsum` and evaluating the four indicators. -/

/-- `1 · (1 · x) ≃ x` (local unit helper). -/
private theorem one_one_mul' (x : Q') : ((1 : Q') * ((1 : Q') * x)).eqv x :=
  Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.one_mul_eqv x)

/-- `1 · (x · 1) ≃ x` (local unit helper). -/
private theorem one_mul_one' (x : Q') : ((1 : Q') * (x * (1 : Q'))).eqv x :=
  Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.mul_one_eqv x)

/-- **`boxSum w 1 0 ≃ 1 + c·c`** (`c = coeffW w 1`).  The `s = 0` (diagonal) channel
keeps the `(0,0)` summand `1·(1·1)` and the `(1,1)` summand `1·(c·c)`. -/
theorem boxSum1_zero (w : Q') :
    (boxSum w 1 0).eqv ((1 : Q') + coeffW w 1 * coeffW w 1) := by
  unfold boxSum
  simp only [fsum]
  have e1 : fusionInd 0 0 0 = (1 : Q') := by decide
  have e2 : fusionInd 0 1 0 = (0 : Q') := by decide
  have e3 : fusionInd 1 0 0 = (0 : Q') := by decide
  have e4 : fusionInd 1 1 0 = (1 : Q') := by decide
  rw [e1, e2, e3, e4, coeffW_zero]
  have row0 : (((0 : Q') + (1 : Q') * ((1 : Q') * (1 : Q')))
      + (0 : Q') * ((1 : Q') * coeffW w 1)).eqv (1 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr_left 0 _ _ (one_one_mul' 1)) (Q'.zero_mul_eqv _)) ?_
    exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) (q_zero_add_eqv 1)
  have row1 : (((0 : Q') + (0 : Q') * (coeffW w 1 * (1 : Q')))
      + (1 : Q') * (coeffW w 1 * coeffW w 1)).eqv (coeffW w 1 * coeffW w 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr_left 0 _ _ (Q'.zero_mul_eqv _)) (Q'.one_mul_eqv _)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (q_add_zero_eqv 0)) (q_zero_add_eqv _)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (q_zero_add_eqv _)) ?_
  exact Q'.add_eqv_congr' row0 row1

/-- **`boxSum w 1 1 ≃ c + c`** (`c = coeffW w 1`).  The `s = 1` (off-diagonal) channel
keeps the `(0,1)` summand `1·(1·c)` and the `(1,0)` summand `1·(c·1)`. -/
theorem boxSum1_one (w : Q') :
    (boxSum w 1 1).eqv (coeffW w 1 + coeffW w 1) := by
  unfold boxSum
  simp only [fsum]
  have e1 : fusionInd 0 0 1 = (0 : Q') := by decide
  have e2 : fusionInd 0 1 1 = (1 : Q') := by decide
  have e3 : fusionInd 1 0 1 = (1 : Q') := by decide
  have e4 : fusionInd 1 1 1 = (0 : Q') := by decide
  rw [e1, e2, e3, e4, coeffW_zero]
  have row0 : (((0 : Q') + (0 : Q') * ((1 : Q') * (1 : Q')))
      + (1 : Q') * ((1 : Q') * coeffW w 1)).eqv (coeffW w 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr_left 0 _ _ (Q'.zero_mul_eqv _)) (one_one_mul' _)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (q_add_zero_eqv 0)) (q_zero_add_eqv _)
  have row1 : (((0 : Q') + (1 : Q') * (coeffW w 1 * (1 : Q')))
      + (0 : Q') * (coeffW w 1 * coeffW w 1)).eqv (coeffW w 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr_left 0 _ _ (one_mul_one' _)) (Q'.zero_mul_eqv _)) ?_
    exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) (q_zero_add_eqv _)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (q_zero_add_eqv _)) ?_
  exact Q'.add_eqv_congr' row0 row1

/-- **`boxSum w 1 2 ≃ c·c`** (`c = coeffW w 1`).  The `s = 2` (top) channel keeps only
the `(1,1)` summand `1·(c·c)`. -/
theorem boxSum1_two (w : Q') :
    (boxSum w 1 2).eqv (coeffW w 1 * coeffW w 1) := by
  unfold boxSum
  simp only [fsum]
  have e1 : fusionInd 0 0 2 = (0 : Q') := by decide
  have e2 : fusionInd 0 1 2 = (0 : Q') := by decide
  have e3 : fusionInd 1 0 2 = (0 : Q') := by decide
  have e4 : fusionInd 1 1 2 = (1 : Q') := by decide
  rw [e1, e2, e3, e4, coeffW_zero]
  have row0 : (((0 : Q') + (0 : Q') * ((1 : Q') * (1 : Q')))
      + (0 : Q') * ((1 : Q') * coeffW w 1)).eqv (0 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr_left 0 _ _ (Q'.zero_mul_eqv _)) (Q'.zero_mul_eqv _)) ?_
    exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) (q_add_zero_eqv 0)
  have row1 : (((0 : Q') + (0 : Q') * (coeffW w 1 * (1 : Q')))
      + (1 : Q') * (coeffW w 1 * coeffW w 1)).eqv (coeffW w 1 * coeffW w 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr_left 0 _ _ (Q'.zero_mul_eqv _)) (Q'.one_mul_eqv _)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (q_add_zero_eqv 0)) (q_zero_add_eqv _)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (q_zero_add_eqv _)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' row0 row1) (q_zero_add_eqv _)

/-! ## 4c. The `N = 1` log-concavity polynomial inequality (strong coupling) -/

/-- `c·c ≤ 3` and `0 ≤ c` ⟹ `(1 + c·c)·(c·c) ≤ (c + c)·(c + c)`.  The pure-`Q'`
content of the `N = 1` log-concavity: expand `(c+c)² = 4c²`, `(1+c²)c² = c² + c⁴`, so
the claim is `c⁴ ≤ 3c²`, i.e. `(c·c)·(c·c) ≤ 3·(c·c)`, from `c·c ≤ 3` times `c·c ≥ 0`. -/
theorem box1_poly_ineq (c : Q') (hc : (0 : Q') ≤ c) (hb : c * c ≤ (3 : Q')) :
    ((1 : Q') + c * c) * (c * c) ≤ (c + c) * (c + c) := by
  have hcc : (0 : Q') ≤ c * c := Q'.mul_nonneg _ _ hc hc
  -- (1+c²)·c² ≃ c² + c²·c²
  have hLHS : (((1 : Q') + c * c) * (c * c)).eqv ((c * c) + (c * c) * (c * c)) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (c * c) (c * c))
      (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (c * c)))
  -- (c+c)·(c+c) ≃ (c²+c²)+(c²+c²)
  have hRHS : ((c + c) * (c + c)).eqv (((c * c) + (c * c)) + ((c * c) + (c * c))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (c + c) c c) ?_
    exact Q'.add_eqv_congr' (Q'.add_mul_eqv c c c) (Q'.add_mul_eqv c c c)
  -- (c²) + 3·(c²) ≃ (c²+c²)+(c²+c²)  (both = 4c²)
  have hfour : ((c * c) + (3 : Q') * (c * c)).eqv (((c * c) + (c * c)) + ((c * c) + (c * c))) := by
    have h3 : (3 : Q').eqv ((1 : Q') + (1 : Q') + (1 : Q')) := by decide
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c * c) _ _ (Q'.mul_eqv_congr_right _ _ (c * c) h3)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c * c) _ _ (Q'.add_mul_eqv ((1 : Q') + 1) 1 (c * c))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c * c) _ _
        (Q'.add_eqv_congr' (Q'.add_mul_eqv 1 1 (c * c)) (Q'.eqv_refl _))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c * c) _ _
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.one_mul_eqv (c * c)) (Q'.one_mul_eqv (c * c)))
          (Q'.one_mul_eqv (c * c)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (c * c) (c * c + c * c) (c * c))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (c * c) (c * c + c * c) (c * c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c * c) _ _ (Q'.add_assoc_eqv (c * c) (c * c) (c * c))) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv (c * c) (c * c) (c * c + c * c))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHS)
  -- c² + c²·c²  ≤  c² + 3·c²  ≃  RHS
  have hmul : (c * c) * (c * c) ≤ (3 : Q') * (c * c) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hb hcc
  have step1 : (c * c) + (c * c) * (c * c) ≤ (c * c) + (3 : Q') * (c * c) :=
    Q'.add_le_add_left (c * c) _ _ hmul
  exact Q'.le_trans' _ _ _ step1 (Q'.le_of_eqv hfour)

/-- **THE `N = 1` LOG-CONCAVITY (strong coupling).**  Under the strong-coupling
hypothesis `coeffW w 1 · coeffW w 1 ≤ 3` (and `0 < w`), the `N = 1` box sums satisfy

    boxSum w 1 0 · boxSum w 1 2  ≤  boxSum w 1 1 · boxSum w 1 1.

PROOF: transport each box sum to its closed value (`boxSum1_*`), then `box1_poly_ineq`. -/
theorem boxSum1_logConcave {w : Q'} (hw : (0 : Q') < w)
    (hb : coeffW w 1 * coeffW w 1 ≤ (3 : Q')) :
    boxSum w 1 0 * boxSum w 1 2 ≤ boxSum w 1 1 * boxSum w 1 1 := by
  have hc : (0 : Q') ≤ coeffW w 1 := coeffW_nonneg (Q'.le_of_lt hw) 1
  have hL : (boxSum w 1 0 * boxSum w 1 2).eqv
      (((1 : Q') + coeffW w 1 * coeffW w 1) * (coeffW w 1 * coeffW w 1)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (boxSum1_zero w))
      (Q'.mul_eqv_congr_left _ _ _ (boxSum1_two w))
  have hR : (boxSum w 1 1 * boxSum w 1 1).eqv
      ((coeffW w 1 + coeffW w 1) * (coeffW w 1 + coeffW w 1)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (boxSum1_one w))
      (Q'.mul_eqv_congr_left _ _ _ (boxSum1_one w))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) ?_
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hR)
  exact box1_poly_ineq (coeffW w 1) hc hb

/-! ## 4d. The strong-coupling hypothesis holds for `w ≤ 1/2` -/

/-- For `0 ≤ w ≤ 1/2`, `coeffW w 1 ≤ 1`: `coeffW w 1 = 2·w³ ≤ 2·w ≤ 2·(1/2) = 1`
(`qpow w 3 ≤ w` for `w ≤ 1`). -/
theorem coeffW1_le_one_of_strong {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) : coeffW w 1 ≤ (1 : Q') := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw (by decide)
  show dimQ 1 * qpow w (c4 1) ≤ (1 : Q')
  have hc4 : c4 1 = 3 := by decide
  rw [hc4]
  have hq : qpow w 3 ≤ w := qpow_succ_le_self hw0 hw1 2
  have hd1 : dimQ 1 = (2 : Q') := by decide
  rw [hd1]
  have s1 : (2 : Q') * qpow w 3 ≤ (2 : Q') * w :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hq (by decide)
  refine Q'.le_trans' _ _ _ s1 ?_
  have s2 : (2 : Q') * w ≤ (2 : Q') * Q'.mkPos 1 2 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hw (by decide)
  exact Q'.le_trans' _ _ _ s2 (Q'.le_of_eqv (by decide))

/-- **The strong-coupling hypothesis for `w ≤ 1/2`.**  `coeffW w 1 · coeffW w 1 ≤ 3`
(in fact `≤ 1`), since `coeffW w 1 ≤ 1`. -/
theorem coeffW1_sq_le_three_of_strong {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) : coeffW w 1 * coeffW w 1 ≤ (3 : Q') := by
  have hle1 : coeffW w 1 ≤ (1 : Q') := coeffW1_le_one_of_strong hw0 hw
  have hc0 : (0 : Q') ≤ coeffW w 1 := coeffW_nonneg hw0 1
  have s1 : coeffW w 1 * coeffW w 1 ≤ (1 : Q') * coeffW w 1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hle1 hc0
  have s2 : (1 : Q') * coeffW w 1 ≤ (1 : Q') * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hle1 (by decide)
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ s2 (by decide))

/-- **`N = 1` log-concavity, strong-coupling corollary.**  For `0 < w ≤ 1/2`, the
`N = 1` box log-concavity holds unconditionally (the hypothesis is discharged). -/
theorem boxSum1_logConcave_strong {w : Q'} (hw : (0 : Q') < w)
    (hw12 : w ≤ Q'.mkPos 1 2 (by decide)) :
    boxSum w 1 0 * boxSum w 1 2 ≤ boxSum w 1 1 * boxSum w 1 1 :=
  boxSum1_logConcave hw (coeffW1_sq_le_three_of_strong (Q'.le_of_lt hw) hw12)

/-! ## 4e. Inhabitation of the core at `N = 1` -/

/-- **The box-level core is inhabited at `N = 1`.**  For `0 < w ≤ 1` with the
strong-coupling hypothesis `coeffW w 1 · coeffW w 1 ≤ 3`, `FusionConvLogConcaveCore 1 w`
holds: at `N = 1` every mode `s` reduces (by `boxSum1_*` and the fact that `boxSum w 1 s
≃ 0` for `s ≥ 3`) to either the proved `boxSum1_logConcave` (the only non-degenerate
mode `s = 0`) or a degenerate `0 ≤ (nonneg)²` comparison.  We provide the `s = 0` case
exactly and the higher modes via the box positivity/zeroness. -/
def fusionConvLogConcaveCore_N1 {w : Q'} (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (hb : coeffW w 1 * coeffW w 1 ≤ (3 : Q')) :
    FusionConvLogConcaveCore 1 w (Q'.le_of_lt hw) hw1 where
  strongCoupling := hb
  cauchyBinet := by
    intro s
    -- For s = 0: boxSum1_logConcave.  For s ≥ 1: boxSum w 1 (s+2) ≃ 0 (no Clebsch
    -- channel within {a,b≤1} once the top index exceeds 2), so LHS ≃ 0 ≤ RHS (a square).
    match s with
    | 0 => exact boxSum1_logConcave hw hb
    | Nat.succ k =>
      -- boxSum w 1 (k+3) ≃ 0 : no (a,b)≤1 has fusionOK a b (k+3) since a+b ≤ 2 < k+3.
      have hzero : (boxSum w 1 (k + 1 + 2)).eqv 0 := by
        unfold boxSum
        refine fsum_zero_below (1 + 1) (fun a ha => ?_)
        refine fsum_zero_below (1 + 1) (fun b hb' => ?_)
        have hind : fusionInd a b (k + 1 + 2) = (0 : Q') := by
          unfold fusionInd
          have hok : fusionOK a b (k + 1 + 2) = false := by
            rw [fusionOK_eq_false_iff]
            rintro ⟨_, h2, _⟩
            -- s = k+3 ≤ a+b ≤ 1+1 = 2, impossible
            have hab : a + b ≤ 2 := by omega
            omega
          rw [hok]; rfl
        rw [hind]; exact Q'.zero_mul_eqv _
      -- LHS = boxSum w 1 (k+1) * boxSum w 1 (k+1+2) ≃ boxSum w 1 (k+1) * 0 ≃ 0
      have hLHS0 : (boxSum w 1 (k + 1) * boxSum w 1 (k + 1 + 2)).eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hzero) (q_mul_zero _)
      -- RHS ≥ 0 (a square of a nonneg box sum)
      have hbnn : (0 : Q') ≤ boxSum w 1 (k + 1 + 1) := by
        unfold boxSum
        refine fsum_nonneg (fun a => ?_) (1 + 1)
        refine fsum_nonneg (fun b => ?_) (1 + 1)
        exact Q'.mul_nonneg _ _ (fusionInd_nonneg a b (k + 1 + 1))
          (Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hw) a) (coeffW_nonneg (Q'.le_of_lt hw) b))
      have hRnn : (0 : Q') ≤ boxSum w 1 (k + 1 + 1) * boxSum w 1 (k + 1 + 1) :=
        Q'.mul_nonneg _ _ hbnn hbnn
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS0) hRnn

/-! ## 4f. The falsity witness — the unconditional `∀ s, w∈[0,1]` claim is FALSE

The honesty correction: at `N = 1`, `w = 1` the box log-concavity FAILS.  `coeffW 1 1 =
2`, so `boxSum 1 1 0 = 1 + 4 = 5`, `boxSum 1 1 2 = 4`, `boxSum 1 1 1 = 2 + 2 = 4`, and
`5·4 = 20 > 16 = 4·4`.  This is a CONSTRUCTIVE refutation of any unconditional claim. -/

/-- `(a·b).eqv (a'·b')` from `a ≃ a'`, `b ≃ b'` (local congruence). -/
private theorem mul_eqv_both' {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

/-- **THE FALSITY WITNESS.**  The `N = 1`, `w = 1` box log-concavity FAILS:

    ¬ (boxSum 1 1 0 · boxSum 1 1 2  ≤  boxSum 1 1 1 · boxSum 1 1 1)    (20 ≰ 16).

A constructive counterexample refuting the unconditional `∀ s, ∀ w∈[0,1]` claim: the
truncation at `N = 1` clips the convolution support and the cross-difference goes
negative at the weak-coupling boundary `w = 1`.  Hence the strong-coupling hypothesis
in `FusionConvLogConcaveCore` is NECESSARY, not decorative. -/
theorem boxSum1_logConcave_FALSE_at_one :
    ¬ (boxSum (1 : Q') 1 0 * boxSum (1 : Q') 1 2
        ≤ boxSum (1 : Q') 1 1 * boxSum (1 : Q') 1 1) := by
  intro h
  have hc : (coeffW (1 : Q') 1).eqv (2 : Q') := by
    show (dimQ 1 * qpow (1 : Q') (c4 1)).eqv (2 : Q'); decide
  have hL : (boxSum (1 : Q') 1 0 * boxSum (1 : Q') 1 2).eqv (20 : Q') := by
    refine Q'.eqv_trans _ _ _ (mul_eqv_both' (boxSum1_zero 1) (boxSum1_two 1)) ?_
    refine Q'.eqv_trans _ _ _
      (mul_eqv_both' (Q'.add_eqv_congr_left 1 _ _ (mul_eqv_both' hc hc)) (mul_eqv_both' hc hc)) ?_
    decide
  have hR : (boxSum (1 : Q') 1 1 * boxSum (1 : Q') 1 1).eqv (16 : Q') := by
    refine Q'.eqv_trans _ _ _ (mul_eqv_both' (boxSum1_one 1) (boxSum1_one 1)) ?_
    refine Q'.eqv_trans _ _ _
      (mul_eqv_both' (Q'.add_eqv_congr' hc hc) (Q'.add_eqv_congr' hc hc)) ?_
    decide
  have h20 : (20 : Q') ≤ (16 : Q') :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hR))
  exact absurd h20 (by decide)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, pure `Q'`/`Nat`):
  * `fusionOK_self_zero` / `fusionInd_self_zero` / `box_channel_pos` — the non-empty
    `(s,0)` Clebsch channel carries strictly-positive mass.
  * `bondMovedCoeff_p2_pos` — FUSED-TOWER POSITIVITY at EVERY mode `s ≤ N` (`g_s > 0`).
  * `logConcaveCross` / `logConcaveCross_eq_boxDiff` / `bondMovedCoeff_logConcave_of_core`
    — the log-concavity cross-difference, its rewrite into the closed Clebsch box
    double-sum form, and the sorry-free REDUCTION of `g_{s+1}² ≥ g_s·g_{s+2}` to the box
    core.
  * `boxSum1_zero` / `boxSum1_one` / `boxSum1_two` — the EXACT closed `Q'` values of the
    `N = 1` box sums (`1+c²`, `c+c`, `c²`, `c = coeffW w 1`).
  * `box1_poly_ineq` / `boxSum1_logConcave` — the `N = 1` log-concavity
    `B_0·B_2 ≤ B_1²` under `c·c ≤ 3`, via the pure-`Q'` polynomial inequality
    `(1+c²)c² ≤ (c+c)²`.
  * `coeffW1_le_one_of_strong` / `coeffW1_sq_le_three_of_strong` /
    `boxSum1_logConcave_strong` — the strong-coupling regime `w ≤ 1/2` discharges the
    hypothesis (`coeffW w 1 ≤ 1`), giving the `N = 1` log-concavity unconditionally there.
  * `fusionConvLogConcaveCore_N1` — INHABITS the box core at `N = 1` (all modes: `s = 0`
    by `boxSum1_logConcave`; `s ≥ 1` degenerately, since `boxSum w 1 (s+2) ≃ 0`).
  * `boxSum1_logConcave_FALSE_at_one` — the FALSITY WITNESS: `¬ (B_0·B_2 ≤ B_1²)` at
    `N = 1`, `w = 1` (`20 ≰ 16`), a constructive refutation of the unconditional claim.

NAMED OPEN (general `N`):
  * `FusionConvLogConcaveCore` — the box log-concavity for general `N` UNDER the
    strong-coupling hypothesis.  Inhabited at `N = 1`; general `N` open.  HONESTY: this
    is NOT the classical "convolution preserves log-concavity" (FALSE here on two counts
    — the truncation at `N` breaks it for `w → 1`, witnessed by
    `boxSum1_logConcave_FALSE_at_one`; and SU(2) fusion does NOT preserve log-concavity
    for GENERIC log-concave inputs).  The genuine general-`N` content is the
    heat-kernel-specific `(r,d)` Gaussian-theta local-CLT (`FusionRDFactor`), NOT a
    finite rational inequality.

HONEST VERDICT.  This proves the fused-tower positivity; the sorry-free reduction of the
log-concavity to the box core; the `N = 1` case EXACTLY (closed box values + a clean
polynomial inequality), with the strong-coupling `w ≤ 1/2` corollary and the core
inhabited at `N = 1`; AND a constructive REFUTATION of the prior unconditional claim.
It CORRECTS the false premise that this is the classical convolution-log-concavity: the
SU(2) fusion does not preserve log-concavity for generic inputs, and the truncation
breaks it for `w → 1`, so the general-`N` statement is heat-kernel-specific (the `(r,d)`
local-CLT), NOT a finite combinatorial Cauchy–Binet.  Log-concavity is a STRUCTURAL
sub-fact: necessary, NOT sufficient, for the sharp dominance local CLT.  This is NOT a
4D Yang–Mills mass gap. -/

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
#print axioms YMGap.Continuum.SelfFusionLogConcave.boxSum1_zero
#print axioms YMGap.Continuum.SelfFusionLogConcave.boxSum1_one
#print axioms YMGap.Continuum.SelfFusionLogConcave.boxSum1_two
#print axioms YMGap.Continuum.SelfFusionLogConcave.box1_poly_ineq
#print axioms YMGap.Continuum.SelfFusionLogConcave.boxSum1_logConcave
#print axioms YMGap.Continuum.SelfFusionLogConcave.coeffW1_le_one_of_strong
#print axioms YMGap.Continuum.SelfFusionLogConcave.coeffW1_sq_le_three_of_strong
#print axioms YMGap.Continuum.SelfFusionLogConcave.boxSum1_logConcave_strong
#print axioms YMGap.Continuum.SelfFusionLogConcave.fusionConvLogConcaveCore_N1
#print axioms YMGap.Continuum.SelfFusionLogConcave.boxSum1_logConcave_FALSE_at_one
