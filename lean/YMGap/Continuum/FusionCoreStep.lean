/-
Track A / R2 -- Fusion `CoreStep` local-CLT node: Rounds A-K (consolidated).

This module is the MERGE of the former per-round files
`FusionCoreStepRoundA.lean` ... `FusionCoreStepRoundK.lean` into a single,
clearly-sectioned file (reviewer-navigability consolidation of `Continuum/`).
Every declaration, docstring, and `#print axioms` gate from the original
eleven files is preserved verbatim; each round keeps its own namespace
`YMGap.Continuum.FusionCoreStepRound{A..K}`, so all downstream references
resolve unchanged. The rounds were a strictly linear dependency chain
A -> B -> ... -> K; they are concatenated here in that same order, so every
later round sees the earlier rounds exactly as before.

Rounds L and M are NOT included here: `FusionCoreStepRoundL` depends on
`AutoconvGershgorin`, which depends (via `LocalCLTSteepestDescent`) on
`FusionCoreStepRoundJ`. Folding L/M into this module would create an import
cycle merged -> AutoconvGershgorin -> LocalCLTSteepestDescent -> merged, so they
live in the sibling `FusionCoreStepLM.lean`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, and `decide` only on closed
concrete-rational / finite-index facts.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreInduction
import YMGap.Continuum.FusionLogConcave
import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.FusionGenFunction
import YMGap.Continuum.FusionResidualBound


/-! ===========================================================================
    ## Round A  (was `FusionCoreStepRoundA.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round A of the fusion `CoreStep` local-CLT node.

# What this module settles (read first — load-bearing honesty)

The sibling `FusionCoreInduction` reduces the general-`N` box log-concavity core
`FusionConvLogConcaveCore` to a single per-step CROSS-TERM inequality `CoreStep N`
(its `step` field), via the PROVED reduction
`fusionConvLogConcaveCore_succ_of_coreStep : core N → CoreStep N → core (N+1)`.

ROUND-A FINDING (machine-checked).  `CoreStep N` is **UNSATISFIABLE for `N ≥ 2`** —
not merely unproven.  Its `step` inequality at `N = 2`, channel `s = 0`, strong
coupling `w = 1/2` is FALSE: this module proves the strict REVERSE inequality by
`decide` (`coreStep2_s0_FALSE_half`).  The reduction lemma is sound, but its
hypothesis can never be inhabited for `N ≥ 2`: the additive decomposition
`boxSum (N+1) ≃ boxSum N + Δ` splits the level-`(N+1)` Cauchy–Binet
`(A+a)(C+c) ≤ (B+b)²` into `A·C ≤ B²` (the level-`N` core) PLUS a cross-term, and
that split throws away the (large) `A·C ≤ B²` slack, demanding each isolated border
term be self-financing — which it is not.  Any attempt to "prove `CoreStep N`" is
therefore dead on arrival.

ROUND-A DELIVERABLE (green).  We BYPASS the lossy split and prove the actual target —
the DIRECT box Cauchy–Binet `boxSum N s · boxSum N (s+2) ≤ boxSum N (s+1)²` — at the
concrete strong-coupling value `w = 1/2`, lifting the inhabited core from `N = 2`
(`FusionCoreInduction.core_N2_half`) to `N = 3` and `N = 4`:

  * `boxSum3_tail`, `boxSum4_tail` — the mode tails (`a+b ≤ 2N` kills high modes).
  * `core_N3_half`, `core_N4_half` — `FusionConvLogConcaveCore {3,4} (1/2)` INHABITED
    unconditionally at `w = 1/2` (every channel a closed `Q'` `decide`; the tail by
    `boxSum{3,4}_tail`).  This is the genuine `N = 2 → 3 → 4` push of the box core,
    done DIRECTLY (never through the false `CoreStep`).
  * `s1Dom_N3_half`, `s1Dom_N4_half` — wired through `FusionLogConcave.s1Dominance_of_p2`
    to `S1Dominance {3,4} (1/2) 2`.

ROUND-A REFRAMING (the corrected uniform residual).  The honest uniform-in-`N` target
that REPLACES `CoreStep` is the DIRECT box Cauchy–Binet for ALL `N` at once, packaged
as `UniformBoxLogConcave w`.  `coreOfUniform` shows a single `UniformBoxLogConcave`
witness yields `FusionConvLogConcaveCore N` for EVERY `N` (hence `S1Dominance N w 2`
for every `N` via `s1DominanceOfUniform`).  This is the sharp, satisfiable residual:
inhabited "pointwise so far" at `N = 0,1,2,3,4` (`w = 1/2`); the open content is its
inhabitation for ALL `N` simultaneously — the heat-kernel `(r,d)` local-CLT, exactly
as documented in `SelfFusionLogConcave`.

This is NOT a 4D Yang–Mills mass gap; it is the honest settling of the `CoreStep`
node — a machine-checked refutation of the additive per-step form, the direct
Cauchy–Binet core pushed two more levels, and the corrected uniform residual named.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, and `decide` only on closed
concrete-rational / finite-index facts.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundA

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreInduction

/-- The concrete strong-coupling value `w = 1/2`. -/
abbrev wH : Q' := Q'.mkPos 1 2 (by decide)

/-! ## 1. The machine-checked refutation of the additive `CoreStep`

`CoreStep N` (`FusionCoreInduction.CoreStep`) demands, per channel `s`, with
`A = boxSum N s`, `B = boxSum N (s+1)`, `C = boxSum N (s+2)`, `a = Δ s`, `b = Δ (s+1)`,
`c = Δ (s+2)` (`Δ = boxSumDelta N`):

    A·c + (a·C + a·c)  ≤  (B·b + B·b) + b·b.

We prove the strict REVERSE at `N = 2`, `s = 0`, `w = 1/2`, refuting the per-step form
outright. -/

/-- **`CoreStep 2` channel `s = 0` is FALSE at `w = 1/2`.**  The additive per-step
cross-term inequality does not hold: the left side strictly exceeds the right.  A
closed `Q'` `decide` — the load-bearing confirmation that `CoreStep N` is
UNSATISFIABLE for `N ≥ 2`, so the `core N → CoreStep N → core (N+1)` route (sound as a
reduction) can never have its hypothesis inhabited. -/
theorem coreStep2_s0_FALSE_half :
    ¬ ( boxSum wH 2 0 * boxSumDelta wH 2 (0 + 2)
          + (boxSumDelta wH 2 0 * boxSum wH 2 (0 + 2)
             + boxSumDelta wH 2 0 * boxSumDelta wH 2 (0 + 2))
        ≤ (boxSum wH 2 (0 + 1) * boxSumDelta wH 2 (0 + 1)
           + boxSum wH 2 (0 + 1) * boxSumDelta wH 2 (0 + 1))
          + boxSumDelta wH 2 (0 + 1) * boxSumDelta wH 2 (0 + 1) ) := by decide

/-- **No `CoreStep 2` witness exists at `w = 1/2`.**  Immediate from
`coreStep2_s0_FALSE_half`: any `CoreStep 2 wH` would discharge channel `s = 0`,
contradicting the proven strict reverse. -/
theorem no_coreStep2_half : (CoreStep 2 wH) → False :=
  fun cs => coreStep2_s0_FALSE_half (cs.step 0)

/-! ## 2. Box-sum mode tails — `a + b ≤ 2N` kills the high modes -/

/-- **`boxSum w 3 (k+7) ≃ 0`** — no `(a,b) ≤ 3` reaches mode `s = k+7` (`a+b ≤ 6`). -/
theorem boxSum3_tail (w : Q') (k : Nat) : (boxSum w 3 (k + 7)).eqv 0 := by
  unfold boxSum
  refine fsum_zero_below (3 + 1) (fun a ha => ?_)
  refine fsum_zero_below (3 + 1) (fun b hb => ?_)
  have hind : fusionInd a b (k + 7) = (0 : Q') := by
    unfold fusionInd
    have hok : fusionOK a b (k + 7) = false := by
      rw [fusionOK_eq_false_iff]; rintro ⟨_, h2, _⟩; omega
    rw [hok]; rfl
  rw [hind]; exact Q'.zero_mul_eqv _

/-- **`boxSum w 4 (k+9) ≃ 0`** — no `(a,b) ≤ 4` reaches mode `s = k+9` (`a+b ≤ 8`). -/
theorem boxSum4_tail (w : Q') (k : Nat) : (boxSum w 4 (k + 9)).eqv 0 := by
  unfold boxSum
  refine fsum_zero_below (4 + 1) (fun a ha => ?_)
  refine fsum_zero_below (4 + 1) (fun b hb => ?_)
  have hind : fusionInd a b (k + 9) = (0 : Q') := by
    unfold fusionInd
    have hok : fusionOK a b (k + 9) = false := by
      rw [fusionOK_eq_false_iff]; rintro ⟨_, h2, _⟩; omega
    rw [hok]; rfl
  rw [hind]; exact Q'.zero_mul_eqv _

/-- The degenerate Cauchy–Binet tail at `N = 3`: for `s = k+5`, the right factor
`boxSum 3 (s+2) ≃ 0`, so the cross-product is `≤` any square. -/
private theorem cauchyBinet_tail3 {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    boxSum w 3 (k + 5) * boxSum w 3 (k + 5 + 2)
      ≤ boxSum w 3 (k + 5 + 1) * boxSum w 3 (k + 5 + 1) := by
  have hz : (boxSum w 3 (k + 5 + 2)).eqv 0 := boxSum3_tail w k
  have hLHS0 : (boxSum w 3 (k + 5) * boxSum w 3 (k + 5 + 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (q_mul_zero _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS0)
    (Q'.mul_nonneg _ _ (boxSum_nonneg hw0 3 (k + 5 + 1)) (boxSum_nonneg hw0 3 (k + 5 + 1)))

/-- The degenerate Cauchy–Binet tail at `N = 4`: for `s = k+7`, the right factor
`boxSum 4 (s+2) ≃ 0`. -/
private theorem cauchyBinet_tail4 {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    boxSum w 4 (k + 7) * boxSum w 4 (k + 7 + 2)
      ≤ boxSum w 4 (k + 7 + 1) * boxSum w 4 (k + 7 + 1) := by
  have hz : (boxSum w 4 (k + 7 + 2)).eqv 0 := boxSum4_tail w k
  have hLHS0 : (boxSum w 4 (k + 7) * boxSum w 4 (k + 7 + 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (q_mul_zero _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS0)
    (Q'.mul_nonneg _ _ (boxSum_nonneg hw0 4 (k + 7 + 1)) (boxSum_nonneg hw0 4 (k + 7 + 1)))

/-! ## 3. The DIRECT box Cauchy–Binet core, lifted to `N = 3` and `N = 4` (`w = 1/2`) -/

/-- **`core_N3_half` — `FusionConvLogConcaveCore 3 (1/2)` INHABITED unconditionally at
the strong-coupling value `w = 1/2`.**  Every excited channel `s = 0,…,4` is a closed
`Q'` computation (`decide`); the high modes `s ≥ 5` are degenerate (`boxSum3_tail`).
This is the genuine direct lift of the box core past `core_N2_half`, BYPASSING the
unsatisfiable additive `CoreStep`. -/
def core_N3_half : FusionConvLogConcaveCore 3 wH (by decide) (by decide) where
  strongCoupling := by decide
  cauchyBinet := by
    intro s
    match s with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | (k + 5) => exact cauchyBinet_tail3 (by decide) k

/-- **`core_N4_half` — `FusionConvLogConcaveCore 4 (1/2)` INHABITED at `w = 1/2`.**
Further evidence: channels `s = 0,…,6` by `decide`; `s ≥ 7` by `boxSum4_tail`. -/
def core_N4_half : FusionConvLogConcaveCore 4 wH (by decide) (by decide) where
  strongCoupling := by decide
  cauchyBinet := by
    intro s
    match s with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | (k + 7) => exact cauchyBinet_tail4 (by decide) k

/-! ## 4. Wiring to `S1Dominance` at `w = 1/2` -/

/-- The first-excited edge `bmc 2 ≤ bmc 1` at `N = 3`, `w = 1/2` (`decide`). -/
theorem edge3_half : bondMovedCoeff 3 wH 2 2 ≤ bondMovedCoeff 3 wH 2 1 := by decide

/-- The first-excited edge `bmc 2 ≤ bmc 1` at `N = 4`, `w = 1/2` (`decide`). -/
theorem edge4_half : bondMovedCoeff 4 wH 2 2 ≤ bondMovedCoeff 4 wH 2 1 := by decide

/-- **`s1Dom_N3_half` — `S1Dominance 3 (1/2) 2`, wired from `core_N3_half`.** -/
def s1Dom_N3_half : YMGap.Continuum.S1Dominance.S1Dominance 3 wH 2 :=
  YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2 (by decide) core_N3_half edge3_half

/-- **`s1Dom_N4_half` — `S1Dominance 4 (1/2) 2`, wired from `core_N4_half`.** -/
def s1Dom_N4_half : YMGap.Continuum.S1Dominance.S1Dominance 4 wH 2 :=
  YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2 (by decide) core_N4_half edge4_half

/-! ## 5. The CORRECTED uniform residual — the direct box Cauchy–Binet for ALL `N`

The honest replacement for the (unsatisfiable) additive `CoreStep`: package the DIRECT
box log-concavity `boxSum N s · boxSum N (s+2) ≤ boxSum N (s+1)²` for ALL `N` and `s` at
once.  Unlike `CoreStep`, this keeps the level-`N` Cauchy–Binet slack attached to the
dominant diagonal terms — it is the satisfiable target, inhabited pointwise at every
`N` checked so far. -/

/-- **`UniformBoxLogConcave w`** — the corrected uniform-in-`N` residual: the strong
coupling hypothesis plus the DIRECT box Cauchy–Binet for every truncation `N` and mode
`s`.  (Replaces `CoreStep`, which is unsatisfiable for `N ≥ 2`.) -/
structure UniformBoxLogConcave (w : Q') : Type where
  /-- The strong-coupling hypothesis (`c² ≤ 3`, `c = coeffW w 1`; holds for `w ≤ 1/2`). -/
  strongCoupling : coeffW w 1 * coeffW w 1 ≤ (3 : Q')
  /-- The direct box log-concavity, uniformly in `N` and `s`. -/
  cauchyBinet : ∀ N s,
    boxSum w N s * boxSum w N (s + 2) ≤ boxSum w N (s + 1) * boxSum w N (s + 1)

/-- **`coreOfUniform` — a single `UniformBoxLogConcave` witness yields the box core for
EVERY `N`.**  This is why the uniform residual is the right object: inhabit it once and
the entire `N`-tower of `FusionConvLogConcaveCore` follows (and then `S1Dominance N w 2`
for every `N`, below). -/
def coreOfUniform {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (u : UniformBoxLogConcave w) (N : Nat) :
    FusionConvLogConcaveCore N w hw0 hw1 where
  strongCoupling := u.strongCoupling
  cauchyBinet := fun s => u.cauchyBinet N s

/-- **`s1DominanceOfUniform` — `S1Dominance N w 2` for EVERY `N` from one
`UniformBoxLogConcave` witness plus the per-`N` edge inputs.**  The structural payoff of
the corrected residual: all-`N` first-excited dominance reduces to ONE uniform box
log-concavity datum (and the elementary edge comparisons). -/
def s1DominanceOfUniform {w : Q'} (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (u : UniformBoxLogConcave w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2 hw
    (coreOfUniform (Q'.le_of_lt hw) hw1 u N) hedge

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `coreStep2_s0_FALSE_half`, `no_coreStep2_half` — the machine-checked REFUTATION of
    the additive `CoreStep` at `N = 2` (`w = 1/2`): the per-step cross-term inequality
    is FALSE, so `CoreStep N` is UNSATISFIABLE for `N ≥ 2`.
  * `boxSum3_tail`, `boxSum4_tail` — the mode tails.
  * `core_N3_half`, `core_N4_half` — the DIRECT box Cauchy–Binet core INHABITED at
    `w = 1/2` for `N = 3` and `N = 4` (the genuine `N = 2 → 3 → 4` lift, bypassing the
    false `CoreStep`).
  * `edge3_half`, `edge4_half`, `s1Dom_N3_half`, `s1Dom_N4_half` — wired to
    `S1Dominance {3,4} (1/2) 2`.
  * `UniformBoxLogConcave`, `coreOfUniform`, `s1DominanceOfUniform` — the CORRECTED
    uniform-in-`N` residual (direct box log-concavity for all `N`) and the proof that a
    single witness yields the whole `N`-tower of cores and `S1Dominance`.

NAMED OPEN:
  * Inhabitation of `UniformBoxLogConcave w` for the symbolic strong-coupling family
    (`0 < w ≤ 1/2`) — equivalently the direct box Cauchy–Binet at general `N`.  This is
    the heat-kernel-specific `(r,d)` Gaussian local-CLT (NOT a finite rational
    inequality, NOT the generic "convolution preserves log-concavity"; see
    `SelfFusionLogConcave`).  It is inhabited pointwise at `N = 0,1,2` (symbolic, via
    `FusionCoreInduction.fusionConvLogConcaveCore_N2`) and at `N = 3,4` (`w = 1/2`,
    this module); the open content is the all-`N`, symbolic-`w` statement.

HONEST VERDICT.  The `CoreStep` node is SETTLED in Round A: the additive per-step form
is refuted by machine check (dead, not merely open), the DIRECT box Cauchy–Binet core
is pushed two further levels (`N = 3, 4` at `w = 1/2`), and the corrected uniform
residual `UniformBoxLogConcave` is named, shown to imply the entire `N`-tower, and
located precisely as the heat-kernel local-CLT.  This is a structural advance on one
box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundA

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundA.coreStep2_s0_FALSE_half
#print axioms YMGap.Continuum.FusionCoreStepRoundA.no_coreStep2_half
#print axioms YMGap.Continuum.FusionCoreStepRoundA.boxSum3_tail
#print axioms YMGap.Continuum.FusionCoreStepRoundA.boxSum4_tail
#print axioms YMGap.Continuum.FusionCoreStepRoundA.core_N3_half
#print axioms YMGap.Continuum.FusionCoreStepRoundA.core_N4_half
#print axioms YMGap.Continuum.FusionCoreStepRoundA.edge3_half
#print axioms YMGap.Continuum.FusionCoreStepRoundA.edge4_half
#print axioms YMGap.Continuum.FusionCoreStepRoundA.s1Dom_N3_half
#print axioms YMGap.Continuum.FusionCoreStepRoundA.s1Dom_N4_half
#print axioms YMGap.Continuum.FusionCoreStepRoundA.coreOfUniform
#print axioms YMGap.Continuum.FusionCoreStepRoundA.s1DominanceOfUniform


/-! ===========================================================================
    ## Round B  (was `FusionCoreStepRoundB.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round B of the fusion box log-concavity node.

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundA` proved the DIRECT box Cauchy–Binet
`boxSum N s · boxSum N (s+2) ≤ boxSum N (s+1)²` at `w = 1/2` for `N = 3, 4`, named the
unsatisfiability of the additive `CoreStep`, and packaged the corrected uniform-in-`N`
residual `UniformBoxLogConcave w`.  Round B pushes that data and refines the residual:

ROUND-B DELIVERABLE 1 (concrete, green).  The direct box Cauchy–Binet core lifted TWO
further levels at `w = 1/2`:
  * `boxSum5_tail`, `boxSum6_tail` — the mode tails (`a + b ≤ 2N` kills high modes).
  * `core_N5_half`, `core_N6_half` — `FusionConvLogConcaveCore {5,6} (1/2)` INHABITED
    unconditionally at `w = 1/2` (every excited channel a closed `Q'` `decide`; the
    tails by `boxSum{5,6}_tail`).  The genuine `N = 4 → 5 → 6` push of the box core,
    done DIRECTLY (never through the false `CoreStep`).
  * `s1Dom_N5_half`, `s1Dom_N6_half` — wired to `S1Dominance {5,6} (1/2) 2`.

ROUND-B DELIVERABLE 2 (structural, general-`N`, green).  THE CAUCHY–BINET / TOTAL-
POSITIVITY STRUCTURE of the box log-concavity, made explicit and uniform in `N`:
  * `boxSum_mul_eq_quad` — the product of two box sums is the FULL quadruple Clebsch
    sum `Σ_{a,a',b,b'} K(a,b,s)·K(a',b',t)` (`K(a,b,s) = fusionInd a b s · c_a c_b`).
    Pure `(Σ)(Σ) = ΣΣ` distributivity, axiom-clean, every `N`.
  * `quadDiff` / `boxDiff_eq_quadDiff` — the box cross-difference
    `boxSum(s+1)² − boxSum(s)·boxSum(s+2)` expanded as the SINGLE symmetric quadruple
    sum of the Cauchy–Binet kernel `W_s(a,b,a',b') = fusionInd a b (s+1)·fusionInd a' b'
    (s+1) − fusionInd a b s·fusionInd a' b' (s+2)`, weighted by `c_a c_b c_{a'} c_{b'}`.
  * `UniformBoxQuadCertificate` / `uniformOfQuad` — the SHARPER named residual: the
    aggregate nonnegativity of `quadDiff` (the Cauchy–Binet quadruple form) for all `N`,
    `s`, which IMPLIES `UniformBoxLogConcave` and hence the whole `N`-tower of cores and
    `S1Dominance`.  This is the exact TP₂ / Karlin total-positivity content.

ROUND-B DELIVERABLE 3 (the Gaussian magnitude input for the symbolic route).
  * `coeffW1_le_quarter` — `coeffW w 1 ≤ 1/4` on `0 ≤ w ≤ 1/2` (`c₁ = 2w³ ≤ 2·(1/8)`).
    This is the Gaussian magnitude fact BEYOND log-concavity that the symbolic
    channel certificates need (the `c₁ ≤ 1/4` and the super-geometric ratio decay are
    exactly where generic-log-concave counterexamples bite); proved here for reuse.

# HONESTY — what is NOT closed

The certificate `quadDiff ≥ 0` is NOT pointwise (per-summand) true: the Cauchy–Binet
kernel `W_s` is NOT pointwise `≥ 0`, and generic (even Pólya-frequency) log-concave
weights make the truncated box sum FAIL log-concavity.  The certificate MUST consume the
Gaussian magnitude decay of `c_i = (i+1) w^{i(i+2)}` (hence `coeffW1_le_quarter` and the
ratio decay).  So `quadDiff ≥ 0` for all `N` is the genuine open content — the heat-
kernel `(r,d)` local-CLT — NOT a finite rational inequality.  It is inhabited POINTWISE
at `N = 0,…,6` (`w = 1/2`, this module and `FusionCoreStepRoundA`); the open content is
the all-`N`, symbolic-`w` statement.  The symbolic `N = 3, 4` per-channel SOS
certificates remain NAMED-OPEN; the magnitude input they require is now available.

This is NOT a 4D Yang–Mills mass gap; it is the honest two-level push of the box core
and the explicit Cauchy–Binet/total-positivity refinement of the uniform residual.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the proved `fsum` algebra, structural inductions, and
`decide` only on closed concrete-rational / finite-index facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level.
-/


namespace YMGap.Continuum.FusionCoreStepRoundB

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundA

/-! ## 1. Box-sum mode tails at `N = 5, 6` -/

/-- **`boxSum w 5 (k+11) ≃ 0`** — no `(a,b) ≤ 5` reaches mode `s = k+11` (`a+b ≤ 10`). -/
theorem boxSum5_tail (w : Q') (k : Nat) : (boxSum w 5 (k + 11)).eqv 0 := by
  unfold boxSum
  refine fsum_zero_below (5 + 1) (fun a ha => ?_)
  refine fsum_zero_below (5 + 1) (fun b hb => ?_)
  have hind : fusionInd a b (k + 11) = (0 : Q') := by
    unfold fusionInd
    have hok : fusionOK a b (k + 11) = false := by
      rw [fusionOK_eq_false_iff]; rintro ⟨_, h2, _⟩; omega
    rw [hok]; rfl
  rw [hind]; exact Q'.zero_mul_eqv _

/-- **`boxSum w 6 (k+13) ≃ 0`** — no `(a,b) ≤ 6` reaches mode `s = k+13` (`a+b ≤ 12`). -/
theorem boxSum6_tail (w : Q') (k : Nat) : (boxSum w 6 (k + 13)).eqv 0 := by
  unfold boxSum
  refine fsum_zero_below (6 + 1) (fun a ha => ?_)
  refine fsum_zero_below (6 + 1) (fun b hb => ?_)
  have hind : fusionInd a b (k + 13) = (0 : Q') := by
    unfold fusionInd
    have hok : fusionOK a b (k + 13) = false := by
      rw [fusionOK_eq_false_iff]; rintro ⟨_, h2, _⟩; omega
    rw [hok]; rfl
  rw [hind]; exact Q'.zero_mul_eqv _

/-- The degenerate Cauchy–Binet tail at `N = 5`: for `s = k+9`, the right factor
`boxSum 5 (s+2) ≃ 0`. -/
private theorem cauchyBinet_tail5 {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    boxSum w 5 (k + 9) * boxSum w 5 (k + 9 + 2)
      ≤ boxSum w 5 (k + 9 + 1) * boxSum w 5 (k + 9 + 1) := by
  have hz : (boxSum w 5 (k + 9 + 2)).eqv 0 := boxSum5_tail w k
  have hLHS0 : (boxSum w 5 (k + 9) * boxSum w 5 (k + 9 + 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (q_mul_zero _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS0)
    (Q'.mul_nonneg _ _ (boxSum_nonneg hw0 5 (k + 9 + 1)) (boxSum_nonneg hw0 5 (k + 9 + 1)))

/-- The degenerate Cauchy–Binet tail at `N = 6`: for `s = k+11`, the right factor
`boxSum 6 (s+2) ≃ 0`. -/
private theorem cauchyBinet_tail6 {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    boxSum w 6 (k + 11) * boxSum w 6 (k + 11 + 2)
      ≤ boxSum w 6 (k + 11 + 1) * boxSum w 6 (k + 11 + 1) := by
  have hz : (boxSum w 6 (k + 11 + 2)).eqv 0 := boxSum6_tail w k
  have hLHS0 : (boxSum w 6 (k + 11) * boxSum w 6 (k + 11 + 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (q_mul_zero _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS0)
    (Q'.mul_nonneg _ _ (boxSum_nonneg hw0 6 (k + 11 + 1)) (boxSum_nonneg hw0 6 (k + 11 + 1)))

/-! ## 2. The DIRECT box Cauchy–Binet core, lifted to `N = 5` and `N = 6` (`w = 1/2`) -/

/-- **`core_N5_half` — `FusionConvLogConcaveCore 5 (1/2)` INHABITED at `w = 1/2`.**
Excited channels `s = 0,…,8` by `decide`; the high modes `s ≥ 9` are degenerate
(`boxSum5_tail`).  The genuine direct lift of the box core past `core_N4_half`. -/
def core_N5_half : FusionConvLogConcaveCore 5 wH (by decide) (by decide) where
  strongCoupling := by decide
  cauchyBinet := by
    intro s
    match s with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | 8 => decide
    | (k + 9) => exact cauchyBinet_tail5 (by decide) k

/-- **`core_N6_half` — `FusionConvLogConcaveCore 6 (1/2)` INHABITED at `w = 1/2`.**
Excited channels `s = 0,…,10` by `decide`; `s ≥ 11` by `boxSum6_tail`. -/
def core_N6_half : FusionConvLogConcaveCore 6 wH (by decide) (by decide) where
  strongCoupling := by decide
  cauchyBinet := by
    intro s
    match s with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | 8 => decide
    | 9 => decide
    | 10 => decide
    | (k + 11) => exact cauchyBinet_tail6 (by decide) k

/-! ## 3. Wiring to `S1Dominance` at `w = 1/2` -/

/-- The first-excited edge `bmc 2 ≤ bmc 1` at `N = 5`, `w = 1/2` (`decide`). -/
theorem edge5_half : bondMovedCoeff 5 wH 2 2 ≤ bondMovedCoeff 5 wH 2 1 := by decide

/-- The first-excited edge `bmc 2 ≤ bmc 1` at `N = 6`, `w = 1/2` (`decide`). -/
theorem edge6_half : bondMovedCoeff 6 wH 2 2 ≤ bondMovedCoeff 6 wH 2 1 := by decide

/-- **`s1Dom_N5_half` — `S1Dominance 5 (1/2) 2`, wired from `core_N5_half`.** -/
def s1Dom_N5_half : YMGap.Continuum.S1Dominance.S1Dominance 5 wH 2 :=
  YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2 (by decide) core_N5_half edge5_half

/-- **`s1Dom_N6_half` — `S1Dominance 6 (1/2) 2`, wired from `core_N6_half`.** -/
def s1Dom_N6_half : YMGap.Continuum.S1Dominance.S1Dominance 6 wH 2 :=
  YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2 (by decide) core_N6_half edge6_half

/-! ## 4. The Cauchy–Binet / total-positivity structure (general `N`, axiom-clean)

The box log-concavity is, modally, the TP₂ minor positivity of the theta-weighted
Clebsch kernel.  We make this explicit and uniform in `N`: expand the box cross-
difference as the FULL symmetric quadruple sum of the Cauchy–Binet kernel.  This is the
structural backbone of the LGV/total-positivity route — pure `(Σ)(Σ)=ΣΣ` algebra. -/

/-- The single Clebsch summand `K(a,b,s) = fusionInd a b s · (c_a · c_b)`. -/
def boxKer (w : Q') (s a b : Nat) : Q' := fusionInd a b s * (coeffW w a * coeffW w b)

/-- `boxSum` is the double `fsum` of `boxKer` (definitional). -/
theorem boxSum_eq_ker (w : Q') (N s : Nat) :
    boxSum w N s = fsum (fun a => fsum (fun b => boxKer w s a b) (N + 1)) (N + 1) := rfl

/-- **Single-sum product law** `(Σ f)(Σ g) ≃ Σᵢ Σⱼ f i · g j`. -/
theorem fsum_mul_fsum (f g : Nat → Q') (m n : Nat) :
    (fsum f m * fsum g n).eqv (fsum (fun i => fsum (fun j => f i * g j) n) m) :=
  Q'.eqv_trans _ _ _ (fsum_mul_const f (fsum g n) m)
    (fsum_eqv_congr _ _ (fun i => fsum_const_mul (f i) g n) m)

/-- The Cauchy–Binet quadruple sum `Σ_{a,a',b,b'} K(a,b,s)·K(a',b',t)`. -/
def quadProd (w : Q') (N s t : Nat) : Q' :=
  fsum (fun a => fsum (fun a' => fsum (fun b => fsum (fun b' =>
    boxKer w s a b * boxKer w t a' b') (N + 1)) (N + 1)) (N + 1)) (N + 1)

/-- **The product of two box sums is the Cauchy–Binet quadruple sum.**
`boxSum N s · boxSum N t ≃ quadProd N s t`, uniformly in `N`. -/
theorem boxSum_mul_eq_quad (w : Q') (N s t : Nat) :
    (boxSum w N s * boxSum w N t).eqv (quadProd w N s t) := by
  -- Outer product over `a, a'`.
  have h1 :
      (boxSum w N s * boxSum w N t).eqv
        (fsum (fun a => fsum (fun a' =>
          fsum (fun b => boxKer w s a b) (N + 1) * fsum (fun b' => boxKer w t a' b') (N + 1))
          (N + 1)) (N + 1)) :=
    fsum_mul_fsum (fun a => fsum (fun b => boxKer w s a b) (N + 1))
      (fun a' => fsum (fun b' => boxKer w t a' b') (N + 1)) (N + 1) (N + 1)
  -- Inner product over `b, b'`, threaded through the two outer sums.
  refine Q'.eqv_trans _ _ _ h1 ?_
  refine fsum_eqv_congr _ _ (fun a => ?_) (N + 1)
  refine fsum_eqv_congr _ _ (fun a' => ?_) (N + 1)
  exact fsum_mul_fsum (fun b => boxKer w s a b) (fun b' => boxKer w t a' b') (N + 1) (N + 1)

/-! ### 4a. Generic quadruple-sum `add`/`neg` combinators -/

/-- Depth-1 reverse-add `Σ f + Σ g ≃ Σ (f + g)`. -/
private theorem q1_add (f g : Nat → Q') (n : Nat) :
    (fsum f n + fsum g n).eqv (fsum (fun i => f i + g i) n) :=
  Q'.eqv_symm (fsum_add f g n)

/-- Depth-1 reverse-neg `-(Σ f) ≃ Σ (-f)`. -/
private theorem q1_neg (f : Nat → Q') (n : Nat) :
    (-(fsum f n)).eqv (fsum (fun i => -(f i)) n) :=
  Q'.eqv_symm (fsum_neg f n)

private theorem q2_add (F G : Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (F a) n) n + fsum (fun a => fsum (G a) n) n).eqv
      (fsum (fun a => fsum (fun b => F a b + G a b) n) n) :=
  Q'.eqv_trans _ _ _ (q1_add (fun a => fsum (F a) n) (fun a => fsum (G a) n) n)
    (fsum_eqv_congr _ _ (fun a => q1_add (F a) (G a) n) n)

private theorem q2_neg (F : Nat → Nat → Q') (n : Nat) :
    (-(fsum (fun a => fsum (F a) n) n)).eqv
      (fsum (fun a => fsum (fun b => -(F a b)) n) n) :=
  Q'.eqv_trans _ _ _ (q1_neg (fun a => fsum (F a) n) n)
    (fsum_eqv_congr _ _ (fun a => q1_neg (F a) n) n)

private theorem q3_add (F G : Nat → Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (fun b => fsum (F a b) n) n) n
      + fsum (fun a => fsum (fun b => fsum (G a b) n) n) n).eqv
      (fsum (fun a => fsum (fun b => fsum (fun c => F a b c + G a b c) n) n) n) :=
  Q'.eqv_trans _ _ _
    (q1_add (fun a => fsum (fun b => fsum (F a b) n) n)
      (fun a => fsum (fun b => fsum (G a b) n) n) n)
    (fsum_eqv_congr _ _ (fun a => q2_add (F a) (G a) n) n)

private theorem q3_neg (F : Nat → Nat → Nat → Q') (n : Nat) :
    (-(fsum (fun a => fsum (fun b => fsum (F a b) n) n) n)).eqv
      (fsum (fun a => fsum (fun b => fsum (fun c => -(F a b c)) n) n) n) :=
  Q'.eqv_trans _ _ _ (q1_neg (fun a => fsum (fun b => fsum (F a b) n) n) n)
    (fsum_eqv_congr _ _ (fun a => q2_neg (F a) n) n)

private theorem q4_add (F G : Nat → Nat → Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (fun b => fsum (fun c => fsum (F a b c) n) n) n) n
      + fsum (fun a => fsum (fun b => fsum (fun c => fsum (G a b c) n) n) n) n).eqv
      (fsum (fun a => fsum (fun b => fsum (fun c => fsum (fun d =>
        F a b c d + G a b c d) n) n) n) n) :=
  Q'.eqv_trans _ _ _
    (q1_add (fun a => fsum (fun b => fsum (fun c => fsum (F a b c) n) n) n)
      (fun a => fsum (fun b => fsum (fun c => fsum (G a b c) n) n) n) n)
    (fsum_eqv_congr _ _ (fun a => q3_add (F a) (G a) n) n)

private theorem q4_neg (F : Nat → Nat → Nat → Nat → Q') (n : Nat) :
    (-(fsum (fun a => fsum (fun b => fsum (fun c => fsum (F a b c) n) n) n) n)).eqv
      (fsum (fun a => fsum (fun b => fsum (fun c => fsum (fun d => -(F a b c d)) n) n) n) n) :=
  Q'.eqv_trans _ _ _
    (q1_neg (fun a => fsum (fun b => fsum (fun c => fsum (F a b c) n) n) n) n)
    (fsum_eqv_congr _ _ (fun a => q3_neg (F a) n) n)

/-! ### 4b. The box cross-difference as a single Cauchy–Binet quadruple sum -/

/-- The Cauchy–Binet kernel summand at channel `s`:
`K(a,b,s+1)·K(a',b',s+1) − K(a,b,s)·K(a',b',s+2)`. -/
def quadW (w : Q') (s a a' b b' : Nat) : Q' :=
  boxKer w (s + 1) a b * boxKer w (s + 1) a' b'
    + -(boxKer w s a b * boxKer w (s + 2) a' b')

/-- The Cauchy–Binet quadruple difference: the box cross-difference as ONE quadruple
sum of the kernel `quadW`. -/
def quadDiff (w : Q') (N s : Nat) : Q' :=
  fsum (fun a => fsum (fun a' => fsum (fun b => fsum (fun b' =>
    quadW w s a a' b b') (N + 1)) (N + 1)) (N + 1)) (N + 1)

/-- **`boxDiff_eq_quadDiff` — the box cross-difference IS the Cauchy–Binet quadruple
sum.**  `boxSum(s+1)² − boxSum(s)·boxSum(s+2) ≃ quadDiff N s`, uniformly in `N`.  This
is the explicit total-positivity form: log-concavity ⇔ nonnegativity of the weighted
`2×2` Cauchy–Binet minor sum. -/
theorem boxDiff_eq_quadDiff (w : Q') (N s : Nat) :
    (boxSum w N (s + 1) * boxSum w N (s + 1)
      + -(boxSum w N s * boxSum w N (s + 2))).eqv (quadDiff w N s) := by
  -- Expand both products as quadruple sums.
  have hP : (boxSum w N (s + 1) * boxSum w N (s + 1)).eqv (quadProd w N (s + 1) (s + 1)) :=
    boxSum_mul_eq_quad w N (s + 1) (s + 1)
  have hN : (boxSum w N s * boxSum w N (s + 2)).eqv (quadProd w N s (s + 2)) :=
    boxSum_mul_eq_quad w N s (s + 2)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hP (Q'.neg_eqv_congr _ _ hN)) ?_
  -- Distribute the negation into the second quadruple sum.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (quadProd w N (s + 1) (s + 1)) _ _
      (q4_neg (fun a a' b => fun b' => boxKer w s a b * boxKer w (s + 2) a' b') (N + 1))) ?_
  -- Merge the two quadruple sums into one.
  exact q4_add
    (fun a a' b => fun b' => boxKer w (s + 1) a b * boxKer w (s + 1) a' b')
    (fun a a' b => fun b' => -(boxKer w s a b * boxKer w (s + 2) a' b')) (N + 1)

/-! ### 4c. The sharper uniform residual — aggregate Cauchy–Binet positivity -/

/-- **`UniformBoxQuadCertificate w`** — the SHARPER uniform-in-`N` residual: the
aggregate nonnegativity of the Cauchy–Binet quadruple difference for every truncation
`N` and channel `s`, plus the strong-coupling hypothesis.  This is the exact TP₂ /
Karlin total-positivity content of the box log-concavity.

HONESTY.  `quadDiff` is NOT a sum of nonnegative terms — the kernel `quadW` is not
pointwise `≥ 0` — so this residual genuinely requires the Gaussian magnitude decay of
`coeffW` (`coeffW1_le_quarter` and the super-geometric ratio decay), not log-concavity
of the inputs alone.  It is the same heat-kernel local-CLT content as
`UniformBoxLogConcave`, recast in the explicit Cauchy–Binet quadruple form. -/
structure UniformBoxQuadCertificate (w : Q') : Type where
  /-- The strong-coupling hypothesis (`c² ≤ 3`, `c = coeffW w 1`; holds for `w ≤ 1/2`). -/
  strongCoupling : coeffW w 1 * coeffW w 1 ≤ (3 : Q')
  /-- Aggregate nonnegativity of the Cauchy–Binet quadruple difference, for all `N`, `s`. -/
  quadNonneg : ∀ N s, (0 : Q') ≤ quadDiff w N s

/-- **`uniformOfQuad` — the Cauchy–Binet certificate IMPLIES the uniform box log-
concavity residual.**  Aggregate `quadDiff ≥ 0` transports across `boxDiff_eq_quadDiff`
to the box cross-difference, hence `boxSum(s)·boxSum(s+2) ≤ boxSum(s+1)²` for every `N`,
`s`.  A single `UniformBoxQuadCertificate` therefore yields the whole `N`-tower of
`FusionConvLogConcaveCore` (via `coreOfUniform`) and `S1Dominance` (via
`s1DominanceOfUniform`). -/
def uniformOfQuad {w : Q'} (cert : UniformBoxQuadCertificate w) : UniformBoxLogConcave w where
  strongCoupling := cert.strongCoupling
  cauchyBinet := fun N s => by
    have hD : (0 : Q') ≤ boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)) :=
      Q'.le_trans' _ _ _ (cert.quadNonneg N s)
        (Q'.ge_of_eqv (boxDiff_eq_quadDiff w N s))
    exact Q'.le_of_sub_nonneg hD

/-! ### 4d. Small-`N` evidence (`w = 1/2`): the certificate fires from the proved cores -/

/-- The Cauchy–Binet quadruple difference is nonnegative at `w = 1/2` for any `N`-core.
From `FusionConvLogConcaveCore N (1/2)` (`cauchyBinet` field), the box cross-difference
is `≥ 0`, and transports to `quadDiff` via `boxDiff_eq_quadDiff`.  Demonstrates the
sharper residual is satisfied wherever the box core is inhabited. -/
theorem quadDiff_nonneg_of_core {N : Nat}
    (core : FusionConvLogConcaveCore N wH (by decide) (by decide)) (s : Nat) :
    (0 : Q') ≤ quadDiff wH N s :=
  Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le (core.cauchyBinet s))
    (Q'.le_of_eqv (boxDiff_eq_quadDiff wH N s))

/-- Cauchy–Binet positivity witnessed at `N = 5`, `w = 1/2` (all channels), from
`core_N5_half`. -/
theorem quadDiff_nonneg_N5_half (s : Nat) : (0 : Q') ≤ quadDiff wH 5 s :=
  quadDiff_nonneg_of_core core_N5_half s

/-- Cauchy–Binet positivity witnessed at `N = 6`, `w = 1/2` (all channels), from
`core_N6_half`. -/
theorem quadDiff_nonneg_N6_half (s : Nat) : (0 : Q') ≤ quadDiff wH 6 s :=
  quadDiff_nonneg_of_core core_N6_half s

/-! ## 5. The Gaussian magnitude input for the symbolic route -/

/-- **`coeffW1_le_quarter` — `coeffW w 1 ≤ 1/4` on `0 ≤ w ≤ 1/2`.**  Since
`c₁ = coeffW w 1 = dimQ 1 · w^{C₄(1)} = 2·w³` and `w³ ≤ (1/2)³ = 1/8` (`qpow_mono`),
`c₁ ≤ 2·(1/8) = 1/4`.  This is the Gaussian magnitude fact BEYOND log-concavity that the
symbolic high-channel box certificates require (the regime where generic log-concave
counterexamples bite); proved here for reuse by the symbolic `N ≥ 3` certificates. -/
theorem coeffW1_le_quarter {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) :
    coeffW w 1 ≤ Q'.mkPos 1 4 (by decide) := by
  have hstep : coeffW w 1 ≤ dimQ 1 * qpow wH (c4 1) := by
    show dimQ 1 * qpow w (c4 1) ≤ dimQ 1 * qpow wH (c4 1)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono hw0 hw12 (c4 1)) (dimQ_nonneg 1)
  exact Q'.le_trans' _ _ _ hstep (by decide)

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `boxSum5_tail`, `boxSum6_tail` — the mode tails.
  * `core_N5_half`, `core_N6_half` — the DIRECT box Cauchy–Binet core INHABITED at
    `w = 1/2` for `N = 5` and `N = 6` (the genuine `N = 4 → 5 → 6` lift).
  * `edge5_half`, `edge6_half`, `s1Dom_N5_half`, `s1Dom_N6_half` — wired to
    `S1Dominance {5,6} (1/2) 2`.
  * `fsum_mul_fsum`, `boxSum_mul_eq_quad` — the product-of-box-sums = Cauchy–Binet
    quadruple sum (uniform in `N`).
  * `quadDiff`, `boxDiff_eq_quadDiff` — the box cross-difference as ONE symmetric
    quadruple sum of the Cauchy–Binet kernel `quadW` (the explicit TP₂ minor form).
  * `UniformBoxQuadCertificate`, `uniformOfQuad` — the sharper uniform residual
    (aggregate Cauchy–Binet positivity) and the proof that it implies
    `UniformBoxLogConcave` (hence the whole `N`-tower of cores and `S1Dominance`).
  * `quadDiff_nonneg_of_core`, `quadDiff_nonneg_N5_half`, `quadDiff_nonneg_N6_half` —
    the certificate is SATISFIED at `w = 1/2`, `N = 0,…,6` (small-`N` evidence).
  * `coeffW1_le_quarter` — the Gaussian magnitude input `c₁ ≤ 1/4` for the symbolic route.

NAMED OPEN:
  * Inhabitation of `UniformBoxQuadCertificate w` (equivalently `UniformBoxLogConcave w`)
    for the symbolic strong-coupling family `0 < w ≤ 1/2` — the aggregate Cauchy–Binet
    positivity `quadDiff ≥ 0` for ALL `N` and `s`.  This is NOT pointwise (the kernel
    `quadW` is not `≥ 0`); it requires the Gaussian magnitude decay (`coeffW1_le_quarter`
    + ratio decay), i.e. the heat-kernel `(r,d)` local-CLT, NOT a finite rational
    inequality.  Inhabited pointwise at `N = 0,…,6` (`w = 1/2`).
  * The symbolic `N = 3, 4` per-channel SOS certificates (the analogues of the proved
    `polyI0`/`polyI1`/`polyI2` at `N = 2`).  Their required Gaussian magnitude input
    `coeffW1_le_quarter` is now available; the high-channel certificates remain open.

HONEST VERDICT.  Round B pushes the direct box Cauchy–Binet core two further levels
(`N = 5, 6` at `w = 1/2`), makes the LGV/total-positivity structure of the box log-
concavity EXPLICIT and uniform in `N` (the box cross-difference IS a single weighted
Cauchy–Binet quadruple sum), and packages the sharper residual `UniformBoxQuadCertificate`
with the proof that it drives the whole `N`-tower — plus the Gaussian magnitude input
`coeffW1_le_quarter` for the symbolic route.  This is a structural advance on one box-
level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundB

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundB.boxSum5_tail
#print axioms YMGap.Continuum.FusionCoreStepRoundB.boxSum6_tail
#print axioms YMGap.Continuum.FusionCoreStepRoundB.core_N5_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.core_N6_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.edge5_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.edge6_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.s1Dom_N5_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.s1Dom_N6_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.fsum_mul_fsum
#print axioms YMGap.Continuum.FusionCoreStepRoundB.boxSum_mul_eq_quad
#print axioms YMGap.Continuum.FusionCoreStepRoundB.boxDiff_eq_quadDiff
#print axioms YMGap.Continuum.FusionCoreStepRoundB.uniformOfQuad
#print axioms YMGap.Continuum.FusionCoreStepRoundB.quadDiff_nonneg_of_core
#print axioms YMGap.Continuum.FusionCoreStepRoundB.quadDiff_nonneg_N5_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.quadDiff_nonneg_N6_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.coeffW1_le_quarter


/-! ===========================================================================
    ## Round C  (was `FusionCoreStepRoundC.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round C of the fusion box log-concavity node: the GAUSSIAN MAGNITUDE
ATOM, proved symbolically, and the honest reduction of the Cauchy–Binet quadruple
certificate to the single remaining (aggregate Gershgorin/TP₂) bookkeeping residual.

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundB` packaged the SHARP uniform-in-`N` residual
`UniformBoxQuadCertificate w` (aggregate nonnegativity `quadDiff ≥ 0` of the
Cauchy–Binet quadruple difference) and provided the WEAK Gaussian magnitude input
`coeffW1_le_quarter` (`c₁ ≤ 1/4`).  The header of Round B flags that the certificate is
NOT pointwise true and genuinely requires the Gaussian magnitude DECAY of `coeffW`,
strictly beyond the log-concavity `coeffW_logConcave` already in tree.  Round C supplies
that decay as a clean, SYMBOLIC, all-`s` atom and uses it to factor the certificate.

ROUND-C DELIVERABLE 1 (the missing magnitude atom — PROVED, symbolic, all `s`).
  * `coeffW_superLogConcave` — **super-log-concavity with a uniform factor-4 slack**:
    for `0 ≤ w ≤ 1/2` and EVERY `s`,
        coeffW w s · coeffW w (s+2)  ≤  (1/4) · (coeffW w (s+1) · coeffW w (s+1)).
    This is strictly stronger than `coeffW_logConcave` (which only gives the `≤ 1·`
    bound).  Proof: the EXACT heat-kernel log-concavity identity
    `heatNorm(s)·heatNorm(s+2) ≃ w²·heatNorm(s+1)²` (defect EXACTLY `w²`), the dimension
    log-concavity `(s+1)(s+3) ≤ (s+2)²`, and `w² ≤ 1/4` on `w ≤ 1/2`.  The factor-4
    slack is the load-bearing magnitude reserve that survives the `N`-truncation (which
    is exactly what breaks naive log-concavity, cf. `boxSum1_logConcave_FALSE_at_one`).
  * `coeffW_superLogConcave_four` — the same fact in clean factor-4 form
    `4·(c_s·c_{s+2}) ≤ c_{s+1}²`.
  * `coeffW_logConcave_of_super` — confirms it RECOVERS plain log-concavity (so the atom
    is a genuine strengthening, not an orthogonal claim).

ROUND-C DELIVERABLE 2 (the honest reduction of the quad certificate).
  * `QuadGershgorinClosure w` — the NAMED-OPEN residual that remains AFTER the magnitude
    atom: the aggregate Gershgorin/TP₂ bookkeeping that turns the per-mode super-log-
    concavity into aggregate `quadDiff ≥ 0` for all `N`, `s`.  This is the single sharp
    residual the symbolic certificate now reduces to.
  * `uniformBoxQuadOfClosure` — **the reduction**: a `QuadGershgorinClosure w` witness
    yields `UniformBoxQuadCertificate w` on `0 ≤ w ≤ 1/2`, with the magnitude input
    DISCHARGED by `coeffW_superLogConcave` and the strong-coupling field discharged by
    `coeffW1_sq_le_three_of_strong`.  Honest: the closure field is genuinely open; the
    magnitude half is now closed and folded in.
  * `s1DominanceOfQuad` — the end-to-end wiring `UniformBoxQuadCertificate ⟹ S1Dominance`
    for EVERY `N` (through `uniformOfQuad`, `coreOfUniform`, `s1DominanceOfUniform`).

ROUND-C DELIVERABLE 3 (small-`N` evidence, green).
  * `quadDiff_nonneg_N3_half`, `quadDiff_nonneg_N4_half` — the certificate's aggregate
    field SATISFIED at `w = 1/2`, `N = 3, 4`, from the Round-A direct cores (closing the
    `N = 0,…,6` pointwise ladder together with Round B's `N5,N6`).

# HONESTY — what is NOT closed

The magnitude atom is genuinely proved (all `s`, symbolic `w ≤ 1/2`).  But it is NOT
sufficient on its own: `quadDiff` is not a sum of nonnegative terms — the per-mode atom
must be aggregated against the fusion indicator's total-positivity to dominate the
off-diagonal cross terms.  That aggregation (`QuadGershgorinClosure`) is the genuine
remaining open content — the heat-kernel `(r,d)` local-CLT, NOT a finite rational
inequality.  Round C closes the MAGNITUDE half and names the residual sharply; it does
NOT inhabit `QuadGershgorinClosure` for general `N`.

This is NOT a 4D Yang–Mills mass gap; it is the symbolic Gaussian magnitude atom of the
box log-concavity node and the honest reduction of the quad certificate to one residual.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `qpow`/`heatNorm`/`coeffW` lemmas, structural
reductions, and `decide` only on closed concrete-rational facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level.
-/


namespace YMGap.Continuum.FusionCoreStepRoundC

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB

/-- The closed rational constant `1/4` (the uniform Gaussian magnitude reserve). -/
abbrev quarter : Q' := Q'.mkPos 1 4 (by decide)

/-! ## 1. The Gaussian magnitude atom — super-log-concavity with a factor-4 slack -/

/-- **`coeffW_superLogConcave` — the Gaussian factor-4 super-log-concavity atom.**
For `0 ≤ w ≤ 1/2` and every mode `s`,

    coeffW w s · coeffW w (s+2)  ≤  (1/4) · (coeffW w (s+1) · coeffW w (s+1)).

This is STRICTLY STRONGER than `coeffW_logConcave` (the `≤ 1·` bound): the heat-kernel
weight has a uniform factor-4 reserve at strong coupling.  PROOF.  Through
`coeffW = dimQ · heatNorm`, the four-factor regroup `mul_swap4` splits the product into a
dimension part `dimQ s · dimQ (s+2) = (s+1)(s+3)` and a normalized part
`heatNorm s · heatNorm (s+2)`, the latter EXACTLY `w² · heatNorm(s+1)²`
(`heatNorm_logConcave_exact`).  Then `(s+1)(s+3) ≤ (s+2)²` (`dimQ_logConcave`) and
`w² ≤ 1/4` (from `w ≤ 1/2`, `qpow_mono`) give the factor `(s+1)(s+3)·w² ≤ (1/4)(s+2)²`,
which is the claim after restoring the common normalized square `heatNorm(s+1)² ≥ 0`. -/
theorem coeffW_superLogConcave {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s : Nat) :
    coeffW w s * coeffW w (s + 2)
      ≤ quarter * (coeffW w (s + 1) * coeffW w (s + 1)) := by
  -- nonnegativities
  have hDnn : (0 : Q') ≤ dimQ s * dimQ (s + 2) :=
    Q'.mul_nonneg _ _ (dimQ_nonneg s) (dimQ_nonneg (s + 2))
  have hH1nn : (0 : Q') ≤ heatNorm w (s + 1) * heatNorm w (s + 1) :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 _) (qpow_nonneg w hw0 _)
  have hq14nn : (0 : Q') ≤ quarter := by decide
  -- w² ≤ 1/4 on [0,1/2]
  have hw2q : qpow w 2 ≤ quarter :=
    Q'.le_trans' _ _ _ (qpow_mono hw0 hw12 2) (by decide)
  -- (s+1)(s+3) ≤ (s+2)²
  have hDle : dimQ s * dimQ (s + 2) ≤ dimQ (s + 1) * dimQ (s + 1) := dimQ_logConcave s
  -- scalar bound  D·w² ≤ (1/4)·D1
  have hA1 : (dimQ s * dimQ (s + 2)) * qpow w 2
      ≤ (dimQ s * dimQ (s + 2)) * quarter :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hw2q hDnn
  have hA2 : (dimQ s * dimQ (s + 2)) * quarter
      ≤ (dimQ (s + 1) * dimQ (s + 1)) * quarter :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hDle hq14nn
  have hA3 : ((dimQ (s + 1) * dimQ (s + 1)) * quarter).eqv
      (quarter * (dimQ (s + 1) * dimQ (s + 1))) :=
    Q'.mul_comm_eqv _ _
  have hAscalar : (dimQ s * dimQ (s + 2)) * qpow w 2
      ≤ quarter * (dimQ (s + 1) * dimQ (s + 1)) :=
    Q'.le_trans' _ _ _ hA1 (Q'.le_trans' _ _ _ hA2 (Q'.le_of_eqv hA3))
  -- multiply through by the normalized square H1 ≥ 0
  have hB : ((dimQ s * dimQ (s + 2)) * qpow w 2)
        * (heatNorm w (s + 1) * heatNorm w (s + 1))
      ≤ (quarter * (dimQ (s + 1) * dimQ (s + 1)))
        * (heatNorm w (s + 1) * heatNorm w (s + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hAscalar hH1nn
  -- LHS rewrite:  c_s·c_{s+2} ≃ (D·w²)·H1
  have hLHS : (coeffW w s * coeffW w (s + 2)).eqv
      (((dimQ s * dimQ (s + 2)) * qpow w 2)
        * (heatNorm w (s + 1) * heatNorm w (s + 1))) := by
    have e0 : (coeffW w s * coeffW w (s + 2)).eqv
        ((dimQ s * dimQ (s + 2)) * (heatNorm w s * heatNorm w (s + 2))) := by
      show ((dimQ s * heatNorm w s) * (dimQ (s + 2) * heatNorm w (s + 2))).eqv _
      exact mul_swap4 (dimQ s) (heatNorm w s) (dimQ (s + 2)) (heatNorm w (s + 2))
    have e1 : ((dimQ s * dimQ (s + 2)) * (heatNorm w s * heatNorm w (s + 2))).eqv
        ((dimQ s * dimQ (s + 2))
          * (qpow w 2 * (heatNorm w (s + 1) * heatNorm w (s + 1)))) :=
      Q'.mul_eqv_congr_left _ _ _ (heatNorm_logConcave_exact w s)
    have e2 : ((dimQ s * dimQ (s + 2))
          * (qpow w 2 * (heatNorm w (s + 1) * heatNorm w (s + 1)))).eqv
        (((dimQ s * dimQ (s + 2)) * qpow w 2)
          * (heatNorm w (s + 1) * heatNorm w (s + 1))) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    exact Q'.eqv_trans _ _ _ e0 (Q'.eqv_trans _ _ _ e1 e2)
  -- RHS rewrite:  (1/4·D1)·H1 ≃ (1/4)·(c_{s+1}·c_{s+1})
  have hRHS : ((quarter * (dimQ (s + 1) * dimQ (s + 1)))
        * (heatNorm w (s + 1) * heatNorm w (s + 1))).eqv
      (quarter * (coeffW w (s + 1) * coeffW w (s + 1))) := by
    have e3 : ((quarter * (dimQ (s + 1) * dimQ (s + 1)))
          * (heatNorm w (s + 1) * heatNorm w (s + 1))).eqv
        (quarter * ((dimQ (s + 1) * dimQ (s + 1))
          * (heatNorm w (s + 1) * heatNorm w (s + 1)))) :=
      Q'.mul_assoc_eqv _ _ _
    have e4 : ((dimQ (s + 1) * dimQ (s + 1))
          * (heatNorm w (s + 1) * heatNorm w (s + 1))).eqv
        (coeffW w (s + 1) * coeffW w (s + 1)) :=
      mul_swap4 (dimQ (s + 1)) (dimQ (s + 1)) (heatNorm w (s + 1)) (heatNorm w (s + 1))
    exact Q'.eqv_trans _ _ _ e3 (Q'.mul_eqv_congr_left _ _ _ e4)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS)
    (Q'.le_trans' _ _ _ hB (Q'.le_of_eqv hRHS))

/-- **`coeffW_superLogConcave_four` — the factor-4 form** `4·(c_s·c_{s+2}) ≤ c_{s+1}²`.
Multiply the super-log-concavity atom by `4 ≥ 0` and cancel `4·(1/4) ≃ 1`. -/
theorem coeffW_superLogConcave_four {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (s : Nat) :
    (4 : Q') * (coeffW w s * coeffW w (s + 2))
      ≤ coeffW w (s + 1) * coeffW w (s + 1) := by
  have h := coeffW_superLogConcave hw0 hw12 s
  have h4 : (4 : Q') * (coeffW w s * coeffW w (s + 2))
      ≤ (4 : Q') * (quarter * (coeffW w (s + 1) * coeffW w (s + 1))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h (by decide)
  have he : ((4 : Q') * (quarter * (coeffW w (s + 1) * coeffW w (s + 1)))).eqv
      (coeffW w (s + 1) * coeffW w (s + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (4 : Q') quarter _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (show ((4 : Q') * quarter).eqv 1 by decide)) ?_
    exact Q'.one_mul_eqv _
  exact Q'.le_trans' _ _ _ h4 (Q'.le_of_eqv he)

/-- **`coeffW_logConcave_of_super` — the atom recovers plain log-concavity.**
Since `1/4 ≤ 1` and `c_{s+1}² ≥ 0`, the super-log-concave bound implies
`c_s·c_{s+2} ≤ c_{s+1}²`.  Confirms the atom is a genuine STRENGTHENING of
`coeffW_logConcave`, not an orthogonal statement. -/
theorem coeffW_logConcave_of_super {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (s : Nat) :
    coeffW w s * coeffW w (s + 2) ≤ coeffW w (s + 1) * coeffW w (s + 1) := by
  have h := coeffW_superLogConcave hw0 hw12 s
  have hsqnn : (0 : Q') ≤ coeffW w (s + 1) * coeffW w (s + 1) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 (s + 1)) (coeffW_nonneg hw0 (s + 1))
  have hstep : quarter * (coeffW w (s + 1) * coeffW w (s + 1))
      ≤ (1 : Q') * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : quarter ≤ (1 : Q')) hsqnn
  exact Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.one_mul_eqv _)))

/-! ## 2. The honest reduction of the Cauchy–Binet quad certificate

With the magnitude half closed, the symbolic `quadDiff ≥ 0` certificate reduces to ONE
residual: the aggregate Gershgorin/TP₂ bookkeeping that converts the proved per-mode
super-log-concavity into aggregate nonnegativity of the quadruple difference.  We name
that residual sharply and prove the reduction `closure ⟹ certificate`, with the
magnitude input discharged by `coeffW_superLogConcave`. -/

/-- **`QuadGershgorinClosure w`** — the NAMED-OPEN residual remaining after the magnitude
atom.  Its single field is the implication "(per-mode factor-4 super-log-concavity for
every `s`) ⟹ (aggregate `quadDiff ≥ 0` for every `N`, `s`)" — i.e. the Gershgorin/TP₂
bookkeeping that aggregates the diagonal factor-4 reserve against the off-diagonal cross
leakage of the fusion-indicator kernel.  This is the genuine open content (the
heat-kernel `(r,d)` local-CLT), NOT a finite rational inequality.  The hypothesis of the
implication is exactly what `coeffW_superLogConcave` supplies. -/
structure QuadGershgorinClosure (w : Q') : Type where
  /-- The aggregate bookkeeping: per-mode super-log-concavity drives `quadDiff ≥ 0`. -/
  closure :
    (∀ s, coeffW w s * coeffW w (s + 2)
        ≤ quarter * (coeffW w (s + 1) * coeffW w (s + 1)))
      → ∀ N s, (0 : Q') ≤ quadDiff w N s

/-- **`uniformBoxQuadOfClosure` — THE REDUCTION.**  On `0 ≤ w ≤ 1/2`, a
`QuadGershgorinClosure w` witness yields the sharp `UniformBoxQuadCertificate w`: the
magnitude hypothesis of its `closure` field is DISCHARGED by `coeffW_superLogConcave`
(proved here, all `s`), and the strong-coupling field by `coeffW1_sq_le_three_of_strong`.
Hence — composed with `uniformOfQuad` — a single closure witness drives the whole
`N`-tower of `FusionConvLogConcaveCore` and `S1Dominance`.  Honest: the closure field is
the genuine remaining open content; the magnitude half is now closed. -/
def uniformBoxQuadOfClosure {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (gc : QuadGershgorinClosure w) : UniformBoxQuadCertificate w where
  strongCoupling := coeffW1_sq_le_three_of_strong hw0 hw12
  quadNonneg := gc.closure (fun s => coeffW_superLogConcave hw0 hw12 s)

/-- **`uniformBoxLogConcaveOfClosure`** — the same reduction one step further: a closure
witness yields `UniformBoxLogConcave w` (the direct box log-concavity for all `N`), via
`uniformOfQuad`. -/
def uniformBoxLogConcaveOfClosure {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (gc : QuadGershgorinClosure w) :
    YMGap.Continuum.FusionCoreStepRoundA.UniformBoxLogConcave w :=
  uniformOfQuad (uniformBoxQuadOfClosure hw0 hw12 gc)

/-! ## 3. End-to-end wiring `UniformBoxQuadCertificate ⟹ S1Dominance` (every `N`) -/

/-- **`s1DominanceOfQuad` — the sharp quad certificate drives first-excited dominance
for EVERY `N`.**  Through `uniformOfQuad` (box log-concavity) and `s1DominanceOfUniform`,
a single `UniformBoxQuadCertificate` plus the per-`N` edge input yields `S1Dominance N w
2`.  The structural payoff: all-`N` `s = 1`-dominance reduces to ONE Cauchy–Binet datum. -/
def s1DominanceOfQuad {w : Q'} (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (cert : UniformBoxQuadCertificate w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  YMGap.Continuum.FusionCoreStepRoundA.s1DominanceOfUniform hw hw1
    (uniformOfQuad cert) N hedge

/-! ## 4. Small-`N` evidence — the aggregate field at `w = 1/2`, `N = 3, 4` -/

/-- Cauchy–Binet positivity witnessed at `N = 3`, `w = 1/2` (all channels), from the
Round-A direct core `core_N3_half`. -/
theorem quadDiff_nonneg_N3_half (s : Nat) : (0 : Q') ≤ quadDiff wH 3 s :=
  quadDiff_nonneg_of_core YMGap.Continuum.FusionCoreStepRoundA.core_N3_half s

/-- Cauchy–Binet positivity witnessed at `N = 4`, `w = 1/2` (all channels), from the
Round-A direct core `core_N4_half`. -/
theorem quadDiff_nonneg_N4_half (s : Nat) : (0 : Q') ≤ quadDiff wH 4 s :=
  quadDiff_nonneg_of_core YMGap.Continuum.FusionCoreStepRoundA.core_N4_half s

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `coeffW_superLogConcave` — the SYMBOLIC, all-`s` Gaussian factor-4 super-log-
    concavity atom `c_s·c_{s+2} ≤ (1/4)·c_{s+1}²` on `0 ≤ w ≤ 1/2`.  The magnitude decay
    Round B flagged as required and missing; strictly stronger than `coeffW_logConcave`.
  * `coeffW_superLogConcave_four` — its factor-4 form `4·(c_s·c_{s+2}) ≤ c_{s+1}²`.
  * `coeffW_logConcave_of_super` — recovers plain log-concavity (genuine strengthening).
  * `uniformBoxQuadOfClosure` / `uniformBoxLogConcaveOfClosure` — the REDUCTION of the
    sharp `UniformBoxQuadCertificate` (and `UniformBoxLogConcave`) to the single residual
    `QuadGershgorinClosure`, with the magnitude input DISCHARGED by the atom and strong
    coupling by `coeffW1_sq_le_three_of_strong`.
  * `s1DominanceOfQuad` — end-to-end `UniformBoxQuadCertificate ⟹ S1Dominance` (every `N`).
  * `quadDiff_nonneg_N3_half`, `quadDiff_nonneg_N4_half` — the aggregate field satisfied
    at `w = 1/2`, `N = 3, 4`.

NAMED OPEN:
  * `QuadGershgorinClosure w` — the aggregate Gershgorin/TP₂ bookkeeping (per-mode
    super-log-concavity ⟹ aggregate `quadDiff ≥ 0`) for general `N`.  This is the genuine
    remaining content — the heat-kernel `(r,d)` local-CLT — NOT a finite rational
    inequality; `quadDiff` is not a sum of nonnegative terms, so the proved magnitude atom
    must still be aggregated against the fusion-indicator total positivity.

HONEST VERDICT.  Round C CLOSES the Gaussian magnitude half of the box log-concavity
node — the symbolic, all-`s` factor-4 super-log-concavity that Round B named as required
but did not have — and REDUCES the sharp Cauchy–Binet quad certificate to ONE remaining
residual, the aggregate Gershgorin/TP₂ bookkeeping, with the magnitude input fully
discharged and the whole `N`-tower wiring in place.  This is a structural advance on one
box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundC

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundC.coeffW_superLogConcave
#print axioms YMGap.Continuum.FusionCoreStepRoundC.coeffW_superLogConcave_four
#print axioms YMGap.Continuum.FusionCoreStepRoundC.coeffW_logConcave_of_super
#print axioms YMGap.Continuum.FusionCoreStepRoundC.uniformBoxQuadOfClosure
#print axioms YMGap.Continuum.FusionCoreStepRoundC.uniformBoxLogConcaveOfClosure
#print axioms YMGap.Continuum.FusionCoreStepRoundC.s1DominanceOfQuad
#print axioms YMGap.Continuum.FusionCoreStepRoundC.quadDiff_nonneg_N3_half
#print axioms YMGap.Continuum.FusionCoreStepRoundC.quadDiff_nonneg_N4_half


/-! ===========================================================================
    ## Round D  (was `FusionCoreStepRoundD.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round D of the fusion box log-concavity node: the STRAND (Clebsch)
reindexing of the box sum and the honest split of `QuadGershgorinClosure` into ONE
analytic core (truncated lag-correlation TP₂) plus two finite combinatorial bridges.

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundC` closed the Gaussian MAGNITUDE half of the box log-concavity node
(`coeffW_superLogConcave`, the all-`s` factor-4 super-log-concavity) and reduced the
sharp Cauchy–Binet quad certificate to ONE opaque residual `QuadGershgorinClosure w`
(the implication "per-mode super-log-concavity ⟹ aggregate `quadDiff ≥ 0`").  Round D
attacks `QuadGershgorinClosure` itself.  It does NOT inhabit it for general `N` (that is
the genuine heat-kernel local-CLT and remains open), but it makes three honest advances:

ROUND-D DELIVERABLE 1 (the strand/Clebsch foundation — PROVED, axiom-clean).
  * `fusionOK_strand` — the unique nonneg-integer "triangle/strand" parametrization of
    SU(2) admissibility:
        fusionOK a b t = true  ⟺  ∃ p q r, a = q+r ∧ b = p+r ∧ t = p+q.
    (Inverse `p=(b+t−a)/2`, `q=(a+t−b)/2`, `r=(a+b−t)/2`; the triangle inequalities and
    the evenness of `a+b+t` are EXACTLY `p,q,r ≥ 0`.)  Pure `omega` over
    `fusionOK_eq_true_iff`.  This is the combinatorial backbone the arXiv leads missed:
    it exhibits the FULL `(a,b,t)`-symmetry of admissibility and is the change of
    variables under which the box sum becomes an antidiagonal line-sum of a lag-
    correlation (the route in which the magnitude reserve `coeffW_superLogConcave` is the
    boundary defect a Karlin TP₂ argument must absorb).
  * `fusionOK_symm_ab`, `fusionOK_symm_bt` — the strand symmetry made explicit (the box
    kernel is symmetric in the whole admissible triple, not just `a ↔ b`).

ROUND-D DELIVERABLE 2 (the honest barrier — PROVED, `decide`).
  * `indBracket` / `bracket_can_be_negative` — the ANTISYMMETRIZED indicator bracket
    `B_{X,Y}(s) = 2 f_X(s+1)f_Y(s+1) − f_X(s)f_Y(s+2) − f_X(s+2)f_Y(s)`
    (`f = fusionInd`) is NOT sign-definite: at `X=(0,0)`, `Y=(1,1)`, `s=0` it equals `−1`.
    Hence a pure Cauchy–Binet "sum of nonnegative `2×2` indicator minors" CANNOT close
    `quadDiff ≥ 0`; the `coeffW`-magnitudes must rescue the negative pairs.  This is the
    precise, machine-checked reason `QuadGershgorinClosure` genuinely consumes the
    super-log-concavity reserve — it rules out the leads' naive routes.

ROUND-D DELIVERABLE 3 (the sharp split of the residual — REDUCTION, axiom-clean).
  * `lagCorr w N p q` — the truncated lag-correlation `Σ_{r : p+r,q+r ≤ N} c_{p+r} c_{q+r}`
    of the theta weight (symmetric in `p,q`: `lagCorr_symm`; nonneg: `lagCorr_nonneg`).
  * `lineSum S t = Σ_{p+q=t} S(p,q)` — the antidiagonal line-sum operator.
  * `LagCorrTP2 w` — the SHARP analytic residual (A2): `lagCorr` is TP₂ (log-supermodular)
    in its two strand arguments.  This is strictly smaller and more honestly named than
    `QuadGershgorinClosure`: it is the genuine "truncated lag-correlation of a super-log-
    concave theta weight is totally positive of order 2" local-CLT.
  * `lagCorr_diag_logConcave_of_TP2` — a PROVED per-minor consequence: `LagCorrTP2`
    implies the diagonal log-concavity `lagCorr(p,p+1)² ≤ lagCorr(p,p)·lagCorr(p+1,p+1)`.
    Confirms A2 has real content and the minor mechanism fires.
  * `StrandReduction w` — the two finite combinatorial bridges packaged as Type-level
    fields: A1 (`reindex`, the strand identity `boxSum N t ≃ lineSum (lagCorr w N) t`) and
    A3 (`lineSumLogConcave`, the Karlin antidiagonal line-sum log-concavity).
  * `quadGershgorinOfStrandReduction` — THE REDUCTION (proved `def`): a `StrandReduction`
    witness inhabits `QuadGershgorinClosure w`.  So the monolithic closure splits into
    {A1 finite reindex} + {A3 finite line-sum}, with A3 seeded by the analytic core A2.
  * `s1DominanceOfStrandReduction` — end-to-end: composed with
    `uniformBoxQuadOfClosure` and `s1DominanceOfQuad`, a single `StrandReduction` witness
    drives `S1Dominance N w 2` for EVERY `N`.

# HONESTY — what is NOT closed

`QuadGershgorinClosure w` is NOT inhabited here for general `N`.  Round D splits it into
three sharply-named pieces — A1 (`reindex`, finite), A2 (`LagCorrTP2`, the analytic
local-CLT core), A3 (`lineSumLogConcave`, finite Karlin line-sum) — and proves the
foundation (`fusionOK_strand`), the honest barrier (`bracket_can_be_negative`), the per-
minor case (`lagCorr_diag_logConcave_of_TP2`), and the reduction `A1 + A3 ⟹ closure`.
A1, A2, A3 remain Type-level NAMED-OPEN structures (never `sorry`).  The genuine open
content concentrates into A2: "the truncated lag-correlation of a super-log-concave theta
weight is TP₂", with the proved factor-4 reserve `coeffW_superLogConcave` as exactly the
`N`-truncation boundary defect a Karlin argument must absorb.

This is NOT a 4D Yang–Mills mass gap; it is the strand reindexing of one box-level log-
concavity sub-fact and the honest decomposition of its single open residual.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, `omega` over the decidable admissibility predicate, the
reused `fsum`/`coeffW`/`boxSum`/`quadDiff` lemmas, structural reductions, and `decide`
only on closed concrete-rational / finite facts.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundD

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundC

/-! ## 1. The strand (Clebsch) parametrization of SU(2) admissibility -/

/-- **`fusionOK_strand` — the triangle/strand parametrization.**  SU(2) admissibility
`χ_t ∈ χ_a·χ_b` has a unique nonneg-integer "strand" form:

    fusionOK a b t = true  ⟺  ∃ p q r : Nat,  a = q+r ∧ b = p+r ∧ t = p+q.

Forward: `p=(b+t−a)/2`, `q=(a+t−b)/2`, `r=(a+b−t)/2`; the triangle inequalities
(`|a−b| ≤ t ≤ a+b`) and the evenness of `a+b+t` make these nonneg integers with the
stated sums.  Reverse: `a=q+r`, `b=p+r`, `t=p+q` give `|a−b| = |q−p| ≤ p+q = t ≤ a+b`
and `a+b+t = 2(p+q+r)` even.  Pure `omega` over `fusionOK_eq_true_iff`.  This exhibits
the full `(a,b,t)`-symmetry of admissibility and is the change of variables under which
`boxSum` becomes an antidiagonal line-sum of a lag-correlation. -/
theorem fusionOK_strand (a b t : Nat) :
    fusionOK a b t = true ↔
      ∃ p q r : Nat, a = q + r ∧ b = p + r ∧ t = p + q := by
  rw [fusionOK_eq_true_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    -- expand `max/min` into linear inequalities (this `omega` does not auto-expand them)
    have h1' : a ≤ b + t ∧ b ≤ a + t := by
      rcases Nat.le_total a b with hle | hle
      · have em : Nat.max a b = b := Nat.max_eq_right hle
        have en : Nat.min a b = a := Nat.min_eq_left hle
        exact ⟨by omega, by omega⟩
      · have em : Nat.max a b = a := Nat.max_eq_left hle
        have en : Nat.min a b = b := Nat.min_eq_right hle
        exact ⟨by omega, by omega⟩
    obtain ⟨hab, hba⟩ := h1'
    exact ⟨(b + t - a) / 2, (a + t - b) / 2, (a + b - t) / 2,
      by omega, by omega, by omega⟩
  · rintro ⟨p, q, r, ha, hb, ht⟩
    subst ha; subst hb; subst ht
    rcases Nat.le_total (q + r) (p + r) with hle | hle
    · have em : Nat.max (q + r) (p + r) = p + r := Nat.max_eq_right hle
      have en : Nat.min (q + r) (p + r) = q + r := Nat.min_eq_left hle
      refine ⟨?_, ?_, ?_⟩ <;> omega
    · have em : Nat.max (q + r) (p + r) = q + r := Nat.max_eq_left hle
      have en : Nat.min (q + r) (p + r) = p + r := Nat.min_eq_right hle
      refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **`fusionOK_symm_ab`** — admissibility is symmetric under `a ↔ b` (the `p ↔ q`
strand transposition). -/
theorem fusionOK_symm_ab (a b t : Nat) : fusionOK a b t = fusionOK b a t := by
  cases h1 : fusionOK a b t <;> cases h2 : fusionOK b a t <;> try rfl
  · have hcon : fusionOK a b t = true := by
      obtain ⟨p, q, r, hb, ha, ht⟩ := (fusionOK_strand b a t).mp h2
      exact (fusionOK_strand a b t).mpr ⟨q, p, r, ha, hb, by omega⟩
    rw [hcon] at h1; exact Bool.noConfusion h1
  · have hcon : fusionOK b a t = true := by
      obtain ⟨p, q, r, ha, hb, ht⟩ := (fusionOK_strand a b t).mp h1
      exact (fusionOK_strand b a t).mpr ⟨q, p, r, hb, ha, by omega⟩
    rw [hcon] at h2; exact Bool.noConfusion h2

/-- **`fusionOK_symm_bt`** — admissibility is symmetric under `b ↔ t` (the `q ↔ r`
strand transposition; a genuinely non-trivial face of the symmetry, since `t` is
syntactically the distinguished fusion channel, yet the strand form makes the triple
fully symmetric). -/
theorem fusionOK_symm_bt (a b t : Nat) : fusionOK a b t = fusionOK a t b := by
  cases h1 : fusionOK a b t <;> cases h2 : fusionOK a t b <;> try rfl
  · have hcon : fusionOK a b t = true := by
      obtain ⟨p, q, r, ha, ht, hb⟩ := (fusionOK_strand a t b).mp h2
      exact (fusionOK_strand a b t).mpr ⟨p, r, q, by omega, by omega, by omega⟩
    rw [hcon] at h1; exact Bool.noConfusion h1
  · have hcon : fusionOK a t b = true := by
      obtain ⟨p, q, r, ha, hb, ht⟩ := (fusionOK_strand a b t).mp h1
      exact (fusionOK_strand a t b).mpr ⟨p, r, q, by omega, by omega, by omega⟩
    rw [hcon] at h2; exact Bool.noConfusion h2

/-! ## 2. The honest barrier — the antisymmetrized indicator bracket is not sign-definite

Antisymmetrizing the Cauchy–Binet quadruple sum by swapping the two super-indices
`X=(a,b) ↔ Y=(a',b')` in the negative half collapses `quadDiff` to a symmetric sum
`½ Σ_{X,Y} C(X)C(Y) · B_{X,Y}(s)` over the PURELY COMBINATORIAL indicator bracket
`B`.  If `B` were `≥ 0` always, a sum-of-nonnegative-minors argument would close the node
with no magnitude input.  It is NOT: the witness below shows `B = −1 < 0`, so the
`coeffW`-magnitudes (super-log-concavity) are genuinely load-bearing. -/

/-- The antisymmetrized indicator bracket
`B_{X,Y}(s) = 2 f_X(s+1)f_Y(s+1) − f_X(s)f_Y(s+2) − f_X(s+2)f_Y(s)`,
`X=(a,b)`, `Y=(a',b')`, `f = fusionInd`. -/
def indBracket (s a b a' b' : Nat) : Q' :=
  (2 : Q') * (fusionInd a b (s + 1) * fusionInd a' b' (s + 1))
    + -(fusionInd a b s * fusionInd a' b' (s + 2))
    + -(fusionInd a b (s + 2) * fusionInd a' b' s)

/-- **`bracket_can_be_negative` — the indicator bracket is NOT sign-definite.**  At
`X=(0,0)`, `Y=(1,1)`, `s=0` the bracket equals `−1`, hence is not `≥ 0`.  Machine-checked
reason that the indicator Cauchy–Binet alone cannot close `quadDiff ≥ 0`: the magnitude
reserve `coeffW_superLogConcave` must dominate the negative pairs. -/
theorem bracket_can_be_negative : ¬ ((0 : Q') ≤ indBracket 0 0 0 1 1) := by decide

/-! ## 3. The truncated lag-correlation and the antidiagonal line-sum -/

/-- The truncated lag-correlation of the theta weight:
`lagCorr w N p q = Σ_{r=0}^{N − max(p,q)} c_{p+r} · c_{q+r}` (the `r`-cutoff is exactly
`p+r ≤ N` and `q+r ≤ N`).  Symmetric in `p,q`. -/
def lagCorr (w : Q') (N p q : Nat) : Q' :=
  fsum (fun r => coeffW w (p + r) * coeffW w (q + r)) (N + 1 - Nat.max p q)

/-- The lag-correlation is nonnegative (a sum of products of nonneg coefficients). -/
theorem lagCorr_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (N p q : Nat) :
    (0 : Q') ≤ lagCorr w N p q :=
  fsum_nonneg (fun r => Q'.mul_nonneg _ _ (coeffW_nonneg hw _) (coeffW_nonneg hw _)) _

/-- The lag-correlation is symmetric in its two strand arguments. -/
theorem lagCorr_symm (w : Q') (N p q : Nat) :
    (lagCorr w N p q).eqv (lagCorr w N q p) := by
  unfold lagCorr
  have hc : Nat.max p q = Nat.max q p := Nat.max_comm p q
  rw [hc]
  exact fsum_eqv_congr _ _ (fun r => Q'.mul_comm_eqv _ _) _

/-- The antidiagonal line-sum operator `lineSum S t = Σ_{p+q=t} S(p,q)
= Σ_{p=0}^{t} S(p, t−p)`. -/
def lineSum (S : Nat → Nat → Q') (t : Nat) : Q' :=
  fsum (fun p => S p (t - p)) (t + 1)

/-! ## 4. The sharp analytic residual (A2): the lag-correlation is TP₂ -/

/-- **`LagCorrTP2 w`** — the SHARP analytic residual remaining after the strand split:
the truncated lag-correlation is TP₂ (log-supermodular) in its two strand arguments,

    p ≤ p',  q ≤ q'   ⟹   lagCorr(p,q')·lagCorr(p',q) ≤ lagCorr(p,q)·lagCorr(p',q').

This is the genuine open core — "truncated lag-correlation of a super-log-concave theta
weight is totally positive of order 2", the heat-kernel local-CLT — strictly smaller and
more honestly named than `QuadGershgorinClosure`.  The proved factor-4 reserve
`coeffW_superLogConcave` is exactly the `N`-truncation boundary defect a Karlin
variation-diminishing argument must absorb. -/
structure LagCorrTP2 (w : Q') : Type where
  /-- Total positivity of order 2 of the truncated lag-correlation. -/
  tp2 : ∀ N p q p' q', p ≤ p' → q ≤ q' →
    lagCorr w N p q' * lagCorr w N p' q ≤ lagCorr w N p q * lagCorr w N p' q'

/-- **`lagCorr_diag_logConcave_of_TP2` — a PROVED per-minor consequence of A2.**  TP₂
specialized to the `2×2` corner `(p,p),(p,p+1),(p+1,p),(p+1,p+1)` and the symmetry
`lagCorr(p,p+1) ≃ lagCorr(p+1,p)` gives the diagonal log-concavity

    lagCorr(p,p+1)²  ≤  lagCorr(p,p) · lagCorr(p+1,p+1).

Confirms A2 carries real content and the minor mechanism fires. -/
theorem lagCorr_diag_logConcave_of_TP2 {w : Q'} (tp : LagCorrTP2 w) (N p : Nat) :
    lagCorr w N p (p + 1) * lagCorr w N p (p + 1)
      ≤ lagCorr w N p p * lagCorr w N (p + 1) (p + 1) := by
  have hle : p ≤ p + 1 := Nat.le_succ p
  -- rewrite the right factor of the LHS square via `lagCorr(p,p+1) ≃ lagCorr(p+1,p)`
  have hsymm : (lagCorr w N p (p + 1)).eqv (lagCorr w N (p + 1) p) :=
    Q'.eqv_symm (lagCorr_symm w N (p + 1) p)
  have e : (lagCorr w N p (p + 1) * lagCorr w N p (p + 1)).eqv
      (lagCorr w N p (p + 1) * lagCorr w N (p + 1) p) :=
    Q'.mul_eqv_congr_left _ _ _ hsymm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e)
    (tp.tp2 N p p (p + 1) (p + 1) hle hle)

/-! ## 5. The strand split of `QuadGershgorinClosure` (A1 + A3 ⟹ closure) -/

/-- **`StrandReduction w`** — the two finite combinatorial bridges of the strand route,
packaged as Type-level fields:

  * `reindex` (A1): the strand identity `boxSum w N t ≃ lineSum (lagCorr w N) t` — the box
    double sum reindexed (via `fusionOK_strand`) as the antidiagonal line-sum of the
    lag-correlation.  Pure finite `fsum` reassociation (no analysis).
  * `lineSumLogConcave` (A3): the Karlin antidiagonal line-sum log-concavity
    `lineSum(s)·lineSum(s+2) ≤ lineSum(s+1)²`, the standard "TP₂ ⟹ line-sums are PF₂"
    fact, seeded by the analytic core `LagCorrTP2` (A2).

Both are finite/axiom-clean in principle; they remain NAMED-OPEN here. -/
structure StrandReduction (w : Q') : Type where
  /-- A1: the strand reindexing identity. -/
  reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t)
  /-- A3: the antidiagonal line-sum log-concavity. -/
  lineSumLogConcave : ∀ N s,
    lineSum (lagCorr w N) s * lineSum (lagCorr w N) (s + 2)
      ≤ lineSum (lagCorr w N) (s + 1) * lineSum (lagCorr w N) (s + 1)

/-- **`quadGershgorinOfStrandReduction` — THE REDUCTION.**  A `StrandReduction w` witness
inhabits `QuadGershgorinClosure w`: transport the line-sum log-concavity (A3) across the
strand reindexing (A1) to the box cross-difference, then across `boxDiff_eq_quadDiff` to
`quadDiff ≥ 0`.  The per-mode super-log-concavity hypothesis of `closure` is not needed
(A3 already supplies the conclusion), so the monolithic residual splits cleanly into the
finite bridges A1, A3 (with A3 seeded by the analytic core `LagCorrTP2`). -/
def quadGershgorinOfStrandReduction {w : Q'} (sr : StrandReduction w) :
    QuadGershgorinClosure w where
  closure := fun _ N s => by
    -- box products ≃ line-sum products (via A1 reindex on each factor)
    have e1 : (boxSum w N s * boxSum w N (s + 2)).eqv
        (lineSum (lagCorr w N) s * lineSum (lagCorr w N) (s + 2)) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (sr.reindex N s))
        (Q'.mul_eqv_congr_left _ _ _ (sr.reindex N (s + 2)))
    have e2 : (lineSum (lagCorr w N) (s + 1) * lineSum (lagCorr w N) (s + 1)).eqv
        (boxSum w N (s + 1) * boxSum w N (s + 1)) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (sr.reindex N (s + 1))))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (sr.reindex N (s + 1))))
    -- box log-concavity from A3 sandwiched between the two transports
    have hbox : boxSum w N s * boxSum w N (s + 2)
        ≤ boxSum w N (s + 1) * boxSum w N (s + 1) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
        (Q'.le_trans' _ _ _ (sr.lineSumLogConcave N s) (Q'.le_of_eqv e2))
    -- box cross-difference ≥ 0, then transport to `quadDiff` (mirrors quadDiff_nonneg_of_core)
    exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hbox)
      (Q'.le_of_eqv (boxDiff_eq_quadDiff w N s))

/-! ## 6. End-to-end wiring — `StrandReduction ⟹ S1Dominance` for every `N` -/

/-- **`s1DominanceOfStrandReduction` — a single strand witness drives first-excited
dominance for EVERY `N`.**  Compose the reduction `quadGershgorinOfStrandReduction`
through `uniformBoxQuadOfClosure` (magnitude discharged by `coeffW_superLogConcave`,
strong coupling by `coeffW1_sq_le_three_of_strong`) and `s1DominanceOfQuad`.  The
structural payoff: all-`N` `s = 1`-dominance reduces to ONE `StrandReduction` datum
(equivalently to the single analytic core `LagCorrTP2` plus the two finite bridges). -/
def s1DominanceOfStrandReduction {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q')) (sr : StrandReduction w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  s1DominanceOfQuad hwpos hw1
    (uniformBoxQuadOfClosure hw0 hw12 (quadGershgorinOfStrandReduction sr)) N hedge

/-! ## 7. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `fusionOK_strand` — the strand/triangle parametrization of SU(2) admissibility (the
    combinatorial backbone; full `(a,b,t)`-symmetry).
  * `fusionOK_symm_ab`, `fusionOK_symm_bt` — two faces of the strand symmetry.
  * `bracket_can_be_negative` — the antisymmetrized indicator bracket is NOT sign-definite
    (`B = −1` at `X=(0,0),Y=(1,1),s=0`): machine-checked proof that the magnitude reserve
    is load-bearing and the indicator Cauchy–Binet alone cannot close the node.
  * `lagCorr`, `lagCorr_nonneg`, `lagCorr_symm`, `lineSum` — the truncated lag-correlation
    and antidiagonal line-sum objects of the strand route.
  * `lagCorr_diag_logConcave_of_TP2` — a per-minor consequence of the analytic core A2.
  * `quadGershgorinOfStrandReduction` — THE REDUCTION: a `StrandReduction` (A1 reindex +
    A3 line-sum) witness inhabits `QuadGershgorinClosure`.
  * `s1DominanceOfStrandReduction` — end-to-end `StrandReduction ⟹ S1Dominance` (every `N`).

NAMED OPEN (Type-level structures, never `sorry`):
  * `LagCorrTP2 w` (A2) — the SHARP analytic core: the truncated lag-correlation of the
    super-log-concave theta weight is TP₂.  The genuine heat-kernel local-CLT; strictly
    smaller and more honest than `QuadGershgorinClosure`.
  * `StrandReduction w` (A1 `reindex` + A3 `lineSumLogConcave`) — the two finite
    combinatorial bridges of the strand route (the strand identity and the Karlin
    line-sum log-concavity), the latter seeded by A2.

HONEST VERDICT.  Round D does NOT inhabit `QuadGershgorinClosure` for general `N`.  It
proves the strand foundation and symmetry, the machine-checked magnitude-is-required
barrier, the per-minor consequence of the analytic core, and the reduction
`A1 + A3 ⟹ closure` — thereby SPLITTING the single opaque residual into three sharply-
named pieces with the entire genuine open content concentrated in ONE analytic core
(`LagCorrTP2`, the truncated-lag-correlation TP₂ local-CLT).  This is a structural advance
on one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundD

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundD.fusionOK_strand
#print axioms YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_ab
#print axioms YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_bt
#print axioms YMGap.Continuum.FusionCoreStepRoundD.bracket_can_be_negative
#print axioms YMGap.Continuum.FusionCoreStepRoundD.lagCorr_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundD.lagCorr_symm
#print axioms YMGap.Continuum.FusionCoreStepRoundD.lagCorr_diag_logConcave_of_TP2
#print axioms YMGap.Continuum.FusionCoreStepRoundD.quadGershgorinOfStrandReduction
#print axioms YMGap.Continuum.FusionCoreStepRoundD.s1DominanceOfStrandReduction


/-! ===========================================================================
    ## Round E  (was `FusionCoreStepRoundE.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round E of the fusion box log-concavity node: the HANKEL (rectangle)
log-concavity atom of the theta weight — the single missing analytic lemma that the
truncated-lag-correlation TP₂ residual (A2 = `LagCorrTP2`) consumes — proved
symbolically for all shifts, together with the Cauchy–Binet per-pair minor-product
positivity that is the per-summand content of A2, and an HONEST correction of the A3
typing.

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundD` split the opaque `QuadGershgorinClosure` residual into three
sharply-named pieces — A1 (`reindex`, finite), A2 (`LagCorrTP2`, the analytic core),
A3 (`lineSumLogConcave`, the line-sum log-concavity) — and reduced `A1 + A3 ⟹ closure`.
Round E attacks A2 at its analytic root and audits A3.

ROUND-E DELIVERABLE 1 (the Hankel/rectangle log-concavity atom — PROVED, all shifts).
  * `coeffW_step` — the SINGLE-STEP Hankel log-concavity of the theta weight: for every
    `m`, `i`,
        coeffW w i · coeffW w (i+m+2)  ≤  coeffW w (i+1) · coeffW w (i+m+1).
    This is `coeffW_logConcave` "spread one notch outward" — the inductive backbone of
    total positivity.  PROOF: induction on `m`; the base is `coeffW_logConcave`, the step
    multiplies the induction hypothesis by the boundary factor, applies
    `coeffW_logConcave` at the moving end, and cancels the common positive factor
    (`coeffW_pos` + `le_of_mul_le_mul_left_pos`).  This is the genuinely NEW lemma the
    leads named as missing for A2.
  * `coeffW_rect` — the full RECTANGLE (Hankel `2×2`-minor) log-concavity: for all `a b i`,
        coeffW w i · coeffW w (i+a+b)  ≤  coeffW w (i+a) · coeffW w (i+b).
    The most-spread product is dominated by any less-spread product with the same total
    index.  PROOF: induction on `b`, peeling one `coeffW_step` at the outer edge and
    closing with the induction hypothesis at `i+1`.  This is exactly the statement that
    every Hankel `2×2` minor of `coeffW` is `≤ 0`, i.e. `coeffW` is Pólya-frequency of
    order 2.

ROUND-E DELIVERABLE 2 (the Cauchy–Binet per-summand atom — PROVED).
  * `coeffW_minor` — the Cauchy–Binet matrix-element form: for the strand rows `p, p+a`
    and columns `r, r+b`,
        coeffW w (p+r) · coeffW w ((p+a)+(r+b))  ≤  coeffW w (p+(r+b)) · coeffW w ((p+a)+r),
    i.e. the `2×2` minor of the Hankel matrix `V_{x,y} = coeffW(x+y)` is `≤ 0`.
  * `coeffMinor` / `coeffMinor_nonpos` — that minor in additive (`X + -Y`) form, proved
    `≤ 0`.
  * `coeffMinorProd_nonneg` — the per-PAIR positivity that drives the truncated-lag-
    correlation TP₂: the product of the two Hankel minors (over rows `(p,p+ap)` and
    `(q,q+aq)` sharing columns `(r,r+b)`) is `≥ 0` (two `≤ 0` factors).  This is the exact
    per-summand content of the Cauchy–Binet/Andréief expansion of `LagCorrTP2`; what
    remains genuinely open in A2 is the algebraic Andréief half-sum identity plus the
    `N`-truncation boundary defect (absorbed by `coeffW_superLogConcave`).

ROUND-E DELIVERABLE 3 (line-sum / lag-correlation finite facts — PROVED).
  * `lineSum_nonneg` — the antidiagonal line-sum of the lag-correlation is `≥ 0`.
  * `lagCorr_tp2_diag` — the DEGENERATE TP₂ slice `p = p'` holds with equality
    (commutativity), an honest green sub-case of `LagCorrTP2`.

# HONESTY — what is NOT closed, and a CORRECTION of the A3 typing

A2 (`LagCorrTP2`) is NOT inhabited here for general `N`.  Round E proves its analytic
ATOM (every Hankel `2×2` minor of `coeffW` is `≤ 0`, all shifts) and the per-summand
Cauchy–Binet positivity, leaving the Andréief half-sum identity and the truncation
boundary defect as the residual.

CORRECTION (A3).  The `RoundD` docstring bills A3 (`lineSumLogConcave`) as following from
the bare `LagCorrTP2.tp2` field by "TP₂ ⟹ line-sums are PF₂".  This is FALSE for a merely
TP₂ kernel: the symmetric rank-1 kernel `K(p,q)=f(p)f(q)` with `f=(1,0,1)` is TP₂ (every
`2×2` minor `= 0`), yet its antidiagonal sums `L=(1,0,2,0,1)` satisfy
`L(1)² = 0 < 2 = L(0)·L(2)` — NOT log-concave.  So A3 cannot be discharged from the
opaque `tp2` field alone; it needs the GRAM/TOEPLITZ structure `lagCorr = V Vᵀ` (`V`
Hankel), i.e. the same `coeffW`-Hankel-minor input proved here, not an abstract TP₂
hypothesis.  Round E records this as a sharp reduction: A3's honest seed is the Hankel
log-concavity of `coeffW` (`coeffW_rect`), NOT `LagCorrTP2`.

This is NOT a 4D Yang–Mills mass gap; it is the analytic Hankel-minor atom of one box-
level log-concavity sub-fact, its per-summand Cauchy–Binet positivity, and an honest
correction of the A3 reduction.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`lagCorr` lemmas, the positive-
cancellation lemma `le_of_mul_le_mul_left_pos`, finite inductions, and `omega` on index
identities.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`sorry`.  All witnesses are `Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundE

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD

/-! ## 1. The single-step Hankel log-concavity of the theta weight -/

/-- **`coeffW_step` — single-step Hankel log-concavity.**  For every `m`, `i`,

    coeffW w i · coeffW w (i+m+2)  ≤  coeffW w (i+1) · coeffW w (i+m+1).

`coeffW_logConcave` "spread one notch outward".  Induction on `m`: base is
`coeffW_logConcave`; the step multiplies the IH by the moving boundary factor, applies
`coeffW_logConcave` at the moving end, and cancels the common positive factor. -/
theorem coeffW_step {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (i : Nat) :
    ∀ m, coeffW w i * coeffW w (i + m + 2) ≤ coeffW w (i + 1) * coeffW w (i + m + 1)
  | 0 => FusionGenFunction.coeffW_logConcave hw0 hw1 i
  | m + 1 => by
      have ih : coeffW w i * coeffW w (i + m + 2)
          ≤ coeffW w (i + 1) * coeffW w (i + m + 1) :=
        coeffW_step hw0 hw1 hwpos i m
      have hlc : coeffW w (i + m + 1) * coeffW w (i + m + 3)
          ≤ coeffW w (i + m + 2) * coeffW w (i + m + 2) :=
        FusionGenFunction.coeffW_logConcave hw0 hw1 (i + m + 1)
      have hz : (0 : Q') ≤ coeffW w (i + m + 3) := coeffW_nonneg hw0 _
      have hB : (0 : Q') ≤ coeffW w (i + 1) := coeffW_nonneg hw0 _
      have hypos : (0 : Q') < coeffW w (i + m + 2) := coeffW_pos hwpos _
      -- step1 : (A·y)·z ≤ (B·x)·z
      have step1 := Q'.mul_le_mul_of_nonneg_right _ _ (coeffW w (i + m + 3)) ih hz
      -- (B·x)·z ≃ B·(x·z)
      have eassoc :=
        Q'.mul_assoc_eqv (coeffW w (i + 1)) (coeffW w (i + m + 1)) (coeffW w (i + m + 3))
      -- step2 : B·(x·z) ≤ B·(y·y)
      have step2 := Q'.mul_le_mul_of_nonneg_left _ _ (coeffW w (i + 1)) hlc hB
      have hcomb : (coeffW w i * coeffW w (i + m + 2)) * coeffW w (i + m + 3)
          ≤ coeffW w (i + 1) * (coeffW w (i + m + 2) * coeffW w (i + m + 2)) :=
        Q'.le_trans' _ _ _ step1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv eassoc) step2)
      -- e1 : (A·y)·z ≃ y·(A·z)
      have e1 : ((coeffW w i * coeffW w (i + m + 2)) * coeffW w (i + m + 3)).eqv
          (coeffW w (i + m + 2) * (coeffW w i * coeffW w (i + m + 3))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (coeffW w i) (coeffW w (i + m + 2)) (coeffW w (i + m + 3))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (coeffW w i) _ _
            (Q'.mul_comm_eqv (coeffW w (i + m + 2)) (coeffW w (i + m + 3)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv (coeffW w i) (coeffW w (i + m + 3)) (coeffW w (i + m + 2)))) ?_
        exact Q'.mul_comm_eqv (coeffW w i * coeffW w (i + m + 3)) (coeffW w (i + m + 2))
      -- e2 : B·(y·y) ≃ y·(B·y)
      have e2 : (coeffW w (i + 1) * (coeffW w (i + m + 2) * coeffW w (i + m + 2))).eqv
          (coeffW w (i + m + 2) * (coeffW w (i + 1) * coeffW w (i + m + 2))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv (coeffW w (i + 1)) (coeffW w (i + m + 2)) (coeffW w (i + m + 2)))) ?_
        exact Q'.mul_comm_eqv (coeffW w (i + 1) * coeffW w (i + m + 2)) (coeffW w (i + m + 2))
      have hY : coeffW w (i + m + 2) * (coeffW w i * coeffW w (i + m + 3))
          ≤ coeffW w (i + m + 2) * (coeffW w (i + 1) * coeffW w (i + m + 2)) :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm e1))
          (Q'.le_trans' _ _ _ hcomb (Q'.le_of_eqv e2))
      exact le_of_mul_le_mul_left_pos hypos hY

/-! ## 2. The rectangle (Hankel `2×2`-minor) log-concavity -/

/-- **`coeffW_rect` — the rectangle Hankel log-concavity.**  For all `a b i`,

    coeffW w i · coeffW w (i+a+b)  ≤  coeffW w (i+a) · coeffW w (i+b).

The most-spread product (extremes `i`, `i+a+b`) is dominated by the less-spread product
with the same index total.  Induction on `b`: peel one `coeffW_step` at the outer edge,
close with the IH at `i+1`.  This is exactly "every Hankel `2×2` minor of `coeffW` is
`≤ 0`" — `coeffW` is Pólya-frequency of order 2. -/
theorem coeffW_rect {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) :
    ∀ b a i, coeffW w i * coeffW w (i + a + b)
      ≤ coeffW w (i + a) * coeffW w (i + b) := by
  intro b
  induction b with
  | zero =>
      intro a i
      exact Q'.le_of_eqv (Q'.mul_comm_eqv (coeffW w i) (coeffW w (i + a)))
  | succ b ih =>
      intro a i
      cases a with
      | zero => exact Q'.le_refl' _
      | succ a' =>
          have hstep := coeffW_step hw0 hw1 hwpos i (a' + b)
          have hih := ih a' (i + 1)
          have e1 : coeffW w (i + (a' + 1) + (b + 1)) = coeffW w (i + (a' + b) + 2) :=
            congrArg (coeffW w) (by omega)
          have e2 : coeffW w (i + 1 + a' + b) = coeffW w (i + (a' + b) + 1) :=
            congrArg (coeffW w) (by omega)
          have e3 : coeffW w (i + 1 + a') = coeffW w (i + (a' + 1)) :=
            congrArg (coeffW w) (by omega)
          have e4 : coeffW w (i + 1 + b) = coeffW w (i + (b + 1)) :=
            congrArg (coeffW w) (by omega)
          rw [e1]
          rw [e2, e3, e4] at hih
          exact Q'.le_trans' _ _ _ hstep hih

/-! ## 3. The Cauchy–Binet per-summand atom -/

/-- **`coeffW_minor` — the Hankel `2×2` minor is `≤ 0`** (Cauchy–Binet matrix-element
form).  For strand rows `p, p+a` and columns `r, r+b`,

    coeffW w (p+r) · coeffW w ((p+a)+(r+b))  ≤  coeffW w (p+(r+b)) · coeffW w ((p+a)+r).

Reindexing of `coeffW_rect` with `i = p+r`, spreads `a` (rows) and `b` (columns). -/
theorem coeffW_minor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (p r a b : Nat) :
    coeffW w (p + r) * coeffW w (p + a + (r + b))
      ≤ coeffW w (p + (r + b)) * coeffW w (p + a + r) := by
  have h := coeffW_rect hw0 hw1 hwpos b a (p + r)
  have e1 : coeffW w (p + r + a + b) = coeffW w (p + a + (r + b)) :=
    congrArg (coeffW w) (by omega)
  have e2 : coeffW w (p + r + a) = coeffW w (p + a + r) :=
    congrArg (coeffW w) (by omega)
  have e3 : coeffW w (p + r + b) = coeffW w (p + (r + b)) :=
    congrArg (coeffW w) (by omega)
  rw [e1, e2, e3] at h
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

/-- The Hankel `2×2` minor of `coeffW` in additive (`X + -Y`) form. -/
def coeffMinor (w : Q') (p a r b : Nat) : Q' :=
  coeffW w (p + r) * coeffW w (p + a + (r + b))
    + -(coeffW w (p + (r + b)) * coeffW w (p + a + r))

/-- `X ≤ Y ⟹ X + -Y ≤ 0`. -/
theorem q_add_neg_nonpos {X Y : Q'} (h : X ≤ Y) : X + -Y ≤ (0 : Q') :=
  Q'.le_trans' _ _ _ (Q'.add_le_add h (Q'.le_refl' (-Y)))
    (Q'.le_of_eqv (Q'.add_neg_self_eqv Y))

/-- **`coeffMinor_nonpos`** — the Hankel minor is `≤ 0` (from `coeffW_minor`). -/
theorem coeffMinor_nonpos {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (p a r b : Nat) :
    coeffMinor w p a r b ≤ (0 : Q') :=
  q_add_neg_nonpos (coeffW_minor hw0 hw1 hwpos p r a b)

/-- Product of two nonpositive rationals is nonnegative. -/
theorem q_mul_nonpos_nonpos {a b : Q'} (ha : a ≤ (0 : Q')) (hb : b ≤ (0 : Q')) :
    (0 : Q') ≤ a * b := by
  have hna : (0 : Q') ≤ -a :=
    Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le ha) (Q'.le_of_eqv (q_zero_add_eqv (-a)))
  have hnb : (0 : Q') ≤ -b :=
    Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hb) (Q'.le_of_eqv (q_zero_add_eqv (-b)))
  have h := Q'.mul_nonneg _ _ hna hnb
  have e : ((-a) * (-b)).eqv (a * b) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b))
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b))
        (Q'.neg_neg_eqv (a * b)))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv e)

/-- **`coeffMinorProd_nonneg` — the Cauchy–Binet per-pair positivity.**  The product of
the two Hankel `2×2` minors (rows `(p, p+ap)` and `(q, q+aq)` sharing the column pair
`(r, r+b)`) is `≥ 0`: two `≤ 0` factors.  This is the exact per-summand content of the
Andréief expansion of the truncated-lag-correlation TP₂ residual `LagCorrTP2`. -/
theorem coeffMinorProd_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (p ap q aq r b : Nat) :
    (0 : Q') ≤ coeffMinor w p ap r b * coeffMinor w q aq r b :=
  q_mul_nonpos_nonpos (coeffMinor_nonpos hw0 hw1 hwpos p ap r b)
    (coeffMinor_nonpos hw0 hw1 hwpos q aq r b)

/-! ## 4. Line-sum / lag-correlation finite facts -/

/-- **`lineSum_nonneg`** — the antidiagonal line-sum of the lag-correlation is `≥ 0`. -/
theorem lineSum_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N t : Nat) :
    (0 : Q') ≤ lineSum (lagCorr w N) t := by
  unfold lineSum
  exact fsum_nonneg (fun p => lagCorr_nonneg hw0 N p (t - p)) _

/-- **`lagCorr_tp2_diag` — the degenerate TP₂ slice `p = p'`.**  With equal rows the
`LagCorrTP2` inequality holds with equality (commutativity), an honest green sub-case of
the analytic core A2. -/
theorem lagCorr_tp2_diag (w : Q') (N p q q' : Nat) :
    lagCorr w N p q' * lagCorr w N p q ≤ lagCorr w N p q * lagCorr w N p q' :=
  Q'.le_of_eqv (Q'.mul_comm_eqv _ _)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `coeffW_step` — single-step Hankel log-concavity of `coeffW` (all `m`, `i`).
  * `coeffW_rect` — the rectangle Hankel `2×2`-minor log-concavity (all `a`, `b`, `i`);
    `coeffW` is Pólya-frequency of order 2.  THE analytic atom A2 was missing.
  * `coeffW_minor`, `coeffMinor`, `coeffMinor_nonpos` — the Cauchy–Binet matrix-element
    form: every Hankel minor of the theta weight is `≤ 0`.
  * `coeffMinorProd_nonneg` — the per-pair Cauchy–Binet positivity (product of two
    minors `≥ 0`): the per-summand content of `LagCorrTP2`.
  * `lineSum_nonneg`, `lagCorr_tp2_diag` — finite line-sum / lag-correlation facts and the
    degenerate `p = p'` TP₂ slice.
  * helpers `q_add_neg_nonpos`, `q_mul_nonpos_nonpos`.

NAMED OPEN (carried from `RoundD`, not inhabited here):
  * `LagCorrTP2 w` (A2) — full TP₂ of the TRUNCATED lag-correlation.  Round E supplies its
    analytic atom (`coeffW_rect`) and per-summand positivity (`coeffMinorProd_nonneg`);
    what remains is the Andréief half-sum identity for the common-range part plus the
    `N`-truncation boundary defect (absorbed by `coeffW_superLogConcave`).
  * `StrandReduction w` (A1 `reindex` + A3 `lineSumLogConcave`).  CORRECTION: A3 does NOT
    follow from the bare `LagCorrTP2.tp2` field (rank-1 `f=(1,0,1)` counterexample,
    `L=(1,0,2,0,1)`); its honest seed is the Gram/Hankel log-concavity of `coeffW`
    (`coeffW_rect`), proved here.

HONEST VERDICT.  Round E proves the missing analytic atom of A2 — every Hankel `2×2`
minor of the theta weight is `≤ 0` (`coeffW` is PF₂), for all shifts — and the per-pair
Cauchy–Binet positivity that is the per-summand content of the truncated-lag-correlation
TP₂, and CORRECTS the A3 reduction (the bare TP₂ field is insufficient; the Hankel
structure proved here is the right seed).  It does NOT inhabit `LagCorrTP2`,
`StrandReduction`, `QuadGershgorinClosure`, or `S1Dominance` for general `N`.  This is a
structural advance on one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills
mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundE

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffW_step
#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffW_rect
#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffW_minor
#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffMinor_nonpos
#print axioms YMGap.Continuum.FusionCoreStepRoundE.q_mul_nonpos_nonpos
#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffMinorProd_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundE.lineSum_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundE.lagCorr_tp2_diag


/-! ===========================================================================
    ## Round F  (was `FusionCoreStepRoundF.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round F of the fusion box log-concavity node: the ANDRÉIEF / CAUCHY–BINET
HALF-SUM IDENTITY, proved in full, closing the COMMON-RANGE total positivity (A2's
analytic core), plus an HONEST routing of the remaining open content to the single
sharpest residual (A3 = the `r`-aggregation / sum-of-log-concave wall).

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundE` proved the per-summand Cauchy–Binet positivity
(`coeffMinorProd_nonneg`: a product of two Hankel `2×2` minors is `≥ 0`) and the Hankel
rectangle log-concavity (`coeffW_rect`), and named the remaining open content of A2
(`LagCorrTP2`) as the Andréief half-sum identity plus the `N`-truncation boundary defect.
Round F supplies that half-sum identity SYMBOLICALLY and closes the common-range total
positivity it implies.

ROUND-F DELIVERABLE 1 (the generic Plücker / Andréief identity — PROVED, axiom-clean).
  * `plucker8` — the 8-variable bilinear-minor identity
        (α γ)(β'δ') − (α δ)(β'γ')  +  (α'γ')(β δ) − (α'δ')(β γ)
          =  (α β' − α' β) · (γ δ' − γ' δ).
    This is the per-pair antisymmetrized content of the Andréief/Cauchy–Binet expansion:
    the symmetrized `(a,b)+(b,a)` summand of the `2×2` line-correlation determinant equals
    the PRODUCT of the two row-minors.  Pure `Q'` distributivity + four `mul_swap4`
    monomial regroupings; no positivity, no new axiom.

ROUND-F DELIVERABLE 2 (the half-sum determinant identity and its nonnegativity — PROVED).
  * `lagCorrCR` — the COMMON-RANGE lag-correlation `Σ_{r<n} c_{p+r} c_{q+r}` (a single
    shared cutoff `n` for all strand arguments; `lagCorr w N p q = lagCorrCR w (N+1−max p q)
    p q` by `lagCorr_eq_cr`).
  * `Mdet` — the `2×2` line-correlation determinant
        lagCorrCR(p,q)·lagCorrCR(p',q') − lagCorrCR(p,q')·lagCorrCR(p',q).
  * `Mdet_double_eq` — THE HALF-SUM IDENTITY: `Mdet + Mdet ≃ Σ_a Σ_b minorProd(a,b)`,
    where `minorProd(a,b) = pminor(p,p',a,b)·pminor(q,q',a,b)` is the product of the two
    Hankel row-minors.  (`fsum_mul_fsum` to open the products into a double sum, `fsum_swap`
    to symmetrize `a↔b`, and `plucker8` per summand.)
  * `minorProd_nonneg` — every summand is `≥ 0` (two `≤ 0` Hankel minors for `a ≤ b`, two
    `≥ 0` for `b ≤ a`), via `coeffMinor_nonpos` + the antisymmetry `pminor_antisymm`.
  * `Mdet_nonneg` — hence `Mdet ≥ 0` (the doubled sum is `≥ 0`; cancel the positive `2`).

ROUND-F DELIVERABLE 3 (the closed common-range total positivity — PROVED).
  * `lagCorrTP2_common` — `p ≤ p', q ≤ q' ⟹ lagCorrCR(p,q')·lagCorrCR(p',q) ≤
    lagCorrCR(p,q)·lagCorrCR(p',q')`.  The genuine "common-range truncated lag-correlation
    of the theta weight is totally positive of order 2", proved UNCONDITIONALLY (the
    Andréief half-sum closes it; no `LagCorrTP2`, no `QuadGershgorinClosure` hypothesis).

# HONESTY — what is NOT closed (the dependency correction kept sharp)

`StrandReduction`'s two fields are A1 (`reindex`, the strand bijection
`boxSum ≃ lineSum lagCorr`) and A3 (`lineSumLogConcave`, the antidiagonal line-sum
log-concavity); A2 (`LagCorrTP2`) is a stepping-stone that SEEDS A3, not a field on the
critical path.  Round F closes the COMMON-RANGE half-sum core (`lagCorrTP2_common`) — the
genuine new analytic result the scout's tool targets — but this does NOT inhabit
`StrandReduction`, and hence does NOT close `S1Dominance` for all `N`, because:

  * A2 with the REAL per-pair ranges (`lagCorr`, range `N+1−max(p,q)`, shortest for
    `(p',q')`) differs from the common-range `Mdet` by the boundary surplus of the three
    longer sums.  That boundary defect — absorbed by the factor-4 reserve
    `coeffW_superLogConcave` — is the residual of full `LagCorrTP2` (NAMED open here).
  * A3 is the GENUINE WALL.  A sum `Σ_r h_r` of per-shift log-concave autoconvolutions is
    NOT log-concave in general (`bracket_can_be_negative`; the rank-1 `f=(1,0,1)`,
    `L=(1,0,2,0,1)` slice of `RoundE`).  The half-sum gives TP₂ of the kernel but TP₂ does
    NOT imply PF₂ of its antidiagonal line-sums.  So A3 = `lineSumLogConcave` =
    `QuadGershgorinClosure` (the heat-kernel local-CLT) is the single sharpest residual,
    now with seed `coeffW_rect` and the `r`-aggregation as the isolated open content.

This is NOT a 4D Yang–Mills mass gap; it is the symbolic Andréief half-sum identity, the
closed common-range total positivity of the theta weight, and the honest routing of the
remaining open content to the `r`-aggregation wall (A3).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`coeffMinor` lemmas, `mul_swap4`
regroupings, finite `fsum` algebra (`fsum_mul_fsum`, `fsum_swap`, `fsum_add`, `fsum_neg`,
`fsum_nonneg`), and `omega` on index identities.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundF

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundE

/-! ## 0. Small `Q'` helpers -/

/-- `0 ≤ -x` from `x ≤ 0`. -/
theorem neg_nonneg_of_nonpos {x : Q'} (hx : x ≤ (0 : Q')) : (0 : Q') ≤ -x :=
  Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hx) (Q'.le_of_eqv (q_zero_add_eqv (-x)))

/-- `(-a)·(-b) ≃ a·b`. -/
theorem neg_mul_neg_eqv (a b : Q') : ((-a) * (-b)).eqv (a * b) :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b))
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b))
      (Q'.neg_neg_eqv (a * b)))

/-! ## 1. The generic Plücker / Andréief minor identity -/

/-- **`plucker8` — the bilinear `2×2`-minor (Plücker) identity over `Q'`.**

    ((α·γ)·(β'·δ') − (α·δ)·(β'·γ'))  +  ((α'·γ')·(β·δ) − (α'·δ')·(β·γ))
      ≃  (α·β' − α'·β) · (γ·δ' − γ'·δ).

The left side is the symmetrized `(a,b)+(b,a)` summand of a `2×2` line-correlation
determinant; the right side is the product of the two row-minors.  Proof: expand the RHS
by distributivity into four signed monomials, expand the LHS, and match each monomial via
`mul_swap4` (four-factor regrouping) + commutativity.  Pure `Q'` algebra. -/
theorem plucker8 (α α' β β' γ γ' δ δ' : Q') :
    (((α * γ) * (β' * δ') + -((α * δ) * (β' * γ')))
      + ((α' * γ') * (β * δ) + -((α' * δ') * (β * γ)))).eqv
      ((α * β' + -(α' * β)) * (γ * δ' + -(γ' * δ))) := by
  -- RHS ≃ E := (m1 + m2) + (m3 + m4) with the four canonical signed monomials.
  have hRHS : ((α * β' + -(α' * β)) * (γ * δ' + -(γ' * δ))).eqv
      (((α * β') * (γ * δ') + -((α * β') * (γ' * δ)))
        + (-((α' * β) * (γ * δ')) + (α' * β) * (γ' * δ))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (α * β') (-(α' * β)) (γ * δ' + -(γ' * δ))) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · -- (α·β')·(γδ' + -(γ'δ)) ≃ m1 + m2
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (α * β') (γ * δ') (-(γ' * δ))) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (α * β') (γ' * δ))
    · -- (-(α'·β))·(γδ' + -(γ'δ)) ≃ m3 + m4
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-(α' * β)) (γ * δ') (-(γ' * δ))) ?_
      refine Q'.add_eqv_congr' ?_ ?_
      · exact Q'.neg_mul_eqv (α' * β) (γ * δ')
      · exact neg_mul_neg_eqv (α' * β) (γ' * δ)
  -- LHS monomial matches (L1≃m1, L2≃m2, L3≃m4, L4≃m3).
  have hL1 : ((α * γ) * (β' * δ')).eqv ((α * β') * (γ * δ')) := mul_swap4 α γ β' δ'
  have hL2 : (-((α * δ) * (β' * γ'))).eqv (-((α * β') * (γ' * δ))) := by
    refine Q'.neg_eqv_congr _ _ ?_
    refine Q'.eqv_trans _ _ _ (mul_swap4 α δ β' γ') ?_
    exact Q'.mul_eqv_congr_left (α * β') _ _ (Q'.mul_comm_eqv δ γ')
  have hL3 : ((α' * γ') * (β * δ)).eqv ((α' * β) * (γ' * δ)) := mul_swap4 α' γ' β δ
  have hL4 : (-((α' * δ') * (β * γ))).eqv (-((α' * β) * (γ * δ'))) := by
    refine Q'.neg_eqv_congr _ _ ?_
    refine Q'.eqv_trans _ _ _ (mul_swap4 α' δ' β γ) ?_
    exact Q'.mul_eqv_congr_left (α' * β) _ _ (Q'.mul_comm_eqv δ' γ)
  -- LHS ≃ E (the second group needs an a↔b commute, L3+L4 ≃ m4+m3 ≃ m3+m4).
  have hLHS : (((α * γ) * (β' * δ') + -((α * δ) * (β' * γ')))
      + ((α' * γ') * (β * δ) + -((α' * δ') * (β * γ)))).eqv
      (((α * β') * (γ * δ') + -((α * β') * (γ' * δ)))
        + (-((α' * β) * (γ * δ')) + (α' * β) * (γ' * δ))) := by
    refine Q'.add_eqv_congr' (Q'.add_eqv_congr' hL1 hL2) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hL3 hL4) ?_
    exact Q'.add_comm_eqv ((α' * β) * (γ' * δ)) (-((α' * β) * (γ * δ')))
  exact Q'.eqv_trans _ _ _ hLHS (Q'.eqv_symm hRHS)

/-! ## 2. The common-range lag-correlation and its `2×2` determinant -/

/-- The COMMON-RANGE lag-correlation `Σ_{r<n} c_{p+r}·c_{q+r}` (a single cutoff `n`). -/
def lagCorrCR (w : Q') (n p q : Nat) : Q' :=
  fsum (fun r => coeffW w (p + r) * coeffW w (q + r)) n

/-- The real `lagCorr` (RoundD, range `N+1−max p q`) is the common-range correlation at
the pair-dependent cutoff `N+1−max p q`.  (Definitional bridge.) -/
theorem lagCorr_eq_cr (w : Q') (N p q : Nat) :
    lagCorr w N p q = lagCorrCR w (N + 1 - Nat.max p q) p q := rfl

/-- The single Hankel row-minor `pminor(p,p',a,b) = c_{p+a}c_{p'+b} − c_{p+b}c_{p'+a}`. -/
def pminor (w : Q') (p p' a b : Nat) : Q' :=
  coeffW w (p + a) * coeffW w (p' + b) + -(coeffW w (p + b) * coeffW w (p' + a))

/-- The `2×2` line-correlation determinant of the common-range lag-correlation. -/
def Mdet (w : Q') (n p q p' q' : Nat) : Q' :=
  lagCorrCR w n p q * lagCorrCR w n p' q' + -(lagCorrCR w n p q' * lagCorrCR w n p' q)

/-- The symmetrized determinant summand (the `(a,b)` term of `Mdet` opened as a double
sum). -/
def term2 (w : Q') (p q p' q' a b : Nat) : Q' :=
  (coeffW w (p + a) * coeffW w (q + a)) * (coeffW w (p' + b) * coeffW w (q' + b))
    + -((coeffW w (p + a) * coeffW w (q' + a)) * (coeffW w (p' + b) * coeffW w (q + b)))

/-- The product of the two row-minors — the per-pair summand of the half-sum. -/
def minorProd (w : Q') (p q p' q' a b : Nat) : Q' :=
  pminor w p p' a b * pminor w q q' a b

/-! ### 2a. Antisymmetry of the row-minor and per-summand nonnegativity -/

/-- **`pminor_antisymm`** — `pminor(p,p',a,b) ≃ −pminor(p,p',b,a)` (the Hankel minor is
antisymmetric in its two column indices). -/
theorem pminor_antisymm (w : Q') (p p' a b : Nat) :
    (pminor w p p' a b).eqv (-(pminor w p p' b a)) := by
  unfold pminor
  -- pminor a b = P + -Q,  pminor b a = Q + -P  with  P = c_{p+a}c_{p'+b}, Q = c_{p+b}c_{p'+a}
  -- so -(pminor b a) = -(Q + -P) ≃ -Q + P ≃ P + -Q.
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_add_eqv (coeffW w (p + b) * coeffW w (p' + a))
      (-(coeffW w (p + a) * coeffW w (p' + b)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (coeffW w (p + a) * coeffW w (p' + b)))) ?_
  exact Q'.add_comm_eqv _ _

/-- **`pminor_eq_coeffMinor`** — for `p ≤ p'` and `a ≤ b`, the row-minor equals the
`RoundE` Hankel minor `coeffMinor w p (p'−p) a (b−a)`. -/
theorem pminor_eq_coeffMinor {w : Q'} {p p' a b : Nat} (hpp' : p ≤ p') (hab : a ≤ b) :
    pminor w p p' a b = coeffMinor w p (p' - p) a (b - a) := by
  unfold pminor coeffMinor
  rw [show p' + b = p + (p' - p) + (a + (b - a)) by omega,
      show p + b = p + (a + (b - a)) by omega,
      show p' + a = p + (p' - p) + a by omega]

/-- **`pminor_nonpos`** — for `p ≤ p'` and `a ≤ b`, the row-minor is `≤ 0`. -/
theorem pminor_nonpos {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p p' a b : Nat} (hpp' : p ≤ p') (hab : a ≤ b) :
    pminor w p p' a b ≤ (0 : Q') := by
  rw [pminor_eq_coeffMinor hpp' hab]
  exact coeffMinor_nonpos hw0 hw1 hwpos p (p' - p) a (b - a)

/-- **`pminor_nonneg`** — for `p ≤ p'` and `b ≤ a`, the row-minor is `≥ 0` (antisymmetry
flips the `a ≤ b` sign). -/
theorem pminor_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p p' a b : Nat} (hpp' : p ≤ p') (hba : b ≤ a) :
    (0 : Q') ≤ pminor w p p' a b := by
  have hnp : pminor w p p' b a ≤ (0 : Q') := pminor_nonpos hw0 hw1 hwpos hpp' hba
  exact Q'.le_trans' _ _ _ (neg_nonneg_of_nonpos hnp)
    (Q'.le_of_eqv (Q'.eqv_symm (pminor_antisymm w p p' a b)))

/-- **`minorProd_nonneg`** — every half-sum summand is `≥ 0`.  Both row-minors are `≤ 0`
when `a ≤ b` (product of two nonpositives) and both `≥ 0` when `b ≤ a`. -/
theorem minorProd_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p q p' q' : Nat} (hpp' : p ≤ p') (hqq' : q ≤ q') (a b : Nat) :
    (0 : Q') ≤ minorProd w p q p' q' a b := by
  unfold minorProd
  rcases Nat.le_total a b with hab | hba
  · exact q_mul_nonpos_nonpos (pminor_nonpos hw0 hw1 hwpos hpp' hab)
      (pminor_nonpos hw0 hw1 hwpos hqq' hab)
  · exact Q'.mul_nonneg _ _ (pminor_nonneg hw0 hw1 hwpos hpp' hba)
      (pminor_nonneg hw0 hw1 hwpos hqq' hba)

/-! ### 2b. Depth-2 `fsum` add / neg combinators -/

/-- `Σ_a Σ_b F + Σ_a Σ_b G ≃ Σ_a Σ_b (F + G)`. -/
theorem q2_add (F G : Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (F a) n) n + fsum (fun a => fsum (G a) n) n).eqv
      (fsum (fun a => fsum (fun b => F a b + G a b) n) n) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (fsum_add (fun a => fsum (F a) n) (fun a => fsum (G a) n) n)) ?_
  exact fsum_eqv_congr _ _ (fun a => Q'.eqv_symm (fsum_add (F a) (G a) n)) n

/-- `−(Σ_a Σ_b F) ≃ Σ_a Σ_b (−F)`. -/
theorem q2_neg (F : Nat → Nat → Q') (n : Nat) :
    (-(fsum (fun a => fsum (F a) n) n)).eqv
      (fsum (fun a => fsum (fun b => -(F a b)) n) n) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (fsum_neg (fun a => fsum (F a) n) n)) ?_
  exact fsum_eqv_congr _ _ (fun a => Q'.eqv_symm (fsum_neg (F a) n)) n

/-! ### 2c. The half-sum identity -/

/-- The pointwise Plücker identity in `coeffW` form: the symmetrized determinant summand
`term2(a,b) + term2(b,a)` equals the product of row-minors `minorProd(a,b)`. -/
theorem term2_swap_eq_minorProd (w : Q') (p q p' q' a b : Nat) :
    (term2 w p q p' q' a b + term2 w p q p' q' b a).eqv (minorProd w p q p' q' a b) := by
  unfold term2 minorProd pminor
  exact plucker8 (coeffW w (p + a)) (coeffW w (p + b)) (coeffW w (p' + a))
    (coeffW w (p' + b)) (coeffW w (q + a)) (coeffW w (q + b)) (coeffW w (q' + a))
    (coeffW w (q' + b))

/-- **`Mdet_eq_termSum`** — the common-range determinant is the double sum of `term2`.
`fsum_mul_fsum` opens each product of column sums into a double sum; the two double sums
combine into one. -/
theorem Mdet_eq_termSum (w : Q') (n p q p' q' : Nat) :
    (Mdet w n p q p' q').eqv
      (fsum (fun a => fsum (fun b => term2 w p q p' q' a b) n) n) := by
  unfold Mdet
  have hAB : (lagCorrCR w n p q * lagCorrCR w n p' q').eqv
      (fsum (fun a => fsum (fun b =>
        (coeffW w (p + a) * coeffW w (q + a)) * (coeffW w (p' + b) * coeffW w (q' + b)))
        n) n) :=
    fsum_mul_fsum (fun a => coeffW w (p + a) * coeffW w (q + a))
      (fun b => coeffW w (p' + b) * coeffW w (q' + b)) n n
  have hCD : (lagCorrCR w n p q' * lagCorrCR w n p' q).eqv
      (fsum (fun a => fsum (fun b =>
        (coeffW w (p + a) * coeffW w (q' + a)) * (coeffW w (p' + b) * coeffW w (q + b)))
        n) n) :=
    fsum_mul_fsum (fun a => coeffW w (p + a) * coeffW w (q' + a))
      (fun b => coeffW w (p' + b) * coeffW w (q + b)) n n
  -- Mdet ≃ ΣΣ kPlus + -(ΣΣ kMinus) ≃ ΣΣ kPlus + ΣΣ (-kMinus) ≃ ΣΣ (kPlus + -kMinus) = ΣΣ term2
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hAB (Q'.neg_eqv_congr _ _ hCD)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
    (q2_neg (fun a b =>
      (coeffW w (p + a) * coeffW w (q' + a)) * (coeffW w (p' + b) * coeffW w (q + b))) n)) ?_
  exact q2_add
    (fun a b => (coeffW w (p + a) * coeffW w (q + a)) * (coeffW w (p' + b) * coeffW w (q' + b)))
    (fun a b => -((coeffW w (p + a) * coeffW w (q' + a)) * (coeffW w (p' + b) * coeffW w (q + b))))
    n

/-- **`Mdet_double_eq` — THE ANDRÉIEF HALF-SUM IDENTITY.**  Twice the common-range
determinant equals the double sum of the row-minor products:
`Mdet + Mdet ≃ Σ_a Σ_b minorProd(a,b)`.  (`Mdet ≃ Σ term2(a,b) ≃ Σ term2(b,a)` by the
`a↔b` swap; add and apply `term2_swap_eq_minorProd` per summand.) -/
theorem Mdet_double_eq (w : Q') (n p q p' q' : Nat) :
    (Mdet w n p q p' q' + Mdet w n p q p' q').eqv
      (fsum (fun a => fsum (fun b => minorProd w p q p' q' a b) n) n) := by
  have hS : (Mdet w n p q p' q').eqv
      (fsum (fun a => fsum (fun b => term2 w p q p' q' a b) n) n) :=
    Mdet_eq_termSum w n p q p' q'
  -- swapped form: Mdet ≃ ΣΣ term2(b,a)
  have hSwap : (fsum (fun a => fsum (fun b => term2 w p q p' q' a b) n) n).eqv
      (fsum (fun a => fsum (fun b => term2 w p q p' q' b a) n) n) :=
    fsum_swap (fun a b => term2 w p q p' q' a b) n n
  have hS' : (Mdet w n p q p' q').eqv
      (fsum (fun a => fsum (fun b => term2 w p q p' q' b a) n) n) :=
    Q'.eqv_trans _ _ _ hS hSwap
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hS hS') ?_
  refine Q'.eqv_trans _ _ _
    (q2_add (fun a b => term2 w p q p' q' a b) (fun a b => term2 w p q p' q' b a) n) ?_
  exact fsum_eqv_congr _ _
    (fun a => fsum_eqv_congr _ _ (fun b => term2_swap_eq_minorProd w p q p' q' a b) n) n

/-! ## 3. Nonnegativity of the determinant and the closed common-range TP₂ -/

/-- **`Mdet_nonneg`** — the common-range `2×2` line-correlation determinant is `≥ 0`.
The doubled determinant is `Σ_a Σ_b minorProd ≥ 0` (`fsum_nonneg` twice, `minorProd_nonneg`
per summand); cancel the positive factor `2`. -/
theorem Mdet_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p q p' q' : Nat} (hpp' : p ≤ p') (hqq' : q ≤ q') (n : Nat) :
    (0 : Q') ≤ Mdet w n p q p' q' := by
  -- doubled determinant ≥ 0
  have hsum : (0 : Q') ≤ fsum (fun a => fsum (fun b => minorProd w p q p' q' a b) n) n :=
    fsum_nonneg (fun a =>
      fsum_nonneg (fun b => minorProd_nonneg hw0 hw1 hwpos hpp' hqq' a b) n) n
  have hdouble : (0 : Q') ≤ Mdet w n p q p' q' + Mdet w n p q p' q' :=
    Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (Mdet_double_eq w n p q p' q'))
  -- 0 ≤ 2 · Mdet, then cancel the positive 2
  have h2pos : (0 : Q') < Q'.ofNat 2 := Q'.ofNat_succ_pos 1
  have hmul : (0 : Q') ≤ Q'.ofNat 2 * Mdet w n p q p' q' :=
    Q'.le_trans' _ _ _ hdouble (Q'.ge_of_eqv (ofNat_two_mul_eqv (Mdet w n p q p' q')))
  have hmul0 : Q'.ofNat 2 * (0 : Q') ≤ Q'.ofNat 2 * Mdet w n p q p' q' :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (q_mul_zero (Q'.ofNat 2))) hmul
  exact le_of_mul_le_mul_left_pos h2pos hmul0

/-- **`lagCorrTP2_common` — THE CLOSED COMMON-RANGE TOTAL POSITIVITY (A2's analytic core).**
For `0 < w ≤ 1` and any shared cutoff `n`,

    p ≤ p',  q ≤ q'   ⟹   lagCorrCR(p,q')·lagCorrCR(p',q) ≤ lagCorrCR(p,q)·lagCorrCR(p',q').

The truncated lag-correlation of the theta weight at a single common range is totally
positive of order 2 — proved UNCONDITIONALLY via the Andréief half-sum identity
(`Mdet_nonneg`), no `LagCorrTP2`/`QuadGershgorinClosure` hypothesis. -/
theorem lagCorrTP2_common {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p q p' q' : Nat} (hpp' : p ≤ p') (hqq' : q ≤ q') (n : Nat) :
    lagCorrCR w n p q' * lagCorrCR w n p' q ≤ lagCorrCR w n p q * lagCorrCR w n p' q' :=
  Q'.le_of_sub_nonneg (Mdet_nonneg hw0 hw1 hwpos hpp' hqq' n)

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `plucker8` — the generic bilinear `2×2`-minor (Plücker/Andréief) identity over `Q'`.
  * `pminor_antisymm`, `pminor_eq_coeffMinor`, `pminor_nonpos`, `pminor_nonneg`,
    `minorProd_nonneg` — the row-minor algebra and per-summand sign (from `coeffMinor`).
  * `Mdet_eq_termSum`, `Mdet_double_eq` — the half-sum identity `Mdet + Mdet ≃
    Σ_a Σ_b minorProd(a,b)`.
  * `Mdet_nonneg` — the common-range `2×2` line-correlation determinant is `≥ 0`.
  * `lagCorrTP2_common` — the CLOSED common-range total positivity of the theta weight
    (A2's analytic core), proved unconditionally.
  * `lagCorr_eq_cr` — the definitional bridge from the real per-pair `lagCorr` to
    `lagCorrCR`.

NAMED OPEN (carried; NOT inhabited here — the honest dependency correction):
  * `LagCorrTP2 w` (A2, full per-pair ranges) — equals `lagCorrTP2_common` PLUS the
    boundary reconciliation of the four different per-pair cutoffs `N+1−max(·,·)` (the
    surplus terms of the three longer sums), absorbed by `coeffW_superLogConcave`.  A2 is a
    stepping-stone, NOT a field of `StrandReduction`.
  * `StrandReduction w` = A1 (`reindex`) + A3 (`lineSumLogConcave`).  A3 is the GENUINE
    WALL: `Σ_r h_r` of per-shift log-concave autoconvolutions is not log-concave in general
    (`bracket_can_be_negative`); TP₂ of the kernel (proved here for the common range) does
    NOT imply PF₂ of its antidiagonal line-sums.  A3 = `QuadGershgorinClosure` (the
    heat-kernel local-CLT), seed `coeffW_rect`, with the `r`-aggregation isolated as the
    single sharpest residual.

HONEST VERDICT.  Round F proves the Andréief/Cauchy–Binet half-sum identity and closes the
COMMON-RANGE total positivity of the theta weight — the genuine new analytic result A2's
core needed — but this does NOT inhabit `StrandReduction` and does NOT close `S1Dominance`
for all `N`: the per-pair boundary defect (full A2) and, decisively, the `r`-aggregation /
sum-of-log-concave wall (A3 = `QuadGershgorinClosure`) remain the open content.  This is a
structural advance on one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass
gap. -/

end YMGap.Continuum.FusionCoreStepRoundF

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundF.plucker8
#print axioms YMGap.Continuum.FusionCoreStepRoundF.pminor_antisymm
#print axioms YMGap.Continuum.FusionCoreStepRoundF.pminor_eq_coeffMinor
#print axioms YMGap.Continuum.FusionCoreStepRoundF.pminor_nonpos
#print axioms YMGap.Continuum.FusionCoreStepRoundF.pminor_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundF.minorProd_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundF.term2_swap_eq_minorProd
#print axioms YMGap.Continuum.FusionCoreStepRoundF.Mdet_eq_termSum
#print axioms YMGap.Continuum.FusionCoreStepRoundF.Mdet_double_eq
#print axioms YMGap.Continuum.FusionCoreStepRoundF.Mdet_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundF.lagCorrTP2_common


/-! ===========================================================================
    ## Round G  (was `FusionCoreStepRoundG.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round G of the fusion box log-concavity node: the GREEN "DOMINANT
CENTRAL TERM" DISCRIMINANT ENGINE and the honest reduction of A3
(`StrandReduction.lineSumLogConcave` / `QuadGershgorinClosure`) to ONE sharp named
residual — a concrete central-autoconvolution reserve `δ ≥ ε² + 2ε`.

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundD/F` split `QuadGershgorinClosure` into the finite strand reindex
(A1), the analytic common-range TP₂ core (A2, CLOSED in Round F: `lagCorrTP2_common`),
and the genuine wall A3 `StrandReduction.lineSumLogConcave` (the antidiagonal line-sum
log-concavity — a sum `Σ_r H_r` of per-shift log-concave autoconvolutions is not
log-concave in general).  Round G attacks A3 by CONVERTING the opaque "aggregate
Gershgorin/TP₂" bookkeeping into a fully green `Q'` discriminant engine plus a SINGLE
concrete numeric reserve target, replacing the hand-wave "factor-4 margin" with a sharp
threshold.

ROUND-G DELIVERABLE 1 (the green discriminant engine — PROVED, pure `Q'` arithmetic).
  * `prod_le_prod` — monotone product bound `x ≤ X, y ≤ Y, 0 ≤ y, 0 ≤ X ⟹ x·y ≤ X·Y`.
  * `dominant_term_LC` (E1) — the general reserve/domination threshold: with an
    `ε`-domination of the off-central mass and a `(1+δ)` central reserve, if
    `ε² + 2ε ≤ δ` then `(am+bm)·(ap+bp) ≤ (a₀+b₀)²`.  Robust: NO log-concavity assumed on
    the off mass `b`.  (Proved by the monotone route `a±+b± ≤ (1+ε)a±`, giving the sharp
    `(1+ε)² ≤ 1+δ` threshold; the discriminant is never expanded.)
  * `dominant_term_LC_four` (E3) — the clean factor-4 corollary (`δ=3, ε=1`): the exact
    reserve `4·(amap) ≤ a₀²` pays the three unit domination terms.  This is where the
    factor-4 is *exactly* load-bearing.
  * `dominant_term_LC3` — the 3-shift grouping (`b := b + c`), from E3.

ROUND-G DELIVERABLE 2 (the dominant-central-term magnitude bound — PROVED, all `s`).
  * `coeffW_ratio_quarter` — the all-`s` geometric ratio reserve `4·c_{s+1} ≤ c_s` on
    `0 < w ≤ 1/2`, by induction from `coeffW_superLogConcave_four` (the factor-4 atom) with
    base `coeffW1_le_quarter` and the strict positivity `coeffW_pos` for the cancellation.
    This is the `ρ_s ≤ 1/4` backbone from which the geometric shift-tail `H_r ≤ 16^{-r}H_0`
    (hence `ε = Σ_{r≥1}16^{-r} = 1/15`) descends.
  * `coeffW_weak_decreasing` — the immediate consequence `c_{s+1} ≤ c_s`.

ROUND-G DELIVERABLE 3 (the reduction of A3 to ONE sharp named residual — REDUCTION).
  * `CentralAutoconvReserve w` — the SINGLE sharp residual: a decomposition
    `lineSum = H₀ + off` (central autoconvolution + off-central mass), an `ε`-domination
    `off ≤ ε·H₀`, and the central reserve `(1+δ)·H₀(s)·H₀(s+2) ≤ H₀(s+1)²` with the sharp
    threshold `ε² + 2ε ≤ δ`.  This pins the opaque `LagCorrTP2`/`QuadGershgorinClosure`
    down to a concrete uniform central-autoconvolution log-concavity margin.
  * `lineSumLogConcaveOfReserve` — THE REDUCTION: a reserve witness discharges A3
    (`StrandReduction.lineSumLogConcave`) for every `N, s`, via E1.
  * `strandReductionOfReserve` — packaged with the finite A1 reindex, yields a full
    `StrandReduction` (hence `S1Dominance` for every `N` through Round D's wiring).
  * `eps_fifteenth_threshold` — the concrete numeric anchor: with `ε = 1/15` the sharp
    threshold is `δ ≥ 31/225` (`decide`), the honest quantified residual replacing the
    "factor-4" hand-wave.

# HONESTY — what is NOT closed

The residual `CentralAutoconvReserve` is a Type-level NAMED-OPEN structure; it is NOT
inhabited here for general `N`.  Its `reserve` field (the truncated central-autoconvolution
log-concavity margin `δ ≥ 31/225`, uniform in `s` and in the `N`-truncation) is the genuine
remaining local-CLT content — now sharply quantified rather than opaque.  Round G closes
the *aggregation algebra* of A3 (the discriminant engine) and reduces A3 to this ONE
concrete inequality; it does NOT prove that inequality.  This is NOT a 4D Yang–Mills mass
gap; it is a structural sharpening of one box-level sub-fact.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`lineSum`/`lagCorr` lemmas, structural
reductions, and `decide` only on closed concrete-rational facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level.
-/


namespace YMGap.Continuum.FusionCoreStepRoundG

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD

/-! ## 0. Small `Q'` helpers -/

/-- **`prod_le_prod`** — monotone product bound: `x ≤ X`, `y ≤ Y`, `0 ≤ y`, `0 ≤ X` give
`x·y ≤ X·Y` (multiply `x ≤ X` on the right by `y ≥ 0`, then `y ≤ Y` on the left by
`X ≥ 0`). -/
theorem prod_le_prod {x X y Y : Q'} (hx : x ≤ X) (hy : y ≤ Y)
    (hy0 : (0 : Q') ≤ y) (hX : (0 : Q') ≤ X) : x * y ≤ X * Y :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right x X y hx hy0)
    (Q'.mul_le_mul_of_nonneg_left y Y X hy hX)

/-- `((1+e)·a) ≃ a + e·a`. -/
theorem oneEps_mul_eqv (e a : Q') : ((1 + e) * a).eqv (a + e * a) :=
  Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 e a)
    (Q'.add_eqv_congr_right (1 * a) a (e * a) (Q'.one_mul_eqv a))

/-- `(4:Q')·z ≃ (z+z)+(z+z)` — the closed scalar split of the factor-4 reserve. -/
theorem four_mul_eqv (z : Q') : ((4 : Q') * z).eqv ((z + z) + (z + z)) := by
  have h4 : ((4 : Q') : Q').eqv (((1 : Q') + 1) + (1 + 1)) := by decide
  have twoz : (((1 : Q') + 1) * z).eqv (z + z) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 z)
      (Q'.add_eqv_congr' (Q'.one_mul_eqv z) (Q'.one_mul_eqv z))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (4 : Q') ((1 + 1) + (1 + 1)) z h4) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 + 1) (1 + 1) z) ?_
  exact Q'.add_eqv_congr' twoz twoz

/-- `(x+x)·(y+y) ≃ 4·(x·y)` — the factor-4 form of the doubled central product. -/
theorem two_two_mul_eqv (x y : Q') : ((x + x) * (y + y)).eqv ((4 : Q') * (x * y)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv x x (y + y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_add_eqv x y y) (Q'.mul_add_eqv x y y)) ?_
  exact Q'.eqv_symm (four_mul_eqv (x * y))

/-- **`sq_oneEps_le`** — the sharp threshold `(1+e)² ≤ 1+d` when `e² + (e+e) ≤ d`.
`(1+e)² ≃ (1+e)+(e+e²) ≃ 1 + (e+(e+e²))` and `e+(e+e²) ≃ e²+(e+e) ≤ d`. -/
theorem sq_oneEps_le (e d : Q') (_he : (0 : Q') ≤ e)
    (hthr : e * e + (e + e) ≤ d) : (1 + e) * (1 + e) ≤ (1 + d) := by
  have hexp : ((1 + e) * (1 + e)).eqv ((1 + e) + (e + e * e)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 e (1 + e)) ?_
    refine Q'.add_eqv_congr' (Q'.one_mul_eqv (1 + e)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv e 1 e) ?_
    exact Q'.add_eqv_congr_right (e * 1) e (e * e) (Q'.mul_one_eqv e)
  have hassoc : (((1 + e) + (e + e * e))).eqv (1 + (e + (e + e * e))) :=
    Q'.add_assoc_eqv 1 e (e + e * e)
  have hsum : e + (e + e * e) ≤ d := by
    have he2 : (e + (e + e * e)).eqv (e * e + (e + e)) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv e e (e * e)))
        (Q'.add_comm_eqv (e + e) (e * e))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he2) hthr
  have hstep : (1 + (e + (e + e * e))) ≤ (1 + d) := Q'.add_le_add_left 1 _ d hsum
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hexp)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) hstep)

/-! ## 1. The green discriminant engine (E1, E3, 3-shift) -/

/-- **E1 — `dominant_term_LC` — the general reserve/domination threshold.**  With a
`(1+δ)` central reserve `(1+δ)·amap ≤ a₀²`, an `ε`-domination of the off masses
(`b± ≤ ε·a±`), and the sharp threshold `ε² + 2ε ≤ δ` (here written `ε·ε + (ε+ε) ≤ δ`), the
perturbed central product dominates:

    (am+bm)·(ap+bp) ≤ (a₀+b₀)·(a₀+b₀).

NO log-concavity is assumed on the off mass `b`.  Proof: `a±+b± ≤ (1+ε)·a±`, so the LHS is
`≤ (1+ε)²·amap ≤ (1+δ)·amap ≤ a₀² ≤ (a₀+b₀)²`. -/
theorem dominant_term_LC {ε δ am a₀ ap bm b₀ bp : Q'}
    (ham : (0 : Q') ≤ am) (hap : (0 : Q') ≤ ap) (ha₀ : (0 : Q') ≤ a₀)
    (hbp : (0 : Q') ≤ bp) (hb₀ : (0 : Q') ≤ b₀) (hε : (0 : Q') ≤ ε)
    (hres : (1 + δ) * (am * ap) ≤ a₀ * a₀)
    (hdomL : bm ≤ ε * am) (hdomR : bp ≤ ε * ap)
    (hthr : ε * ε + (ε + ε) ≤ δ) :
    (am + bm) * (ap + bp) ≤ (a₀ + b₀) * (a₀ + b₀) := by
  have hOneEps : (0 : Q') ≤ 1 + ε := Q'.zero_le_add 1 ε (by decide) hε
  have hXm : (0 : Q') ≤ (1 + ε) * am := Q'.mul_nonneg _ _ hOneEps ham
  have hAB : (0 : Q') ≤ ap + bp := Q'.zero_le_add _ _ hap hbp
  have hx : am + bm ≤ (1 + ε) * am :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left am bm (ε * am) hdomL)
      (Q'.ge_of_eqv (oneEps_mul_eqv ε am))
  have hy : ap + bp ≤ (1 + ε) * ap :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left ap bp (ε * ap) hdomR)
      (Q'.ge_of_eqv (oneEps_mul_eqv ε ap))
  have step1 : (am + bm) * (ap + bp) ≤ ((1 + ε) * am) * ((1 + ε) * ap) :=
    prod_le_prod hx hy hAB hXm
  have hswap : (((1 + ε) * am) * ((1 + ε) * ap)).eqv (((1 + ε) * (1 + ε)) * (am * ap)) :=
    mul_swap4 (1 + ε) am (1 + ε) ap
  have hsq : (1 + ε) * (1 + ε) ≤ 1 + δ := sq_oneEps_le ε δ hε hthr
  have haa : (0 : Q') ≤ am * ap := Q'.mul_nonneg _ _ ham hap
  have step2 : ((1 + ε) * (1 + ε)) * (am * ap) ≤ (1 + δ) * (am * ap) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsq haa
  have ha0b0 : a₀ ≤ a₀ + b₀ := Q'.add_le_self_of_nonneg a₀ b₀ hb₀
  have hX0 : (0 : Q') ≤ a₀ + b₀ := Q'.zero_le_add _ _ ha₀ hb₀
  have step4 : a₀ * a₀ ≤ (a₀ + b₀) * (a₀ + b₀) := prod_le_prod ha0b0 ha0b0 ha₀ hX0
  exact Q'.le_trans' _ _ _ step1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap)
      (Q'.le_trans' _ _ _ step2
        (Q'.le_trans' _ _ _ hres step4)))

/-- **E3 — `dominant_term_LC_four` — the clean factor-4 corollary.**  The exact reserve
`4·(amap) ≤ a₀²` pays the three unit domination terms: `(a±+b±) ≤ (a±+a±)`, so the LHS is
`≤ (am+am)(ap+ap) ≃ 4·amap ≤ a₀² ≤ (a₀+b₀)²`.  This is where the factor-4 is *exactly*
load-bearing (plain log-concavity, `δ=0`, fails). -/
theorem dominant_term_LC_four {am a₀ ap bm b₀ bp : Q'}
    (ham : (0 : Q') ≤ am) (hap : (0 : Q') ≤ ap) (ha₀ : (0 : Q') ≤ a₀)
    (hbp : (0 : Q') ≤ bp) (hb₀ : (0 : Q') ≤ b₀)
    (hres : (4 : Q') * (am * ap) ≤ a₀ * a₀)
    (hdomL : bm ≤ am) (hdomR : bp ≤ ap) :
    (am + bm) * (ap + bp) ≤ (a₀ + b₀) * (a₀ + b₀) := by
  have hAB : (0 : Q') ≤ ap + bp := Q'.zero_le_add _ _ hap hbp
  have hXm : (0 : Q') ≤ am + am := Q'.zero_le_add _ _ ham ham
  have hx : am + bm ≤ am + am := Q'.add_le_add_left am bm am hdomL
  have hy : ap + bp ≤ ap + ap := Q'.add_le_add_left ap bp ap hdomR
  have step1 : (am + bm) * (ap + bp) ≤ (am + am) * (ap + ap) := prod_le_prod hx hy hAB hXm
  have step2 : (am + am) * (ap + ap) ≤ (4 : Q') * (am * ap) :=
    Q'.le_of_eqv (two_two_mul_eqv am ap)
  have ha0b0 : a₀ ≤ a₀ + b₀ := Q'.add_le_self_of_nonneg a₀ b₀ hb₀
  have hX0 : (0 : Q') ≤ a₀ + b₀ := Q'.zero_le_add _ _ ha₀ hb₀
  have step4 : a₀ * a₀ ≤ (a₀ + b₀) * (a₀ + b₀) := prod_le_prod ha0b0 ha0b0 ha₀ hX0
  exact Q'.le_trans' _ _ _ step1
    (Q'.le_trans' _ _ _ step2 (Q'.le_trans' _ _ _ hres step4))

/-- **`dominant_term_LC3` — the 3-shift grouping.**  Group the off mass `b := b + c` and
apply E3: the domination hypotheses `b± + c± ≤ a±` are exactly the shift bound restricted
to `r ∈ {1,2}` (`H₁+H₂ ≤ (1/16+1/256)·H₀ < H₀`). -/
theorem dominant_term_LC3 {am a₀ ap bm b₀ bp cm c₀ cp : Q'}
    (ham : (0 : Q') ≤ am) (hap : (0 : Q') ≤ ap) (ha₀ : (0 : Q') ≤ a₀)
    (hbp : (0 : Q') ≤ bp) (hb₀ : (0 : Q') ≤ b₀)
    (hcp : (0 : Q') ≤ cp) (hc₀ : (0 : Q') ≤ c₀)
    (hres : (4 : Q') * (am * ap) ≤ a₀ * a₀)
    (hdomL : bm + cm ≤ am) (hdomR : bp + cp ≤ ap) :
    (am + bm + cm) * (ap + bp + cp) ≤ (a₀ + b₀ + c₀) * (a₀ + b₀ + c₀) := by
  have hE := dominant_term_LC_four (bm := bm + cm) (b₀ := b₀ + c₀) (bp := bp + cp)
    ham hap ha₀ (Q'.zero_le_add _ _ hbp hcp) (Q'.zero_le_add _ _ hb₀ hc₀)
    hres hdomL hdomR
  have eL : ((am + bm + cm) * (ap + bp + cp)).eqv
      ((am + (bm + cm)) * (ap + (bp + cp))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.add_assoc_eqv am bm cm))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.add_assoc_eqv ap bp cp))
  have eR : ((a₀ + (b₀ + c₀)) * (a₀ + (b₀ + c₀))).eqv
      ((a₀ + b₀ + c₀) * (a₀ + b₀ + c₀)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv a₀ b₀ c₀)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv a₀ b₀ c₀)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
    (Q'.le_trans' _ _ _ hE (Q'.le_of_eqv eR))

/-! ## 2. The dominant-central-term magnitude bound (all `s`) -/

/-- **`coeffW_ratio_quarter` — the all-`s` geometric ratio reserve `4·c_{s+1} ≤ c_s`.**
On `0 < w ≤ 1/2`, by induction: base `4·c₁ ≤ 4·(1/4) = 1 = c₀` (`coeffW1_le_quarter`); step
from the factor-4 atom `4·c_s·c_{s+2} ≤ c_{s+1}²` (`coeffW_superLogConcave_four`): the IH
`4c_{s+1} ≤ c_s` gives `c_{s+1} ≤ c_s`, so `c_{s+1}² ≤ c_s·c_{s+1}`, hence
`(4·c_{s+2})·c_s ≤ c_{s+1}·c_s`; cancel `c_s > 0` (`coeffW_pos`).  This is the `ρ_s ≤ 1/4`
backbone driving the geometric shift-tail `H_r ≤ 16^{-r}H₀` (hence `ε = 1/15`). -/
theorem coeffW_ratio_quarter {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) :
    ∀ s, (4 : Q') * coeffW w (s + 1) ≤ coeffW w s := by
  intro s
  induction s with
  | zero =>
    have h1 : coeffW w 1 ≤ Q'.mkPos 1 4 (by decide) := coeffW1_le_quarter hw0 hw12
    have hmul : (4 : Q') * coeffW w 1 ≤ (4 : Q') * (Q'.mkPos 1 4 (by decide)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ h1 (by decide)
    have he : ((4 : Q') * (Q'.mkPos 1 4 (by decide))).eqv 1 := by decide
    have h0 : coeffW w 0 = 1 := coeffW_zero w
    show (4 : Q') * coeffW w 1 ≤ coeffW w 0
    rw [h0]
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv he)
  | succ s ih =>
    have super := coeffW_superLogConcave_four hw0 hw12 s
    have cs_pos : (0 : Q') < coeffW w s :=
      YMGap.Continuum.FusionResidualBound.coeffW_pos hwpos s
    have c1_nn : (0 : Q') ≤ coeffW w (s + 1) := coeffW_nonneg hw0 (s + 1)
    have h_c1_le_4c1 : coeffW w (s + 1) ≤ (4 : Q') * coeffW w (s + 1) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW w (s + 1))))
        (Q'.mul_le_mul_of_nonneg_right (1 : Q') (4 : Q') (coeffW w (s + 1)) (by decide) c1_nn)
    have Cs : coeffW w (s + 1) ≤ coeffW w s := Q'.le_trans' _ _ _ h_c1_le_4c1 ih
    have hsq_le : coeffW w (s + 1) * coeffW w (s + 1) ≤ coeffW w s * coeffW w (s + 1) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ Cs c1_nn
    have hkey : (4 : Q') * (coeffW w s * coeffW w (s + 2)) ≤ coeffW w s * coeffW w (s + 1) :=
      Q'.le_trans' _ _ _ super hsq_le
    have eL : ((4 : Q') * (coeffW w s * coeffW w (s + 2))).eqv
        (coeffW w s * ((4 : Q') * coeffW w (s + 2))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (4 : Q') _ _
          (Q'.mul_comm_eqv (coeffW w s) (coeffW w (s + 2)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (4 : Q') (coeffW w (s + 2)) (coeffW w s))) ?_
      exact Q'.mul_comm_eqv ((4 : Q') * coeffW w (s + 2)) (coeffW w s)
    have hcancel : coeffW w s * ((4 : Q') * coeffW w (s + 2)) ≤ coeffW w s * coeffW w (s + 1) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv eL) hkey
    show (4 : Q') * coeffW w (s + 2) ≤ coeffW w (s + 1)
    exact YMGap.Continuum.FusionQuotientCollapse.le_of_mul_le_mul_left_pos cs_pos hcancel

/-- **`coeffW_weak_decreasing`** — `c_{s+1} ≤ c_s` on `0 < w ≤ 1/2` (immediate from the
ratio reserve: `c_{s+1} ≤ 4·c_{s+1} ≤ c_s`). -/
theorem coeffW_weak_decreasing {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (s : Nat) : coeffW w (s + 1) ≤ coeffW w s := by
  have c1_nn : (0 : Q') ≤ coeffW w (s + 1) := coeffW_nonneg hw0 (s + 1)
  have h_c1_le_4c1 : coeffW w (s + 1) ≤ (4 : Q') * coeffW w (s + 1) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW w (s + 1))))
      (Q'.mul_le_mul_of_nonneg_right (1 : Q') (4 : Q') (coeffW w (s + 1)) (by decide) c1_nn)
  exact Q'.le_trans' _ _ _ h_c1_le_4c1 (coeffW_ratio_quarter hw0 hw12 hwpos s)

/-! ## 3. The reduction of A3 to ONE sharp named residual -/

/-- **`CentralAutoconvReserve w`** — the SINGLE sharp residual A3 reduces to.  It carries a
decomposition of the antidiagonal line-sum into a central autoconvolution `H₀` and an
off-central mass `off`, an `ε`-domination `off ≤ ε·H₀`, and the central-autoconvolution
reserve `(1+δ)·H₀(s)·H₀(s+2) ≤ H₀(s+1)²` with the sharp threshold `ε·ε + (ε+ε) ≤ δ`
(i.e. `δ ≥ ε² + 2ε`).  This replaces the opaque `QuadGershgorinClosure` / `LagCorrTP2`
bookkeeping with a concrete uniform inequality (`δ ≥ 31/225` at `ε = 1/15`).  It is
NAMED-OPEN (never `sorry`); its `reserve` field is the genuine remaining local-CLT content,
now sharply quantified. -/
structure CentralAutoconvReserve (w : Q') : Type where
  /-- The central shift term `H₀ = c∗c` (pure autoconvolution of the theta weight). -/
  H0 : Nat → Nat → Q'
  /-- The off-central mass `b = Σ_{r≥1} H_r`. -/
  off : Nat → Nat → Q'
  /-- The shift decomposition of the line-sum: `lineSum = H₀ + off`. -/
  decomp : ∀ N t, (lineSum (lagCorr w N) t).eqv (H0 N t + off N t)
  /-- The central term is nonneg. -/
  H0nonneg : ∀ N t, (0 : Q') ≤ H0 N t
  /-- The off-central mass is nonneg. -/
  offNonneg : ∀ N t, (0 : Q') ≤ off N t
  /-- The geometric-tail domination constant `ε` (`= 1/15` from `Σ_{r≥1}16^{-r}`). -/
  eps : Q'
  /-- The central-autoconvolution reserve constant `δ` (`≥ 31/225`). -/
  delta : Q'
  /-- `ε ≥ 0`. -/
  epsNonneg : (0 : Q') ≤ eps
  /-- The sharp threshold `ε² + 2ε ≤ δ`. -/
  threshold : eps * eps + (eps + eps) ≤ delta
  /-- The off mass is `ε`-dominated by the central term (uniform in `N, t`). -/
  dominate : ∀ N t, off N t ≤ eps * H0 N t
  /-- The central-autoconvolution log-concavity reserve (uniform in `N, s`). -/
  reserve : ∀ N s, (1 + delta) * (H0 N s * H0 N (s + 2)) ≤ H0 N (s + 1) * H0 N (s + 1)

/-- **`lineSumLogConcaveOfReserve` — THE REDUCTION.**  A `CentralAutoconvReserve` witness
discharges A3 (`StrandReduction.lineSumLogConcave`) for every `N, s`: apply E1
(`dominant_term_LC`) with `a± = H₀(s), H₀(s+2)`, `a₀ = H₀(s+1)`, `b = off`, then transport
across the `decomp` decomposition. -/
def lineSumLogConcaveOfReserve {w : Q'} (r : CentralAutoconvReserve w) :
    ∀ N s, lineSum (lagCorr w N) s * lineSum (lagCorr w N) (s + 2)
      ≤ lineSum (lagCorr w N) (s + 1) * lineSum (lagCorr w N) (s + 1) := by
  intro N s
  have hE := dominant_term_LC
    (am := r.H0 N s) (a₀ := r.H0 N (s + 1)) (ap := r.H0 N (s + 2))
    (bm := r.off N s) (b₀ := r.off N (s + 1)) (bp := r.off N (s + 2))
    (ε := r.eps) (δ := r.delta)
    (r.H0nonneg N s) (r.H0nonneg N (s + 2)) (r.H0nonneg N (s + 1))
    (r.offNonneg N (s + 2)) (r.offNonneg N (s + 1)) r.epsNonneg
    (r.reserve N s) (r.dominate N s) (r.dominate N (s + 2)) r.threshold
  have eL : (lineSum (lagCorr w N) s * lineSum (lagCorr w N) (s + 2)).eqv
      ((r.H0 N s + r.off N s) * (r.H0 N (s + 2) + r.off N (s + 2))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (r.decomp N s))
      (Q'.mul_eqv_congr_left _ _ _ (r.decomp N (s + 2)))
  have eR : ((r.H0 N (s + 1) + r.off N (s + 1)) * (r.H0 N (s + 1) + r.off N (s + 1))).eqv
      (lineSum (lagCorr w N) (s + 1) * lineSum (lagCorr w N) (s + 1)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (r.decomp N (s + 1))))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (r.decomp N (s + 1))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
    (Q'.le_trans' _ _ _ hE (Q'.le_of_eqv eR))

/-- **`strandReductionOfReserve`** — packaged with the finite A1 strand reindex, a
`CentralAutoconvReserve` witness yields a full `StrandReduction w` (hence, through Round D's
`s1DominanceOfStrandReduction`, `S1Dominance N w 2` for every `N`).  This exhibits the
central-autoconvolution reserve as the SOLE remaining analytic input on the A3 side. -/
def strandReductionOfReserve {w : Q'}
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (r : CentralAutoconvReserve w) : StrandReduction w where
  reindex := reindex
  lineSumLogConcave := lineSumLogConcaveOfReserve r

/-! ## 4. The concrete numeric anchor (the sharp threshold) -/

/-- **`eps_fifteenth_threshold` — the concrete residual constant.**  With the geometric-tail
domination `ε = 1/15` (`= Σ_{r≥1}16^{-r}`), the sharp central-autoconvolution threshold
`ε² + 2ε ≤ δ` is met exactly at `δ = 31/225`:

    (1/15)·(1/15) + ((1/15)+(1/15)) = 1/225 + 30/225 = 31/225.

This is the honest, quantified residual replacing the "factor-4" hand-wave: a ~14%
autoconvolution reserve, uniform in `s` and in the `N`-truncation. -/
theorem eps_fifteenth_threshold :
    (Q'.mkPos 1 15 (by decide)) * (Q'.mkPos 1 15 (by decide))
        + ((Q'.mkPos 1 15 (by decide)) + (Q'.mkPos 1 15 (by decide)))
      ≤ Q'.mkPos 31 225 (by decide) := by decide

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `prod_le_prod`, `oneEps_mul_eqv`, `four_mul_eqv`, `two_two_mul_eqv`, `sq_oneEps_le`
    — the `Q'` discriminant-engine helpers.
  * `dominant_term_LC` (E1) — the general sharp reserve/domination threshold
    `ε² + 2ε ≤ δ ⟹ (am+bm)(ap+bp) ≤ (a₀+b₀)²`.
  * `dominant_term_LC_four` (E3) — the factor-4 corollary.
  * `dominant_term_LC3` — the 3-shift grouping.
  * `coeffW_ratio_quarter` — the all-`s` geometric ratio reserve `4·c_{s+1} ≤ c_s`.
  * `coeffW_weak_decreasing` — `c_{s+1} ≤ c_s`.
  * `lineSumLogConcaveOfReserve` — THE REDUCTION of A3 to `CentralAutoconvReserve`.
  * `strandReductionOfReserve` — reserve + finite reindex ⟹ full `StrandReduction`.
  * `eps_fifteenth_threshold` — the concrete residual constant `δ ≥ 31/225` at `ε = 1/15`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `CentralAutoconvReserve w` — the SINGLE sharp residual: the `H₀+off` decomposition,
    the `ε`-domination `off ≤ ε·H₀`, and the central-autoconvolution reserve
    `(1+δ)·H₀(s)·H₀(s+2) ≤ H₀(s+1)²` with `δ ≥ ε² + 2ε`.  Its `reserve` field is the
    genuine remaining local-CLT content (the truncated central-autoconvolution
    log-concavity margin `δ ≥ 31/225`, uniform in `s` and the `N`-truncation), now sharply
    quantified rather than opaque.

HONEST VERDICT.  Round G converts the opaque "aggregate Gershgorin/TP₂" bookkeeping of A3
into a fully green `Q'` discriminant engine (E1/E3/3-shift), proves the all-`s` geometric
ratio reserve that pins the domination constant to `ε = 1/15`, and REDUCES A3
(`StrandReduction.lineSumLogConcave` / `QuadGershgorinClosure`) to ONE concrete named
residual — the central-autoconvolution reserve `δ ≥ 31/225`.  It does NOT prove that
reserve.  This is a structural sharpening of one box-level log-concavity sub-fact; it is
NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundG.prod_le_prod
#print axioms YMGap.Continuum.FusionCoreStepRoundG.four_mul_eqv
#print axioms YMGap.Continuum.FusionCoreStepRoundG.two_two_mul_eqv
#print axioms YMGap.Continuum.FusionCoreStepRoundG.sq_oneEps_le
#print axioms YMGap.Continuum.FusionCoreStepRoundG.dominant_term_LC
#print axioms YMGap.Continuum.FusionCoreStepRoundG.dominant_term_LC_four
#print axioms YMGap.Continuum.FusionCoreStepRoundG.dominant_term_LC3
#print axioms YMGap.Continuum.FusionCoreStepRoundG.coeffW_ratio_quarter
#print axioms YMGap.Continuum.FusionCoreStepRoundG.coeffW_weak_decreasing
#print axioms YMGap.Continuum.FusionCoreStepRoundG.lineSumLogConcaveOfReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundG.strandReductionOfReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundG.eps_fifteenth_threshold


/-! ===========================================================================
    ## Round H  (was `FusionCoreStepRoundH.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round H of the fusion box log-concavity node: PINNING the abstract
`CentralAutoconvReserve` residual (Round G) to CONCRETE objects and PROVING the finite
part.  Round G reduced A3 (`StrandReduction.lineSumLogConcave`) to a Type-level structure
`CentralAutoconvReserve w` whose `H0`, `off`, `decomp`, `H0nonneg`, `offNonneg` fields were
ALL abstract free data.  Round H replaces `H0`/`off` by the CONCRETE truncated central
autoconvolution `H0auto` (the `r = 0` shift slice of the antidiagonal line-sum) and its
tail `offAuto` (the `r ≥ 1` shifts), and PROVES `decomp`, `H0nonneg`, `offNonneg` against
the REAL `lineSum (lagCorr w N)` — no longer hypotheses.

# What this module adds (read first — load-bearing honesty)

The antidiagonal line-sum expands as
    lineSum (lagCorr w N) t = Σ_{p=0}^{t} Σ_{r=0}^{nP-1} c_{p+r}·c_{(t−p)+r},   nP = N+1−max(p,t−p),
i.e. a sum over shifts `r` of partial autoconvolutions.  Round H isolates the `r = 0` slice
(the pure central autoconvolution, TRUNCATED by the per-`p` cutoff `min 1 nP`) as `H0auto`
and the `r ≥ 1` remainder as `offAuto`, and closes the split.

ROUND-H DELIVERABLE 1 (the concrete objects + the PROVED finite split).
  * `H0auto` / `offAuto` — the concrete `r = 0` central-autoconvolution slice and its
    `r ≥ 1` tail, as explicit finite `fsum`s of the theta weight `coeffW`.
  * `fsum_split_at` — the generic front/tail `fsum` split `Σ_{k<a+b} f = Σ_{k<a} f +
    Σ_{k<b} f(a+·)` (clean induction on `b`).
  * `decomp_auto` — THE PROVED SPLIT: `lineSum (lagCorr w N) t ≃ H0auto w N t + offAuto w N t`
    for EVERY `N, t` (per-`p` front extraction via `fsum_split_at`, lifted by `fsum_add`).
    This was a HYPOTHESIS (`decomp`) in Round G; here it is a theorem against the real
    line-sum.
  * `H0auto_nonneg`, `offAuto_nonneg` — both slices are `≥ 0` (`coeffW_nonneg`).

ROUND-H DELIVERABLE 2 (the reduction of A3 to the TWO sharp bump inequalities).
  * `AutoconvBumpBounds w` — the sharpened residual: exactly the two remaining
    concrete inequalities, at the pinned constants `ε = 1/15`, `δ = 31/225`:
      - `dominate` : `offAuto ≤ (1/15)·H0auto`   (the geometric shift-tail domination),
      - `reserve`  : `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`   (the central-
        autoconvolution log-concavity margin).
    Both are the genuine local-CLT "bump" content, now stated on a CONCRETE object.
  * `reserveOfBumpBounds` — THE ASSEMBLY: a `AutoconvBumpBounds w` witness inhabits the
    full `CentralAutoconvReserve w`, discharging `decomp`/`H0nonneg`/`offNonneg` by the
    proved finite facts and `threshold` by `eps_fifteenth_threshold`.
  * `strandReductionOfBumpBounds`, `s1DominanceOfBumpBounds` — wired through Round G's
    `strandReductionOfReserve` and Round D's `s1DominanceOfStrandReduction`: a bump-bounds
    witness (plus the A1 strand reindex and the per-`N` edge input) yields `S1Dominance N w
    2` for EVERY `N`.

# HONESTY — what is NOT closed

`AutoconvBumpBounds w` is a Type-level NAMED-OPEN structure; it is NOT inhabited here for
general `N`.  Its two fields (`dominate`, `reserve`) are the genuine remaining local-CLT
content — the tail domination and the central-autoconvolution log-concavity margin, now
CONCRETE and sharply quantified, uniform in `s` and in the `N`-truncation.  Round H proves
the finite decomposition and nonnegativity that Round G assumed, shrinking the A3 residual
from "an abstract reserve structure" to "two explicit inequalities on the truncated
autoconvolution".  It does NOT prove those inequalities.  This is a structural sharpening of
one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`lagCorr`/`lineSum` lemmas, finite
`fsum` algebra, `omega` on index identities, and `decide` on closed concrete-rational
facts.  Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundH

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundG

/-! ## 0. A generic front/tail `fsum` split -/

/-- **`fsum_split_at`** — split a finite sum at index `a`:
`Σ_{k<a+b} f k ≃ (Σ_{k<a} f k) + (Σ_{r<b} f (a+r))`.  Clean induction on `b`. -/
theorem fsum_split_at (f : Nat → Q') (a b : Nat) :
    (fsum f (a + b)).eqv (fsum f a + fsum (fun r => f (a + r)) b) := by
  induction b with
  | zero =>
      -- `a + 0 = a`, `fsum _ 0 = 0`
      exact Q'.eqv_symm (q_add_zero_eqv (fsum f a))
  | succ b ih =>
      show (fsum f (a + b) + f (a + b)).eqv
          (fsum f a + (fsum (fun r => f (a + r)) b + f (a + b)))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f (a + b)) ih) ?_
      exact Q'.add_assoc_eqv (fsum f a) (fsum (fun r => f (a + r)) b) (f (a + b))

/-! ## 1. The concrete central-autoconvolution slice and its tail -/

/-- The per-pair shift cutoff `nP N t p = N + 1 − max(p, t−p)` (the `r`-range of the strand
correlation `lagCorr w N p (t−p)`). -/
def nP (N t p : Nat) : Nat := N + 1 - Nat.max p (t - p)

/-- The antidiagonal correlation summand `c_{p+r}·c_{(t−p)+r}` (the `r`-th shift term at
antidiagonal position `p` of the line-sum at total `t`). -/
def ccT (w : Q') (t p r : Nat) : Q' := coeffW w (p + r) * coeffW w ((t - p) + r)

/-- **`H0auto` — the concrete truncated central autoconvolution** (the `r = 0` shift slice).
For each `p` it keeps the single `r = 0` term `c_p·c_{t−p}` when the cutoff admits it
(`min 1 nP = 1`), else nothing (`min 1 nP = 0`). -/
def H0auto (w : Q') (N t : Nat) : Q' :=
  fsum (fun p => fsum (ccT w t p) (Nat.min 1 (nP N t p))) (t + 1)

/-- **`offAuto` — the concrete off-central tail** (the `r ≥ 1` shifts). -/
def offAuto (w : Q') (N t : Nat) : Q' :=
  fsum (fun p =>
    fsum (fun r => ccT w t p (Nat.min 1 (nP N t p) + r))
      (nP N t p - Nat.min 1 (nP N t p))) (t + 1)

/-- `lagCorr w N p (t−p)` is definitionally the `ccT`/`nP` correlation sum. -/
theorem lagCorr_ccT (w : Q') (N t p : Nat) :
    lagCorr w N p (t - p) = fsum (ccT w t p) (nP N t p) := rfl

/-! ### 1a. Nonnegativity of both slices -/

/-- `ccT ≥ 0` (product of nonneg theta weights). -/
theorem ccT_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (t p r : Nat) :
    (0 : Q') ≤ ccT w t p r :=
  Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)

/-- **`H0auto_nonneg`** — the central slice is `≥ 0`. -/
theorem H0auto_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N t : Nat) :
    (0 : Q') ≤ H0auto w N t :=
  fsum_nonneg (fun p => fsum_nonneg (fun r => ccT_nonneg hw0 t p r) _) _

/-- **`offAuto_nonneg`** — the off-central tail is `≥ 0`. -/
theorem offAuto_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N t : Nat) :
    (0 : Q') ≤ offAuto w N t :=
  fsum_nonneg (fun p =>
    fsum_nonneg (fun _ => ccT_nonneg hw0 t p _) _) _

/-! ### 1b. The proved finite decomposition -/

/-- **`decomp_auto` — THE PROVED SHIFT DECOMPOSITION.**  For every `N, t`,

    lineSum (lagCorr w N) t  ≃  H0auto w N t + offAuto w N t.

Per antidiagonal position `p`, the strand correlation `lagCorr w N p (t−p) =
Σ_{r<nP} c_{p+r}c_{(t−p)+r}` splits (`fsum_split_at` at `min 1 nP`) into its `r = 0` head
(kept iff `nP ≥ 1`) and its `r ≥ 1` tail; summing over `p` (`fsum_add`) gives the split.
This was a HYPOTHESIS in Round G; here it is a theorem against the real line-sum. -/
theorem decomp_auto {w : Q'} (N t : Nat) :
    (lineSum (lagCorr w N) t).eqv (H0auto w N t + offAuto w N t) := by
  have key : ∀ p, (lagCorr w N p (t - p)).eqv
      (fsum (ccT w t p) (Nat.min 1 (nP N t p))
        + fsum (fun r => ccT w t p (Nat.min 1 (nP N t p) + r))
            (nP N t p - Nat.min 1 (nP N t p))) := by
    intro p
    have hle : Nat.min 1 (nP N t p) ≤ nP N t p := Nat.min_le_right 1 (nP N t p)
    have hcount :
        Nat.min 1 (nP N t p) + (nP N t p - Nat.min 1 (nP N t p)) = nP N t p := by omega
    have hsplit := fsum_split_at (ccT w t p) (Nat.min 1 (nP N t p))
      (nP N t p - Nat.min 1 (nP N t p))
    rw [hcount] at hsplit
    rw [lagCorr_ccT]
    exact hsplit
  refine Q'.eqv_trans _ _ _ ?_ (fsum_add
    (fun p => fsum (ccT w t p) (Nat.min 1 (nP N t p)))
    (fun p => fsum (fun r => ccT w t p (Nat.min 1 (nP N t p) + r))
        (nP N t p - Nat.min 1 (nP N t p)))
    (t + 1))
  exact fsum_eqv_congr _ _ key (t + 1)

/-! ## 2. The reduction of A3 to the two sharp bump inequalities -/

/-- **`AutoconvBumpBounds w`** — the sharpened A3 residual on the CONCRETE truncated
autoconvolution.  Exactly the two remaining local-CLT "bump" inequalities, at the pinned
constants `ε = 1/15`, `δ = 31/225`:
  * `dominate` — the geometric shift-tail domination `offAuto ≤ (1/15)·H0auto`;
  * `reserve`  — the central-autoconvolution log-concavity margin
    `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.
NAMED-OPEN (never `sorry`); these two are the genuine remaining content, now concrete. -/
structure AutoconvBumpBounds (w : Q') : Type where
  /-- The geometric shift-tail domination (uniform in `N, t`). -/
  dominate : ∀ N t, offAuto w N t ≤ Q'.mkPos 1 15 (by decide) * H0auto w N t
  /-- The central-autoconvolution log-concavity margin (uniform in `N, s`). -/
  reserve : ∀ N s,
    (1 + Q'.mkPos 31 225 (by decide)) * (H0auto w N s * H0auto w N (s + 2))
      ≤ H0auto w N (s + 1) * H0auto w N (s + 1)

/-- **`reserveOfBumpBounds` — THE ASSEMBLY.**  A `AutoconvBumpBounds w` witness inhabits the
full Round-G `CentralAutoconvReserve w`, with `H0`/`off` pinned to the concrete slices,
`decomp`/`H0nonneg`/`offNonneg` discharged by the proved finite facts, `ε = 1/15`,
`δ = 31/225`, and `threshold` by `eps_fifteenth_threshold`. -/
def reserveOfBumpBounds {w : Q'} (hw0 : (0 : Q') ≤ w) (bb : AutoconvBumpBounds w) :
    CentralAutoconvReserve w where
  H0 := H0auto w
  off := offAuto w
  decomp := fun N t => decomp_auto N t
  H0nonneg := fun N t => H0auto_nonneg hw0 N t
  offNonneg := fun N t => offAuto_nonneg hw0 N t
  eps := Q'.mkPos 1 15 (by decide)
  delta := Q'.mkPos 31 225 (by decide)
  epsNonneg := by decide
  threshold := eps_fifteenth_threshold
  dominate := bb.dominate
  reserve := bb.reserve

/-! ## 3. Wiring — a bump-bounds witness drives `S1Dominance` for every `N` -/

/-- **`strandReductionOfBumpBounds`** — with the A1 strand reindex, a bump-bounds witness
yields a full `StrandReduction w`. -/
def strandReductionOfBumpBounds {w : Q'} (hw0 : (0 : Q') ≤ w)
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (bb : AutoconvBumpBounds w) : StrandReduction w :=
  strandReductionOfReserve reindex (reserveOfBumpBounds hw0 bb)

/-- **`s1DominanceOfBumpBounds`** — end-to-end: a bump-bounds witness (plus the A1 strand
reindex and the per-`N` edge input) drives `S1Dominance N w 2` for EVERY `N`, through Round
G's `strandReductionOfReserve` and Round D's `s1DominanceOfStrandReduction`. -/
def s1DominanceOfBumpBounds {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (bb : AutoconvBumpBounds w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  s1DominanceOfStrandReduction hw0 hw12 hwpos hw1
    (strandReductionOfBumpBounds hw0 reindex bb) N hedge

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `fsum_split_at` — the generic front/tail `fsum` split.
  * `H0auto_nonneg`, `offAuto_nonneg` — nonnegativity of both concrete slices.
  * `decomp_auto` — THE finite shift decomposition `lineSum ≃ H0auto + offAuto`, proved
    against the real line-sum (a HYPOTHESIS in Round G).
  * `reserveOfBumpBounds` — the assembly: bump-bounds ⟹ full `CentralAutoconvReserve`,
    with the finite fields discharged.
  * `strandReductionOfBumpBounds`, `s1DominanceOfBumpBounds` — the wiring to `S1Dominance`
    (every `N`).

NAMED OPEN (Type-level structure, never `sorry`):
  * `AutoconvBumpBounds w` — the two remaining sharp inequalities on the CONCRETE truncated
    autoconvolution: the geometric shift-tail domination `offAuto ≤ (1/15)·H0auto` and the
    central-autoconvolution log-concavity margin `(1+31/225)·H0auto(s)·H0auto(s+2) ≤
    H0auto(s+1)²`.  These are the genuine remaining local-CLT content, now concrete and
    sharply quantified, uniform in `s` and the `N`-truncation.

HONEST VERDICT.  Round H PINS the abstract Round-G reserve to the concrete truncated central
autoconvolution `H0auto` and its tail `offAuto`, PROVES the finite decomposition and
nonnegativity that Round G assumed, and reduces A3 to exactly TWO explicit bump inequalities.
It does NOT prove those inequalities.  This is a structural sharpening of one box-level
log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundH

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundH.fsum_split_at
#print axioms YMGap.Continuum.FusionCoreStepRoundH.H0auto_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundH.offAuto_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundH.decomp_auto
#print axioms YMGap.Continuum.FusionCoreStepRoundH.reserveOfBumpBounds
#print axioms YMGap.Continuum.FusionCoreStepRoundH.strandReductionOfBumpBounds
#print axioms YMGap.Continuum.FusionCoreStepRoundH.s1DominanceOfBumpBounds


/-! ===========================================================================
    ## Round I  (was `FusionCoreStepRoundI.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round I of the fusion box log-concavity node: CLOSING the geometric
shift-tail DOMINATION field of Round H's `AutoconvBumpBounds`, and REDUCING the two-field
residual to the single RESERVE field.

# What this module adds (read first — load-bearing honesty)

Round H reduced A3 (`StrandReduction.lineSumLogConcave`) to `AutoconvBumpBounds w`, whose
TWO fields are the genuine local-CLT "bump" content on the CONCRETE truncated central
autoconvolution:
  * `dominate` : `offAuto w N t ≤ (1/15)·H0auto w N t`   (the geometric shift-tail),
  * `reserve`  : `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`  (the log-concavity margin).

Round I PROVES the `dominate` field OUTRIGHT — for every `N, t`, uniformly, from the all-`s`
geometric ratio reserve `4·c_{s+1} ≤ c_s` (`coeffW_ratio_quarter`, Round G) — and reduces
`AutoconvBumpBounds` to a ONE-field residual `AutoconvReserveResidual` (just `reserve`).

ROUND-I DELIVERABLE 1 (the geometric-tail engine — PROVED, pure `Q'`/`Nat`).
  * `geoPow r n` — the explicit `r^n` power (`geoPow r 0 = 1`, `geoPow r (n+1) = r·geoPow r n`).
  * `quarter_of_four_le` — `4·x ≤ y ⟹ x ≤ (1/4)·y` (cancel the factor 4).
  * `leg_geo` — the per-leg geometric decay `c_{k+n} ≤ (1/4)^n·c_k` (induction on `n` off
    `coeffW_ratio_quarter`).  This is the `ρ ≤ 1/4` backbone at the coefficient level.
  * `geoPow_quarter_sq` — `(1/4)^n·(1/4)^n ≃ (1/16)^n` (the two-leg combine).
  * `ccT_geo` — the per-term two-leg bound `ccT t p σ ≤ (1/16)^σ·ccT t p 0`
    (`prod_le_prod` on the two legs + the square combine).
  * `geoSum_inv` — the EXACT finite geometric telescoping `Σ_{r<M}(1/16)^r + (16/15)·(1/16)^M
    ≃ 16/15`; hence `geoTail_le : Σ_{r<M}(1/16)^r ≤ 16/15` and `geoShiftTail_le :
    Σ_{r<M}(1/16)^{r+1} ≤ 1/15`.

ROUND-I DELIVERABLE 2 (the domination field — PROVED, uniform in `N, t`).
  * `off_slice_le` — the per-antidiagonal-position bound `offSlice p ≤ (1/15)·H0Slice p`
    (case split on the cutoff `nP`: both slices vanish when `nP = 0`; the geometric tail
    when `nP ≥ 1`).
  * `offAuto_dominate` — THE FIELD: `offAuto w N t ≤ (1/15)·H0auto w N t` for every `N, t`
    (`fsum` monotonicity + scalar pull-out over `off_slice_le`).

ROUND-I DELIVERABLE 3 (the one-field reduction — REDUCTION).
  * `AutoconvReserveResidual w` — the SOLE remaining sharp inequality: the reserve
    `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.
  * `bumpBoundsOfReserve` — a reserve residual inhabits the full Round-H
    `AutoconvBumpBounds w` (its `dominate` field discharged by `offAuto_dominate`).
  * `centralReserveOfResidual`, `s1DominanceOfResidual` — wired through Round H:
    reserve residual (plus the A1 strand reindex + per-`N` edge input) drives
    `CentralAutoconvReserve` and `S1Dominance N w 2` for every `N`.

# HONESTY — what is NOT closed

The `reserve` field remains NAMED-OPEN (`AutoconvReserveResidual`, never `sorry`): it is the
genuine local-CLT central-autoconvolution log-concavity margin `δ ≥ 31/225`, which — as the
Round-H analysis records — consumes `coeffW`'s STRICT super-log-concavity (plain geometric
ratio-`1/4` coefficients give only `≈ 9/8 < 256/225`, so factor-1 log-concavity is provably
insufficient).  Round I does NOT prove it.  The A1 strand reindex (`reindex`) also remains a
threaded hypothesis.  What Round I DOES close is the `dominate` field in full and the
reduction of the two-field bump residual to the single reserve inequality.  This is a
structural sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills
mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`H0auto`/`offAuto` lemmas, finite
inductions, `Nat.min`/`omega` on the cutoff, and `decide` on closed concrete-rational facts.
Every load-bearing declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are
`Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundI

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundG
open YMGap.Continuum.FusionCoreStepRoundH

/-! ## 0. The pinned geometric constants -/

/-- The per-leg decay ratio `1/4`. -/
abbrev qq4 : Q' := Q'.mkPos 1 4 (by decide)
/-- The two-leg (per-term) decay ratio `1/16`. -/
abbrev qq16 : Q' := Q'.mkPos 1 16 (by decide)
/-- The domination constant `ε = 1/15`. -/
abbrev qq15 : Q' := Q'.mkPos 1 15 (by decide)
/-- The full geometric-series bound `16/15 = Σ_{r≥0}(1/16)^r`. -/
abbrev qq1615 : Q' := Q'.mkPos 16 15 (by decide)

/-! ## 1. The explicit power `r^n` -/

/-- `geoPow r n = r^n` (`geoPow r 0 = 1`, `geoPow r (n+1) = r·geoPow r n`). -/
def geoPow (r : Q') : Nat → Q'
  | 0 => 1
  | (n + 1) => r * geoPow r n

/-- Powers of a nonneg base are nonneg. -/
theorem geoPow_nonneg {r : Q'} (hr : (0 : Q') ≤ r) (n : Nat) : (0 : Q') ≤ geoPow r n := by
  induction n with
  | zero => show (0 : Q') ≤ (1 : Q'); decide
  | succ n ih => exact Q'.mul_nonneg _ _ hr ih

/-! ## 2. The per-leg geometric decay -/

/-- **`quarter_of_four_le`** — cancel a factor 4: `4·x ≤ y ⟹ x ≤ (1/4)·y`. -/
theorem quarter_of_four_le {x y : Q'} (h : (4 : Q') * x ≤ y) : x ≤ qq4 * y := by
  have hnn : (0 : Q') ≤ qq4 := by decide
  have hstep : qq4 * ((4 : Q') * x) ≤ qq4 * y :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h hnn
  have e : (qq4 * ((4 : Q') * x)).eqv x := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv qq4 (4 : Q') x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (qq4 * (4 : Q')) 1 x (by decide)) ?_
    exact Q'.one_mul_eqv x
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e) hstep

/-- **`leg_geo`** — the per-leg geometric decay `c_{k+n} ≤ (1/4)^n·c_k` on `0 < w ≤ 1/2`.
Induction on `n` from `coeffW_ratio_quarter`. -/
theorem leg_geo {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (k : Nat) : ∀ n, coeffW w (k + n) ≤ geoPow qq4 n * coeffW w k := by
  intro n
  induction n with
  | zero =>
      show coeffW w k ≤ geoPow qq4 0 * coeffW w k
      exact Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW w k))
  | succ n ih =>
      have hr := coeffW_ratio_quarter hw0 hw12 hwpos (k + n)
      have hq : coeffW w ((k + n) + 1) ≤ qq4 * coeffW w (k + n) := quarter_of_four_le hr
      have hstep : qq4 * coeffW w (k + n) ≤ qq4 * (geoPow qq4 n * coeffW w k) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (by decide)
      have e : (qq4 * (geoPow qq4 n * coeffW w k)).eqv (geoPow qq4 (n + 1) * coeffW w k) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv qq4 (geoPow qq4 n) (coeffW w k))
      show coeffW w (k + (n + 1)) ≤ geoPow qq4 (n + 1) * coeffW w k
      exact Q'.le_trans' _ _ _ hq (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv e))

/-- **`geoPow_quarter_sq`** — the two-leg square combine `(1/4)^n·(1/4)^n ≃ (1/16)^n`. -/
theorem geoPow_quarter_sq (n : Nat) :
    (geoPow qq4 n * geoPow qq4 n).eqv (geoPow qq16 n) := by
  induction n with
  | zero => show ((1 : Q') * 1).eqv 1; decide
  | succ n ih =>
      show ((qq4 * geoPow qq4 n) * (qq4 * geoPow qq4 n)).eqv (qq16 * geoPow qq16 n)
      refine Q'.eqv_trans _ _ _ (mul_swap4 qq4 (geoPow qq4 n) qq4 (geoPow qq4 n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (qq4 * qq4) qq16 (geoPow qq4 n * geoPow qq4 n) (by decide)) ?_
      exact Q'.mul_eqv_congr_left qq16 _ _ ih

/-- **`ccT_geo`** — the per-term two-leg geometric bound `ccT t p σ ≤ (1/16)^σ·ccT t p 0`. -/
theorem ccT_geo {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (t p σ : Nat) : ccT w t p σ ≤ geoPow qq16 σ * ccT w t p 0 := by
  have hleg1 : coeffW w (p + σ) ≤ geoPow qq4 σ * coeffW w p := leg_geo hw0 hw12 hwpos p σ
  have hleg2 : coeffW w ((t - p) + σ) ≤ geoPow qq4 σ * coeffW w (t - p) :=
    leg_geo hw0 hw12 hwpos (t - p) σ
  have hy0 : (0 : Q') ≤ coeffW w ((t - p) + σ) := coeffW_nonneg hw0 _
  have hX : (0 : Q') ≤ geoPow qq4 σ * coeffW w p :=
    Q'.mul_nonneg _ _ (geoPow_nonneg (by decide) σ) (coeffW_nonneg hw0 _)
  have hprod : ccT w t p σ
      ≤ (geoPow qq4 σ * coeffW w p) * (geoPow qq4 σ * coeffW w (t - p)) :=
    prod_le_prod hleg1 hleg2 hy0 hX
  have eswap : ((geoPow qq4 σ * coeffW w p) * (geoPow qq4 σ * coeffW w (t - p))).eqv
      ((geoPow qq4 σ * geoPow qq4 σ) * (coeffW w p * coeffW w (t - p))) :=
    mul_swap4 (geoPow qq4 σ) (coeffW w p) (geoPow qq4 σ) (coeffW w (t - p))
  have esq : ((geoPow qq4 σ * geoPow qq4 σ) * (coeffW w p * coeffW w (t - p))).eqv
      (geoPow qq16 σ * (coeffW w p * coeffW w (t - p))) :=
    Q'.mul_eqv_congr_right _ _ _ (geoPow_quarter_sq σ)
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv eswap) (Q'.le_of_eqv esq))

/-! ## 3. The finite geometric telescoping tail -/

/-- **`geoSum_inv`** — the EXACT finite geometric telescoping identity
`Σ_{r<M}(1/16)^r + (16/15)·(1/16)^M ≃ 16/15`.  Induction on `M`. -/
theorem geoSum_inv (M : Nat) :
    (fsum (geoPow qq16) M + qq1615 * geoPow qq16 M).eqv qq1615 := by
  induction M with
  | zero =>
      show ((0 : Q') + qq1615 * (1 : Q')).eqv qq1615
      decide
  | succ M ih =>
      show ((fsum (geoPow qq16) M + geoPow qq16 M) + qq1615 * (qq16 * geoPow qq16 M)).eqv qq1615
      have hcqg : (qq1615 * (qq16 * geoPow qq16 M)).eqv (qq15 * geoPow qq16 M) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv qq1615 qq16 (geoPow qq16 M))) ?_
        exact Q'.mul_eqv_congr_right (qq1615 * qq16) qq15 (geoPow qq16 M) (by decide)
      have hgg : (geoPow qq16 M + qq15 * geoPow qq16 M).eqv (qq1615 * geoPow qq16 M) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right (geoPow qq16 M) ((1 : Q') * geoPow qq16 M)
            (qq15 * geoPow qq16 M) (Q'.eqv_symm (Q'.one_mul_eqv (geoPow qq16 M)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_mul_eqv (1 : Q') qq15 (geoPow qq16 M))) ?_
        exact Q'.mul_eqv_congr_right ((1 : Q') + qq15) qq1615 (geoPow qq16 M) (by decide)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (fsum (geoPow qq16) M + geoPow qq16 M)
          (qq1615 * (qq16 * geoPow qq16 M)) (qq15 * geoPow qq16 M) hcqg) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (fsum (geoPow qq16) M) (geoPow qq16 M) (qq15 * geoPow qq16 M)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (fsum (geoPow qq16) M)
          (geoPow qq16 M + qq15 * geoPow qq16 M) (qq1615 * geoPow qq16 M) hgg) ?_
      exact ih

/-- **`geoTail_le`** — `Σ_{r<M}(1/16)^r ≤ 16/15` (drop the nonneg telescoping remainder). -/
theorem geoTail_le (M : Nat) : fsum (geoPow qq16) M ≤ qq1615 := by
  have hnn : (0 : Q') ≤ qq1615 * geoPow qq16 M :=
    Q'.mul_nonneg _ _ (by decide) (geoPow_nonneg (by decide) M)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (fsum (geoPow qq16) M) (qq1615 * geoPow qq16 M) hnn)
    (Q'.le_of_eqv (geoSum_inv M))

/-- **`geoShiftTail_le`** — the shifted tail `Σ_{r<M}(1/16)^{r+1} ≤ 1/15`. -/
theorem geoShiftTail_le (M : Nat) : fsum (fun r => geoPow qq16 (r + 1)) M ≤ qq15 := by
  have e1 : (fsum (fun r => geoPow qq16 (r + 1)) M).eqv (qq16 * fsum (geoPow qq16) M) :=
    Q'.eqv_symm (fsum_const_mul qq16 (geoPow qq16) M)
  have h2 : qq16 * fsum (geoPow qq16) M ≤ qq16 * qq1615 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (geoTail_le M) (by decide)
  have e3 : (qq16 * qq1615).eqv qq15 := by decide
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv e3))

/-! ## 4. The domination field -/

/-- **`off_slice_le`** — the per-antidiagonal-position domination
`offSlice p ≤ (1/15)·H0Slice p`.  Case split on the cutoff `nP N t p`: when `nP = 0` both
slices are the empty sum `0`; when `nP ≥ 1` the head is the single `r = 0` term and the tail
is the geometric shift-tail dominated by `1/15` of it. -/
theorem off_slice_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (N t p : Nat) :
    fsum (fun r => ccT w t p (Nat.min 1 (nP N t p) + r)) (nP N t p - Nat.min 1 (nP N t p))
      ≤ qq15 * fsum (ccT w t p) (Nat.min 1 (nP N t p)) := by
  rcases Nat.eq_zero_or_pos (nP N t p) with hK0 | hKpos
  · rw [hK0]
    have hmin : Nat.min 1 0 = 0 := by decide
    rw [hmin]
    show (0 : Q') ≤ qq15 * fsum (ccT w t p) 0
    exact Q'.mul_nonneg _ _ (by decide) (fsum_nonneg (fun i => ccT_nonneg hw0 t p i) 0)
  · have hmin : Nat.min 1 (nP N t p) = 1 := Nat.min_eq_left hKpos
    rw [hmin]
    have hterm : ∀ r, ccT w t p (1 + r) ≤ geoPow qq16 (r + 1) * ccT w t p 0 := by
      intro r
      have h := ccT_geo hw0 hw12 hwpos t p (1 + r)
      have e : geoPow qq16 (1 + r) = geoPow qq16 (r + 1) := by rw [Nat.add_comm 1 r]
      rw [e] at h
      exact h
    have hmono : fsum (fun r => ccT w t p (1 + r)) (nP N t p - 1)
        ≤ fsum (fun r => geoPow qq16 (r + 1) * ccT w t p 0) (nP N t p - 1) :=
      fsum_mono hterm (nP N t p - 1)
    have epull : (fsum (fun r => geoPow qq16 (r + 1) * ccT w t p 0) (nP N t p - 1)).eqv
        (fsum (fun r => geoPow qq16 (r + 1)) (nP N t p - 1) * ccT w t p 0) :=
      Q'.eqv_symm (fsum_mul_const (fun r => geoPow qq16 (r + 1)) (ccT w t p 0) (nP N t p - 1))
    have hstep : fsum (fun r => geoPow qq16 (r + 1)) (nP N t p - 1) * ccT w t p 0
        ≤ qq15 * ccT w t p 0 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (geoShiftTail_le (nP N t p - 1))
        (ccT_nonneg hw0 t p 0)
    have efs1 : (qq15 * ccT w t p 0).eqv (qq15 * fsum (ccT w t p) 1) :=
      Q'.mul_eqv_congr_left qq15 (ccT w t p 0) (fsum (ccT w t p) 1)
        (Q'.eqv_symm (q_zero_add_eqv (ccT w t p 0)))
    exact Q'.le_trans' _ _ _ hmono
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv epull)
        (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv efs1)))

/-- **`offAuto_dominate` — THE DOMINATION FIELD (PROVED).**  For every `N, t`,

    offAuto w N t  ≤  (1/15)·H0auto w N t.

`fsum` monotonicity over `off_slice_le`, then scalar pull-out (`fsum_const_mul`). -/
theorem offAuto_dominate {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (N t : Nat) : offAuto w N t ≤ qq15 * H0auto w N t := by
  have hmono : offAuto w N t
      ≤ fsum (fun p => qq15 * fsum (ccT w t p) (Nat.min 1 (nP N t p))) (t + 1) :=
    fsum_mono (fun p => off_slice_le hw0 hw12 hwpos N t p) (t + 1)
  have epull : (fsum (fun p => qq15 * fsum (ccT w t p) (Nat.min 1 (nP N t p))) (t + 1)).eqv
      (qq15 * H0auto w N t) :=
    Q'.eqv_symm
      (fsum_const_mul qq15 (fun p => fsum (ccT w t p) (Nat.min 1 (nP N t p))) (t + 1))
  exact Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv epull)

/-! ## 5. The one-field reduction of `AutoconvBumpBounds` -/

/-- **`AutoconvReserveResidual w`** — the SOLE remaining sharp inequality of the bump
residual after Round I closes `dominate`: the central-autoconvolution log-concavity margin
`(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.  NAMED-OPEN (never `sorry`); it is the
genuine local-CLT reserve consuming `coeffW`'s STRICT super-log-concavity. -/
structure AutoconvReserveResidual (w : Q') : Type where
  /-- The central-autoconvolution log-concavity margin (uniform in `N, s`). -/
  reserve : ∀ N s,
    (1 + Q'.mkPos 31 225 (by decide)) * (H0auto w N s * H0auto w N (s + 2))
      ≤ H0auto w N (s + 1) * H0auto w N (s + 1)

/-- **`bumpBoundsOfReserve` — THE ONE-FIELD REDUCTION.**  A reserve residual inhabits the
full Round-H `AutoconvBumpBounds w`: the `dominate` field is discharged by `offAuto_dominate`
(this round), the `reserve` field is carried through. -/
def bumpBoundsOfReserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (rr : AutoconvReserveResidual w) : AutoconvBumpBounds w where
  dominate := fun N t => offAuto_dominate hw0 hw12 hwpos N t
  reserve := rr.reserve

/-- **`centralReserveOfResidual`** — the reserve residual inhabits Round G's full
`CentralAutoconvReserve w` (its finite fields + the now-proved domination all discharged). -/
def centralReserveOfResidual {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (rr : AutoconvReserveResidual w) : CentralAutoconvReserve w :=
  reserveOfBumpBounds hw0 (bumpBoundsOfReserve hw0 hw12 hwpos rr)

/-- **`s1DominanceOfResidual` — end-to-end.**  The reserve residual (plus the A1 strand
reindex and the per-`N` edge input) drives `S1Dominance N w 2` for EVERY `N`, with the
`dominate` field now internally discharged. -/
def s1DominanceOfResidual {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (rr : AutoconvReserveResidual w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  s1DominanceOfBumpBounds hw0 hw12 hwpos hw1 reindex
    (bumpBoundsOfReserve hw0 hw12 hwpos rr) N hedge

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `geoPow`, `geoPow_nonneg`, `quarter_of_four_le`, `leg_geo`, `geoPow_quarter_sq`,
    `ccT_geo` — the per-term geometric-tail engine.
  * `geoSum_inv`, `geoTail_le`, `geoShiftTail_le` — the exact finite geometric telescoping.
  * `off_slice_le` — the per-antidiagonal-position domination.
  * `offAuto_dominate` — THE DOMINATION FIELD `offAuto ≤ (1/15)·H0auto`, uniform in `N, t`.
  * `bumpBoundsOfReserve` — the one-field reduction (`dominate` discharged).
  * `centralReserveOfResidual`, `s1DominanceOfResidual` — the wiring to
    `CentralAutoconvReserve` and `S1Dominance` (every `N`).

NAMED OPEN (Type-level structure, never `sorry`):
  * `AutoconvReserveResidual w` — the SOLE remaining sharp inequality: the central-
    autoconvolution log-concavity margin `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.
    This is the genuine local-CLT reserve consuming `coeffW`'s strict super-log-concavity.
  * the A1 strand reindex `reindex` remains a threaded hypothesis.

HONEST VERDICT.  Round I PROVES the geometric shift-tail domination field of Round H's
`AutoconvBumpBounds` outright — for every `N, t`, uniformly — and reduces the two-field bump
residual to the SINGLE reserve inequality.  It does NOT prove the reserve.  This is a
structural sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass
gap. -/

end YMGap.Continuum.FusionCoreStepRoundI

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundI.quarter_of_four_le
#print axioms YMGap.Continuum.FusionCoreStepRoundI.leg_geo
#print axioms YMGap.Continuum.FusionCoreStepRoundI.geoPow_quarter_sq
#print axioms YMGap.Continuum.FusionCoreStepRoundI.ccT_geo
#print axioms YMGap.Continuum.FusionCoreStepRoundI.geoSum_inv
#print axioms YMGap.Continuum.FusionCoreStepRoundI.geoTail_le
#print axioms YMGap.Continuum.FusionCoreStepRoundI.geoShiftTail_le
#print axioms YMGap.Continuum.FusionCoreStepRoundI.off_slice_le
#print axioms YMGap.Continuum.FusionCoreStepRoundI.offAuto_dominate
#print axioms YMGap.Continuum.FusionCoreStepRoundI.bumpBoundsOfReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundI.centralReserveOfResidual
#print axioms YMGap.Continuum.FusionCoreStepRoundI.s1DominanceOfResidual


/-! ===========================================================================
    ## Round J  (was `FusionCoreStepRoundJ.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round J of the fusion box log-concavity node: the DIAGONAL (3/4) MINOR
RESERVE atom of the central-autoconvolution log-concavity margin (`AutoconvReserveResidual`),
proved symbolically for all modes, together with an HONEST machine-checked CORRECTION of the
naive "summand-wise" route to the reserve.

# What this module adds (read first — load-bearing honesty)

Round I reduced Round H's `AutoconvBumpBounds` to the SINGLE open field
`AutoconvReserveResidual.reserve`,

    (1 + 31/225)·H0auto(s)·H0auto(s+2)  ≤  H0auto(s+1)²        (uniform in `N, s`),

with `256/225 = (16/15)²` the two-leg square of Round I's geometric constant.  A natural
attack expands the central-autoconvolution defect `H0auto(s+1)² − H0auto(s)·H0auto(s+2)` as
a Menon convolution defect and hopes to write it as a sum of MANIFESTLY nonnegative terms:
a DIAGONAL part (`p = q`) carrying the factor-4 Casimir reserve, plus an OFF-DIAGONAL part
paired as symmetrized `2×2` minors.  Round J supplies the diagonal atom in full and shows —
machine-checked — that the off-diagonal part is NOT sign-definite, so the naive summand
route does NOT close the reserve (the wall is genuine, not a bookkeeping gap).

ROUND-J DELIVERABLE 1 (the diagonal (3/4) minor reserve — PROVED, symbolic, all `s`).
  * `coeffW_diagReserve` — the diagonal reserve in additive form: for `0 ≤ w ≤ 1/2`,
        (3/4)·c_{s+1}²  +  c_s·c_{s+2}   ≤   c_{s+1}²,
    i.e. the diagonal minor `δ_s := c_{s+1}² − c_s·c_{s+2}` has strength `δ_s ≥ (3/4)·c_{s+1}²`.
    This is exactly `1 − 1/4` of the mode square, the (3/4)=(1−K⁻¹) Casimir reserve at `K=4`,
    read off `coeffW_superLogConcave` (`c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`).  It is the diagonal
    (`p=q`) contribution the Menon autoconvolution defect identity would consume.
  * `coeffW_diagMinor_reserve` — the same fact in the `X + -Y` minor form
        (3/4)·c_{s+1}²  ≤  c_{s+1}²  +  −(c_s·c_{s+2}),
    the shape the defect identity pairs against the off-diagonal block.

ROUND-J DELIVERABLE 2 (the honest correction — the summand route provably does NOT close it).
  * `offMinor_wrong_direction` — a machine-checked refutation of the naive off-diagonal
    summand bound.  A summand-wise proof of the reserve would pair each off-diagonal Menon
    term `c_m·c_{n+2} + c_n·c_{m+2}` against `2·c_{m+1}·c_{n+1}` and hope both legs satisfy
    `c_·c_· ≤ c_{·+1}·c_{·+1}`.  At the true theta weight (`w = 1/2`, `(m,n) = (0,2)`) the
    second leg is
        c_2·c_2  ≤  c_3·c_1        — FALSE  (`c_2² = 9/65536 > 2/65536 = c_1·c_3`).
    For `n ≥ m+2` the pair `{c_n, c_{m+2}}` is LESS spread than `{c_{n+1}, c_{m+1}}`, so
    log-concavity makes it LARGER, not smaller.  Hence the symmetrized off-diagonal minor is
    NOT `≥ 0` in general, and the reserve is not a sum of manifestly nonnegative summands.
  * `symMinor`, `symMinor_can_be_negative` — the full symmetrized off-diagonal minor
    `T(m,n) = 2c_{m+1}c_{n+1} − c_m c_{n+2} − c_n c_{m+2}` and a decidable witness that it is
    `< 0` at `w = 1/2`, `(m,n) = (0,2)`.  This is the exact analogue of Round D's
    `bracket_can_be_negative` for the autoconvolution reserve.

# HONESTY — what is NOT closed

`AutoconvReserveResidual w` (Round I) remains NAMED-OPEN; Round J does NOT inhabit it, and
the A1 strand reindex remains a threaded hypothesis.  What Round J DOES prove is the diagonal
factor-`(3/4)` minor reserve (all `s`, symbolic `w ≤ 1/2`) and the machine-checked fact that
the off-diagonal block is genuinely indefinite — so the wall is real: the reserve requires
an AGGREGATE cancellation (the `QuadGershgorinClosure` / heat-kernel local-CLT content), not
a summand-wise nonnegativity.  This corrects the naive summand plan and sharpens the residual;
it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`coeffW_superLogConcave` lemmas, small
`Q'`-algebra congruences, and `decide` on closed concrete-rational facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only
(the `decide` refutations depend on NO axioms).  No `Classical.*`, no `native_decide`, no
`sorry`.  All witnesses are `Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundJ

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionCoreStepRoundI

/-- The diagonal Casimir reserve constant `3/4 = 1 − 1/4` (the `(1 − K⁻¹)` minor strength
at `K = 4`). -/
abbrev qq34 : Q' := Q'.mkPos 3 4 (by decide)

/-! ## 0. A small `Q'` algebra helper -/

/-- **`le_add_neg_of_add_le`** — rearrange `a + Y ≤ X` into the minor (`X + -Y`) form
`a ≤ X + -Y`.  Add `-Y` to both sides and cancel `Y + -Y ≃ 0`. -/
theorem le_add_neg_of_add_le {a Y X : Q'} (h : a + Y ≤ X) : a ≤ X + -Y := by
  have hstep : (a + Y) + -Y ≤ X + -Y := Q'.add_le_add h (Q'.le_refl' (-Y))
  have e : ((a + Y) + -Y).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a Y (-Y)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (Y + -Y) 0 (Q'.add_neg_self_eqv Y)) ?_
    exact q_add_zero_eqv a
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e) hstep

/-! ## 1. The diagonal (3/4) minor reserve -/

/-- **`coeffW_diagReserve` — the diagonal (3/4) minor reserve (additive form).**
For `0 ≤ w ≤ 1/2` and every mode `s`,

    (3/4)·(c_{s+1}·c_{s+1})  +  c_s·c_{s+2}   ≤   c_{s+1}·c_{s+1}.

Equivalently the diagonal minor `δ_s = c_{s+1}² − c_s·c_{s+2}` has reserve `δ_s ≥ (3/4)c_{s+1}²`.
PROOF.  `coeffW_superLogConcave` gives `c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`; adding `(3/4)·c_{s+1}²`
to both sides and `(3/4 + 1/4) ≃ 1` closes it. -/
theorem coeffW_diagReserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s : Nat) :
    qq34 * (coeffW w (s + 1) * coeffW w (s + 1)) + coeffW w s * coeffW w (s + 2)
      ≤ coeffW w (s + 1) * coeffW w (s + 1) := by
  -- `X := c_{s+1}²`, `Y := c_s·c_{s+2}`, with `Y ≤ (1/4)·X` from super-log-concavity.
  have h : coeffW w s * coeffW w (s + 2)
      ≤ quarter * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    coeffW_superLogConcave hw0 hw12 s
  have hstep :
      qq34 * (coeffW w (s + 1) * coeffW w (s + 1)) + coeffW w s * coeffW w (s + 2)
        ≤ qq34 * (coeffW w (s + 1) * coeffW w (s + 1))
          + quarter * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    Q'.add_le_add (Q'.le_refl' _) h
  -- `(3/4)·X + (1/4)·X ≃ X`
  have e : (qq34 * (coeffW w (s + 1) * coeffW w (s + 1))
        + quarter * (coeffW w (s + 1) * coeffW w (s + 1))).eqv
      (coeffW w (s + 1) * coeffW w (s + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv qq34 quarter (coeffW w (s + 1) * coeffW w (s + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (qq34 + quarter) 1 _ (by decide)) ?_
    exact Q'.one_mul_eqv _
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv e)

/-- **`coeffW_diagMinor_reserve` — the diagonal reserve in `X + -Y` minor form.**

    (3/4)·(c_{s+1}·c_{s+1})   ≤   (c_{s+1}·c_{s+1})  +  −(c_s·c_{s+2}).

The shape the Menon autoconvolution defect identity pairs against the off-diagonal block. -/
theorem coeffW_diagMinor_reserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s : Nat) :
    qq34 * (coeffW w (s + 1) * coeffW w (s + 1))
      ≤ coeffW w (s + 1) * coeffW w (s + 1) + -(coeffW w s * coeffW w (s + 2)) :=
  le_add_neg_of_add_le (coeffW_diagReserve hw0 hw12 s)

/-! ## 2. The honest correction — the off-diagonal block is NOT sign-definite -/

/-- The full symmetrized off-diagonal Menon minor
`T(m,n) = 2·c_{m+1}·c_{n+1} − c_m·c_{n+2} − c_n·c_{m+2}` (in `X + -Y` form), the pairing a
naive summand-wise proof of the reserve would need `≥ 0`. -/
def symMinor (w : Q') (m n : Nat) : Q' :=
  (coeffW w (m + 1) * coeffW w (n + 1) + coeffW w (m + 1) * coeffW w (n + 1))
    + -(coeffW w m * coeffW w (n + 2) + coeffW w n * coeffW w (m + 2))

/-- **`offMinor_wrong_direction` — the naive off-diagonal leg is FALSE.**  A summand-wise
proof of the reserve pairs `c_n·c_{m+2}` against `c_{n+1}·c_{m+1}` and hopes for `≤`.  At the
true theta weight (`w = 1/2`, `(m,n) = (0,2)`) this leg reads `c_2·c_2 ≤ c_3·c_1`, which is
FALSE: `c_2² = 9/65536 > 2/65536 = c_1·c_3` (for `n ≥ m+2` the pair `{c_n, c_{m+2}}` is LESS
spread than `{c_{n+1}, c_{m+1}}`, so log-concavity makes it LARGER).  Machine-checked. -/
theorem offMinor_wrong_direction :
    ¬ (coeffW wH 2 * coeffW wH 2 ≤ coeffW wH 3 * coeffW wH 1) := by decide

/-- **`symMinor_can_be_negative` — the symmetrized off-diagonal minor is indefinite.**  At
`w = 1/2`, `(m,n) = (0,2)` the pairing `T(0,2) = 2·c_1·c_3 − c_0·c_4 − c_2·c_2` is `< 0`
(`= −1285/16777216`).  Hence the autoconvolution reserve is NOT a sum of manifestly
nonnegative summands: the off-diagonal block must be dominated by an AGGREGATE cancellation
(the `QuadGershgorinClosure` / heat-kernel local-CLT content), not summand-wise.  The exact
analogue of `bracket_can_be_negative` for the reserve.  Machine-checked (no axioms). -/
theorem symMinor_can_be_negative : ¬ ((0 : Q') ≤ symMinor wH 0 2) := by decide

/-! ## 3. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`; the `decide` refutations depend
on NO axioms):
  * `le_add_neg_of_add_le` — the `a + Y ≤ X ⟹ a ≤ X + -Y` rearrangement.
  * `coeffW_diagReserve`, `coeffW_diagMinor_reserve` — the diagonal factor-`(3/4)` minor
    reserve of the central-autoconvolution log-concavity margin, all `s`, symbolic `w ≤ 1/2`.
  * `offMinor_wrong_direction`, `symMinor_can_be_negative` — the machine-checked CORRECTION:
    the naive off-diagonal summand leg is false and the symmetrized off-diagonal minor is
    strictly negative, so the reserve is not a sum of nonnegative summands.

NAMED OPEN (carried from Round I, NOT inhabited here):
  * `AutoconvReserveResidual w` — the reserve `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.
    Round J supplies its diagonal reserve and shows the off-diagonal block is indefinite;
    what remains is the AGGREGATE cancellation of the indefinite off-diagonal block against
    the diagonal `(3/4)`-reserve, uniform in the `N`-truncation — the same
    `QuadGershgorinClosure` / heat-kernel local-CLT wall.
  * the A1 strand reindex `reindex` remains a threaded hypothesis.

HONEST VERDICT.  Round J PROVES the diagonal `(3/4)` Casimir minor reserve of the reserve
inequality and MACHINE-CHECKS that the off-diagonal Menon block is not sign-definite — so the
reserve genuinely needs aggregate cancellation, not summand-wise nonnegativity.  This
corrects the naive summand plan and sharpens the residual; it is NOT a 4D Yang–Mills mass
gap. -/

end YMGap.Continuum.FusionCoreStepRoundJ

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundJ.le_add_neg_of_add_le
#print axioms YMGap.Continuum.FusionCoreStepRoundJ.coeffW_diagReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundJ.coeffW_diagMinor_reserve
#print axioms YMGap.Continuum.FusionCoreStepRoundJ.offMinor_wrong_direction
#print axioms YMGap.Continuum.FusionCoreStepRoundJ.symMinor_can_be_negative


/-! ===========================================================================
    ## Round K  (was `FusionCoreStepRoundK.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round K of the fusion box log-concavity node: the CROSS-STRAND
LOCALISATION of the central-autoconvolution reserve.  Two new symbolic all-`s` atoms
that pin *exactly where* the reserve wall lives — the diagonal / single-strand content
holds with a proved margin to spare, so the SOLE open content is the cross-strand
aggregation — together with a CONSOLIDATED restatement of the exact
`FusionConvLogConcaveCore` and the complete downstream chain to the excited-suppression
(`S1Dominance`) datum.

# Why this module exists (read first — load-bearing honesty)

Rounds A–J reduced the box log-concavity core `SelfFusionLogConcave.FusionConvLogConcaveCore`
to a SINGLE quantitative local-CLT residual, reachable by two equivalent routes:

  * Track B (box / Cauchy–Binet): `FusionConvLogConcaveCore` ⟸ `UniformBoxLogConcave`
    ⟸ `UniformBoxQuadCertificate` ⟸ `QuadGershgorinClosure` (RoundA/B/C).
  * Track A (line-sum / autoconvolution): `S1Dominance` ⟸ `StrandReduction`
    ⟸ `CentralAutoconvReserve` ⟸ `AutoconvBumpBounds` ⟸ `AutoconvReserveResidual`
    (RoundD–J), the last being the central-autoconvolution log-concavity MARGIN
    `(1 + 31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.

Round J proved the DIAGONAL factor-`(3/4)` minor reserve and MACHINE-REFUTED the naive
symmetrised off-diagonal summand route (`symMinor_can_be_negative`).  So the wall is
genuinely the CROSS-STRAND aggregate cancellation, not a bookkeeping gap.

Round K localises this precisely.  The reserve constant is `256/225 = 1 + 31/225`.  Applied
to a SINGLE strand (or the diagonal `p = q` block of the autoconvolution defect), the
super-log-concavity atom `coeffW_superLogConcave` (`c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`, RoundC)
gives the reserve with a UNIFORM factor of room, because

    (256/225) · (1/4)  =  64/225  <  1.

So the diagonal / single-strand half of the reserve is TRUE with a `225/64 ≈ 3.5×` margin,
for every mode, symbolically on `w ≤ 1/2`.  The genuine open content — as Round J's
refutation already isolates — is exactly the CROSS-strand (`p ≠ q`) aggregation, where the
symmetrised minor is indefinite and needs the heat-kernel local-CLT cancellation.  These
atoms make the "where is the wall" verdict quantitative and machine-checked.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat`)

  * `coeffW_strandReserve` — the SINGLE-STRAND reserve: for `0 ≤ w ≤ 1/2` and every `s`,
        (1 + 31/225) · (c_s · c_{s+2})  ≤  c_{s+1} · c_{s+1}.
    The exact reserve constant `256/225`, discharged on one strand with margin (`64/225 ≤ 1`).
  * `fusionMeasure_superLogConcave` — the TWO-BODY (p = 2 fusion measure) magnitude reserve:
        (c_a·c_{a+2})·(c_b·c_{b+2})  ≤  (1/16) · ((c_{a+1}·c_{a+1})·(c_{b+1}·c_{b+1})).
    A factor-`1/16` strengthening of `R1LocalCLT.fusionMeasure_logConcave` (which has the
    plain factor `1`), on the strong-coupling window.  This is the magnitude reserve of the
    two-body fusion channel that builds `boxSum`.
  * `fusionConvLogConcaveCore_of_uniform` — CONSOLIDATION: a single `UniformBoxLogConcave w`
    witness (the sharp Track-B residual) inhabits `FusionConvLogConcaveCore N w` for EVERY
    `N` (re-export of `coreOfUniform`), and `s1Dominance_all_of_uniform` completes the chain
    to the excited-suppression datum `S1Dominance N w 2` for every `N` (with the per-`N`
    edge input).  The exact statement + the complete chain-to-defect in one auditable place.

# HONEST verdict and scope

Round K does NOT close the residual.  It proves the diagonal / single-strand half of the
reserve holds with a uniform margin, quantifying Round J's refutation into a precise "the
open content is the cross-strand aggregation" statement, and adds the two-body magnitude
reserve of the fusion channel.  The SOLE remaining open content is the cross-strand
aggregate cancellation — `AutoconvReserveResidual` / `LagCorrTP2` / `QuadGershgorinClosure`,
the heat-kernel `(r,d)` local-CLT — NOT a finite rational inequality, and NOT the (repeatedly
machine-refuted) generic "convolution preserves log-concavity".  This is a structural
sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap, and
it inhabits NO Clay-frontier bundle.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW_superLogConcave` / `mul_swap4` lemmas,
positive-factor monotonicity, and `decide` only on closed concrete-rational constants.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundK

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC

/-- The exact reserve constant `256/225 = 1 + 31/225` (Round I's two-leg square
`(16/15)²`). -/
abbrev reserveC : Q' := 1 + Q'.mkPos 31 225 (by decide)

/-! ## 1. The single-strand reserve — the diagonal half holds with margin -/

/-- **`coeffW_strandReserve` — the single-strand reserve (all `s`, symbolic `w ≤ 1/2`).**

    (1 + 31/225) · (c_s · c_{s+2})  ≤  c_{s+1} · c_{s+1}.

This is `AutoconvReserveResidual`'s constant applied to a SINGLE strand.  It holds with a
uniform factor of room: `coeffW_superLogConcave` gives `c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`, and
`(256/225)·(1/4) = 64/225 ≤ 1`.  So the diagonal / single-strand half of the reserve is
`≈ 3.5×` inside the bound at every mode — the wall is NOT here.  The genuine open content is
the CROSS-strand (`p ≠ q`) aggregation (Round J's `symMinor_can_be_negative`). -/
theorem coeffW_strandReserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (s : Nat) :
    reserveC * (coeffW w s * coeffW w (s + 2))
      ≤ coeffW w (s + 1) * coeffW w (s + 1) := by
  -- super-log-concavity: `c_s·c_{s+2} ≤ (1/4)·c_{s+1}²`
  have h : coeffW w s * coeffW w (s + 2)
      ≤ quarter * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    coeffW_superLogConcave hw0 hw12 s
  have hsqnn : (0 : Q') ≤ coeffW w (s + 1) * coeffW w (s + 1) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 (s + 1)) (coeffW_nonneg hw0 (s + 1))
  -- scale by `reserveC ≥ 0`
  have h1 : reserveC * (coeffW w s * coeffW w (s + 2))
      ≤ reserveC * (quarter * (coeffW w (s + 1) * coeffW w (s + 1))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h (by decide)
  -- `reserveC · (quarter · Y) ≃ (reserveC · quarter) · Y`
  have e : (reserveC * (quarter * (coeffW w (s + 1) * coeffW w (s + 1)))).eqv
      ((reserveC * quarter) * (coeffW w (s + 1) * coeffW w (s + 1))) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv reserveC quarter _)
  -- `(reserveC · quarter) · Y ≤ 1 · Y ≤ Y`  since `reserveC · quarter = 64/225 ≤ 1`
  have h2 : (reserveC * quarter) * (coeffW w (s + 1) * coeffW w (s + 1))
      ≤ (1 : Q') * (coeffW w (s + 1) * coeffW w (s + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : reserveC * quarter ≤ (1 : Q')) hsqnn
  refine Q'.le_trans' _ _ _ h1 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
  exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-! ## 2. The two-body (p = 2 fusion measure) magnitude reserve -/

/-- The strong-coupling two-body reserve constant `1/16 = (1/4)²`. -/
abbrev sixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- **`fusionMeasure_superLogConcave` — the two-body magnitude reserve (all `a,b`, `w ≤ 1/2`).**

    (c_a·c_{a+2})·(c_b·c_{b+2})  ≤  (1/16) · ((c_{a+1}·c_{a+1})·(c_{b+1}·c_{b+1})).

This is the factor-`1/16` strong-coupling strengthening of
`R1LocalCLT.fusionMeasure_logConcave` (plain factor `1`): the two-body fusion channel that
builds `boxSum` carries a uniform `(1/4)²` magnitude reserve.  Proof: multiply two copies of
the RoundC atom `coeffW_superLogConcave` (nonneg factors) and combine `(1/4)·(1/4) = 1/16`
via the four-factor regroup `mul_swap4`. -/
theorem fusionMeasure_superLogConcave {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (a b : Nat) :
    (coeffW w a * coeffW w (a + 2)) * (coeffW w b * coeffW w (b + 2))
      ≤ sixteenth
          * ((coeffW w (a + 1) * coeffW w (a + 1))
             * (coeffW w (b + 1) * coeffW w (b + 1))) := by
  have hA : coeffW w a * coeffW w (a + 2)
      ≤ quarter * (coeffW w (a + 1) * coeffW w (a + 1)) :=
    coeffW_superLogConcave hw0 hw12 a
  have hB : coeffW w b * coeffW w (b + 2)
      ≤ quarter * (coeffW w (b + 1) * coeffW w (b + 1)) :=
    coeffW_superLogConcave hw0 hw12 b
  have hLBnn : (0 : Q') ≤ coeffW w b * coeffW w (b + 2) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 b) (coeffW_nonneg hw0 (b + 2))
  have hQAnn : (0 : Q') ≤ quarter * (coeffW w (a + 1) * coeffW w (a + 1)) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 (a + 1)) (coeffW_nonneg hw0 (a + 1)))
  -- `LA·LB ≤ (¼A')·LB ≤ (¼A')·(¼B')`
  have step1 : (coeffW w a * coeffW w (a + 2)) * (coeffW w b * coeffW w (b + 2))
      ≤ (quarter * (coeffW w (a + 1) * coeffW w (a + 1))) * (coeffW w b * coeffW w (b + 2)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hA hLBnn
  have step2 : (quarter * (coeffW w (a + 1) * coeffW w (a + 1))) * (coeffW w b * coeffW w (b + 2))
      ≤ (quarter * (coeffW w (a + 1) * coeffW w (a + 1)))
          * (quarter * (coeffW w (b + 1) * coeffW w (b + 1))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hB hQAnn
  -- `(¼A')·(¼B') ≃ (¼·¼)·(A'·B') ≃ (1/16)·(A'·B')`
  have eswap : ((quarter * (coeffW w (a + 1) * coeffW w (a + 1)))
        * (quarter * (coeffW w (b + 1) * coeffW w (b + 1)))).eqv
      ((quarter * quarter)
        * ((coeffW w (a + 1) * coeffW w (a + 1)) * (coeffW w (b + 1) * coeffW w (b + 1)))) :=
    mul_swap4 quarter (coeffW w (a + 1) * coeffW w (a + 1)) quarter
      (coeffW w (b + 1) * coeffW w (b + 1))
  have econst : ((quarter * quarter)
        * ((coeffW w (a + 1) * coeffW w (a + 1)) * (coeffW w (b + 1) * coeffW w (b + 1)))).eqv
      (sixteenth
        * ((coeffW w (a + 1) * coeffW w (a + 1)) * (coeffW w (b + 1) * coeffW w (b + 1)))) :=
    Q'.mul_eqv_congr_right (quarter * quarter) sixteenth _ (by decide)
  refine Q'.le_trans' _ _ _ step1 ?_
  refine Q'.le_trans' _ _ _ step2 ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eswap) (Q'.le_of_eqv econst)

/-! ## 3. Consolidation — the exact core statement and the complete chain to the defect -/

/-- **`fusionConvLogConcaveCore_of_uniform` — the sharp Track-B residual drives the whole
`N`-tower of the box log-concavity core.**  A single `UniformBoxLogConcave w` witness (the
direct box log-concavity for ALL `N`, the corrected uniform residual of RoundA) inhabits
`SelfFusionLogConcave.FusionConvLogConcaveCore N w` for EVERY `N`.  Re-export of
`FusionCoreStepRoundA.coreOfUniform`, surfaced here as the one-line consolidation of the
exact box-core statement against its single residual. -/
def fusionConvLogConcaveCore_of_uniform {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (u : UniformBoxLogConcave w) (N : Nat) :
    FusionConvLogConcaveCore N w hw0 hw1 :=
  coreOfUniform hw0 hw1 u N

/-- **`s1Dominance_all_of_uniform` — the complete chain to the excited-suppression datum.**
The single Track-B residual `UniformBoxLogConcave w` (plus the elementary per-`N`
first-excited edge `bmc 2 ≤ bmc 1`) drives `S1Dominance N w 2` — the `s = 1`-dominance /
excited-mode-suppression datum, i.e. the defect bound the bond-moving control consumes — for
EVERY `N`.  Re-export of `FusionCoreStepRoundA.s1DominanceOfUniform`, exhibiting that the
downstream chain `core ⟹ log-concavity ⟹ peak ⟹ s = 1-dominance` is COMPLETE: the ONLY open
content is the residual `u`. -/
def s1Dominance_all_of_uniform {w : Q'} (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (u : UniformBoxLogConcave w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  s1DominanceOfUniform hw hw1 u N hedge

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `coeffW_strandReserve` — the single-strand reserve `(1+31/225)·c_s·c_{s+2} ≤ c_{s+1}²`,
    all `s`, symbolic `w ≤ 1/2`, with the margin `(256/225)·(1/4) = 64/225 ≤ 1`.  The
    diagonal / single-strand half of `AutoconvReserveResidual` — proved, with room to spare.
  * `fusionMeasure_superLogConcave` — the two-body factor-`1/16` magnitude reserve of the
    p = 2 fusion channel (strong-coupling strengthening of `R1LocalCLT.fusionMeasure_logConcave`).
  * `fusionConvLogConcaveCore_of_uniform`, `s1Dominance_all_of_uniform` — the consolidated
    exact box-core statement + the complete downstream chain to `S1Dominance N w 2` (every
    `N`), driven by the single residual `UniformBoxLogConcave w`.

NAMED OPEN (carried, NOT inhabited here):
  * The CROSS-strand aggregation of the reserve — `AutoconvReserveResidual` (Track A) /
    `QuadGershgorinClosure` (Track B) / `LagCorrTP2` — where the symmetrised off-diagonal
    minor is indefinite (`FusionCoreStepRoundJ.symMinor_can_be_negative`).  This is the
    heat-kernel `(r,d)` Gaussian-theta local-CLT, NOT a finite rational inequality, and NOT
    the machine-refuted generic "convolution preserves log-concavity".

HONEST VERDICT.  Round K localises the reserve wall: the diagonal / single-strand half holds
with a uniform `≈ 3.5×` margin (proved, all `s`), and the two-body fusion channel carries a
`1/16` magnitude reserve.  So the SOLE open content is the cross-strand aggregate
cancellation.  The downstream chain (core ⟹ log-concavity ⟹ peak ⟹ `s = 1`-dominance) is
COMPLETE and re-exported.  This is a structural sharpening of one box-level log-concavity
sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundK

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundK.coeffW_strandReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundK.fusionMeasure_superLogConcave
#print axioms YMGap.Continuum.FusionCoreStepRoundK.fusionConvLogConcaveCore_of_uniform
#print axioms YMGap.Continuum.FusionCoreStepRoundK.s1Dominance_all_of_uniform
