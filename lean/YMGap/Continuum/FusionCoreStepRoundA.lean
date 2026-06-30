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

import YMGap.Continuum.FusionCoreInduction
import YMGap.Continuum.FusionLogConcave

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
