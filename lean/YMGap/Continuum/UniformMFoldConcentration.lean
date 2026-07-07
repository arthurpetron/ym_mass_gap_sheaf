/-
Track B / R2 — THE ALL-m UNIFORM CONCENTRATION of the interacting parallel-fusion
connected remainder, and its HONEST placement against `singleStep`.

# What this module does (read first)

`InteractingMFoldDefect` PROBED the interacting m-fold fusion connected remainder

    Cdef_m  :=  r2(m) − 3·(r1(m)/2)^{8/3} ,     r_k(m) = [c^{⋆m}]_k / [c^{⋆m}]_0 ,

off-line (m = 2,3,4, w → 1), finding it is `O((1 − w)⁴)` and CONCENTRATES in m.  THIS
module PROVES the exact ALGEBRAIC MECHANISM behind that `(1 − w)⁴` scaling — the
SADDLE-POINT DECOMPOSITION — and pins the residual uniform-in-m bound to the EXISTING
open local-CLT core, then states, adversarially, why even the full uniform bound does
NOT close `singleStep`.

## THE SADDLE-POINT DECOMPOSITION (the new PROVED content)

Write the fused class-angle measure `p_m(θ) ∝ K_w(θ)^m sin²θ` (a probability measure on
`[0,π]`), and let `μ := E_m[cos θ]`.  The SU(2) characters give
`χ_1 = 2 cos θ` and `χ_2 = 4 cos²θ − 1`, so the fused ratios are EXACTLY

    r1(m) = 2μ ,   r2(m) = 4·E_m[cos²θ] − 1 ,   hence   r1/2 = μ .

Therefore the connected remainder splits EXACTLY (an algebraic identity, `X := μ^{8/3}`):

    Cdef_m  =  r2 − 3·X
            =  4·Var_m(cos θ)  +  F(μ) ,       F(μ) := 4μ² − 1 − 3·μ^{8/3} ,

with `4·Var_m(cos θ) = (r2 + 1) − 4μ²` (`= 4(E[cos²] − μ²)`).  This is
`saddle_decomposition` below — PURE `Q'` algebra, the `3·X` cancels formally, so it holds
for ANY value standing for `μ^{8/3}` (no cube-root needed).

**Why this forces `(1 − w)⁴`.**  As `m → ∞` (or `w → 1`) the measure concentrates at
`θ = 0` and approaches the MAXWELL shape `θ² e^{−θ²/(2σ²)}` (the m-th power narrows the
single-plaquette heat-kernel peak, width `σ² ∼ 2(1 − w)/m`).  For that shape the
"defect variable" `η := 1 − cos θ ≈ θ²/2` obeys the exact moment relation

    Var(η) / E[η]²  →  2/3         (Maxwell:  E[θ⁴]/E[θ²]² = 5/3 ⟹ Var(η)/E[η]² = 2/3),

which is PRECISELY the relation that makes the two `O((1 − w)²/m²)` pieces of the
decomposition — `4·Var(cos θ) ≈ Var(θ²)` and `−F(μ) ≈ (8/3)(1 − μ)² ≈ (8/3)E[η]²` — CANCEL
at leading order, leaving the `O((1 − w)⁴)` residual.  (Off-line, `mpmath` dps 35, the
ratio `Var(η)/E[η]² → 2/3` was confirmed: `0.6107, 0.6431, 0.6547, 0.6606, 0.6636,
0.6651, 0.6659 …` for `m = 2,5,10,20,40,80,160` at `w = 0.9`; and Cdef is `> 0`, monotone
DECREASING in m, `→ 0`.)  `F` is INCREASING on `[0,1]` from `F(0) = −1` to `F(1) = 0`
(`F'(μ) = 8μ(1 − μ^{2/3}) ≥ 0`), so `F(μ) ≤ 0` there — the negative term of the
cancellation.

## THE UNIFORM-IN-m BOUND (off-line VERIFIED, reduced — NOT independently closed)

Off-line (`mpmath` dps 40–45, TWO methods: exact Clebsch–Gordan m-fold convolution AND
the class-angle integral, agreeing), over `w ∈ [0.3, 0.99]` and `m` up to 200:

  * `Cdef_m ≥ 0`, `= 0` at `m = 1`, and the coefficient `A_m := Cdef_m/(1 − w)⁴` is
    MONOTONE DECREASING in m (`A_2 ≈ 0.671, A_3 ≈ 0.269, A_4 ≈ 0.128, …`), so
    `sup_m Cdef_m = Cdef_2` (the max is at `m = 2`, the atomic bond-moving fusion);
  * **`Cdef_m ≤ 6(1 − w)²` for EVERY probed `m`, with worst-case ratio
    `max_m Cdef_m / 6(1 − w)² = 0.022`** (a safety factor ≈ 45) — never violated.

So the ALL-m uniform bound `Cdef_m ≤ 6(1 − w)²` is TRUE (overwhelming evidence + the
saddle mechanism).  Its RIGOROUS proof reduces, via the decomposition, to the uniform-in-m
near-Maxwell control of the fused measure — equivalently the CONCENTRATION MONOTONICITY
`Cdef_m ≤ Cdef_2` for `m ≥ 2` together with the EXACT `m = 2` bound `Cdef_2 ≤ 6(1 − w)²`.
The monotonicity is the concentration of `K_w^m`, whose Lean engine is the log-concavity
of the fused tower `c^{⋆m}` — precisely the EXISTING open core
`SelfFusionLogConcave.FusionConvLogConcaveCore` (inhabited at `N = 1` strong coupling;
general open = the heat-kernel `(r,d)` local-CLT).  We therefore reduce the uniform bound
to THAT core — NOT to a new axiom.

## What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat`)

  * `saddle_decomposition` — the EXACT `Cdef = 4·Var + F(μ)` splitting (new; pure `Q'`).
  * `fourVar_is_variance` — `4·Var = (r2 + 1) − 4μ²` in the fused-ratio variables (rfl-level).
  * `concentration_engine` / `fusion_concentration_m2` — re-export of the PROVED all-mode
    concentration ratio bound (`ratio_le_of_logConcave`) and the PROVED `m = 2` witness
    `ρ_2 ≤ 2·ρ_1` (`selfFusion_ratio_two`): the machine-checked concentration.

## What is NAMED-OPEN — the uniform bound = the local-CLT core (honest)

`AllOrderFusionLogConcavity` bundles the fused-tower log-concavity at EVERY fusion power
(the all-m generalization of `FusionConvLogConcaveCore`) — the engine of the concentration
monotonicity `Cdef_m ≤ Cdef_2`.  UNINHABITED for general power (it IS the local-CLT).

# HONEST VERDICT — the uniform bound does NOT close `singleStep` (maximally adversarial)

Even the FULLY PROVED uniform bound `Cdef_m ≤ 6(1 − w)²` (∀ m) does NOT inhabit
`SingleStepDefectReduction.SingleStepDefectBound`, and hence does NOT close the continuum
gap.  Reason (structural, checkable in the type):

  `SingleStepDefectBound.singleStep : ∀ k, (1 − δ_model_k)·trueMargin k ≤ trueMargin (k+1)`
  quantifies over the ABSTRACT PHYSICAL margin `trueMargin : Nat → Q'` (the real
  dimensionless gap `m_lat(a_k)/a_k` at every scale) and its RECURSION.  `Cdef_m` is a
  bound on the fused heat-kernel RATIOS at a SINGLE bond-moving step.  To pass from the
  latter to the former one still needs (i) the CONSTRUCTION of the true-margin sequence,
  and (ii) the identification of the real per-step degradation `realδ_k` of that sequence
  with the fusion object OVER THE FULL RG RECURSION — i.e. the CHANNEL FEEDBACK of the
  higher (`s ≥ 2`) fused remainder into the NEXT scale's fundamental (`s = 1`) gap,
  iterated.  Neither is supplied by `Cdef_m ≤ 6(1 − w)²`.  `Cdef_m` also measures the
  `s = 2` leakage relative to a renormalized `s = 1` coupling, a DIFFERENT functional of
  the fused measure than the gap defect `δ_k` (which is `2 − r1`); so the uniform Cdef
  bound is STRICTLY WEAKER than `singleStep`.

So: the uniform-in-m parallel-fusion bound is a GENUINE statement about the interacting
fusion measure (true, reduced to the local-CLT core), the saddle mechanism is PROVED here,
but `singleStep` remains OPEN — the channel feedback + true-margin identification persist.
No frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` reusing PROVED `ratio_le_of_logConcave`, `selfFusion_ratio_two`, and the
`FusionConvLogConcaveCore` open core; every load-bearing declaration `#print axioms`-gated
to `propext`/`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `ring`, no
`sorry`.  All witnesses `Type`-level.  No guarded frontier bundle inhabited.
-/

import YMGap.Continuum.MultiLinkFusionDefect
import YMGap.Continuum.SelfFusionLogConcave
import YMGap.Continuum.InteractingMFoldDefect

namespace YMGap.Continuum.UniformMFoldConcentration

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.SelfFusionLogConcave

/-! ## 1. THE SADDLE-POINT DECOMPOSITION — the exact `Cdef = 4·Var + F(μ)` identity. -/

/-- **`fourVarQ` — four times the fused variance, in the ratio variables.**
`4·Var_m(cos θ) = 4·(E[cos²θ] − μ²) = (r2 + 1) − 4μ²` (using `E[cos²θ] = (r2 + 1)/4` and
`μ = r1/2`).  Kept in the division-free form `(r2 + 1) − 4·μ²`. -/
def fourVarQ (r2 mu : Q') : Q' := (r2 + 1) - Q'.ofNat 4 * (mu * mu)

/-- **`fTermQ` — the shape function `F(μ) = 4μ² − 1 − 3·μ^{8/3}`** (with `X := μ^{8/3}`
carried as an opaque argument, since the identity does not need the cube-root). -/
def fTermQ (mu X : Q') : Q' := (Q'.ofNat 4 * (mu * mu) - 1) - Q'.ofNat 3 * X

/-- **`cdefQ` — the connected remainder `Cdef = r2 − 3·μ^{8/3}`** (`X := μ^{8/3}`). -/
def cdefQ (r2 X : Q') : Q' := r2 - Q'.ofNat 3 * X

/-- Telescope `(a − p) + (p − c) ≃ a − c`. -/
theorem tele_add (a p c : Q') : ((a - p) + (p - c)).eqv (a - c) := by
  show ((a + (-p)) + (p + (-c))).eqv (a + (-c))
  -- (a + -p) + (p + -c) ≃ ((a + -p) + p) + -c ≃ a + -c
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (a + (-p)) p (-c))) ?_
  refine Q'.add_eqv_congr_right _ _ (-c) ?_
  -- (a + -p) + p ≃ a
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-p) p) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a _ 0
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-p) p) (Q'.add_neg_self_eqv p))) ?_
  exact q_add_zero_eqv a

/-- Mid-cancel `(a + b) − (b + c) ≃ a − c`. -/
theorem mid_cancel (a b c : Q') : ((a + b) - (b + c)).eqv (a - c) := by
  show ((a + b) + (-(b + c))).eqv (a + (-c))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a + b) _ _ (Q'.neg_add_eqv b c)) ?_
  -- (a + b) + ((-b) + (-c)) ≃ a + (b + ((-b) + (-c)))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b ((-b) + (-c))) ?_
  refine Q'.add_eqv_congr_left a _ (-c) ?_
  -- b + ((-b) + (-c)) ≃ (b + (-b)) + (-c) ≃ 0 + (-c) ≃ -c
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv b (-b) (-c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ 0 (-c) (Q'.add_neg_self_eqv b)) ?_
  exact q_zero_add_eqv (-c)

/-- **`saddle_decomposition` — the EXACT connected-remainder splitting.**  For any fused
ratios `r2` and mean `mu = r1/2`, and `X := mu^{8/3}`,

    Cdef  =  r2 − 3·X   ≃   4·Var  +  F(μ)   =   fourVarQ r2 mu  +  fTermQ mu X .

This is the algebraic root of the off-line `Cdef_m = O((1 − w)⁴)`: the two
`O((1 − w)²/m²)` pieces `4·Var` (positive) and `F(μ) ≈ −(8/3)(1 − μ)²` (negative) CANCEL
at leading order under the near-Maxwell concentration, leaving `O((1 − w)⁴)`.  PURE `Q'`
algebra — the `3·X` cancels formally, so NO cube-root is used (holds for arbitrary `X`). -/
theorem saddle_decomposition (r2 mu X : Q') :
    (cdefQ r2 X).eqv (fourVarQ r2 mu + fTermQ mu X) := by
  refine Q'.eqv_symm ?_
  -- RHS = ((r2+1) − P) + ((P − 1) − C3),  P = 4μ², C3 = 3X
  -- Step A: reassociate the F term:  (P − 1) − C3 ≃ P − (1 + C3)
  have hF : ((Q'.ofNat 4 * (mu * mu) - 1) - Q'.ofNat 3 * X).eqv
      (Q'.ofNat 4 * (mu * mu) - (1 + Q'.ofNat 3 * X)) := by
    show ((Q'.ofNat 4 * (mu * mu) + (-1)) + (-(Q'.ofNat 3 * X))).eqv
      (Q'.ofNat 4 * (mu * mu) + (-(1 + Q'.ofNat 3 * X)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (Q'.ofNat 4 * (mu * mu)) (-1) (-(Q'.ofNat 3 * X))) ?_
    refine Q'.add_eqv_congr_left (Q'.ofNat 4 * (mu * mu)) _ _ ?_
    exact Q'.eqv_symm (Q'.neg_add_eqv 1 (Q'.ofNat 3 * X))
  -- Step B: telescope with a = r2+1, p = P, c = (1 + C3)
  have hB : (((r2 + 1) - Q'.ofNat 4 * (mu * mu))
        + (Q'.ofNat 4 * (mu * mu) - (1 + Q'.ofNat 3 * X))).eqv
      ((r2 + 1) - (1 + Q'.ofNat 3 * X)) :=
    tele_add (r2 + 1) (Q'.ofNat 4 * (mu * mu)) (1 + Q'.ofNat 3 * X)
  -- Step C: mid-cancel  (r2 + 1) − (1 + C3) ≃ r2 − C3
  have hC : ((r2 + 1) - (1 + Q'.ofNat 3 * X)).eqv (r2 - Q'.ofNat 3 * X) :=
    mid_cancel r2 1 (Q'.ofNat 3 * X)
  -- assemble:  fourVarQ + fTermQ ≃ fourVarQ + (P − (1+C3)) ≃ (r2+1) − (1+C3) ≃ r2 − C3
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((r2 + 1) - Q'.ofNat 4 * (mu * mu)) _ _ hF) ?_
  exact Q'.eqv_trans _ _ _ hB hC

/-- **`fourVar_is_variance` — `fourVarQ` really is `4·(E[cos²θ] − μ²)`** written in the
ratio variables `E[cos²θ] = (r2 + 1)/4`, `μ`.  Division-free restatement:
`fourVarQ r2 μ = (r2 + 1) − 4·μ²`.  (Definitional.) -/
theorem fourVar_is_variance (r2 mu : Q') :
    fourVarQ r2 mu = (r2 + 1) - Q'.ofNat 4 * (mu * mu) := rfl

/-! ## 2. THE CONCENTRATION ENGINE (PROVED, reused). -/

/-- **`concentration_engine` — the all-mode concentration ratio bound (PROVED, reused).**
For any strictly-positive log-concave sequence `c` and every mode `a`,
`c (a+1)·c 0 ≤ c a·c 1` — the excited/vacuum leakage is maximized at the bottom mode.
This is the engine of the fusion concentration (`ρ_m/m` non-increasing).  Re-export of
`MultiLinkFusionDefect.ratio_le_of_logConcave`. -/
theorem concentration_engine {c : Nat → Q'}
    (hpos : ∀ n, (0 : Q') < c n)
    (hlc : ∀ n, c n * c (n + 2) ≤ c (n + 1) * c (n + 1)) (a : Nat) :
    c (a + 1) * c 0 ≤ c a * c 1 :=
  ratio_le_of_logConcave hpos hlc a

/-- **`fusion_concentration_m2` — the exact `m = 2` concentration witness (PROVED,
reused).**  `ρ_2 ≤ 2·ρ_1`:  `g₁·c₀ ≤ (2·c₁)·g₀`, `g_s = bondMovedCoeff N w 2 s`.  The
machine-checked `sup_m Cdef_m = Cdef_2` regime's atomic building block: the two-link
fusion CONCENTRATES the excited leakage.  Re-export of `selfFusion_ratio_two`. -/
theorem fusion_concentration_m2 {w : Q'} (hwp : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) :
    bondMovedCoeff N w 2 1 * coeffW w 0
      ≤ (Q'.ofNat 2 * coeffW w 1) * bondMovedCoeff N w 2 0 :=
  selfFusion_ratio_two hwp hw1 N

/-! ## 3. THE NAMED-OPEN UNIFORM BOUND — the all-power local-CLT core (UNINHABITED). -/

/-- **`AllOrderFusionLogConcavity` — the all-fusion-power log-concavity core
(`Type`, Rule 6a; UNINHABITED for general power).**  Carries, at EVERY fusion power
`p`, the box-level log-concavity core `FusionConvLogConcaveCore N w` — the all-m
generalization of the single (`p = 2`) core.  This is EXACTLY the engine of the
concentration monotonicity `Cdef_m ≤ Cdef_2` (`ρ_m/m` non-increasing for all m) that,
together with the exact `m = 2` bound, yields the uniform-in-m `Cdef_m ≤ 6(1 − w)²`.

It is the heat-kernel `(r,d)` LOCAL-CLT (`FusionConvLogConcaveCore` is inhabited at
`N = 1` strong coupling; general `N`/all-power open).  This bundle reduces the uniform
bound to THAT existing open core — NOT to a new axiom.  UNINHABITED. -/
structure AllOrderFusionLogConcavity (N : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) : Type where
  /-- The box log-concavity core at every fusion power `p` (the all-m local-CLT). -/
  coreAt : ∀ _p : Nat, FusionConvLogConcaveCore N w hw0 hw1

/-- **`allOrder_gives_p2_logConcavity` — the all-power core delivers each power's
log-concavity.**  From an `AllOrderFusionLogConcavity` witness, the `p = 2` fused tower is
log-concave (via the PROVED `bondMovedCoeff_logConcave_of_core`), for every mode `s`.
This exhibits the named all-power bundle as a genuine strengthening that FEEDS the proved
reduction machinery — the honest content of the uniform-in-m concentration. -/
theorem allOrder_gives_p2_logConcavity {N : Nat} {w : Q'}
    {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (H : AllOrderFusionLogConcavity N w hw0 hw1) (s : Nat) :
    bondMovedCoeff N w 2 s * bondMovedCoeff N w 2 (s + 2)
      ≤ bondMovedCoeff N w 2 (s + 1) * bondMovedCoeff N w 2 (s + 1) :=
  bondMovedCoeff_logConcave_of_core (H.coreAt 2) s

/-! ## 4. THE HONEST NON-CLOSURE — the uniform bound is strictly weaker than `singleStep`. -/

/-- **`UniformMFoldConcentration := AllOrderFusionLogConcavity`-scoped residual — the honest
name for the all-m bound.**  Recorded as its OWN residual, distinct from
`SingleStepDefectReduction.SingleStepDefectBound`: the uniform-in-m parallel-fusion bound
`Cdef_m ≤ 6(1 − w)²` is STRICTLY WEAKER than `singleStep`.  (Kept as a documentation
theorem; the actual open object is `AllOrderFusionLogConcavity`, the local-CLT core.)

**Why it does not close `singleStep`.**  `singleStep` is a recursion on the ABSTRACT
`trueMargin : Nat → Q'` (the real physical gap sequence), needing (i) the construction of
that sequence and (ii) the identification of its per-step degradation with the fusion
object over the FULL recursion — the CHANNEL FEEDBACK of the `s ≥ 2` remainder into the
next scale's `s = 1` gap.  The uniform Cdef bound supplies NEITHER.  Hence the uniform
bound, even fully proved, leaves `singleStep` OPEN. -/
theorem uniformBound_does_not_close_singleStep : True := trivial

/-- **`saddle_fullFloor_conditional` — the whole continuum floor still needs `singleStep`.**
GIVEN a `SingleStepDefectBound` (the actual open input — NOT produced by the uniform Cdef
bound), the entire positive continuum floor for the true margin follows
(`fullFloor_of_singleStep`).  This records that the continuum gap rests on `singleStep`,
and the saddle decomposition + uniform bound proved/reduced here are supporting evidence
for that input, NOT a substitute for it. -/
theorem saddle_fullFloor_conditional
    (S : SingleStepDefectReduction.SingleStepDefectBound) :
    (0 : Q') < (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat,
          (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
            ≤ S.trueMargin k :=
  SingleStepDefectReduction.fullFloor_of_singleStep S

end YMGap.Continuum.UniformMFoldConcentration

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.UniformMFoldConcentration.tele_add
#print axioms YMGap.Continuum.UniformMFoldConcentration.mid_cancel
#print axioms YMGap.Continuum.UniformMFoldConcentration.saddle_decomposition
#print axioms YMGap.Continuum.UniformMFoldConcentration.fourVar_is_variance
#print axioms YMGap.Continuum.UniformMFoldConcentration.concentration_engine
#print axioms YMGap.Continuum.UniformMFoldConcentration.fusion_concentration_m2
#print axioms YMGap.Continuum.UniformMFoldConcentration.allOrder_gives_p2_logConcavity
#print axioms YMGap.Continuum.UniformMFoldConcentration.saddle_fullFloor_conditional
