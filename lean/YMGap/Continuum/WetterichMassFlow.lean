/-
Track B / R2 — **THE WETTERICH (FUNCTIONAL RG) EXACT-FLOW MASS-TERM EQUATION with the
THRESHOLD / DECOUPLING structure**: the TRUNCATED (local-potential-approximation, LPA)
threshold flow is CONSTRUCTIBLE and GENERATES a bounded nonzero IR mass that FREEZES at
the decoupling scale (dimensional transmutation, machine-checked); the EXACT flow needs
the full non-perturbative `Γ_k''` (the interacting inverse propagator) = `singleStep`.

# The obligation (read first)

The effective average action `Γ_k` obeys the EXACT Wetterich flow equation

    ∂_t Γ_k = (1/2) · Tr[ (Γ_k'' + R_k)^{-1} · ∂_t R_k ] ,      t = log k ,

with `R_k` the IR regulator.  The mass gap is the mass term `m²_k` in the IR action
`Γ_{k=0}`.  Perturbatively the theory is massless (`m²_Λ = 0`); the flow is meant to
GENERATE `m²_{k=0} > 0` non-perturbatively.

Project the Wetterich equation onto the mass term.  In the LPA (truncating `Γ_k` to a
local potential) the flow of the dimensionless mass `u_k = m²_k / k²` reads

    ∂_t u_k = 2·u_k − c·g²_k·ℓ(u_k) ,                                    (LPA mass flow)

where `ℓ(u)` is a THRESHOLD FUNCTION: it is `O(1)` while the mode is active (`u < 1`,
i.e. `m² < k²`) and DECOUPLES — `ℓ → 0` — once the mode is heavy (`u > 1`, `m² > k²`).
The threshold is the crux: when `m²_k > k²` the mode decouples and the flow STOPS — the
mass FREEZES at the scale where `m² ~ k²` (dimensional transmutation).  The frozen value
`m²_{k=0}` is the dynamical mass.

The integrated (physical) form.  Blocking `k_n = Λ·b^{-n}` (n=0 UV, n→∞ IR), the physical
mass² `M²_n` accumulates the per-shell source gated by the decoupling threshold:

    M²_0 = 0            (m²_Λ = 0, perturbatively massless UV)
    M²_{n+1} = M²_n + s_n · Θ(M²_n , k²_n) ,     Θ = 1 if M²_n < k²_n else 0 ,   (`wetterichFlow`)

with `s_n = c·g²_n·(threshold prefactor)` the mass GENERATED at shell `n` (the Wetterich
RHS projected on the mass term) and `Θ` the SHARP decoupling threshold (the mode's source
switches OFF once `M² ≥ k²`).  Since `M²_n` accumulates while `k²_n → 0`, the dimensionless
`u_n = M²_n/k²_n` eventually exceeds `1` and the flow FREEZES: the frozen `M²` is the gap.

# What is genuinely new here (beyond `EffectiveActionMassFlow.massFlow`)

`massFlow` is a LINEAR always-on recursion.  The Wetterich flow adds the DECOUPLING /
FREEZING threshold `Θ` — the physical mechanism of dimensional transmutation.  Proved,
axiom-clean, for the TRUNCATED (LPA) flow with a given condensate source:

  * **PERTURBATIVE MASSLESSNESS** — with `s ≡ 0` the flow keeps `M² = 0` at every scale
    (`wetterichFlow_perturbatively_massless`): the theory is massless in perturbation theory.
  * **GENERATION** — a nonzero active source generates a STRICTLY POSITIVE mass
    (`wetterichFlow_massGenerated`), monotone-accumulated (`wetterichFlow_mono`).
  * **FREEZING (the new decoupling theorem)** — once the mode is decoupled (`k²_n ≤ M²_n`)
    the threshold shuts the source off and the mass is FROZEN: `M²_{n+1} ≃ M²_n`
    (`wetterichFlow_freezes`).  This is the Wetterich threshold, absent from the linear flow.
  * **DIMENSIONAL TRANSMUTATION (concrete)** — for the model condensate source the flow
    REACHES decoupling at a finite scale (`n = 4`, `k²_4 = 1/256 ≤` the mass floor `1/100`)
    and freezes (`wetterichFlow_decoupling_reached`, `wetterichFlow_frozen_at_decoupling`).
  * **BOUNDED frozen mass** — `M²_n ≤ srcSum = 1/70` at every scale
    (`wetterichFlow_massBounded`), so the frozen mass sits in `(0, 1/70]`.

# THE DECISIVE CHECK (maximally adversarial) — truncated model vs exact `Γ_k''`

The Wetterich flow is EXACT.  But its RHS is `(Γ_k'' + R_k)^{-1}` — the FULL, field-dependent,
NON-PERTURBATIVE inverse propagator `Γ_k''` (the curvature of the exact effective action).
The TRUNCATED (LPA) flow above replaces `Γ_k''` by the local truncation and takes the source
`s_n` as GIVEN data (the model condensate) — exactly as `massFlow` takes its source as given.
So the truncated threshold flow is a MODEL that generates and freezes a mass; it does NOT
establish that the REAL 4D flow's exact `Γ_k''` produces the nonzero condensate source.  The
EXACT flow's non-perturbative `Γ_k''` IS the interacting inverse propagator = the interacting
measure = `singleStep`.

Encoded (def-alias, UNINHABITED, NOT one of the 5 guarded types):
`ExactWetterichVertex := SingleStepDefectReduction.SingleStepDefectBound`.

So the functional-RG mass-term flow ISOLATES the exact `Γ_k''` = `singleStep`, PLUS the
genuinely new machine-checked threshold/decoupling flow and its freezing / dimensional-
transmutation theorems.  No guarded frontier bundle is inhabited; nothing is faked; the 4D
Yang–Mills mass gap remains OPEN.

# Numerics (verified `/tmp/wett_verify.py`, sympy exact + mpmath dps 50)

  * discrete threshold flow: `M² : 0 → 1/100 → 13/1000 → 139/10000 → 1417/100000`, then
    FROZEN from `n=4` (source off); frozen `M² = 1417/100000 ∈ (0, 1/70]`;
  * `k²_n = (1/4)^n`; decoupling (`k²_n ≤` floor `1/100`) first at `n=4` (`k²_4 = 1/256`);
  * `srcSum = srcHead/(1−srcRate) = (1/100)/(7/10) = 1/70`, recurrence exact;
  * the LPA ODE with a FIXED perturbative `g²` has `RHS(u=0) = −c·g² < 0` — it does NOT
    generate a mass by itself; the generating source must be the non-perturbative condensate
    = `Γ_k''` = `singleStep` (confirms the isolation, no overclaim).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` + a decidable `Q'` threshold `if`, the `finSum`/geometric-tail backbone
(`RationalTail.geometric_tail_closure`), and the named residual
`SingleStepDefectReduction.SingleStepDefectBound`.  Every load-bearing declaration is gated
with `#print axioms`; permitted output `propext` / `Quot.sound` only (or empty).  No
`Classical.*`, no `native_decide` (only `decide` on closed decidable `Q'` facts), no `ring`,
no `sorry`.  All witnesses `Type`-level.  No frontier bundle inhabited.
-/
import YMGap.Continuum.CondensateGeometricErosion
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.WetterichMassFlow

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum

/-! ## 0. Local `Q'` order / algebra glue (self-contained `Int`-order arithmetic). -/

/-- `a < b ≤ c ⟹ a < c` (local copy, pattern of `AFExpLift.lt_of_lt_of_le`). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.le_of_lt a.den_pos : (0 : Int) ≤ (a.den : Int))
    have hr : (b.num * (c.den : Int)) * (a.den : Int)
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    have hr2 : (c.num * (b.den : Int)) * (a.den : Int)
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [hr, hr2] at this; exact this
  have s3 : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right s3
    (by exact_mod_cast Nat.le_of_lt b.den_pos : (0 : Int) ≤ (b.den : Int))

/-- `¬ (a < a)` on `Q'` (strict order is irreflexive). -/
theorem lt_irrefl' (a : Q') : ¬ (a < a) := by
  intro h
  have : a.num * (a.den : Int) < a.num * (a.den : Int) := h
  exact absurd this (Int.lt_irrefl _)

/-- `a ≤ b ⟹ ¬ (b < a)` — the total-order "not-below" used to switch OFF the threshold
once the mode is decoupled. -/
theorem not_lt_of_le {a b : Q'} (h : a ≤ b) : ¬ (b < a) := by
  intro hlt
  exact lt_irrefl' b (lt_of_lt_of_le hlt h)

/-- `0 ≤ a`, `0 ≤ b ⟹ 0 ≤ a + b` (local copy of `JTPInstance.add_nonneg'`). -/
theorem add_nonneg' {a b : Q'} (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b :=
  Q'.le_trans' _ _ _ ha (Q'.add_le_self_of_nonneg a b hb)

/-! ## 1. THE RG SCALE `k²_n` AND THE SHARP DECOUPLING THRESHOLD `Θ`.

The blocking `k_n = Λ·b^{-n}` (`b = 2`, `Λ = 1`) gives the cutoff-squared `k²_n = (1/4)^n`,
a strictly decreasing scale reaching `0` in the IR.  The dimensionless mass is
`u_n = M²_n / k²_n`; the mode is DECOUPLED once `u_n ≥ 1`, i.e. `M²_n ≥ k²_n`. -/

/-- The reciprocal squared block factor `1/b² = 1/4` (block factor `b = 2`). -/
def invBSq : Q' := Q'.mkPos 1 4 (by decide)

/-- **THE RG CUTOFF-SQUARED SCALE** `k²_n = (1/b²)^n = (1/4)^n` — the running momentum
scale squared, strictly decreasing to `0` in the IR (against which the mass is measured;
`u_n = M²_n / k²_n`, the mode decouples once `M²_n ≥ k²_n`). -/
def kSq : Nat → Q'
  | 0 => 1
  | n + 1 => invBSq * kSq n

@[simp] theorem kSq_zero : kSq 0 = 1 := rfl
@[simp] theorem kSq_succ (n : Nat) : kSq (n + 1) = invBSq * kSq n := rfl

/-- **THE SHARP DECOUPLING THRESHOLD** `Θ(M², k²) = 1` while the mode is ACTIVE (`M² < k²`,
`u < 1`) and `= 0` once it is DECOUPLED (`M² ≥ k²`, `u ≥ 1`).  This is the Wetterich threshold
function projected to the sharp (step) limit: the shell's source switches OFF at decoupling —
the mechanism that FREEZES the mass. -/
def activeFac (Msq kSq : Q') : Q' := if Msq < kSq then (1 : Q') else (0 : Q')

/-- The threshold is `1` on the active side (`M² < k²`). -/
theorem activeFac_active {Msq kSq : Q'} (h : Msq < kSq) : activeFac Msq kSq = 1 := by
  unfold activeFac; exact if_pos h

/-- The threshold is `0` on the decoupled side (`¬ M² < k²`, i.e. `k² ≤ M²`) — the source
switches off. -/
theorem activeFac_decoupled {Msq kSq : Q'} (h : ¬ Msq < kSq) : activeFac Msq kSq = 0 := by
  unfold activeFac; exact if_neg h

/-- The threshold is nonnegative. -/
theorem activeFac_nonneg (Msq kSq : Q') : (0 : Q') ≤ activeFac Msq kSq := by
  unfold activeFac
  by_cases h : Msq < kSq
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

/-- The threshold is at most `1` (it never amplifies). -/
theorem activeFac_le_one (Msq kSq : Q') : activeFac Msq kSq ≤ 1 := by
  unfold activeFac
  by_cases h : Msq < kSq
  · rw [if_pos h]; exact Q'.le_refl' 1
  · rw [if_neg h]; decide

/-! ## 2. THE WETTERICH LPA MASS-TERM FLOW `M²_{n+1} = M²_n + s_n·Θ(M²_n, k²_n)`.

The physical mass² accumulates the per-shell Wetterich source `s_n` GATED by the decoupling
threshold `Θ`.  Once the mode decouples the threshold zeroes the source — the FREEZING that
distinguishes the Wetterich flow from a linear recursion. -/

/-- **THE WETTERICH (LPA) MASS-TERM FLOW.**  `M²_0 = 0` (perturbatively massless UV);
`M²_{n+1} = M²_n + s_n · Θ(M²_n, k²_n)`.  The block-spin flow of the effective action's
mass term, with the sharp decoupling threshold `Θ = activeFac`. -/
def wetterichFlow (s : Nat → Q') : Nat → Q'
  | 0 => 0
  | n + 1 => wetterichFlow s n + s n * activeFac (wetterichFlow s n) (kSq n)

@[simp] theorem wetterichFlow_zero (s : Nat → Q') : wetterichFlow s 0 = 0 := rfl

@[simp] theorem wetterichFlow_succ (s : Nat → Q') (n : Nat) :
    wetterichFlow s (n + 1)
      = wetterichFlow s n + s n * activeFac (wetterichFlow s n) (kSq n) := rfl

/-- **The flow is nonnegative** given a nonnegative source (the mass stays a bona-fide
nonnegative parameter). -/
theorem wetterichFlow_nonneg {s : Nat → Q'} (hs : ∀ n, (0 : Q') ≤ s n) :
    ∀ n, (0 : Q') ≤ wetterichFlow s n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
    show (0 : Q') ≤ wetterichFlow s n + s n * activeFac (wetterichFlow s n) (kSq n)
    exact add_nonneg' (wetterichFlow_nonneg hs n)
      (Q'.mul_nonneg _ _ (hs n) (activeFac_nonneg _ _))

/-- **PERTURBATIVE MASSLESSNESS.**  With the perturbative source `s ≡ 0` (the beta function
renormalizes `g²` but generates NO mass term) and a massless UV boundary, `M²_n ≃ 0` at every
scale — the theory is massless in perturbation theory, MACHINE-CHECKED. -/
theorem wetterichFlow_perturbatively_massless (k : Nat) :
    (wetterichFlow (fun _ => (0 : Q')) k).eqv 0 := by
  induction k with
  | zero => exact Q'.eqv_refl 0
  | succ n ih =>
    show (wetterichFlow (fun _ => (0 : Q')) n
        + (0 : Q') * activeFac (wetterichFlow (fun _ => (0 : Q')) n) (kSq n)).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ 0 _ ih) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
    exact QPoly.q_zero_mul _

/-- **ONE STEP IS NONDECREASING** (nonneg source): `M²_n ≤ M²_{n+1}`. -/
theorem wetterichFlow_mono_step {s : Nat → Q'} (hs : ∀ n, (0 : Q') ≤ s n) (n : Nat) :
    wetterichFlow s n ≤ wetterichFlow s (n + 1) := by
  show wetterichFlow s n
      ≤ wetterichFlow s n + s n * activeFac (wetterichFlow s n) (kSq n)
  exact Q'.add_le_self_of_nonneg _ _
    (Q'.mul_nonneg _ _ (hs n) (activeFac_nonneg _ _))

/-- **THE FLOW IS MONOTONE (nondecreasing) in the scale**: `M²_n ≤ M²_{n+k}` for every
offset `k`.  A generated mass is never lost at a later scale. -/
theorem wetterichFlow_mono {s : Nat → Q'} (hs : ∀ n, (0 : Q') ≤ s n) :
    ∀ (n k : Nat), wetterichFlow s n ≤ wetterichFlow s (n + k)
  | n, 0 => Q'.le_refl' _
  | n, k + 1 => by
    have hstep : wetterichFlow s (n + k) ≤ wetterichFlow s (n + k + 1) :=
      wetterichFlow_mono_step hs (n + k)
    exact Q'.le_trans' _ _ _ (wetterichFlow_mono hs n k) hstep

/-! ## 3. THE FREEZING THEOREM — the decoupling threshold STOPS the flow.

The genuinely new Wetterich piece: once the mode decouples (`k²_n ≤ M²_n`) the threshold
zeroes the shell source and the mass is FROZEN, `M²_{n+1} ≃ M²_n`.  This is the freezing of
the running mass at the scale `m² ~ k²` — dimensional transmutation. -/

/-- **THE FREEZING THEOREM.**  If at scale `n` the mode is DECOUPLED (`k²_n ≤ M²_n`, i.e.
`u_n ≥ 1`), the threshold switches the source off and the mass is FROZEN:
`M²_{n+1} ≃ M²_n`.  The Wetterich flow STOPS at decoupling — the mechanism absent from a
linear (always-on) flow. -/
theorem wetterichFlow_freezes {s : Nat → Q'} (n : Nat)
    (hdec : kSq n ≤ wetterichFlow s n) :
    (wetterichFlow s (n + 1)).eqv (wetterichFlow s n) := by
  show (wetterichFlow s n + s n * activeFac (wetterichFlow s n) (kSq n)).eqv
      (wetterichFlow s n)
  rw [activeFac_decoupled (not_lt_of_le hdec)]
  -- goal: (M + s n * 0).eqv M
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (wetterichFlow s n) (s n * 0) 0 (Q'.mul_zero_eqv (s n))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (wetterichFlow s n))

/-! ## 4. THE MODEL CONDENSATE SOURCE — geometric shell source, summable.

The Wetterich shell source `s_n = c·g²_n·(threshold prefactor)` is modelled by the
non-perturbative condensate `ε_n = exp(−c/β₀g²_n)` (per shell), a geometric
`s_n = srcHead·srcRate^n = (1/100)(3/10)^n` with closed geometric budget `srcSum = 1/70`. -/

/-- Condensate shell-source head `srcHead = 1/100` (the mass floor generated at the first
active shell). -/
def srcHead : Q' := Q'.mkPos 1 100 (by decide)

/-- Condensate shell-source geometric ratio `srcRate = 3/10`. -/
def srcRate : Q' := Q'.mkPos 3 10 (by decide)

/-- Closed geometric budget `srcSum = srcHead/(1−srcRate) = (1/100)/(7/10) = 1/70`. -/
def srcSum : Q' := Q'.mkPos 1 70 (by decide)

/-- **THE CONDENSATE SHELL SOURCE** `s_n = srcHead·srcRate^n = (1/100)(3/10)^n` — the
non-perturbative mass generated per momentum shell (the Wetterich RHS projected on the mass
term, modelled by the condensate `exp(−c/β₀g²)`). -/
def wSource (n : Nat) : Q' := srcHead * srcRate ^ n

theorem wSource_nonneg (n : Nat) : (0 : Q') ≤ wSource n :=
  Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg srcRate (by decide) n)

/-! ## 5. GENERATION + BOUNDED FROZEN MASS (dimensional transmutation). -/

/-- The gated shell contribution never exceeds the raw source (threshold `≤ 1`):
`s_n · Θ ≤ s_n`. -/
theorem gated_le_source {s : Nat → Q'} (hs : ∀ n, (0 : Q') ≤ s n) (n : Nat) :
    s n * activeFac (wetterichFlow s n) (kSq n) ≤ s n := by
  have h1 : s n * activeFac (wetterichFlow s n) (kSq n) ≤ s n * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (activeFac_le_one _ _) (hs n)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_one_eqv (s n)))

/-- **THE FLOW IS DOMINATED BY THE UNGATED SUM**: `M²_n ≤ Σ_{j<n} s_j`.  The threshold only
suppresses; it never adds.  Lets the geometric budget bound the frozen mass. -/
theorem wetterichFlow_le_finSum {s : Nat → Q'} (hs : ∀ n, (0 : Q') ≤ s n) :
    ∀ n, wetterichFlow s n ≤ finSum s n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
    show wetterichFlow s n + s n * activeFac (wetterichFlow s n) (kSq n)
        ≤ finSum s n + s n
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ (wetterichFlow_le_finSum hs n))
      (Q'.add_le_add_left _ _ _ (gated_le_source hs n))

/-- The geometric one-step recurrence `srcHead + srcRate·srcSum ≤ srcSum`
(`1/100 + (3/10)(1/70) = 1/70`, kernel `decide`). -/
theorem src_recurrence : srcHead + srcRate * srcSum ≤ srcSum := by decide

/-- **THE FROZEN MASS IS BOUNDED — DIMENSIONAL TRANSMUTATION CEILING.**  The Wetterich flow
with the condensate source is uniformly bounded by the geometric budget:
`M²_n ≤ srcSum = 1/70` at every scale.  Reuses the PROVED
`RationalTail.geometric_tail_closure`. -/
theorem wetterichFlow_massBounded (n : Nat) :
    wetterichFlow wSource n ≤ srcSum := by
  refine Q'.le_trans' _ _ _ (wetterichFlow_le_finSum wSource_nonneg n) ?_
  show finSum (fun j => srcHead * srcRate ^ j) n ≤ srcSum
  exact geometric_tail_closure srcHead srcRate srcSum (by decide) (by decide)
    src_recurrence n

/-- The first shell is ACTIVE (`M²_0 = 0 < k²_0 = 1`) and generates the mass floor:
`M²_1 = srcHead·1`.  Hence `srcHead ≤ M²_1`. -/
theorem srcHead_le_flow_one : srcHead ≤ wetterichFlow wSource 1 := by
  have hval : wetterichFlow wSource 1
      = 0 + wSource 0 * activeFac (0 : Q') (kSq 0) := rfl
  rw [hval, activeFac_active (show (0 : Q') < kSq 0 by decide), Q'.zero_add']
  -- srcHead ≤ wSource 0 * 1 ;  wSource 0 = srcHead·srcRate^0
  refine Q'.le_trans' _ _ _ (show srcHead ≤ wSource 0 by decide) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv (wSource 0)))

/-- **THE MASS IS GENERATED — STRICTLY POSITIVE (∀ n ≥ 1).**  From the massless UV boundary
the condensate source generates a STRICTLY POSITIVE mass at every scale `n ≥ 1`:
`0 < M²_{n+1}`.  Perturbatively `M² ≡ 0`; the condensate source gives `M² > 0`. -/
theorem wetterichFlow_massGenerated (n : Nat) :
    (0 : Q') < wetterichFlow wSource (n + 1) := by
  have h1 : (0 : Q') < srcHead := by decide
  have h2 : srcHead ≤ wetterichFlow wSource (1 + n) :=
    Q'.le_trans' _ _ _ srcHead_le_flow_one (wetterichFlow_mono wSource_nonneg 1 n)
  have h3 : (1 + n) = (n + 1) := Nat.add_comm 1 n
  rw [h3] at h2
  exact lt_of_lt_of_le h1 h2

/-! ## 6. DIMENSIONAL TRANSMUTATION — decoupling is REACHED, the mass FREEZES.

For the model condensate source the dimensionless mass `u_n = M²_n/k²_n` reaches `1` at a
FINITE scale: `k²_4 = 1/256 ≤` the mass floor `1/100 ≤ M²_4`, so the mode decouples and the
flow FREEZES.  This is the concrete dimensional transmutation — a nonzero mass generated in
the UV-active shells, then frozen once `m² ~ k²`. -/

/-- **DECOUPLING IS REACHED at `n = 4`.**  `k²_4 = 1/256 ≤ M²_4`: the dimensionless mass
`u_4 = M²_4/k²_4 ≥ 1`, so the mode is decoupled.  (The mass floor `srcHead = 1/100` generated
at the first shell already exceeds `k²_4 = 1/256`, and the flow is monotone.) -/
theorem wetterichFlow_decoupling_reached :
    kSq 4 ≤ wetterichFlow wSource 4 := by
  have hk : kSq 4 ≤ srcHead := by decide
  have hM : srcHead ≤ wetterichFlow wSource 4 :=
    Q'.le_trans' _ _ _ srcHead_le_flow_one (wetterichFlow_mono wSource_nonneg 1 3)
  exact Q'.le_trans' _ _ _ hk hM

/-- **THE MASS FREEZES AT THE DECOUPLING SCALE** (`n = 4`): once decoupled, the Wetterich
threshold shuts the source off and `M²_5 ≃ M²_4`.  Combined with monotonicity, the mass is
FROZEN from the transmutation scale onward — the dynamical (IR) mass.  Genuine dimensional
transmutation, machine-checked for the model condensate source. -/
theorem wetterichFlow_frozen_at_decoupling :
    (wetterichFlow wSource 5).eqv (wetterichFlow wSource 4) :=
  wetterichFlow_freezes 4 wetterichFlow_decoupling_reached

/-! ## 7. THE ISOLATION — the exact `Γ_k''` = the interacting inverse propagator = `singleStep`. -/

/-- **THE EXACT WETTERICH VERTEX `Γ_k''` = `singleStep` (named residual, NOT faked).**  The
Wetterich flow is EXACT, but its RHS `(Γ_k'' + R_k)^{-1}` requires the FULL non-perturbative
inverse propagator `Γ_k''` — the curvature of the exact effective action, the interacting
measure.  The TRUNCATED (LPA) flow above replaces `Γ_k''` by the local truncation and takes
the mass source as GIVEN data (the model condensate), exactly as `EffectiveActionMassFlow`
takes its source as given.  The real 4D flow's exact `Γ_k''` producing the nonzero condensate
source is the spacing-uniform gap survival
`SingleStepDefectReduction.SingleStepDefectBound.singleStep` (the renormalon).  Restated as a
`Type`-alias; UNINHABITED (it IS the real RG estimate).  A flow built with an ASSUMED real
`Γ_k''` (a nonzero source floor) would be the Rule-9 fake — deliberately not written.
(Identification at the level of the SAME irreducible core across confirmations, not an `rfl`
between the distinct structures.) -/
def ExactWetterichVertex : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual (Rule 9.8, proof not prose). -/
theorem exactWetterichVertex_eq :
    ExactWetterichVertex = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-! ## 8. The assembled verdict (informational bundle — inhabits NO frontier type). -/

/-- A record of the machine-checked facts of the Wetterich mass-flow assessment.  NOT a
frontier bundle: every field is a genuine PROVED theorem, and it inhabits neither
`SingleStepDefectBound` nor any guarded Clay-frontier type.  It certifies: the perturbative
flow keeps `M² = 0`; the condensate source generates a strictly positive mass; the mass is
uniformly bounded (transmutation ceiling); decoupling is reached at a finite scale; and the
mass FREEZES at decoupling (the Wetterich threshold). -/
structure WetterichVerdict : Type where
  /-- §2 — the perturbative flow keeps the mass identically `0`. -/
  perturbativelyMassless : ∀ k, (wetterichFlow (fun _ => (0 : Q')) k).eqv 0
  /-- §5 — the condensate source generates a strictly positive mass (∀ n ≥ 1). -/
  massGenerated : ∀ n, (0 : Q') < wetterichFlow wSource (n + 1)
  /-- §5 — the generated mass is uniformly bounded (dimensional transmutation). -/
  massBounded : ∀ n, wetterichFlow wSource n ≤ srcSum
  /-- §6 — decoupling is reached at a finite scale (`u_4 ≥ 1`). -/
  decouplingReached : kSq 4 ≤ wetterichFlow wSource 4
  /-- §3/§6 — the mass FREEZES at the decoupling scale (the Wetterich threshold). -/
  massFreezes : (wetterichFlow wSource 5).eqv (wetterichFlow wSource 4)

/-- **The verdict is inhabited by PROVED facts only.**  Every field is a genuine theorem;
NONE inhabits a frontier bundle.  This certifies the honest conclusion: the truncated (LPA)
Wetterich threshold flow generates + freezes a bounded nonzero mass FROM the model condensate
source (dimensional transmutation), and the exact `Γ_k'' = singleStep` remains the residual. -/
def wetterich_verdict : WetterichVerdict where
  perturbativelyMassless := wetterichFlow_perturbatively_massless
  massGenerated := wetterichFlow_massGenerated
  massBounded := wetterichFlow_massBounded
  decouplingReached := wetterichFlow_decoupling_reached
  massFreezes := wetterichFlow_frozen_at_decoupling

/-! ## 9. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT.**

The Wetterich (functional-RG) mass-term flow with the THRESHOLD / DECOUPLING structure is
BUILT.  **CONSTRUCTED (the genuine new pieces):**
  * the Wetterich LPA mass flow `M²_{n+1} = M²_n + s_n·Θ(M²_n,k²_n)` (`wetterichFlow`) with
    the sharp decoupling threshold `Θ` (`activeFac`) — absent from the linear `massFlow`;
  * **PERTURBATIVE MASSLESSNESS** — `s ≡ 0` keeps `M² = 0`
    (`wetterichFlow_perturbatively_massless`): massless in perturbation theory, machine-checked;
  * **GENERATION** — the condensate source generates a strictly positive mass
    (`wetterichFlow_massGenerated`), monotone-accumulated (`wetterichFlow_mono`), bounded by
    `srcSum = 1/70` (`wetterichFlow_massBounded`);
  * **FREEZING (the Wetterich threshold theorem)** — once decoupled (`k²_n ≤ M²_n`) the source
    switches off and `M²_{n+1} ≃ M²_n` (`wetterichFlow_freezes`);
  * **DIMENSIONAL TRANSMUTATION (concrete)** — decoupling is reached at `n = 4`
    (`wetterichFlow_decoupling_reached`) and the mass freezes
    (`wetterichFlow_frozen_at_decoupling`): the frozen mass sits in `(0, 1/70]`.

**RESIDUAL (NOT closed) — the exact flow requires the non-perturbative `Γ_k''`:** the truncated
(LPA) flow uses the LOCAL truncation and takes the mass source as GIVEN data (the model
condensate).  The EXACT Wetterich RHS `(Γ_k'' + R_k)^{-1}` requires the FULL non-perturbative
inverse propagator `Γ_k''` = the interacting measure = `ExactWetterichVertex =
SingleStepDefectBound.singleStep` (UNINHABITED).  So the functional RG does NOT generate the
gap constructively for the real theory — the TRUNCATED threshold flow is a MODEL that generates
+ freezes a mass (dimensional transmutation), and the EXACT flow ISOLATES `Γ_k'' = singleStep`.
This is a further confirmation of the SAME irreducible core, in functional-RG-flow form, PLUS
the genuinely new machine-checked threshold/decoupling flow and its freezing theorem.  No
guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN. -/
theorem wetterichMassFlow_honesty : True := trivial

end YMGap.Continuum.WetterichMassFlow

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WetterichMassFlow.activeFac_nonneg
#print axioms YMGap.Continuum.WetterichMassFlow.activeFac_le_one
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_nonneg
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_perturbatively_massless
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_mono
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_freezes
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_le_finSum
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_massBounded
#print axioms YMGap.Continuum.WetterichMassFlow.srcHead_le_flow_one
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_massGenerated
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_decoupling_reached
#print axioms YMGap.Continuum.WetterichMassFlow.wetterichFlow_frozen_at_decoupling
#print axioms YMGap.Continuum.WetterichMassFlow.exactWetterichVertex_eq
#print axioms YMGap.Continuum.WetterichMassFlow.wetterich_verdict
