/-
Track B / R2 — **CODYNAMIC RECAST of dimensional transmutation: the static,
gameable per-scale rate-match is REPLACED by the RG flow law + a conserved-margin
(summable-budget) invariant.**

# Why this module exists (read first)

`CodynamicHierarchical.DimensionalTransmutation` named the asymptotic-freedom
rate-matching as a single *static* per-scale inequality

    physFloor · aScaling N ≤ (1 − sep N) · ∏_{k<N} ρ_dec(sep k).

That inequality is **one-sided** and compares quantities scale-by-scale in a
fixed reference frame: it asks the rules at scale `N` to certify the gap, with no
constraint linking scale `k` to scale `k+1`.  It is therefore **gameable** — a
rational separator flow that merely *drifts* toward `1` (monotone, `sep → 1`)
keeps the margin large and slips through, with NO genuine renormalization-group
content.  This is a static-reference-frame error: trying to apply the rules of
one scale to another statically will not certify a continuum gap (the same
methodological trap as expecting a single-scale a-priori bound to settle a
multi-scale cascade).

The genuine content is **codynamic** — a statement about the whole RG trajectory:

  * **(i) the flow law (self-similarity).**  One decimation block step of factor
    `b+1` collapses `b+1` links in series, raising the separator to the `(b+1)`-th
    power.  Going one step toward the UV is the inverse:

        sep k ≃ (sep (k+1))^(b+1)      (`selfSimilar`).

    Its unique solution is the `(b+1)`-th-root flow `sep k = sep₀^{1/(b+1)^k}`,
    which is IRRATIONAL — no rational flow satisfies it (`polyFlow` fails it by a
    decidable check, §3).  This is exactly the constraint the static inequality
    dropped, and it is exactly where constructive reals (`CReal`) become
    load-bearing.

  * **(ii) the summable budget (conserved rescaled margin).**  Under the flow law
    the geometrically-rescaled margin is a **flow invariant**:

        (1 − sep N) · ∏_{j=1}^{N} geomSum(sep j, b+1) ≃ 1 − sep₀     (`marginInvariant`).

    Since `geomSum(·, b+1) = (b+1)·ρ_dec`, this says the margin shrinks at exactly
    the geometric spacing rate `(b+1)^{-N}` so that the decimation product
    `∏ρ_dec` converges to a STRICTLY POSITIVE limit — the asymptotic-freedom
    rate-match in integrated/codynamic form.  The physical floor
    `physFloor = (1 − sep₀)·ρ_dec₀ / a₀` EMERGES from the invariant rather than
    being a free, defended constant; positivity is `marginBudget_pos`.

# What is PROVED here (honest)

  * `marginInvariant` — the conserved-rescaled-margin telescoping identity,
    derived from `oneSub_pow_factor` + the flow law.  This is the codynamic
    "summable budget" made exact.
  * `marginBudget_pos` — the rescaled margin stays strictly positive at every
    scale (the budget is bounded below away from `0`), GIVEN `sep₀ < 1`.
  * `polyFlow_to_one`, `polyFlow_mono` — the rational "gaming" flow passes the OLD
    soft hardening guards (`sep → 1`, monotone), yet
  * `polyFlow_not_selfSimilar` — it provably FAILS the flow law (a decidable
    rational check at `k = 0`).  This is the falsification-first confirmation that
    the recast carrier is NOT gameable: the field that closes the hole is the flow
    law, and the static guards alone never sufficed.

# SCOPE — what is NOT claimed

The flow law has NO rational inhabitant (`(b+1)`-th roots are irrational), so this
module makes NO physical-gap claim at the `Q'` level — honestly, it says "a
genuine inhabitant must live in `CReal`."  The conditional theorems here ("IF
self-similar THEN the budget is conserved/positive") hold unconditionally; the
genuine inhabitant (the `(b+1)`-th-root flow built from `CReal.exp`/`CReal.log`)
is constructed downstream.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over `Q'` / `Nat`; every load-bearing declaration gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`.  All data is `Type`-level.
-/

import YMGap.Continuum.CodynamicHierarchical
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.CubeRatioBounds

namespace YMGap.Continuum.CodynamicTransmutation

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CodynamicHierarchical

/-! ## 1. The codynamic flow law and the conserved-margin invariant -/

/-- **The RG flow law (self-similarity).**  One decimation block step of factor
`b+1` raises the separator to the `(b+1)`-th power; the inverse (one step toward
the UV) is `sep k ≃ (sep (k+1))^(b+1)`.  Its unique solution is the
`(b+1)`-th-root flow `sep k = sep₀^{1/(b+1)^k}`, which is irrational — so this
predicate has NO non-trivial rational inhabitant.  It is precisely the codynamic
content the static `rate_matched` inequality dropped. -/
def selfSimilar (b : Nat) (sep : Nat → Q') : Prop :=
  ∀ k, (sep k).eqv (qpow (sep (k + 1)) (b + 1))

/-- The geometric-sum product tail `∏_{j=1}^{N} geomSum(sep j, b+1)` — the
accumulated `(b+1)·ρ_dec` factors that rescale the margin along the flow.  Defined
so the top factor is added on the right (`tail (N+1) = tail N · geomSum(sep (N+1))`). -/
def marginProductTail (b : Nat) (sep : Nat → Q') : Nat → Q'
  | 0 => 1
  | N + 1 => marginProductTail b sep N * geomSum (sep (N + 1)) (b + 1)

@[simp] theorem marginProductTail_zero (b : Nat) (sep : Nat → Q') :
    marginProductTail b sep 0 = 1 := rfl

@[simp] theorem marginProductTail_succ (b : Nat) (sep : Nat → Q') (N : Nat) :
    marginProductTail b sep (N + 1)
      = marginProductTail b sep N * geomSum (sep (N + 1)) (b + 1) := rfl

/-- `(1 − a) ≃ (1 − b)` from `a ≃ b` (one-minus congruence). -/
theorem oneSub_eqv_congr {a b : Q'} (h : a.eqv b) :
    ((1 : Q') - a).eqv ((1 : Q') - b) := by
  show ((1 : Q') + (-a)).eqv ((1 : Q') + (-b))
  exact Q'.add_eqv_congr_left 1 (-a) (-b) (Q'.neg_eqv_congr a b h)

/-- **The per-step margin recurrence (the engine of the telescoping).**  Under the
flow law, `1 − sep k ≃ (1 − sep (k+1)) · geomSum(sep (k+1), b+1)`: one block step
multiplies the dimensionless margin by the geometric-sum factor `(b+1)·ρ_dec`.
Combines `oneSub_pow_factor` (the exact finite-geometric factorization) with
`selfSimilar`. -/
theorem margin_step {b : Nat} {sep : Nat → Q'} (hss : selfSimilar b sep) (k : Nat) :
    ((1 : Q') - sep k).eqv
      (((1 : Q') - sep (k + 1)) * geomSum (sep (k + 1)) (b + 1)) := by
  -- 1 − sep k ≃ 1 − (sep (k+1))^(b+1) ≃ (1 − sep (k+1))·geomSum(sep (k+1), b+1)
  refine Q'.eqv_trans _ _ _ (oneSub_eqv_congr (hss k)) ?_
  exact oneSub_pow_factor (sep (k + 1)) (b + 1)

/-- `x · (y · z) ≃ (x · z) · y` (the swap used to peel the top geomSum factor off
`marginProductTail` and pair it with the leading margin). -/
theorem mul_swap_right (x y z : Q') : (x * (y * z)).eqv ((x * z) * y) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x (y * z) (z * y) (Q'.mul_comm_eqv y z)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv x z y)

/-- **THE CONSERVED-MARGIN INVARIANT (the codynamic "summable budget").**  Under
the flow law the geometrically-rescaled margin is a flow invariant:

    (1 − sep N) · ∏_{j=1}^{N} geomSum(sep j, b+1) ≃ 1 − sep 0,

for every scale `N`.  Because `geomSum(·, b+1) = (b+1)·ρ_dec`, this is exactly the
statement that the margin `1 − sep N` shrinks at the geometric spacing rate
`(b+1)^{-N}` so the decimation product `∏ρ_dec` converges to a positive limit —
the asymptotic-freedom rate-match in integrated form.  A static one-sided
inequality cannot see this; the invariant makes "the margin tracks the spacing"
a THEOREM of the trajectory.  Proof: induction on `N` via `margin_step`. -/
theorem marginInvariant {b : Nat} {sep : Nat → Q'} (hss : selfSimilar b sep) :
    ∀ N, (((1 : Q') - sep N) * marginProductTail b sep N).eqv ((1 : Q') - sep 0)
  | 0 => by
      -- (1 − sep 0)·1 ≃ 1 − sep 0
      show (((1 : Q') - sep 0) * 1).eqv ((1 : Q') - sep 0)
      exact Q'.mul_one_eqv ((1 : Q') - sep 0)
  | N + 1 => by
      -- (1 − sep (N+1)) · (tail N · G) with G = geomSum(sep (N+1), b+1)
      show (((1 : Q') - sep (N + 1))
              * (marginProductTail b sep N * geomSum (sep (N + 1)) (b + 1))).eqv
            ((1 : Q') - sep 0)
      -- peel: x·(tail·G) ≃ (x·G)·tail
      refine Q'.eqv_trans _ _ _
        (mul_swap_right ((1 : Q') - sep (N + 1)) (marginProductTail b sep N)
          (geomSum (sep (N + 1)) (b + 1))) ?_
      -- (x·G) ≃ 1 − sep N  (per-step, reversed)
      have hstep : (((1 : Q') - sep (N + 1)) * geomSum (sep (N + 1)) (b + 1)).eqv
          ((1 : Q') - sep N) := Q'.eqv_symm (margin_step hss N)
      -- ((x·G)·tail) ≃ (1 − sep N)·tail ≃ 1 − sep 0
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (marginProductTail b sep N) hstep) ?_
      exact marginInvariant hss N

/-! ## 2. The emergent positive floor (budget bounded below) -/

/-- Each geometric-sum factor `geomSum(sep j, b+1)` is strictly positive for a
nonnegative separator (`b+1 ≥ 1`, so the sum has the leading `1` term). -/
theorem geomSum_factor_pos {b : Nat} {sep : Nat → Q'} (hnn : ∀ k, (0 : Q') ≤ sep k)
    (j : Nat) : (0 : Q') < geomSum (sep j) (b + 1) :=
  geomSum_succ_pos (hnn j) b

/-- The margin-product tail is strictly positive at every scale (a product of
strictly-positive geometric-sum factors; the empty product is `1`). -/
theorem marginProductTail_pos {b : Nat} {sep : Nat → Q'} (hnn : ∀ k, (0 : Q') ≤ sep k) :
    ∀ N, (0 : Q') < marginProductTail b sep N
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | N + 1 => by
      show (0 : Q') < marginProductTail b sep N * geomSum (sep (N + 1)) (b + 1)
      exact Q'.mul_pos (marginProductTail_pos hnn N) (geomSum_factor_pos hnn (N + 1))

/-- **THE BUDGET IS BOUNDED BELOW AWAY FROM ZERO.**  GIVEN `sep₀ < 1` (a genuine
UV margin to start), the rescaled margin `(1 − sep N)·∏geomSum` stays strictly
positive at every scale — it equals the fixed positive constant `1 − sep₀` by
`marginInvariant`.  Equivalently the per-scale margin `1 − sep N` is positive and
the emergent physical floor `physFloor = (1 − sep₀)·ρ_dec₀/a₀` is strictly
positive: the continuum gap survives the flow, not by a tuned inequality but
because the conserved budget never vanishes. -/
theorem marginBudget_pos {b : Nat} {sep : Nat → Q'} (hss : selfSimilar b sep)
    (h0 : sep 0 < (1 : Q')) (N : Nat) :
    (0 : Q') < ((1 : Q') - sep N) * marginProductTail b sep N :=
  YMGap.Continuum.CubeRatioBounds.pos_of_eqv_of_pos (marginInvariant hss N)
    (sub_pos_of_lt_one h0)

/-! ## 3. The falsification: the rational gaming flow FAILS the flow law

`polyFlow k = 1 − 1/(k+1) = k/(k+1)` is the canonical flow that GAMED the old
static `rate_matched`: it is monotone increasing and `sep → 1`, so it passes
every "soft" hardening guard (`sep_to_one`, `sep_mono`).  We confirm those two,
then show it provably VIOLATES the codynamic flow law `selfSimilar` — by a
DECIDABLE rational computation at `k = 0` (`sep₀ = 0 ≠ (1/2)^2 = (sep₁)^(b+1)`).
This is the falsification-first proof that the recast is non-gameable: the static
guards never sufficed, and the flow law is exactly the discriminator. -/

/-- The rational "gaming" separator flow `polyFlow k = 1 − 1/(k+1)`. -/
def polyFlow : Nat → Q' := fun k => 1 - Q'.invSucc k

/-- **`polyFlow` passes the old soft guard `sep → 1`.**  The margin
`1 − polyFlow k = 1/(k+1)` is driven below every `ε > 0` (take `K = ε.den`). -/
theorem polyFlow_to_one : ∀ ε : Q', (0 : Q') < ε →
    ∃ K : Nat, ∀ k : Nat, K ≤ k → (1 : Q') - polyFlow k ≤ ε := by
  intro ε hε
  refine ⟨ε.den, fun k hk => ?_⟩
  -- 1 − polyFlow k = 1 − (1 − invSucc k) ≃ invSucc k ≤ invSucc ε.den ≤ ε
  have hcollapse : ((1 : Q') - polyFlow k).eqv (Q'.invSucc k) := by
    show ((1 : Q') - (1 - Q'.invSucc k)).eqv (Q'.invSucc k)
    exact YMGap.Continuum.AFRateCalibration.one_sub_one_sub_eqv (Q'.invSucc k)
  have hk' : Q'.invSucc k ≤ Q'.invSucc ε.den := ExpNeg.invSucc_le_of_le hk
  have hden : Q'.invSucc ε.den ≤ ε := HalfPow.invSucc_den_le ε hε
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) (Q'.le_trans' _ _ _ hk' hden)

/-- **`polyFlow` passes the old soft guard monotone-toward-UV.**  `polyFlow` is
monotone increasing: `invSucc` is antitone, so `1 − invSucc k ≤ 1 − invSucc (k+1)`. -/
theorem polyFlow_mono (k : Nat) : polyFlow k ≤ polyFlow (k + 1) := by
  show (1 : Q') - Q'.invSucc k ≤ (1 : Q') - Q'.invSucc (k + 1)
  have hanti : Q'.invSucc (k + 1) ≤ Q'.invSucc k :=
    ExpNeg.invSucc_le_of_le (Nat.le_succ k)
  have hneg : (-(Q'.invSucc k)) ≤ -(Q'.invSucc (k + 1)) := Q'.neg_le_neg hanti
  show (1 : Q') + (-(Q'.invSucc k)) ≤ (1 : Q') + (-(Q'.invSucc (k + 1)))
  exact Q'.add_le_add_left (1 : Q') (-(Q'.invSucc k)) (-(Q'.invSucc (k + 1))) hneg

/-- **THE FALSIFICATION — `polyFlow` VIOLATES the codynamic flow law.**  Despite
passing both soft guards above, `polyFlow` does NOT satisfy `selfSimilar` (here
with block factor `b = 1`, i.e. `b+1 = 2`): at `k = 0`, `polyFlow 0 = 0` while
`(polyFlow 1)^2 = (1/2)^2 = 1/4 ≠ 0`.  A purely DECIDABLE rational computation.
So the rational gaming flow that slipped through the static `rate_matched` is
provably excluded by the flow law — the recast carrier is non-gameable. -/
theorem polyFlow_not_selfSimilar : ¬ selfSimilar 1 polyFlow := by
  intro h
  have h0 : (polyFlow 0).eqv (qpow (polyFlow 1) (1 + 1)) := h 0
  -- the concrete rational identity 0 ≃ 1/4 is decidably false
  have hfalse : ¬ (polyFlow 0).eqv (qpow (polyFlow 1) (1 + 1)) := by decide
  exact hfalse h0

end YMGap.Continuum.CodynamicTransmutation

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CodynamicTransmutation.oneSub_eqv_congr
#print axioms YMGap.Continuum.CodynamicTransmutation.margin_step
#print axioms YMGap.Continuum.CodynamicTransmutation.mul_swap_right
#print axioms YMGap.Continuum.CodynamicTransmutation.marginInvariant
#print axioms YMGap.Continuum.CodynamicTransmutation.marginProductTail_pos
#print axioms YMGap.Continuum.CodynamicTransmutation.marginBudget_pos
#print axioms YMGap.Continuum.CodynamicTransmutation.polyFlow_to_one
#print axioms YMGap.Continuum.CodynamicTransmutation.polyFlow_mono
#print axioms YMGap.Continuum.CodynamicTransmutation.polyFlow_not_selfSimilar
