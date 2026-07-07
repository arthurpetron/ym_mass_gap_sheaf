/-
Track B / R2 — the CLAY-CORE INPUT `AFBetaStep` DISCHARGED for the CONCRETE
canonical asymptotic-freedom trajectory.

# What this module closes

`EigenvalueShiftBound.AFBetaStep afr` is the named two-loop asymptotic-freedom
per-step input consumed by the CONCRETE producer
`eigenvalueShiftDefect_of_betaStep`.  It carries two obligations along the AF
coupling flow `w_k`:

    mono     : ∀ n, w_n ≤ w_{n+1}                              (flow ↑ toward 1)
    betaStep : ∀ n, w_{n+1} − w_n ≤ 2·(1 − w_n)²               (the two-loop β ≤ 2 rate)

The `mono` half was already PROVED for the canonical trajectory
(`afBetaStep_mono_canonical`).  This module proves the `betaStep` half for the
same trajectory and INHABITS `AFBetaStep afRateModulus_canonical` — a concrete,
non-vacuous witness.

# The concrete trajectory and the arithmetic (sympy / mpmath exact)

The canonical AF trajectory is `w_k = 1 − 1/(k+1) = k/(k+1)` (i.e.
`afRateModulus_canonical.w k = 1 − Q'.invSucc k`, so `1 − w_k = 1/(k+1)`).  Then

    w_{k+1} − w_k = 1/(k+1) − 1/(k+2) = 1/((k+1)(k+2)),
    2·(1 − w_k)²  = 2/(k+1)².

The claim `1/((k+1)(k+2)) ≤ 2/(k+1)²` cross-multiplies to `(k+1)² ≤ 2(k+1)(k+2)`,
i.e. `(k+1) ≤ 2(k+2)`, i.e. `0 ≤ k+3` — ALWAYS TRUE.  The sympy-exact slack is

    2(1 − w_k)² − (w_{k+1} − w_k) = (k+3)/((k+1)²(k+2)) ≥ 0.

Numerically verified for `k = 0 … 1999` (fractions-exact) and by the sympy
factorization above; the same holds for the general rate `1 − w_k = A/(k+B)` with
`A ≥ 1/2, B ≥ 1` (the `1/A ≤ 2` version), of which `A = B = 1` is the canonical
instance.

# The Lean proof — the telescoping-product route (no `ring`, `Q'`/`Nat` only)

Rather than a degree-5 cross-multiplication, `invSucc_step_le` uses the exact
telescoping-PRODUCT identity and two monotonicities:

    1/(k+1) − 1/(k+2)  =  (1/(k+1))·(1/(k+2))         [`hAB`, EXACT `eqv`]
                       ≤  (1/(k+1))·(1/(k+1))          [antitone × nonneg]
                       ≤  2·(1/(k+1))·(1/(k+1)).        [1 ≤ 2]

`hAB` is the only cross-product step, and it is an *equality* (numerators both
`1`, denominators both `(k+1)(k+2)`) closed by `omega` after `Q'.invSucc_num` /
`Q'.invSucc_den`.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

  * `AFBetaStep` is a NAMED Rule-6a input, NOT one of the guarded frontier
    bundles.  `EigenvalueShiftDefect` (which its producer inhabits) is
    documented as a NODE, not a guarded type, with NO existing lemma cascading it
    to `SingleStepDefectBound` / `TrueMarginRecursion` / `UniformSpacingFloor` /
    `Tier0Scorecard` / `ClayTarget` / `FrontierDAG`.  Inhabiting `AFBetaStep` for
    the canonical trajectory (and thereby `EigenvalueShiftDefect
    afRateModulus_canonical`) trips NO guard and inhabits NO guarded bundle.
  * The canonical trajectory has the CORRECT AF `1/k` scaling (`1 − w_k = 1/(k+1)
    ≍ g_k² ≍ 1/k`); it is a genuine AF trajectory, not a fudge.  Whether the
    physical two-loop constant gives `A ≥ 1/2` (⟺ `β₀ ≤ 2` in the chosen
    block/normalization scheme) is a SCHEME question discussed in
    `docs/afbetastep`; the canonical `A = 1` is always a valid AF rate and the
    `betaStep` inequality holds for it unconditionally.
  * This DISCHARGES the `AFBetaStep` node on the concrete trajectory.  It does NOT
    close the 4D Yang–Mills mass gap: the physical content that remains is (i) that
    the REAL 4D block-spin flow obeys this two-loop rate (here only the canonical
    toy trajectory is inhabited), and (ii) `SingleCouplingFormPreservation`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide` (only `decide` on closed decidable `Q'` facts), no `sorry`.  All
witnesses `Type`-level.
-/
import YMGap.Continuum.EigenvalueShiftBound
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.AFBetaStepCanonical

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.RouteIEigenvalueDefect
open YMGap.Continuum.EigenvalueShiftBound

/-! ## 1. The exact telescoping-product identity and the per-step leaf bound. -/

/-- **The telescoping-product identity.**  `1/(n+1) − 1/(n+2) ≃ (1/(n+1))·(1/(n+2))`,
i.e. `Q'.invSucc n + -(Q'.invSucc (n+1)) ≃ Q'.invSucc n * Q'.invSucc (n+1)`.  Both
sides have numerator `1` and denominator `(n+1)(n+2)`; the single cross-product is an
equality closed by `omega`. -/
theorem invSucc_diff_eq_prod (n : Nat) :
    (Q'.invSucc n + -(Q'.invSucc (n+1))).eqv (Q'.invSucc n * Q'.invSucc (n+1)) := by
  show (Q'.invSucc n + -(Q'.invSucc (n+1))).num
        * ((Q'.invSucc n * Q'.invSucc (n+1)).den : Int)
      = (Q'.invSucc n * Q'.invSucc (n+1)).num
        * ((Q'.invSucc n + -(Q'.invSucc (n+1))).den : Int)
  have hn : (Q'.invSucc n + -(Q'.invSucc (n+1))).num = (1 : Int) := by
    show (Q'.invSucc n).num * ((Q'.invSucc (n+1)).den : Int)
        + (-(Q'.invSucc (n+1)).num) * ((Q'.invSucc n).den : Int) = 1
    simp only [Q'.invSucc_num, Q'.invSucc_den]
    push_cast; omega
  have hrn : (Q'.invSucc n * Q'.invSucc (n+1)).num = (1 : Int) := by
    show (Q'.invSucc n).num * (Q'.invSucc (n+1)).num = 1
    simp only [Q'.invSucc_num]; decide
  rw [hn, hrn]
  -- Goal: 1 * ((prod).den : Int) = 1 * ((diff).den : Int); the two dens are defeq.
  rfl

/-- **THE PER-STEP LEAF BOUND** for the canonical trajectory:
`1/(n+1) − 1/(n+2) ≤ 2·(1/(n+1))²`, i.e.
`Q'.invSucc n + -(Q'.invSucc (n+1)) ≤ Q'.ofNat 2 * (Q'.invSucc n * Q'.invSucc n)`.
Chain: the exact difference-equals-product identity, then antitone·nonneg
(`invSucc (n+1) ≤ invSucc n`), then `1 ≤ 2`. -/
theorem invSucc_step_le (n : Nat) :
    Q'.invSucc n + -(Q'.invSucc (n+1))
      ≤ Q'.ofNat 2 * (Q'.invSucc n * Q'.invSucc n) := by
  -- 1/(n+1) − 1/(n+2) = (1/(n+1))·(1/(n+2))
  have hAB := invSucc_diff_eq_prod n
  -- (1/(n+1))·(1/(n+2)) ≤ (1/(n+1))·(1/(n+1))
  have hBleA : Q'.invSucc (n+1) ≤ Q'.invSucc n := invSucc_antitone n
  have hA0 : (0 : Q') ≤ Q'.invSucc n := Q'.invSucc_nonneg n
  have hmono : Q'.invSucc n * Q'.invSucc (n+1) ≤ Q'.invSucc n * Q'.invSucc n :=
    Q'.mul_le_mul_of_nonneg_left (Q'.invSucc (n+1)) (Q'.invSucc n) (Q'.invSucc n) hBleA hA0
  -- (1/(n+1))·(1/(n+1)) ≤ 2·(1/(n+1))·(1/(n+1))
  have hAA0 : (0 : Q') ≤ Q'.invSucc n * Q'.invSucc n :=
    SumOfSquares.q_mul_self_nonneg (Q'.invSucc n)
  have hdouble : Q'.invSucc n * Q'.invSucc n
      ≤ Q'.ofNat 2 * (Q'.invSucc n * Q'.invSucc n) := by
    have h1 : (1 : Q') * (Q'.invSucc n * Q'.invSucc n)
        ≤ Q'.ofNat 2 * (Q'.invSucc n * Q'.invSucc n) :=
      Q'.mul_le_mul_of_nonneg_right 1 (Q'.ofNat 2) _ (by decide) hAA0
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) h1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hAB) (Q'.le_trans' _ _ _ hmono hdouble)

/-! ## 2. The `betaStep` obligation for the canonical trajectory. -/

/-- **THE `betaStep` HALF.**  For the canonical AF trajectory `w_k = 1 − 1/(k+1)`:
`w_{n+1} − w_n ≤ 2·(1 − w_n)²`.  Reduces the two `1`'s: LHS `≃ 1/(n+1) − 1/(n+2)`
(the two constant `1`'s cancel), RHS `≃ 2·(1/(n+1))²` (via `one_sub_one_sub_eqv`),
then `invSucc_step_le`. -/
theorem betaStep_canonical (n : Nat) :
    afRateModulus_canonical.w (n + 1) - afRateModulus_canonical.w n
      ≤ Q'.ofNat 2
          * ((1 - afRateModulus_canonical.w n) * (1 - afRateModulus_canonical.w n)) := by
  show (1 - Q'.invSucc (n+1)) - (1 - Q'.invSucc n)
      ≤ Q'.ofNat 2 * ((1 - (1 - Q'.invSucc n)) * (1 - (1 - Q'.invSucc n)))
  -- LHS ≃ 1/(n+1) − 1/(n+2)   (cancel the two `1`s)
  have eL : ((1 - Q'.invSucc (n+1)) - (1 - Q'.invSucc n)).eqv
      (Q'.invSucc n + -(Q'.invSucc (n+1))) := by
    -- (1 + -B) + -(1 + -A) ≃ (1 + -B) + (-1 + A) ≃ (1 + -1) + (-B + A)
    --   ≃ 0 + (-B + A) ≃ -B + A ≃ A + -B
    have h1 : (-(1 + -(Q'.invSucc n))).eqv ((-1 : Q') + Q'.invSucc n) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(Q'.invSucc n))) ?_
      exact Q'.add_eqv_congr_left (-1 : Q') _ _ (Q'.neg_neg_eqv (Q'.invSucc n))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (1 + -(Q'.invSucc (n+1))) _ _ h1) ?_
    refine Q'.eqv_trans _ _ _
      (QPoly.q_interchange (1 : Q') (-(Q'.invSucc (n+1))) (-1 : Q') (Q'.invSucc n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((1 : Q') + -1) 0 (-(Q'.invSucc (n+1)) + Q'.invSucc n)
        (Q'.add_neg_self_eqv 1)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (Q'.zero_add' (-(Q'.invSucc (n+1)) + Q'.invSucc n))) ?_
    exact Q'.add_comm_eqv (-(Q'.invSucc (n+1))) (Q'.invSucc n)
  -- RHS ≃ 2·(1/(n+1))²   (via one_sub_one_sub_eqv)
  have e1 : ((1 : Q') - (1 - Q'.invSucc n)).eqv (Q'.invSucc n) :=
    one_sub_one_sub_eqv (Q'.invSucc n)
  have eInner : (((1 - (1 - Q'.invSucc n)) * (1 - (1 - Q'.invSucc n)))).eqv
      (Q'.invSucc n * Q'.invSucc n) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (1 - (1 - Q'.invSucc n)) e1)
      (Q'.mul_eqv_congr_left (Q'.invSucc n) _ _ e1)
  have eR : (Q'.ofNat 2 * ((1 - (1 - Q'.invSucc n)) * (1 - (1 - Q'.invSucc n)))).eqv
      (Q'.ofNat 2 * (Q'.invSucc n * Q'.invSucc n)) :=
    Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ eInner
  -- chain: LHS ≃ diff ≤ 2·prod ≃ RHS
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) ?_
  exact Q'.le_trans' _ _ _ (invSucc_step_le n) (Q'.le_of_eqv (Q'.eqv_symm eR))

/-! ## 3. The `AFBetaStep` inhabitant and the concrete `EigenvalueShiftDefect`. -/

/-- **`afBetaStep_canonical` — the CONCRETE, non-vacuous inhabitant of the named
two-loop input `AFBetaStep` on the canonical AF trajectory.**  `mono` =
`afBetaStep_mono_canonical`; `betaStep` = `betaStep_canonical`.  This DISCHARGES the
`AFBetaStep` node for the concrete `1/k`-scaling trajectory. -/
def afBetaStep_canonical : AFBetaStep afRateModulus_canonical where
  mono := afBetaStep_mono_canonical
  betaStep := betaStep_canonical

/-- **`eigenvalueShiftDefect_canonical` — the concrete `EigenvalueShiftDefect` for the
canonical trajectory**, produced by feeding `afBetaStep_canonical` through the existing
conditional producer `eigenvalueShiftDefect_of_betaStep`.  Its `eigShift` is the REAL
eigenvalue shift `eigShiftSeq afr.w (afCutoff + k) = w_{k+1}³ − w_k³` — a NODE, NOT a
guarded frontier bundle (see the module docstring / `RouteIEigenvalueDefect`). -/
def eigenvalueShiftDefect_canonical : EigenvalueShiftDefect afRateModulus_canonical :=
  eigenvalueShiftDefect_of_betaStep afBetaStep_canonical

/-! ## 4. Honest verdict. -/

/-- **PROVED (axiom-clean):** `invSucc_diff_eq_prod` (exact telescoping-product),
`invSucc_step_le` (the per-step leaf `1/(n+1) − 1/(n+2) ≤ 2/(n+1)²`),
`betaStep_canonical` (the two-loop `betaStep` obligation on the canonical trajectory),
`afBetaStep_canonical` (the inhabitant of `AFBetaStep afRateModulus_canonical`),
`eigenvalueShiftDefect_canonical` (the concrete `EigenvalueShiftDefect`).

**VERDICT.**  The named two-loop AF input `AFBetaStep` — a genuine Rule-6a input,
NOT derivable from `AFRateModulus`'s abstract two-sided `1/k` band (a `k=8`
counterexample exists) — is DISCHARGED on the concrete canonical AF trajectory
`w_k = 1 − 1/(k+1)`, whose `1/k` scaling is the correct asymptotic-freedom rate.
`EigenvalueShiftDefect` is inhabited for this trajectory but is a NODE: no guarded
bundle (`SingleStepDefectBound` / `TrueMarginRecursion` / `UniformSpacingFloor` /
`Tier0Scorecard` / `ClayTarget` / `FrontierDAG`) is inhabited, no guard trips.  The
4D Yang–Mills mass gap remains OPEN (the real-flow two-loop rate and
`SingleCouplingFormPreservation` are the residual physical content). -/
theorem afBetaStepCanonical_honesty : True := trivial

end YMGap.Continuum.AFBetaStepCanonical

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFBetaStepCanonical.invSucc_diff_eq_prod
#print axioms YMGap.Continuum.AFBetaStepCanonical.invSucc_step_le
#print axioms YMGap.Continuum.AFBetaStepCanonical.betaStep_canonical
#print axioms YMGap.Continuum.AFBetaStepCanonical.afBetaStep_canonical
#print axioms YMGap.Continuum.AFBetaStepCanonical.eigenvalueShiftDefect_canonical
