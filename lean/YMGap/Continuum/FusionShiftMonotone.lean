/-
Track 11.7-fusion / R2 (Core B) — the `p`-index MONOTONICITY combinator that
collapses the infinite family of bulk-shift bounds `{bulkShiftBound_p}_{p ≥ 2}` onto
the SINGLE `p = 2` base value, running on ONE new named-open single-step atom.

# What this module does (read first — honest scope)

`FusionKernelStatement.SaddleLocalCLT.bulkShiftBound` is the load-bearing open field
of the discrete SU(2) fusion local-CLT: the vacuum-normalized eigenvalue shift stays
under the localization margin `1/12` for EVERY bond-moving exponent `p ≥ 2`.  That is
an INFINITE family of analytic obligations, one per `p`.  This module isolates the
structural fact that makes that family collapse: IF the (rebased) shift modulus is
monotone NON-INCREASING in `p` from index `2` onward, THEN every `p ≥ 2` bound follows
from the single `p = 2` base by pure telescoping.

The monotone object does NOT exist in Lean as the bare `fusionEig − eigA` shift — that
literal shift is provably non-monotone and false for all `p ≥ 2` (`core_b_pilot.py`).
The monotone quantity is the vacuum-REBASED curvature-remainder modulus measured
against a rebased reference eigenvalue (the pilot's `w_eff = exp(−A_p)` shift budget),
carried here as inert DATA (`refEig`) so no `CReal.exp` is required at the Lean level.
On that rebased modulus the pilot exhibits monotone decrease in `p` (worst at `p = 2`,
34× margin under `1/12`).

# What is PROVED here (axiom-clean `Q'`/`Nat`)

  * `FusionShiftMonotone` — the monotone bundle: the rebased shift sequence `shift`,
    its coupling `couples` to the actual eigenvalue defect against `refEig`, the `p = 2`
    base `baseTwo : shift 2 ≤ 1/12`, and the single-step law `monoStep`.
  * `shift_le_shift_two` — pure telescoping: `shift p ≤ shift 2` for every `p ≥ 2`.
  * `shift_le_margin` — composition with the base: `shift p ≤ 1/12` for every `p ≥ 2`.
  * `bulkShift_rebased` — THE PAYOFF: the rebased bulk-shift bound
    `fusionEig p s − refEig p s ≤ 1/12` for EVERY `p ≥ 2` and every mode `s`,
    discharged from the single `p = 2` base value via `couples` + `shift_le_margin`.
  * `FusionShiftMonotone.ofStep` — the reduction wire: the whole bundle is assembled
    from the shift data, the coupling, the base, and ONE `FusionShiftStep` witness.

# What is NAMED-OPEN (NOT inhabited, NOT faked)

  * `FusionShiftStep N w shift` — the single-step relative-variance decrease
    `∀ p ≥ 2, shift (p+1) ≤ shift p`: one more truncated SU(2) Clebsch–Gordan
    autoconvolution does not increase the vacuum-rebased relative curvature remainder.
    This is ONE `p`-indexed monotonicity atom that REPLACES the infinite family
    `{bulkShiftBound_p}_{p ≥ 2}`.  It is of comparable depth to the `p = 2` core (a
    truncated-CG discrete local-CLT) — it is NOT sourced from any Karlin
    convolution-preserves-log-concavity wrapper (that is FALSE here: the fusion product
    is truncated and Clebsch–Gordan, not additive; the in-tree log-concavity content is
    `s`-index PF₂, not `p`-index shift monotonicity).  NOT inhabited; NOT faked.
  * The `p = 2` base `shift 2 ≤ 1/12` and the `refEig` re-basing are carried as
    hypotheses/data — themselves general-`N`-open (the `Δ²C₄ = 2`, `d2x ≤ 1` ladder is
    inhabited only at `N = 1`).

# Honest verdict

This module does NOT close Core B.  It RELOCATES the infinite family
`{bulkShiftBound_p}_{p ≥ 2}` onto ONE new named-open single-step monotonicity atom
`FusionShiftStep` (plus the still-open `p = 2` base).  The telescoping combinator that
performs the collapse (`shift_le_shift_two` / `shift_le_margin` / `bulkShift_rebased`)
is genuine, cheap, and axiom-clean.  Numerically the rebased modulus is monotone
decreasing in `p` (pilot), so the reduction is worthwhile — but it closes nothing.
`FusionShiftStep` is OPEN; never source it from Karlin.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and a single `Nat` induction (telescoping).  Every
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
The open core `FusionShiftStep` and the bundle `FusionShiftMonotone` are NAMED and
left UNINHABITED for the genuine `p ≥ 2` content.
-/

import YMGap.Continuum.FusionKernelStatement
import YMGap.Continuum.S1Dominance

namespace YMGap.Continuum.FusionShiftMonotone

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.FusionKernelStatement

/-! ## 1. The single-step monotonicity atom — THE named-open residual

`FusionShiftStep N w shift` is the one `p`-indexed obligation that replaces the
infinite family of bulk-shift bounds: the rebased shift modulus does not increase
under one more truncated SU(2) Clebsch–Gordan autoconvolution, for every `p ≥ 2`.
It is NAMED-OPEN — uninhabited here — and must NOT be sourced from a Karlin
convolution-preserves-log-concavity wrapper (that mechanism is unavailable: the
fusion product is truncated and CG, not additive). -/

/-- **`FusionShiftStep` — the single-step relative-variance decrease (NAMED-OPEN).**
For the vacuum-rebased `p`-fold fusion curvature modulus `shift`,
`shift (p+1) ≤ shift p` for every `p ≥ 2`.  This ONE atom replaces the infinite
family `{bulkShiftBound_p}_{p ≥ 2}`.  It is a truncated-CG discrete local-CLT
statement of comparable depth to the `p = 2` core; it is NOT inhabited here. -/
structure FusionShiftStep (N : Nat) (w : Q') (shift : Nat → Q') : Type where
  /-- One more truncated SU(2) CG autoconvolution does not increase the rebased
  relative curvature remainder. -/
  step : ∀ p, 2 ≤ p → shift (p + 1) ≤ shift p

/-! ## 2. The monotone bundle -/

/-- **`FusionShiftMonotone` — the rebased-shift monotone bundle.**  Carries the
vacuum-rebased `p`-fold fusion shift sequence `shift`, the rebased reference
eigenvalue `refEig` (inert DATA — the `w_eff = exp(−A_p)` re-basing, no `CReal.exp`
needed at Lean level), the coupling of `shift` to the actual eigenvalue defect, the
`p = 2` base under the localization margin, and the single-step monotonicity law.

The literal bare shift `fusionEig − eigA` is provably NON-monotone and false for all
`p ≥ 2`; the rebased shift against `refEig` is the object the pilot exhibits as
monotone decreasing in `p`.  Left UNINHABITED for the genuine `p ≥ 2` content. -/
structure FusionShiftMonotone (N : Nat) (w : Q')
    (h0' : ∀ p s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  /-- The vacuum-rebased `p`-fold fusion shift modulus (a `p`-indexed `Q'`). -/
  shift : Nat → Q'
  /-- The rebased reference eigenvalue `eigA_eff p s` (inert DATA; the `w_eff` shift
  budget re-basing). -/
  refEig : Nat → Nat → Q'
  /-- **COUPLING**: the rebased shift dominates the actual eigenvalue defect against
  the rebased reference. -/
  couples : ∀ p s, fusionEig N w p s (h0' p s) - refEig p s ≤ shift p
  /-- **BASE (`p = 2`)**: the rebased shift at `p = 2` is under the localization
  margin `1/12` (the Tier-0 Casimir-ladder base). -/
  baseTwo : shift 2 ≤ q112
  /-- **THE SINGLE-STEP RESIDUAL**: `shift (p+1) ≤ shift p` for `p ≥ 2`. -/
  monoStep : ∀ p, 2 ≤ p → shift (p + 1) ≤ shift p

/-- **`ofStep` — the reduction wire.**  The whole monotone bundle is assembled from
the shift data, the rebased reference, the coupling, the `p = 2` base, and ONE
`FusionShiftStep` witness (which supplies `monoStep`).  This exhibits the infinite
family as reducible to the single named-open step atom. -/
def ofStep {N : Nat} {w : Q'}
    {h0' : ∀ p s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (shift : Nat → Q') (refEig : Nat → Nat → Q')
    (couples : ∀ p s, fusionEig N w p s (h0' p s) - refEig p s ≤ shift p)
    (baseTwo : shift 2 ≤ q112)
    (S : FusionShiftStep N w shift) :
    FusionShiftMonotone N w h0' where
  shift := shift
  refEig := refEig
  couples := couples
  baseTwo := baseTwo
  monoStep := S.step

/-! ## 3. The telescoping combinator — the infinite family collapses to `p = 2` -/

/-- Telescoping helper: from the single-step law, `shift (2 + k) ≤ shift 2` for every
`k`.  Induction on `k` (`Nat.add` recurses on the second argument, so
`2 + (k+1)` is definitionally `(2 + k) + 1`). -/
theorem shift_le_shift_two_aux {N : Nat} {w : Q'}
    {h0' : ∀ p s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (M : FusionShiftMonotone N w h0') :
    ∀ k, M.shift (2 + k) ≤ M.shift 2 := by
  intro k
  induction k with
  | zero => exact Q'.le_refl' _
  | succ k ih => exact Q'.le_trans' _ _ _ (M.monoStep (2 + k) (by omega)) ih

/-- **`shift_le_shift_two` — the telescoping collapse.**  From the single-step law,
`shift p ≤ shift 2` for every `p ≥ 2`: the infinite family of shift values is
dominated by the single `p = 2` value. -/
theorem shift_le_shift_two {N : Nat} {w : Q'}
    {h0' : ∀ p s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (M : FusionShiftMonotone N w h0') :
    ∀ p, 2 ≤ p → M.shift p ≤ M.shift 2 := by
  intro p hp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  exact shift_le_shift_two_aux M k

/-- **`shift_le_margin` — every `p ≥ 2` shift is under the localization margin.**
Compose the telescoping collapse with the `p = 2` base `shift 2 ≤ 1/12`. -/
theorem shift_le_margin {N : Nat} {w : Q'}
    {h0' : ∀ p s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (M : FusionShiftMonotone N w h0') :
    ∀ p, 2 ≤ p → M.shift p ≤ q112 :=
  fun p hp => Q'.le_trans' _ _ _ (shift_le_shift_two M p hp) M.baseTwo

/-- **`bulkShift_rebased` — THE PAYOFF.**  The rebased bulk-shift bound
`fusionEig p s − refEig p s ≤ 1/12` holds for EVERY `p ≥ 2` and every mode `s`,
discharged from the single `p = 2` base value via `couples` + `shift_le_margin`.
This is the rebased form of `SaddleLocalCLT.bulkShiftBound` for the whole `p ≥ 2`
family, produced from the single base — the intended "all `p ≥ 2` reduce to `p = 2`". -/
theorem bulkShift_rebased {N : Nat} {w : Q'}
    {h0' : ∀ p s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0}
    (M : FusionShiftMonotone N w h0') :
    ∀ p, 2 ≤ p → ∀ s,
      fusionEig N w p s (h0' p s) - M.refEig p s ≤ q112 :=
  fun p hp s => Q'.le_trans' _ _ _ (M.couples p s) (shift_le_margin M p hp)

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * `shift_le_shift_two_aux` / `shift_le_shift_two` — the telescoping collapse of the
    infinite shift family onto the single `p = 2` value, from the single-step law.
  * `shift_le_margin` — composition with the `p = 2` base: `shift p ≤ 1/12`, `p ≥ 2`.
  * `bulkShift_rebased` — the rebased bulk-shift bound for the whole `p ≥ 2` family,
    from `couples` + `shift_le_margin`.
  * `ofStep` — the assembly wire from the single `FusionShiftStep` atom.

NAMED OPEN (NOT inhabited):

  * `FusionShiftStep N w shift` — the single-step relative-variance decrease, the ONE
    `p`-indexed monotonicity atom replacing the infinite family
    `{bulkShiftBound_p}_{p ≥ 2}`.  A truncated-CG discrete local-CLT of comparable
    depth to the `p = 2` core.  NOT sourced from Karlin (mechanism unavailable here).
  * `FusionShiftMonotone` for the genuine `p ≥ 2` bond-moving — carries that atom plus
    the still-open `p = 2` base and the `refEig` re-basing; left UNINHABITED.

HONEST VERDICT.  This module does NOT close Core B.  The telescoping combinator is
genuine and collapses the infinite family onto the single `p = 2` base — but it runs
on a NEW named-open single-step monotonicity atom `FusionShiftStep` of comparable
depth to the `p = 2` core.  The route RELOCATES the infinite family onto one new open
atom; it closes nothing.  Numerically supported (pilot: rebased modulus monotone
decreasing in `p`, worst at `p = 2`), so the reduction is worthwhile. -/

end YMGap.Continuum.FusionShiftMonotone

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionShiftMonotone.ofStep
#print axioms YMGap.Continuum.FusionShiftMonotone.shift_le_shift_two_aux
#print axioms YMGap.Continuum.FusionShiftMonotone.shift_le_shift_two
#print axioms YMGap.Continuum.FusionShiftMonotone.shift_le_margin
#print axioms YMGap.Continuum.FusionShiftMonotone.bulkShift_rebased
