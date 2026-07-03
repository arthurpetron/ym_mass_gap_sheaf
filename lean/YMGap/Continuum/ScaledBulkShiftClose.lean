/-
Track B-converge / R2 — **CLOSING `Stage2ConvergesToMargin.ScaledBulkShift` from
`sl` alone, and the honest ledger of what that close does and does NOT buy.**

# What this module does (read first)

`Stage2ConvergesToMargin.ScaledBulkShift afr N₀ sl` is the trajectory↔graded
DICTIONARY: a reindexing `idx` plus two identifications

    shift_eq  : ∀ k, shift k = sl.gapDefect (idx k)
    budget_eq : ∀ k, δ k * g k = gradedBudget (afr.w (idx k)) N₀ (sl.traj.hZ (idx k))

`hbridge_of_hlocalize` then derives `shift_k ≤ δ_k·g_k` from `sl.hlocalize` by
rewriting through those two identifications.  The object was flagged as an open
"residual dictionary".  This module DISCHARGES it completely:

  * **`qmul_one`** (§1) — the STRICT unit law `a * 1 = a` on `Q'` (NOT merely the
    `.eqv` form `mul_one_eqv`).  It is genuinely provable (`Int.mul_one` on the
    numerator, `Nat.mul_one`/`Nat.add_sub_cancel` on the denominator) — just not by
    `rfl`.  This is the load-bearing correction: the scout report claimed the strict
    `budget_eq` was UNPROVABLE and needed relaxation to `.eqv`; in fact the strict
    equality holds, so the ORIGINAL `ScaledBulkShift` (strict `=`) is inhabitable
    as written, no phrasing fix required.

  * **`ofLocalization`** (§2) — the canonical `sl`-only inhabitant of
    `ScaledBulkShift afr N₀ sl` for EVERY `sl`, with `idx := id`, `shift :=
    sl.gapDefect`, `g := 1`, `δ := gradedBudget(w_k)`.  `shift_eq` is `rfl`;
    `budget_eq` is `qmul_one`.  So the dictionary carries ZERO content beyond `sl`.

  * **`hbridge_closed_from_hlocalize`** (§3) — the payoff: composing the merge
    lemma with the canonical inhabitant, `gapDefect_k ≤ gradedBudget(w_k)·1` is
    derived from `sl.hlocalize` with NO extra hypothesis.  `ScaledBulkShift` is off
    the frontier.

# Honest scope — what this close does NOT do

`ScaledBulkShift`'s `δ, g, idx` are FREE fields; the canonical inhabitant sets
`g := 1`, which is NOT the physical margin `g_k = m_lat(a_k)/a_k`.  The
load-bearing obligation actually consumed by `stage2_convergence` is
`AsymptoticSpectralLoc.SpectralMarginInput.hbridge`, whose `δ, g` are PINNED to the
physical defect and margin.  Nothing here builds a `SpectralMarginInput.hbridge`
from an `sl`, because with the physical `g_k ≠ 1` the unit law `qmul_one` does not
fire and the trajectory↔graded translation becomes real content.  So closing
`ScaledBulkShift` is a correct NAMING/cleanup advance (it removes a decoupled
free-field wrapper), NOT a reduction of the Stage-2 critical path.  The frontier
remains the three independent fields of the single `SpectralMarginInput`
(`hlocalize`, the PINNED `hbridge`, `hadd`); the Clay mass gap stays OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition over already-proved engines; every carrier is
`Type`-level data.  Each load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`, no
`sorry`, no custom `axiom`.
-/

import YMGap.Continuum.Stage2ConvergesToMargin

namespace YMGap.Continuum.ScaledBulkShiftClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.Stage2ConvergesToMargin

/-! ## 1. The STRICT unit law `a * 1 = a` on `Q'`

`RationalsMul.mul_one_eqv` gives only the SEMANTIC form `(a * 1).eqv a`.  The
scout report inferred from that the STRICT `budget_eq` (`δ·g = gradedBudget`, an
`=` on the `DecidableEq` struct `Q'`) was unprovable.  That inference is wrong:
the strict equality holds, established below by unfolding `Q'.mul` and discharging
the numerator with `Int.mul_one` and the denominator with `Nat.mul_one` +
`Nat.add_sub_cancel`.  It is simply not a `rfl`. -/

/-- **STRICT `a * 1 = a`.**  `a * 1 = ⟨a.num * 1, a.den * 1 - 1⟩`; the numerator
reduces via `Int.mul_one`, and the denominator `(a.denPred + 1) * 1 - 1` reduces to
`a.denPred` via `Nat.mul_one` and `Nat.add_sub_cancel`. -/
theorem qmul_one (a : Q') : a * 1 = a := by
  show Q'.mul a 1 = a
  unfold Q'.mul
  show (⟨a.num * 1, a.den * 1 - 1⟩ : Q') = a
  have h1 : a.num * 1 = a.num := Int.mul_one _
  have h2 : a.den * 1 - 1 = a.denPred := by
    show (a.denPred + 1) * 1 - 1 = a.denPred
    rw [Nat.mul_one, Nat.add_sub_cancel]
  rw [h1, h2]

/-! ## 2. The canonical `sl`-only inhabitant of the dictionary -/

/-- **THE CANONICAL INHABITANT (the close).**  For EVERY `sl`, the trajectory↔
graded dictionary `ScaledBulkShift afr N₀ sl` is inhabited by the `sl`-only witness
`idx := id`, `shift := sl.gapDefect`, `g := 1`, `δ := gradedBudget(w_k)`:

  * `shift_eq k : sl.gapDefect k = sl.gapDefect (id k)` holds by `rfl`;
  * `budget_eq k : gradedBudget(w_k)·1 = gradedBudget(w_k)` holds by `qmul_one`.

Since this is available with no extra data, the dictionary carries ZERO content
beyond `sl` — it is discharged, not open. -/
def ofLocalization (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) : ScaledBulkShift afr N₀ sl where
  shift := fun k => sl.gapDefect k
  δ := fun k => gradedBudget (afr.w k) N₀ (sl.traj.hZ k)
  g := fun _ => 1
  idx := fun k => k
  shift_eq := fun _ => rfl
  budget_eq := fun k => qmul_one (gradedBudget (afr.w k) N₀ (sl.traj.hZ k))

/-! ## 3. The payoff — `hbridge` closed from `hlocalize` with no extra hypothesis -/

/-- **THE CLOSE, delivered.**  Composing `hbridge_of_scaledBulkShift` with the
canonical inhabitant, the trajectory scaled-shift control
`sl.gapDefect k ≤ gradedBudget(w_k)·1` follows from `sl.hlocalize` alone.  The
dictionary `ScaledBulkShift` is thus removed from the frontier: it is a proved
consequence of the graded spectral-localization datum. -/
theorem hbridge_closed_from_hlocalize (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) (k : Nat) :
    (ofLocalization afr N₀ sl).shift k
      ≤ (ofLocalization afr N₀ sl).δ k * (ofLocalization afr N₀ sl).g k :=
  hbridge_of_scaledBulkShift (ofLocalization afr N₀ sl) k

/-- The same, in fully-reduced physical notation:
`sl.gapDefect k ≤ gradedBudget(afr.w k) N₀ (sl.traj.hZ k) * 1`, from `hlocalize`. -/
theorem gapDefect_le_gradedBudget_mul_one (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) (k : Nat) :
    sl.gapDefect k ≤ gradedBudget (afr.w k) N₀ (sl.traj.hZ k) * 1 :=
  hbridge_closed_from_hlocalize afr N₀ sl k

/-! ## 4. The decoupling witness (why the close is cleanup, not reduction)

The canonical inhabitant sets `g := 1`.  We record this explicitly: the object we
just closed is NOT pinned to the physical margin, so it cannot supply the
load-bearing `SpectralMarginInput.hbridge` (whose `g_k = m_lat(a_k)/a_k`).  The
lemma below is the honest witness that the close operated on `g = 1`, i.e. on a
surrogate of the physical scaled shift. -/

/-- **DECOUPLING WITNESS.**  The canonical inhabitant's margin field is the
constant `1`, NOT the physical margin `m_lat(a_k)/a_k`.  Hence the unit law
`qmul_one` fired, collapsing `budget_eq` to a triviality — which is exactly why the
close is content-free bookkeeping and does not transport to the pinned
`SpectralMarginInput.hbridge`. -/
theorem canonical_g_is_one (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) (k : Nat) :
    (ofLocalization afr N₀ sl).g k = 1 := rfl

end YMGap.Continuum.ScaledBulkShiftClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ScaledBulkShiftClose.qmul_one
#print axioms YMGap.Continuum.ScaledBulkShiftClose.ofLocalization
#print axioms YMGap.Continuum.ScaledBulkShiftClose.hbridge_closed_from_hlocalize
#print axioms YMGap.Continuum.ScaledBulkShiftClose.gapDefect_le_gradedBudget_mul_one
#print axioms YMGap.Continuum.ScaledBulkShiftClose.canonical_g_is_one
