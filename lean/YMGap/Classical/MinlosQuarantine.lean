/-
CLASSICAL INPUT (CITED, EXTERNAL — NOT a Lean `Classical.choice` quarantine).

# What this module is

A docstringed re-export *interface* for the OPTIONAL cited-classical continuum
COROLLARY of the development: the Bochner–Minlos + Daniell–Kolmogorov σ-additive
lift that produces the `a → 0` continuum MEASURE with tightness. That result is a
classical theorem in the external Gaussian-free-field / constructive-QFT
literature; it is NOT transferable to this Mathlib-free constructive substrate, and
it is NOT re-proved here.

# ARCHITECTURAL STATUS: this is NOT a frontier atom (it is optional packaging)

The Jaffe–Witten / Osterwalder–Schrader requirement is a condition on the POSITIVE
LINEAR FUNCTIONAL (the Schwinger functional), not on a σ-additive measure; that
functional formulation is the continuum target
(`Continuum.FunctionalContinuumTarget`: OS0–OS4 + GNS reconstruction, measure-free).
`CitedMinlosLift`'s dynamical content (`defectRecursion`) is Sub-wall B's
`DefectGapRecursion` and its correlator content (`loopyResidual`) is Sub-wall A's
`LoopyCorrelatorResidual`, both already counted in the frontier; its ONLY
genuinely-new datum is the σ-additive tightness modulus (`tightnessRate`), an
OPTIONAL Bochner–Minlos packaging DOWNSTREAM of the functional target
(`FunctionalContinuumTarget.minlos_is_optional_corollary`).  So `CitedMinlosLift`
has been REMOVED as a required field of the continuum-target bundles
(`ContinuumScorecard.ContinuumTargetReduction`, `Continuum.Tier0Scorecard`,
`Tier0FrontierCorrected.Tier0FrontierC`); it is retained ONLY as this optional
classical-corollary interface.

# Why it lives under `YMGap/Classical/` even though it uses NO Lean classical axiom

AGENTS.md Rule 4 quarantines *Lean* classical axioms (`Classical.choice`,
`Classical.em`, …) under this directory. The Minlos lift is a DIFFERENT category:
there is no Lean classical axiom in play at all. `CitedMinlosLift` is an
UNINHABITED `structure` (`Rubric/ClayScorecard.ClayContinuumExistence`) whose
docstring *cites* an external classical theorem as its intended meaning. We place
its interface here — alongside the Rule-4 quarantine machinery — so that every
cited-classical dependency of the development has exactly one auditable home, and
so `lean/CLASSICAL_LEDGER.md` can index it. This file:

  * introduces NO `axiom`, NO `Classical.*`, NO `native_decide`, NO `sorry`;
  * supplies NO inhabitant of the Minlos structure (by design — supplying one is
    part of the open continuum Clay problem);
  * only RE-EXPORTS the already-named `CitedMinlosLift` under a
    quarantine-namespaced alias, plus axiom-clean CONDITIONAL projection lemmas
    (each of the form "GIVEN a hypothetical inhabitant, here is the witness it
    would carry"), so downstream code can name the dependency without ever
    fabricating it.

Rule 1 status: this module is load-bearing only as an interface; `#print axioms`
on its declarations must show at most `propext`/`Quot.sound` (no classical axiom,
no raw `axiom`). See `lean/CLASSICAL_LEDGER.md` entry [P0.1].
-/
import YMGap.Rubric.ContinuumScorecard

namespace YMGap.Classical.MinlosQuarantine

open YMGap.Constructive
open YMGap.Rubric.ClayScorecard (ClayContinuumExistence)
open YMGap.Rubric.ContinuumScorecard (CitedMinlosLift)

/-- **The quarantined cited-classical Minlos lift, re-exported by name (OPTIONAL
corollary object, NOT a frontier atom).**  Definitionally the continuum-MEASURE
structure `CitedMinlosLift` (= `ClayContinuumExistence`): the `a → 0` σ-additive
measure existence with tightness, discharged classically *elsewhere* by
Bochner–Minlos + Daniell–Kolmogorov and NOT reconstructed here.  It is an OPTIONAL
packaging downstream of the functional continuum target
(`Continuum.FunctionalContinuumTarget`), not a Jaffe–Witten input.  DELIBERATELY
UNINHABITED. -/
abbrev MinlosContinuumLift : Type := CitedMinlosLift

/-- The re-export is the same object as the Clay continuum-existence structure —
no new content, purely an aliasing interface. -/
theorem minlosContinuumLift_eq_clay :
    MinlosContinuumLift = ClayContinuumExistence := rfl

/-- **Conditional projection (axiom-clean): the tightness modulus.**  GIVEN a
hypothetical inhabitant of the cited-classical lift, its continuum tightness rate
is recovered as explicit data. No inhabitant is asserted — this is the honest
"if the classical input were supplied, here is the witness it carries" wire. -/
def tightnessRateOf (h : MinlosContinuumLift) : Nat → Q' :=
  h.tightnessRate

/-- **Conditional projection (axiom-clean): tightness rate nonnegativity.**  The
recovered tightness modulus is genuinely controlling (each value nonnegative),
GIVEN the hypothetical inhabitant. -/
theorem tightnessRateOf_nonneg (h : MinlosContinuumLift) :
    ∀ n : Nat, (0 : Q') ≤ tightnessRateOf h n :=
  h.tightnessRate_nonneg

-- NO inhabitant of `MinlosContinuumLift` is provided in this file, by design.
-- It is an OPTIONAL classical corollary (σ-additive measure packaging) downstream
-- of the functional continuum target, NOT a required Jaffe–Witten / OS input; the
-- OPEN continuum obligation is the functional `a → 0` modulus
-- (`Continuum.FunctionalContinuumTarget`), not this σ-additive lift.

end YMGap.Classical.MinlosQuarantine

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Classical.MinlosQuarantine.minlosContinuumLift_eq_clay
#print axioms YMGap.Classical.MinlosQuarantine.tightnessRateOf
#print axioms YMGap.Classical.MinlosQuarantine.tightnessRateOf_nonneg
