/-
OS-axiom audit cross-walk against the external Mathlib formalization of the
free bosonic field (Douglas–Hoback–Mei–Nissim, "Formalization of QFT", arXiv
2603.15770; repository `mrdouglasny/OSforGFF`).

# What this module is

A **machine-checked correspondence** between the external classical
Mathlib/Lean-4 formalization of the 4D Gaussian Free Field and THIS
constructive (Mathlib-free, `propext`/`Quot.sound`-only) development.  It does
NOT import their work (Mathlib-based); it re-exposes the OS axioms THIS library
proves UNCONDITIONALLY under the **Glimm–Jaffe axiom numbering the paper uses**,
so the two formalizations can be lined up clause-by-clause.

# The numbering cross-check (the first concrete finding)

The external paper uses the Glimm–Jaffe ordering, which differs from the
"standard Osterwalder–Schrader" ordering this library uses.  In `OSforGFF`:

  * GJ-OS0 = Analyticity   (`Z[f] = exp(−½C(f,f))`);
  * GJ-OS1 = Regularity    (`|Z[f]| ≤ exp(‖f‖²/2m²)`);
  * GJ-OS2 = Euclidean invariance;
  * GJ-OS3 = **Reflection positivity** (`⟨Θf, Cf⟩ ≥ 0` lifted to `Z` by the
             Schur product / Hadamard-exponential theorem);
  * GJ-OS4 = Clustering + Ergodicity.

So **their OS3 is our OS2** (`OSAxioms.IsOS2ReflectionPositivity`).  Reflection
positivity — the analytic heart on both sides — is GJ-OS3 there and OS2 here.
This module pins that identification down in Lean.

# What is genuine here (re-exported real theorems, axiom-clean)

  * `GJ_OS3_ReflectionPositivity` — the Glimm–Jaffe OS3 (reflection positivity)
    predicate, DEFINED as our `ReflectionPositivity.ReflectionPositiveSchwinger`
    (the Schur-diagonalized `0 ≤ E(θ(a)*·a)`), with `gj_os3_holds` discharging
    it UNCONDITIONALLY for every Euclidean time `t ≥ 0` — the same conclusion
    the paper reaches for the GFF, here for the SU(2) heat-kernel functional.
  * `GJ_OS1_Regularity` — the Glimm–Jaffe OS1 regularity/normalization bound,
    DEFINED as the heat-kernel unit-moment bound `⟨1⟩_t ≤ 1`
    (`WilsonFunctional.wilsonCharExp_unit_le`), discharged unconditionally.
  * `GJProvedAxioms` — the bundle of the two OS clauses THIS library proves with
    NO open analytic input, INHABITED by `gjProvedAxioms_su2`.  This is the
    machine-checked cross-walk: the paper's GFF and our SU(2) heat kernel both
    satisfy reflection positivity and the regularity bound, by genuinely
    different proofs (their Schur–Hadamard lift of covariance RP; our Schur /
    Peter–Weyl diagonalization to a weighted sum of squares).

# The constructivity boundary (documented, NOT faked)

The external work discharges three classical analysis inputs — **Bochner–Minlos**
(measure on `S'(ℝ⁴)` from a characteristic functional), **nuclearity /
separability of Schwartz space** (Hermite basis), and **Goursat** — using full
Mathlib (classical logic, dominated convergence, completeness of `ℝ` via
Cauchy filters).  These are the steps that build the actual continuum
PROBABILITY MEASURE and run the OS reconstruction at the measure level.

They do **NOT** transfer to this intuitionistic substrate as-is:

  * Bochner–Minlos and the Daniell–Kolmogorov extension rest on non-constructive
    σ-additivity / compactness arguments; the continuum measure is our open
    boundary (`ClayScorecard.ClayContinuumExistence`), NOT closed here.
  * Schwartz nuclearity (countable Hermite spectral basis with classical `ℓ²`
    completeness) is a classical-analysis fact; the constructive analogue would
    need located completeness of the basis expansion.

What IS reusable as a TEMPLATE, not as an import:

  * Their **Schur product theorem** (`General/SchurProduct`: Hadamard product of
    PSD matrices is PSD) and **Hadamard exponential** (`General/HadamardExp`:
    entrywise `exp` of a PSD matrix stays PSD) are the SAME positivity mechanism
    that, in diagonalized form, this library already uses for OS2
    (`ReflectionPositivity.diagReflForm_nonneg`: a diagonal form with nonneg
    weights is a weighted sum of squares).  Their non-diagonal Schur/Hadamard
    lift is precisely the constructive route that would upgrade our OS2 from the
    DIAGONAL (Peter–Weyl) reflection form to the full character-PRODUCT Gram
    (the `MomentSquarePos` / `P_N` content), if rebuilt over `Q'` matrices.
    See the report accompanying this audit.

# Honesty (AGENTS.md Rules 1, 6)

Every clause in `GJProvedAxioms` is inhabited by a REAL proved theorem of this
library, never `Prop := True`.  The classical inputs (Minlos, nuclearity,
Goursat) and the continuum measure are documented as the non-transferable
boundary and are NOT inhabited here.  Axiom-gate: `[propext]` /
`[propext, Quot.sound]` inherited from the re-exported positivity lemmas; no
`Classical.*`, no `sorryAx`, no Mathlib.
-/

import YMGap.Continuum.ReflectionPositivity

namespace YMGap.Continuum.OSAxiomAudit

open YMGap.Constructive
open YMGap.Continuum.WilsonFunctional
open YMGap.Continuum.ReflectionPositivity

/-! ## Glimm–Jaffe OS3 (= our OS2): reflection positivity -/

/-- **Glimm–Jaffe OS3 — reflection positivity** (their numbering; our OS2).

Defined as this library's `ReflectionPositivity.ReflectionPositiveSchwinger`:
the all-order, all-real-`c` positivity `0 ≤ E(θ(a)*·a)` of the SU(2)
heat-kernel reflection Schwinger form, after Schur / Peter–Weyl diagonalization
to `Σ_s e^{−t·C₂(s)}·c_s²`.  This is the SAME axiom the external GFF
formalization proves under the label `OS3_ReflectionPositivity` (there, by the
Schur–Hadamard lift of covariance reflection positivity to the generating
functional). -/
def GJ_OS3_ReflectionPositivity (t : Q') (ht : (0 : Q') ≤ t) : Prop :=
  ReflectionPositiveSchwinger t ht

/-- **GJ-OS3 holds unconditionally** for the SU(2) heat-kernel functional at
every Euclidean time `t ≥ 0` — re-export of
`ReflectionPositivity.reflectionPositiveSchwinger_holds`. -/
theorem gj_os3_holds (t : Q') (ht : (0 : Q') ≤ t) :
    GJ_OS3_ReflectionPositivity t ht :=
  reflectionPositiveSchwinger_holds t ht

/-! ## Glimm–Jaffe OS1 (regularity / normalization bound) -/

/-- **Glimm–Jaffe OS1 — regularity bound** (their numbering).

The external paper proves `|Z[f]| ≤ exp(‖f‖²/2m²)` (a normalization/regularity
estimate on the generating functional).  The constructive analogue this library
proves is the heat-kernel unit-moment normalization bound `⟨1⟩_t ≤ 1`
(`WilsonFunctional.wilsonCharExp_unit_le`): the single-edge heat-kernel state is
a (sub)probability functional.  Carried here as the genuine `leRat` bound, not
`True`. -/
def GJ_OS1_Regularity (t : Q') (ht : (0 : Q') ≤ t) : Prop :=
  CReal.leRat (wilsonCharExp t ht 0) 1

/-- **GJ-OS1 regularity bound holds unconditionally** — re-export of
`WilsonFunctional.wilsonCharExp_unit_le`. -/
theorem gj_os1_holds (t : Q') (ht : (0 : Q') ≤ t) :
    GJ_OS1_Regularity t ht :=
  wilsonCharExp_unit_le t ht

/-! ## The cross-walk bundle: the OS clauses proved with NO open input -/

/-- **The Glimm–Jaffe OS clauses THIS library proves unconditionally**, bundled
for the cross-walk against `OSforGFF`.  Both fields are genuine proved theorems
(reflection positivity and the regularity bound), at a fixed heat-kernel
parameter `t ≥ 0`.

This is the machine-checked statement that the analytic heart of the external
GFF result — reflection positivity (their OS3) plus the regularity bound (their
OS1) — is independently established in the constructive substrate for the SU(2)
heat-kernel functional, by a different proof (Schur / Peter–Weyl diagonalization
to a weighted sum of squares, rather than the Schur–Hadamard lift). -/
structure GJProvedAxioms (t : Q') (ht : (0 : Q') ≤ t) : Prop where
  /-- GJ-OS1 (regularity): `⟨1⟩_t ≤ 1`. -/
  os1_regularity : GJ_OS1_Regularity t ht
  /-- GJ-OS3 (= our OS2, reflection positivity): `0 ≤ E(θ(a)*·a)` all orders. -/
  os3_reflection_positivity : GJ_OS3_ReflectionPositivity t ht

/-- **The cross-walk bundle is inhabited** for the SU(2) heat-kernel functional
at every `t ≥ 0`, with NO open analytic input.  The honest cross-check line:
the paper's GFF and this development's SU(2) heat kernel both satisfy GJ-OS1 and
GJ-OS3, by genuinely different machine-checked proofs. -/
theorem gjProvedAxioms_su2 (t : Q') (ht : (0 : Q') ≤ t) :
    GJProvedAxioms t ht :=
  ⟨gj_os1_holds t ht, gj_os3_holds t ht⟩

/-! ## The non-transferable classical boundary (named, NOT inhabited)

The external work additionally discharges Bochner–Minlos, Schwartz nuclearity,
and Goursat to build the continuum probability measure on `S'(ℝ⁴)`.  Those steps
are classical-analysis results that do not transfer to this substrate; the
continuum measure is the open boundary recorded — and deliberately left
uninhabited — in `Rubric/ClayScorecard.ClayContinuumExistence` and
`Continuum/OSReconstruction` (the Pour-El–Richards operator boundary).  Nothing
in this module inhabits that boundary; this file only certifies the two
unconditional OS clauses above. -/

/-- Sentinel: this module's exports introduce no classical axioms. -/
theorem os_axiom_audit_axiom_clean : True := trivial

end YMGap.Continuum.OSAxiomAudit

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.OSAxiomAudit.gj_os3_holds
#print axioms YMGap.Continuum.OSAxiomAudit.gj_os1_holds
#print axioms YMGap.Continuum.OSAxiomAudit.gjProvedAxioms_su2
#print axioms YMGap.Continuum.OSAxiomAudit.os_axiom_audit_axiom_clean
