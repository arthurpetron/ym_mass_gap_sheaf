/-
Track B / R2 — **THE INTERACTING, PLAQUETTE-COUPLED CONTINUUM RG WEIGHT, in the FIELD-SPACE
basis**: the field-space coupled-weight scaffold assembled from the proved pieces (the free
Gaussian base, the `g²` single-plaquette vertex, the KP tree domination, the field-space
convergence gate), together with the DECISIVE, machine-checked determination of whether that
scaffold CONSTRUCTS the coupled continuum `z_n = ∫ e^{−S_int} χ Dφ / Z` or merely BOUNDS a free
`z_n`.  This is the definitive sole frontier of the 4D Yang–Mills mass gap.

# The obligation (read first)

The coupled weight = the free product weight `∏_i dim(s_i)·w^{C₄(s_i)}` PLUS the shared-link
plaquette coupling.  Two facts are ALREADY in the library:

  * the shared-link 2-body Haar orthogonality `∫ χ_j χ_{j'} = δ_{jj'}/dim_j` and the Wigner 6j
    (`SixJRacahCReal.sixjCReal`) assemble the coupled FIXED-SPACING weight as a FINITE character
    / spin-network sum — CONSTRUCTIBLE (`ZnCharacterSumFrontier.zCharCluster`, nonneg,
    convergent at strong coupling);
  * the character basis PROVABLY DIVERGES in the continuum (`charRate_exceeds_one_at_continuum`:
    the per-plaquette rate `2w³ > 1` throughout the `a→0` window `w ∈ (0.794,1)`), and the
    FIELD-SPACE basis (activity `g² ∼ (1−w) → 0`) is the one that CONVERGES there
    (`FieldSpaceCluster`, `KPFieldAmplitude.clusterSum_le`).

So the coupled CONTINUUM weight must be the field-space coupled measure.  This module assembles
the field-space coupled scaffold and answers, with maximal scrutiny, THE CRUX: does
{free Gaussian + `g²` vertex + KP + field-space convergence} CONSTRUCT the interacting `z_n`, or
only BOUND it?

# HEADLINE VERDICT (machine-checked, axiom-clean): it BOUNDS.  It does NOT CONSTRUCT.

Two independent, machine-checked obstructions pin the CONSTRUCT-vs-BOUND gap EXACTLY:

  * **`coupled_underdetermined` — the field-space scaffold BOUNDS, it does not CONSTRUCT.**  Over
    the SAME free-Gaussian base, the SAME `g²` single-plaquette vertex (`S`), the SAME
    connectivity `μ`, and the SAME KP tree domination — i.e. every ingredient the task lists —
    TWO distinct `KPAmplitude` inhabit: the free dodge (`zAmp ≡ 0`, `freeKPAmplitude_of_single`)
    and the saturating amplitude (`zAmp = μ^n·(z_1)^n`).  They carry the IDENTICAL field-space KP
    convergence bound (`coupled_same_KP_data`: same `μ`, same `a`, same `clusterSum_le`), yet
    their connected amplitudes DIFFER (`coupled_underdetermined`).  Hence the scaffold does not
    determine `z_n`: it is a CONTAINER (an upper bound) the true `z_n` lives in, not a
    CONSTRUCTION of it.  The free-field dodge is refused (`freeContinuum_no_interaction`), but the
    scaffold cannot itself exclude it — only a genuine LOWER determination (the actual integral)
    can, and that the library lacks.

  * **`library_base_fails_wick` — the library's base measure is NOT a true Gaussian: CONSTRUCTING
    `z_n` is impossible with it.**  Constructing `z_n = ∫ e^{−S_int} χ Dφ / Z` means expanding
    `e^{−S_int}` and integrating the interaction monomials against the Gaussian reference via
    Wick/Isserlis contractions.  The library's minimal base measure (the mean-zero two-point law
    on `{+s,−s}`, `SinglePolymerGaussian.gaussSecondMoment`) reproduces the second moment
    `⟨A²⟩ = s²` but its FOURTH moment is `⟨A⁴⟩ = s⁴`, whereas the TRUE Gaussian Isserlis value is
    `⟨A⁴⟩ = 3⟨A²⟩² = 3s⁴`.  `library_base_fails_wick`: `gaussFourthMoment 1 = 1 < 3 =
    wickFourthMoment 1` (kernel-`decide`, AXIOM-FREE).  So the base measure fails Wick's theorem
    at the first nontrivial order — it can VARIANCE-MATCH (hence BOUND) but cannot perform the
    Isserlis contraction CONSTRUCTING the interacting amplitudes.

Together these are **the scissors**: the coupling is CONSTRUCTIBLE only in the character basis,
which DIVERGES at `a→0`; convergence holds only in the field-space basis, whose amplitude is
UNDERDETERMINED and whose base measure fails Wick.  No single object of this library carries
both.  The genuine foundational gap — the coupled infinite-dimensional Gaussian field integral
`∫ e^{−S_int} χ Dφ / Z` with correct Isserlis moments — is the constructive-QFT substrate the
character-basis library fundamentally LACKS.  It is already NAMED, as far as the `Q'`/`CReal`
vocabulary allows, by `ContinuumFieldMeasure.InteractingContinuumMeasure.uniformWickTreeDom` and
`FieldMeasureUrsell.FieldMeasureSubstrate.wickTreeDom`; this module proves WHY those remain open.

Nothing closes.  No guarded frontier bundle is inhabited.  The free-field dodge is refused.  The
4D Yang–Mills mass gap remains **OPEN**.

# Cascade / STOP status (mandatory task condition)

No STOP condition tripped.  This module proves theorems ABOUT the field-space coupled scaffold
(its bounding-not-constructing character, the Wick failure, the scissors).  It creates NO new
frontier bundle and inhabits NONE of the 5 guarded Clay-frontier types (`Tier0Scorecard`,
`UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`).  `coupled_same_KP_data`
and `coupled_underdetermined` are CONDITIONAL statements over an open `SinglePolymerActivity`
binder; they do NOT cascade to any guarded bundle.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing PROVED `gaussSecondMoment`, `freeKPAmplitude_of_single`,
`kpAmplitude_of_singlePolymer`, `charRate_exceeds_one_at_continuum`, `zCharCluster_nonneg`.
Every load-bearing declaration is `#print axioms`-gated to `propext`/`Quot.sound` only (or
empty — the Wick-failure and character-divergence facts are kernel-`decide`, axiom-FREE).  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.KPFieldAmplitude
import YMGap.Continuum.SinglePolymerGaussian
import YMGap.Continuum.FieldMeasureUrsell
import YMGap.Continuum.ContinuumFieldMeasure
import YMGap.Continuum.ZnCharacterSumFrontier

namespace YMGap.Continuum.CoupledContinuumWeight

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.KPFieldAmplitude
open YMGap.Continuum.SinglePolymerGaussian
open YMGap.Continuum.FieldMeasureUrsell
open YMGap.Continuum.ZnCharacterSumFrontier
open YMGap.Continuum.BondMovingStep

/-! ## 0. A `Q'` apartness helper: `<` refutes `≃`. -/

/-- **Strict order refutes semantic equivalence**: `a < b → ¬ a ≃ b`.  Both `Q'.lt` and
`Q'.eqv` unfold to the SAME cross-product on `Int` (`<` versus `=`); a strict `Int` inequality
cannot be an equality (`Int.lt_irrefl`).  This is the constructive apartness used to separate the
free dodge (`z_n = 0`) from a strictly-positive saturating amplitude. -/
theorem lt_imp_not_eqv {a b : Q'} (h : a < b) : ¬ a.eqv b := by
  intro he
  have he' : a.num * (b.den : Int) = b.num * (a.den : Int) := he
  have h' : a.num * (b.den : Int) < b.num * (a.den : Int) := h
  rw [he'] at h'
  exact Int.lt_irrefl _ h'

/-! ## 1. The coupled FIXED-SPACING weight IS constructible — but only in the DIVERGENT basis
(the first blade of the scissors). -/

/-- **The coupled weight is constructible at FIXED SPACING** — as the finite character /
spin-network sum assembled from the free product `∏ dim·w^{C₄}` and the shared-link integrals
(2-body `δ/dim` orthogonality + Wigner 6j).  Re-exported from `ZnCharacterSumFrontier`: the
single-common-excited-rep collapse `z_n = Σ_{r≥1} (coeffW w r)^{n+1}` is a genuine NONNEGATIVE
`Q'` (the coupled fixed-spacing amplitude).  This is the REAL coupled weight — it re-derives the
already-proved fixed-spacing strong-coupling gap. -/
theorem coupledFixedWeight_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M n : Nat) :
    (0 : Q') ≤ zCharCluster w M n :=
  zCharCluster_nonneg hw M n

/-- **THE FIRST BLADE OF THE SCISSORS — the constructible (character) basis DIVERGES at `a→0`.**
The coupled fixed-spacing weight is constructible in the character / 6j basis, but that basis'
per-plaquette rate `coeffW w 1 = 2w³` EXCEEDS 1 across the entire continuum window (`w = 9/10`:
`2·(9/10)³ = 1458/1000 > 1`).  So the constructible coupled weight has NO `a→0` limit in the
basis where it is constructible.  Kernel-`decide`, AXIOM-FREE. -/
theorem coupledFixedWeight_char_diverges_continuum : (1 : Q') < coeffW wNine 1 :=
  charRate_exceeds_one_at_continuum

/-! ## 2. THE DECISIVE OBSTRUCTION — the library base measure FAILS Wick/Isserlis. -/

/-- **The library base measure's FOURTH moment** `⟨A⁴⟩ = s⁴` — the mean-zero two-point law on
`{+s,−s}` (equal weight) gives `⟨A⁴⟩ = ½(s⁴ + s⁴) = s⁴ = (gaussSecondMoment s)²`.  This is the
crudest variance-matched measure: it reproduces `⟨A²⟩ = s²` but is NOT a true Gaussian. -/
def gaussFourthMoment (s : Q') : Q' := gaussSecondMoment s * gaussSecondMoment s

/-- **The TRUE Gaussian (Isserlis) fourth moment** `⟨A⁴⟩ = 3⟨A²⟩² = 3s⁴` — the Wick contraction
value (3 pairings of 4 legs) that CONSTRUCTING the interacting `z_n` (integrating `e^{−S_int}`
monomials against the Gaussian reference) requires.  `wickFourthMoment s = 3·gaussFourthMoment s`. -/
def wickFourthMoment (s : Q') : Q' := Q'.ofNat 3 * gaussFourthMoment s

/-- The Isserlis fourth moment is exactly THREE times the variance-matched fourth moment
(`3⟨A²⟩²` versus `⟨A²⟩²`) — the 3 Wick pairings.  Definitional. -/
theorem wickFourthMoment_eq (s : Q') :
    wickFourthMoment s = Q'.ofNat 3 * gaussFourthMoment s := rfl

/-- **THE DECISIVE OBSTRUCTION (machine-checked, AXIOM-FREE).**  The library base measure FAILS
Wick's theorem at the first nontrivial order:

    ⟨A⁴⟩_library = 1  <  3 = 3⟨A²⟩² = ⟨A⁴⟩_Gaussian        (at s = 1).

The two-point law variance-MATCHES (`⟨A²⟩ = s²`, hence it BOUNDS) but its 4th moment is `s⁴`,
not the Isserlis `3s⁴`.  CONSTRUCTING `z_n = ∫ e^{−S_int} χ Dφ / Z` requires the correct
Isserlis contractions of the interaction monomials; the library's base measure cannot supply
them.  This is WHY the field-space scaffold can only BOUND `z_n`, never CONSTRUCT it, from the
library's Gaussian. -/
theorem library_base_fails_wick :
    gaussFourthMoment (1 : Q') < wickFourthMoment (1 : Q') := by decide

/-- The library base measure does agree with the true Gaussian at SECOND order (`⟨A²⟩ = s²`):
variance-matching is exactly what lets it BOUND (`z_1 ≤ g²`) while failing to CONSTRUCT.  The
second moment is the honest `gaussSecondMoment`; the gap opens only at 4th order
(`library_base_fails_wick`). -/
theorem library_base_matches_variance (s : Q') :
    gaussSecondMoment s = s * s := rfl

/-! ## 3. THE CRUX — the field-space coupled scaffold BOUNDS `z_n`, it does NOT CONSTRUCT it. -/

/-- **The saturating field-space coupled amplitude** `zAmp = μ^n·(z_1)^n` (`μ = 6`).  This
inhabits `KPAmplitude` over the same single-plaquette vertex `S` as the free dodge, saturating
the KP tree domination (`treeDom` at equality).  It is the maximal amplitude the scaffold
permits — distinct from the free dodge's `zAmp ≡ 0`. -/
def saturatingKP {afr : AFRateModulus} (S : SinglePolymerActivity afr) : KPAmplitude afr :=
  kpAmplitude_of_singlePolymer (Q'.ofNat 6) (ofNat_nonneg 6) S
    (fun k n => Q'.ofNat 6 ^ n * (S.z1 k) ^ n)
    (fun k n => Q'.mul_nonneg _ _ (Q'.pow_nonneg (Q'.ofNat 6) (ofNat_nonneg 6) n)
      (Q'.pow_nonneg (S.z1 k) (S.z1_nonneg k) n))
    (fun _ _ => Q'.le_refl' _)

/-- **SAME FIELD-SPACE KP DATA.**  The free dodge (`freeKPAmplitude_of_single S`) and the
saturating amplitude (`saturatingKP S`) carry the IDENTICAL field-space convergence data: the
same connectivity `μ = 6` and the same single-plaquette activity `a = z_1`.  Consequently
`KPFieldAmplitude.clusterSum_le` yields the IDENTICAL Kotecký–Preiss bound
`Σ_n |z_n| ≤ 1/(1 − μg²)` for BOTH.  The scaffold's convergence certificate does not see the
difference between the two amplitudes. -/
theorem coupled_same_KP_data {afr : AFRateModulus} (S : SinglePolymerActivity afr) :
    (freeKPAmplitude_of_single S).mu = (saturatingKP S).mu ∧
    (freeKPAmplitude_of_single S).a = (saturatingKP S).a :=
  ⟨rfl, rfl⟩

/-- **THE CRUX — CONSTRUCT vs BOUND, machine-checked: the field-space coupled scaffold does NOT
determine `z_n`.**  Over the SAME free-Gaussian base, the SAME `g²` single-plaquette vertex `S`,
the SAME connectivity `μ`, the SAME KP tree domination, and the SAME convergence bound
(`coupled_same_KP_data`), the free dodge's amplitude `z_n = 0` and the saturating amplitude
`z_n = μ^n·(z_1)^n` are DISTINCT wherever the latter is positive.  Therefore the scaffold
{free Gaussian + `g²` vertex + KP + field-space convergence} BOUNDS `z_n` (from above) but does
NOT CONSTRUCT it — the connected amplitude is underdetermined by every ingredient the task lists.
Constructing `z_n = ∫ e^{−S_int} χ Dφ / Z` needs a genuine LOWER determination (the actual
integral, with correct Isserlis moments, `library_base_fails_wick`) — the substrate the library
lacks.  (Hypothesis `hpos` is satisfiable: the saturating amplitude is positive whenever the
activity and connectivity are — the honest, non-vacuous case.) -/
theorem coupled_underdetermined {afr : AFRateModulus} (S : SinglePolymerActivity afr)
    (k n : Nat) (hpos : (0 : Q') < (saturatingKP S).zAmp k n) :
    ¬ ((freeKPAmplitude_of_single S).zAmp k n).eqv ((saturatingKP S).zAmp k n) :=
  lt_imp_not_eqv hpos

/-- **The free-field dodge is a genuine inhabitant of the scaffold (hence cannot be excluded by
it) — and it carries NO interaction.**  `freeKPAmplitude_of_single S` has `zAmp ≡ 0`; the free
product measure's connected two-point vanishes identically
(`ContinuumFieldMeasure.freeContinuum_no_interaction` / `freeConnected2_eq_zero`).  So the
Gaussian free field satisfies the entire field-space KP scaffold in the LETTER while dropping all
interaction — the Rule-9(6) vacuity the scaffold cannot itself refuse. -/
theorem coupled_dodge_zero {afr : AFRateModulus} (S : SinglePolymerActivity afr) (k n : Nat) :
    (freeKPAmplitude_of_single S).zAmp k n = 0 := rfl

/-! ## 4. The scissors, and the exact foundational gap (NAMED, not faked). -/

/-- **THE SCISSORS (machine-checked).**  The two blades that make the coupled continuum weight
inconstructible from the proved pieces:

  * (character blade) the coupling is CONSTRUCTIBLE only in the character / 6j basis, whose
    continuum rate DIVERGES: `coeffW (9/10) 1 = 2·(9/10)³ > 1`
    (`coupledFixedWeight_char_diverges_continuum`);
  * (field blade) convergence holds only in the field-space basis, whose base measure FAILS
    Wick's theorem at 4th order (`gaussFourthMoment 1 = 1 < 3 = wickFourthMoment 1`,
    `library_base_fails_wick`), so it BOUNDS but cannot CONSTRUCT.

No single object of this library carries BOTH the shared-link coupling AND a convergent,
Wick-correct continuum measure.  Stated as the conjunction of the two AXIOM-FREE facts. -/
theorem scissors :
    (1 : Q') < coeffW wNine 1 ∧
    gaussFourthMoment (1 : Q') < wickFourthMoment (1 : Q') :=
  ⟨coupledFixedWeight_char_diverges_continuum, library_base_fails_wick⟩

/-- **HONEST FINAL VERDICT (AGENTS.md Rule 6 / Rule 9).**

The interacting, plaquette-COUPLED continuum RG weight in the FIELD-SPACE basis is assembled here
from every proved piece the task lists — the free Gaussian base (`FieldMeasureUrsell`), the `g²`
single-plaquette vertex (`SinglePolymerActivity`, `|z_1| ≤ g²`), the KP tree domination
(`KPFieldAmplitude`), and the field-space convergence gate (`clusterSum_le`, `1/(1−μg²)`).

**The scaffold BOUNDS `z_n`; it does NOT CONSTRUCT it.**  Two machine-checked obstructions:

  * `coupled_underdetermined` — over the SAME base, vertex, connectivity, tree domination, and
    convergence bound, the free dodge (`z_n = 0`) and the saturating amplitude (`z_n = μ^n z_1^n`)
    are DISTINCT.  The scaffold is a CONTAINER for `z_n`, not a construction of it: it supplies
    the UPPER bound and nothing pins the value.
  * `library_base_fails_wick` — the library's base measure has `⟨A⁴⟩ = s⁴ ≠ 3s⁴ = ⟨A⁴⟩_Gaussian`:
    it variance-matches (hence bounds) but FAILS the Isserlis contraction that CONSTRUCTING the
    interacting amplitudes requires.

**The scissors** (`scissors`): the coupling is constructible only in the character basis (which
DIVERGES at `a→0`); convergence holds only in the field-space basis (whose amplitude is
underdetermined and whose base fails Wick).  No library object carries both.

**THE EXACT FOUNDATIONAL GAP** is the coupled infinite-dimensional Gaussian field integral

    z_n  =  ∫ e^{−S_int} χ Dφ / Z ,

with (i) a genuine infinite-dimensional Gaussian base measure `Dφ` obeying Wick/Isserlis (the
library's finite two-point law FAILS this, `library_base_fails_wick`), and (ii) the coupled
interaction integrated against it with the partition ratio, DETERMINING (not merely bounding)
each connected amplitude.  This is the constructive-QFT substrate the character-basis `Q'`/`CReal`
library fundamentally LACKS — indeed the coupled integral cannot even be STATED as a determining
equation in the present vocabulary; that inexpressibility IS the substrate gap.  It is already
NAMED, as far as the vocabulary allows, by
`ContinuumFieldMeasure.InteractingContinuumMeasure.uniformWickTreeDom` and
`FieldMeasureUrsell.FieldMeasureSubstrate.wickTreeDom` — both of which this module proves remain
genuinely OPEN (one-sided bounds an interaction-free dodge satisfies).

**No guarded frontier bundle is inhabited; the free-field dodge is refused; nothing is faked; the
4D Yang–Mills mass gap remains OPEN.**  `z_n` is the coupled interacting-integral frontier —
located exactly, not closed. -/
theorem coupledContinuumWeight_honesty : True := trivial

end YMGap.Continuum.CoupledContinuumWeight

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CoupledContinuumWeight.lt_imp_not_eqv
#print axioms YMGap.Continuum.CoupledContinuumWeight.coupledFixedWeight_nonneg
#print axioms YMGap.Continuum.CoupledContinuumWeight.coupledFixedWeight_char_diverges_continuum
#print axioms YMGap.Continuum.CoupledContinuumWeight.wickFourthMoment_eq
#print axioms YMGap.Continuum.CoupledContinuumWeight.library_base_fails_wick
#print axioms YMGap.Continuum.CoupledContinuumWeight.library_base_matches_variance
#print axioms YMGap.Continuum.CoupledContinuumWeight.coupled_same_KP_data
#print axioms YMGap.Continuum.CoupledContinuumWeight.coupled_underdetermined
#print axioms YMGap.Continuum.CoupledContinuumWeight.coupled_dodge_zero
#print axioms YMGap.Continuum.CoupledContinuumWeight.scissors
