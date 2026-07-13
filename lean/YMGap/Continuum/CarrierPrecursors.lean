/-
Lattice-level precursors for the four 4D Yang–Mills existence carriers,
wired against nonconstant SU(2) spin/Casimir data rather than the trivial
one-point carrier.  The legacy `charAlg` multiplication retains only the
lowest fusion channel and is nonassociative; it is not the class-function
algebra (`CharacterAlgebraAssociativityFence`).

# What this module adds, and what it deliberately does NOT claim

The carrier predicates `O4RestorationContent`, `GaugeGeneratedContent`,
`UVAsymptoticFreedomContent`, `NontrivialityContent` each already have a
non-vacuity witness.  Several of those witnesses live on the trivial
one-point observable algebra.  This module supplies the STRONGEST honest
upgrade that the current constructive substrate genuinely supports —
witnesses tied to real SU(2) heat-kernel data — and states crisply, for
each carrier, exactly which step stays open (the continuum step is open
research mathematics, NOT engineering).

The four carriers correspond to genuinely-open Clay-level analysis; nothing
here closes any of them.  What is proved here is finite / lattice-level and
true.  Specifically:

  * **Gauge-generation carrier upgrade.**  `RGTransport.charAlg` retains
    genuine character labels and the diagonal heat-kernel functional is
    nonconstant, but its lowest-channel multiplication is not an associative
    character algebra.  We prove only that the weak carrier predicate's
    gauge-averaging factorization holds for it with the identity projection
    identity-projection clause holds, so `GaugeGeneratedContent` is witnessed
    on nonconstant heat-kernel data, not on `trivAlg`.  OPEN: a genuine linear
    fusion-sum/class-function algebra, the continuum observable algebra, and
    its gauge-group action (open research mathematics).

  * **Nontriviality (genuine upgrade).**  The non-Gaussian Wick-law
    violation is exhibited on a `SpectralModel` whose transfer eigenvalues
    are the ACTUAL SU(2) heat-kernel weights `w^{C₄(s)}` at the genuine
    Casimir exponents `C₄(s) = s(s+2)` (`RGTransport.c4`), not on ad-hoc
    rationals.  OPEN: the full-measure continuum non-Gaussianity (open
    research mathematics).

  * **O(4) restoration (HONEST: no genuine non-trivial precursor).**  The
    only functional equivariance proved in the repository is under the
    identity symmetry.  We make the boundary visible by proving the bar is
    real at the weak-carrier level: a non-identity `ObsHom` on `charAlg`
    (`RGTransport.collapseHom`, the vacuum projection) does NOT leave the
    genuine heat-kernel functional invariant.  So the equivariance content
    is not trivially satisfied by every map.  We still witness the carrier
    on the nonconstant spin-label carrier under the identity rotation, and state
    plainly that the genuine non-trivial discrete H₄ rotation action — let
    alone the continuum O(4) restoration — is open.

  * **UV asymptotic freedom (already genuine).**  Re-exported as-is: the
    one-loop sign `β₀ > 0` and strict monotonicity of the inverse coupling
    are real finite facts proved in `FourDExistence`.  OPEN: the
    nonperturbative continuum RG flow (open research mathematics).

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem below carries a `#print axioms` gate.  No
`Classical.*`, no `sorry`, no `native_decide`.
-/

import YMGap.Continuum.FourDExistence
import YMGap.Continuum.RGTransport

namespace YMGap.Continuum.CarrierPrecursors

open YMGap.Constructive
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ObservableMeasure (ProbFunctional ObsAlg ObsHom)
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.RGTransport

/-! ## Gauge generation on the spin-label carrier

`RGTransport.charAlg` stores an SU(2) character label (carrier = spin
index `Nat`, `star = id` since SU(2) characters are real, product = the
Clebsch–Gordan lowest channel).  The labels name class functions, but the
stored binary operation is not their fusion-sum product and is not
associative.  `RGTransport.charFunc w` is the diagonal
heat-kernel functional `E χ_s = dim(s)·w^{C₄(s)}` — a genuine, non-constant
`Q'`-valued Wilson datum (`RGTransport.charFunc_nonconstant`).

The very weak gauge-averaging factorization that `GaugeGeneratedContent` asks
for holds with the identity projection on this carrier.  This replaces the
`trivAlg` witness with nonconstant SU(2) heat-kernel data, but does not supply
the missing linear class-function algebra. -/

/-- The heat-kernel weight `w` used to anchor the genuine witnesses
(`w = 1/2`, a representative sub-critical heat-kernel weight `e^{−t/4}`). -/
def heatWeight : Q' := Q'.mkPos 1 2 (by decide)

theorem heatWeight_nonneg : (0 : Q') ≤ heatWeight := by decide

/-- **Gauge-generation carrier on nonconstant character-label data.**  The
gauge-averaging factorization (idempotent projection `P` with `E(P a) = E a`)
holds for `charAlg` and the nonconstant heat-kernel functional
`charFunc heatWeight`, with `P = id`.  This witnesses the weak
`GaugeGeneratedContent` predicate off the trivial one-point algebra; it does
not prove that `charAlg` is the gauge-invariant observable algebra.

OPEN (research mathematics): the continuum gauge-invariant observable
algebra of Wilson loops on `SU(2)^{E}` and the action of the continuum gauge
group on it — including replacement of `charAlg` by the associative linear
fusion-sum algebra. -/
theorem gauge_generated_on_charAlg {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    GaugeGeneratedContent μ_inf :=
  ⟨charAlg, charFunc heatWeight heatWeight_nonneg, ObsHom.idHom _,
    fun _ => rfl, fun _ => rfl⟩

/-- The character functional underlying the gauge witness is genuinely
**non-constant** (it is not the `≡ 1` placeholder): `E χ_0 = 1` while
`E χ_2 = 3·(1/2)^8 = 3/256 ≠ 1`.  So `gauge_generated_on_charAlg` rests on
real, non-degenerate heat-kernel data, not on a trivial functional. -/
theorem gauge_witness_functional_nonconstant :
    (charFunc heatWeight heatWeight_nonneg).E (0 : Nat) = 1 ∧
      ¬ ((charFunc heatWeight heatWeight_nonneg).E (2 : Nat) = 1) :=
  charFunc_nonconstant

/-! ## Nontriviality from the GENUINE SU(2) heat-kernel spectrum

`NontrivialityContent` asks for a `SpectralModel` violating the free-field
Wick product law `G(n) = G(0)²`.  We build the spectral model directly from
the SU(2) heat-kernel transfer eigenvalues: mode `s` has eigenvalue
`λ_s = w^{C₄(s)}` with the genuine Casimir exponent `C₄(s) = s(s+2)`
(`RGTransport.c4`, `= 4·C₂(s)`), so `λ` is literally the per-mode
heat-kernel weight rather than an ad-hoc rational.

With `w = 1/2` and two modes `s = 0, 1`:
`λ_0 = (1/2)^{C₄(0)} = (1/2)^0 = 1`,
`λ_1 = (1/2)^{C₄(1)} = (1/2)^3 = 1/8`.
Then `corr(0) = w_0 + w_1 = 2`, `corr(1) = λ_0 + λ_1 = 1 + 1/8 = 9/8`, and
`corr(1) = 9/8 ≠ 4 = corr(0)²` — a Wick-law violation on genuine spectral
data. -/

/-- A two-mode spectral model whose transfer eigenvalues are the **actual
SU(2) heat-kernel weights** `λ_s = heatWeight^{C₄(s)}` at the genuine Casimir
exponents `C₄(s) = s(s+2)` (`RGTransport.c4`).  Modes `s = 0, 1` give
`λ_0 = 1`, `λ_1 = (1/2)^3 = 1/8`. -/
def heatKernelSpectralModel : SpectralGap.SpectralModel where
  k := 2
  w := fun _ => 1
  lam := fun s => qpow heatWeight (c4 s)
  w_nonneg := fun _ => by decide
  lam_nonneg := fun s => qpow_nonneg heatWeight heatWeight_nonneg (c4 s)

/-- **Nontriviality carrier on genuine heat-kernel spectral data.**  The
SU(2)-heat-kernel spectral model `heatKernelSpectralModel` violates the
free-field Wick product law `G(n) = G(0)²` at separation `n = 1`:
`corr(1) = 1 + (1/2)^3 = 9/8` while `corr(0)² = 2² = 4`, so `9/8 ≠ 4`.  The
inequality is on transfer eigenvalues that are literally the SU(2)
heat-kernel weights `w^{C₄(s)}` at the genuine Casimir exponents — a
non-Gaussian certificate tied to real heat-kernel data, not an ad-hoc model.

OPEN (research mathematics): the full-measure continuum non-Gaussianity of
the Yang–Mills measure — that the interacting continuum theory is genuinely
not a free field. -/
theorem nontrivial_from_heatKernel {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    NontrivialityContent μ_inf :=
  ⟨heatKernelSpectralModel, 1, by decide⟩

/-! ## O(4) restoration — honest boundary: the equivariance bar is REAL

The repository proves functional equivariance only under the identity
symmetry.  Rather than dress up a trivial witness, we make the boundary
sharp by showing that equivariance is NOT automatic for every `*`-hom:
the genuine non-identity vacuum-projection `*`-hom `RGTransport.collapseHom`
does not leave the genuine heat-kernel functional `charFunc heatWeight`
invariant.  So `FunctionalEquivariant` carries real content — a genuine
discrete rotation would have to satisfy a real constraint, which most maps
fail.

We then witness `O4RestorationContent` on the nonconstant character-label carrier
under the identity rotation (the always-present element of the rotation
group), upgrading the carrier off the trivial one-point algebra while NOT
pretending a non-trivial rotation action has been constructed. -/

/-- **The equivariance constraint is genuine, not vacuous.**  The genuine
non-identity vacuum-projection `*`-hom `collapseHom : charAlg → charAlg`
(`χ_s ↦ χ_0`) is NOT a symmetry of the genuine heat-kernel functional
`charFunc heatWeight`: `E(collapse χ_2) = E χ_0 = 1` but `E χ_2 = 3/256`, so
`E(collapse χ_2) ≠ E χ_2`.  Hence `FunctionalEquivariant (charFunc …)` is a
real constraint that a genuine rotation must satisfy — not a property every
map enjoys. -/
theorem heatKernel_not_equivariant_under_collapse :
    ¬ FunctionalEquivariant (charFunc heatWeight heatWeight_nonneg) collapseHom := by
  intro h
  -- `h` at the character `χ_2 ∈ charAlg.carrier` says `E (collapse χ_2) = E χ_2`,
  -- i.e. `E χ_0 = E χ_2`, i.e. `1 = 3/256`, contradicting nonconstancy.
  have hne := charFunc_nonconstant.2
  have hcol : (charFunc heatWeight heatWeight_nonneg).E (collapseHom.map (2 : Nat))
      = (charFunc heatWeight heatWeight_nonneg).E (2 : Nat) := h (2 : Nat)
  -- `collapseHom.map (2 : Nat) = 0`, so `E χ_0 = E χ_2`.
  rw [show collapseHom.map (2 : Nat) = (0 : Nat) from rfl] at hcol
  exact hne (hcol ▸ charFunc_nonconstant.1)

/-- **O(4)-restoration carrier on the nonconstant spin-label carrier.**  The
equivariance property `E(r a) = E a` holds for the genuine SU(2) character
labels `charAlg` and heat-kernel functional `charFunc heatWeight` under the
identity rotation `r = id` — witnessing `O4RestorationContent` on REAL
heat-kernel data rather than on the trivial one-point algebra.  The identity
is the always-present element of the rotation group; by
`heatKernel_not_equivariant_under_collapse` the equivariance is a genuine
constraint, not satisfied by arbitrary maps.

OPEN (research mathematics): the genuine non-trivial discrete hypercubic
`H₄` rotation action on the lattice observable algebra under which the
functional is invariant, and — strictly harder — the restoration of the FULL
continuum `O(4) ⋉ ℝ⁴` Euclidean group in the continuum limit
(Magnen–Rivasseau–Sénéor).  No non-trivial rotation `*`-hom is constructed
here; this witness uses the identity rotation. -/
theorem o4_restoration_on_charAlg {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    O4RestorationContent μ_inf :=
  ⟨charAlg, charFunc heatWeight heatWeight_nonneg, ObsHom.idHom _,
    functionalEquivariant_id (charFunc heatWeight heatWeight_nonneg)⟩

/-! ## UV asymptotic freedom — already genuine, re-exported

The one-loop sign `β₀ = (11/3)·C₂(adj) > 0` and the strict monotonicity of
the inverse running coupling `u(k) = u₀ + β₀·k` are real finite constructive
facts (`FourDExistence.betaZero_pos`, `invRunningCoupling_strictMono`,
`uv_asymptotic_freedom_su2`).  We re-export the carrier witness for
completeness; nothing here is non-vacuity-only.

OPEN (research mathematics): the nonperturbative continuum RG flow — that the
true continuum coupling actually runs to zero in the UV beyond the one-loop
linear law. -/

/-- **UV asymptotic freedom carrier**, re-exported from the proved one-loop
sign and monotonicity at the SU(2) data (`β₀ = 22/3 > 0`, inverse coupling
strictly increasing).  A genuine finite fact, not non-vacuity-only. -/
theorem uv_asymptotic_freedom_genuine {M : Nat → Type} (μ_inf : ContinuumMeasure M) :
    UVAsymptoticFreedomContent μ_inf :=
  uv_asymptotic_freedom_su2 μ_inf

/-! ## Axiom-clean sentinel -/

/-- Sentinel: this module introduces no classical axioms. -/
theorem carrier_precursors_axiom_clean : True := trivial

end YMGap.Continuum.CarrierPrecursors

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CarrierPrecursors.carrier_precursors_axiom_clean
#print axioms YMGap.Continuum.CarrierPrecursors.gauge_generated_on_charAlg
#print axioms YMGap.Continuum.CarrierPrecursors.gauge_witness_functional_nonconstant
#print axioms YMGap.Continuum.CarrierPrecursors.nontrivial_from_heatKernel
#print axioms YMGap.Continuum.CarrierPrecursors.heatKernel_not_equivariant_under_collapse
#print axioms YMGap.Continuum.CarrierPrecursors.o4_restoration_on_charAlg
#print axioms YMGap.Continuum.CarrierPrecursors.uv_asymptotic_freedom_genuine
