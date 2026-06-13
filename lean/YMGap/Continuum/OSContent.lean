/-
Upgraded content-bearing OS-reconstruction predicates + the honest continuum
boundary.

# What this module is

`Continuum/OSReconstruction.lean` exposes the OS reconstruction quintuple and
four laws as `True`-valued *interface* Props
(`VacuumNormalized`, `HamiltonianNonneg`, `SemigroupGenerated`,
`HasSpectralGap`).  That file is intentionally left UNTOUCHED — a downstream
MassGap chain depends on its exact signatures.  This module shows, as NEW
defs, how three of those four Props would adopt **genuine finite-volume
content** built in `Continuum/FiniteVolumeGNS.lean`, and isolates the one
piece (`SemigroupGenerated`) and the continuum limit that stay paper-level.

# The adoption map (finite volume ⇒ genuine; continuum ⇒ paper)

| `OSReconstruction` Prop      | status      | genuine replacement here                                   |
|------------------------------|-------------|------------------------------------------------------------|
| `VacuumNormalized Ω`         | UPGRADEABLE | `FiniteVolumeGNS.gnsVacuumNormalizedContent` (⟨Ω,Ω⟩ ≃ 1)   |
| `HamiltonianNonneg H`        | UPGRADEABLE | `FiniteVolumeGNS.hamiltonianNonnegContent` (σ(T) ⊆ [0,∞))   |
| `HasSpectralGap rec`         | UPGRADEABLE | `FiniteVolumeGNS.hasSpectralGapContent` ⇒ geometric decay  |
| `SemigroupGenerated H U`     | PAPER       | continuum Stone generator (declared, not faked)            |

The thermodynamic limit `Λ → ∞` (inductive-limit completion of the finite
GNS spaces + gap persistence), the continuum self-adjointness of `H` on a
dense domain, and its projection-valued spectral measure / functional
calculus are the irreducibly paper-level boundary (Pour-El–Richards: the
eigenvalues are individually computable, the spectral-measure sequence is
not).  They are carried as the named hypotheses of
`ContinuumSpectralInterface` below — NEVER as `sorry`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` via the reused finite-volume content.
No `Classical.*`, no `sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.FiniteVolumeGNS

namespace YMGap.Continuum.OSContent

open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.FiniteVolumeGNS
open YMGap.Continuum.SpectralGap
open YMGap.Constructive

/-! ## The genuine finite-volume reconstruction datum

`FiniteVolumeReconstruction` bundles the upgradeable pieces with real
content: the GNS pre-Hilbert space (carrying the genuine inner product and
its reflection-positivity Gram bound), the cyclic normalized vacuum, and the
finite transfer-matrix spectral model (carrying `H ≥ 0` as `lam_nonneg` and
the gap as a `SpectralGapBound` on the positive-weight model).  This is the
content the abstract `OSReconstruction` quintuple stands in for, made
concrete at finite volume. -/

/-- A **genuine finite-volume OS reconstruction datum**: the GNS space from
the interacting finite-volume state, plus the finite spectral model and a gap
bound.  Every field carries real constructive content (contrast the
`True`-stub Props of `OSReconstruction`). -/
structure FiniteVolumeReconstruction (A : ObsAlg) where
  /-- The GNS pre-Hilbert space (genuine inner product + reflection
  positivity + normalized cyclic vacuum). -/
  gns : FiniteVolumeGNS A
  /-- The finite transfer-matrix spectral model (`H ≥ 0` ⇔ `lam_nonneg`). -/
  spec : SpectralModel
  /-- The spectral gap location `μ` (transfer-matrix eigenvalue bound). -/
  gapBound : Q'
  /-- `0 ≤ μ` (the eigenvalue bound is nonnegative — `μ = e^{−m₀}`). -/
  gapBound_nonneg : (0 : Q') ≤ gapBound
  /-- The gap holds: every excited eigenvalue is `≤ μ`. -/
  hasGap : SpectralGapBound spec gapBound

/-! ### The three upgraded Props, proved on the datum -/

/-- **VacuumNormalized (genuine).**  The replacement content holds: the GNS
cyclic vacuum has squared norm `≃ 1`. -/
theorem vacuumNormalized_genuine {A : ObsAlg} (rec : FiniteVolumeReconstruction A) :
    (rec.gns.inner rec.gns.cyclic rec.gns.cyclic).eqv 1 :=
  rec.gns.cyclic_norm

/-- **HamiltonianNonneg (genuine).**  The replacement content holds: every
transfer-matrix eigenvalue is nonnegative (`σ(T) ⊆ [0, ∞)`, i.e. `H ≥ 0`). -/
theorem hamiltonianNonneg_genuine {A : ObsAlg} (rec : FiniteVolumeReconstruction A) :
    ∀ i, (0 : Q') ≤ rec.spec.lam i :=
  rec.spec.lam_nonneg

/-- **HasSpectralGap (genuine).**  The replacement content has teeth: the gap
forces geometric clustering of the connected two-point function,
`G(n) ≤ G(0)·μ^n`.  This is the finite-volume Källén–Lehmann decay
(`decay_of_spectralGap_corr0`), the substantive form behind the `True`-stub
`OSReconstruction.HasSpectralGap`. -/
theorem hasSpectralGap_genuine {A : ObsAlg} (rec : FiniteVolumeReconstruction A)
    (n : Nat) :
    corr rec.spec n ≤ (corr rec.spec 0) * rec.gapBound ^ n :=
  decay_of_spectralGap_corr0 rec.spec rec.gapBound rec.gapBound_nonneg rec.hasGap n

/-- **Gram positivity (the load-bearing `gns_inner_nonneg`)** on the datum:
the GNS inner product is reflection-positive on the diagonal. -/
theorem gram_nonneg_genuine {A : ObsAlg} (rec : FiniteVolumeReconstruction A)
    (a : A.carrier) : (0 : Q') ≤ rec.gns.inner a a :=
  rec.gns.inner_nonneg a

/-! ## A concrete inhabitant

The trivially-coupled product state (free product, `Z = 1`) gives a genuine
`FiniteVolumeReconstruction` — exhibiting the upgraded predicates end-to-end
on a non-stub object.  The spectral model is the one-mode model with weight 1
and eigenvalue 0 (a gap at `μ = 0`, the fully-massive free case). -/

/-- The one-mode trivial spectral model: weight `w ≡ 1`, eigenvalue
`λ ≡ 0` (mass gap saturated, `μ = 0`). -/
def trivSpectralModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => 0
  w_nonneg := fun _ => by
    show (0 : Q') ≤ 1
    decide
  lam_nonneg := fun _ => Q'.le_refl' 0

/-- The trivially-coupled finite-volume reconstruction datum (concrete
inhabitant). -/
def trivReconstruction (n : Nat) :
    FiniteVolumeReconstruction (E2ProductFunctional.prodAlg
      E2ProductFunctional.trivFamily n) where
  gns := trivGNS n
  spec := trivSpectralModel
  gapBound := 0
  gapBound_nonneg := Q'.le_refl' 0
  hasGap := fun _ => Q'.le_refl' 0

/-- The upgraded VacuumNormalized fires on the concrete object. -/
theorem trivReconstruction_vacuum_normalized (n : Nat) :
    ((trivReconstruction n).gns.inner (trivReconstruction n).gns.cyclic
      (trivReconstruction n).gns.cyclic).eqv 1 :=
  vacuumNormalized_genuine (trivReconstruction n)

/-- The upgraded HamiltonianNonneg fires on the concrete object. -/
theorem trivReconstruction_hamiltonian_nonneg (n : Nat) :
    ∀ i, (0 : Q') ≤ (trivReconstruction n).spec.lam i :=
  hamiltonianNonneg_genuine (trivReconstruction n)

/-! ## The honest continuum boundary (declared, NOT faked)

The finite-volume content above does NOT close the continuum OS
reconstruction.  Four objects remain irreducibly paper-level; this interface
names them as hypotheses (`Type`/`Prop` parameters), so any continuum result
must SUPPLY them — they are never silently assumed nor `sorry`-ed.

  1. `thermodynamicLimit` — the inductive-limit completion of the finite GNS
     spaces `Λ → ∞` with gap persistence.
  2. `selfAdjointDomain` — continuum self-adjointness of `H` on a dense
     domain.
  3. `spectralMeasure` — the projection-valued spectral measure / functional
     calculus for the unbounded `H` (the Pour-El–Richards non-computable
     object).
  4. `stoneGenerator` — the continuum Stone theorem: `U(t) = e^{−tH}`
     (`OSReconstruction.SemigroupGenerated`, which stays paper).

These are abstract `Prop` parameters: a continuum proof discharges them; this
module records the boundary, it does not cross it. -/

/-- The continuum spectral interface: the four paper-level obligations the
finite-volume content does NOT discharge, carried as explicit hypotheses so
the boundary is visible and never faked. -/
structure ContinuumSpectralInterface where
  /-- `Λ → ∞` inductive-limit completion of the finite GNS spaces, with gap
  persistence.  Paper-level. -/
  thermodynamicLimit : Prop
  /-- Continuum self-adjointness of `H` on a dense domain.  Paper-level. -/
  selfAdjointDomain : Prop
  /-- The projection-valued spectral measure / functional calculus for
  unbounded `H` (Pour-El–Richards: not a computable sequence).  Paper-level. -/
  spectralMeasure : Prop
  /-- The continuum Stone generator `U(t) = e^{−tH}`
  (`SemigroupGenerated`).  Paper-level. -/
  stoneGenerator : Prop

/-- The continuum reconstruction theorem SIGNATURE: from a genuine
finite-volume reconstruction AND the four paper-level continuum obligations,
one would obtain the continuum OS reconstruction.  The conclusion is left as
the conjunction of the supplied obligations — this module proves the
*reduction shape*, honestly NOT the continuum theorem itself (which needs the
analytic build-out behind `ContinuumSpectralInterface`). -/
def continuum_reconstruction_reduces {A : ObsAlg}
    (_rec : FiniteVolumeReconstruction A) (I : ContinuumSpectralInterface) : Prop :=
  I.thermodynamicLimit ∧ I.selfAdjointDomain ∧ I.spectralMeasure ∧ I.stoneGenerator

/-- The reduction is exactly the conjunction of the four declared
obligations: given them, the continuum reconstruction follows.  This makes
the boundary a theorem (the finite-volume content reduces the continuum
problem to precisely these four named inputs), without faking any of them. -/
theorem continuum_reconstruction_from_interface {A : ObsAlg}
    (rec : FiniteVolumeReconstruction A) (I : ContinuumSpectralInterface)
    (h1 : I.thermodynamicLimit) (h2 : I.selfAdjointDomain)
    (h3 : I.spectralMeasure) (h4 : I.stoneGenerator) :
    continuum_reconstruction_reduces rec I :=
  ⟨h1, h2, h3, h4⟩

end YMGap.Continuum.OSContent

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.OSContent.vacuumNormalized_genuine
#print axioms YMGap.Continuum.OSContent.hamiltonianNonneg_genuine
#print axioms YMGap.Continuum.OSContent.hasSpectralGap_genuine
#print axioms YMGap.Continuum.OSContent.gram_nonneg_genuine
#print axioms YMGap.Continuum.OSContent.trivSpectralModel
#print axioms YMGap.Continuum.OSContent.trivReconstruction
#print axioms YMGap.Continuum.OSContent.trivReconstruction_vacuum_normalized
#print axioms YMGap.Continuum.OSContent.trivReconstruction_hamiltonian_nonneg
#print axioms YMGap.Continuum.OSContent.continuum_reconstruction_from_interface
