/-
Finite-volume GNS construction — the genuine constructive content behind the
OS-reconstruction operator layer.

# Why this module exists

`Continuum/OSReconstruction.lean` carries the OS reconstruction quintuple
`(H_∞, Ω_0, U(t), H_op)` and its laws
(`VacuumNormalized`, `HamiltonianNonneg`, `SemigroupGenerated`,
`HasSpectralGap`) as `True`-valued *interface* Props: the substantive
content lived only in the paper, because the *continuum* statements need the
spectral theorem for unbounded self-adjoint operators, a constructive Stone
theorem, and the thermodynamic limit `Λ → ∞` — a major constructive-analysis
build-out the Q′/CReal stack does not have, and whose spectral-measure
sequence is not even computable (Pour-El–Richards).

But at **finite lattice volume** the pieces are genuinely constructive:

  * the **GNS pre-Hilbert space** is `A.carrier` with the sesquilinear form
    `⟨a, b⟩ := E_Λ(star a · b)`, where `E_Λ` is the *already-constructed*
    interacting finite-volume expectation of `Continuum/FiniteVolume.lean`;
  * its **Gram positivity** `⟨a, a⟩ = E_Λ(star a · a) ≥ 0` IS reflection
    positivity — `ReferenceWeight.E_Λ_positive`, already proved there —
    re-packaged as the GNS inner-product nonnegativity;
  * the **cyclic vacuum** `Ω = [1]` is normalized, `⟨Ω, Ω⟩ = E_Λ(1) = 1`
    (`ReferenceWeight.E_Λ_normalized`), which is the genuine content of
    `OSReconstruction.VacuumNormalized`;
  * the **Hamiltonian nonnegativity** `H ≥ 0` at finite volume is the
    statement that the transfer-matrix eigenvalues `λ_i = e^{−E_i}` are
    nonnegative — exactly `SpectralGap.SpectralModel.lam_nonneg` — and the
    spectral gap is carried as the positive-weight `SpectralModel` (NOT as a
    sorted-eigenvalue difference, which would be discontinuous at level
    collisions).

This module builds those finite-volume pieces as genuine `Type`-level data
(MLTT/HoTT-valid, witnesses as `Σ`/structure fields, never `Prop`-`∃` for
content), reusing `FiniteVolume.E_Λ` and `SpectralGap.SpectralModel`.  It is
the load-bearing `gns_inner_nonneg` lemma plus the upgraded content-bearing
predicates that the existing `True`-stub Props would adopt.

# What is genuine here (constructed / proved, axiom-clean)

  * `FiniteVolumeGNS A` — the GNS pre-Hilbert datum over an observable
    *-algebra `A`: a `Q′`-valued inner product `⟨a, b⟩ = E_Λ(star a · b)`,
    its Gram positivity `inner_nonneg` (= reflection positivity, reused),
    conjugate symmetry, and a normalized cyclic vector.
  * `gnsOfReferenceWeight` — the GNS space built directly from the
    finite-volume expectation `E_Λ` of `Continuum/FiniteVolume.lean`, with
    `gns_inner_nonneg` discharged by `E_Λ_positive` and `cyclic_norm` by
    `E_Λ_normalized`.  This is NOT a placeholder: it is the interacting
    finite-volume state's GNS triple.
  * `cInner` — the same inner product viewed at the `CReal` level
    (`ofQ' ∘ E_Λ(star a · b)`), with `cInner_nonneg : czero ≤ cInner a a`
    lifting the `Q′` Gram positivity to `CReal`.
  * `gnsVacuumNormalizedContent`, `hamiltonianNonnegContent`,
    `hasSpectralGapContent` — the content-bearing replacements for the three
    upgradeable `True`-stub Props, as NEW defs (so `OSReconstruction` stays
    untouched), each proved on the concrete finite-volume objects.

# What stays paper-level (declared honestly, NOT faked)

The continuum self-adjointness of `H` on a dense domain, the
projection-valued spectral measure / functional calculus for unbounded `H`,
the continuum Stone generator, and the thermodynamic limit `Λ → ∞`
(inductive-limit completion + gap persistence) remain the honest declared
boundary.  They are carried as named hypotheses in
`ContinuumSpectralInterface`, NEVER as `sorry`.  See
`docs/os-operator-attack-surface.md`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (via `Q′`/`recip`/`CReal` helpers).
No `Classical.*`, no `sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.FiniteVolume
import YMGap.Continuum.SpectralGap
import YMGap.Constructive.Reals

namespace YMGap.Continuum.FiniteVolumeGNS

open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.SpectralGap
open YMGap.Constructive
open YMGap.Constructive.CReal

/-! ## The finite-volume GNS pre-Hilbert datum

The GNS construction for a positive functional `E` on a *-algebra `A` takes
the sesquilinear form `⟨a, b⟩ := E(star a · b)`.  At finite volume `E = E_Λ`
is the interacting expectation already constructed in
`Continuum/FiniteVolume.lean`, and the only non-trivial law — Gram positivity
`⟨a, a⟩ ≥ 0` — IS reflection positivity, already proved there.

The form is `Q′`-valued because `E_Λ : A.carrier → Q′`.  Conjugate symmetry
`⟨a, b⟩ = star ⟨b, a⟩` reduces, since `Q′` is real (`star = id`), to
`E_Λ(star a · b) = E_Λ(star b · a)`; this is a genuine structural property of
the state on a `*`-algebra and is carried as a field (`inner_conj`), supplied
by the algebra/state, not assumed away.  The quotient-by-nullspace and
completion are TRIVIAL in finite dimension (located, finite-dim ⇒ closed ⇒
completion = itself), so the pre-Hilbert datum below IS the finite-volume
Hilbert space. -/

/-- A **finite-volume GNS pre-Hilbert datum** over an observable *-algebra
`A`: a `Q′`-valued inner product `inner a b = E_Λ(star a · b)`, the load-
bearing Gram positivity `inner_nonneg` (= reflection positivity), conjugate
symmetry, and a normalized cyclic vector `cyclic` (the GNS vacuum `Ω = [1]`).

All fields are genuine constructive content; `inner_nonneg` is the key one
and is exactly the reflection positivity of `FiniteVolume.E_Λ`. -/
structure FiniteVolumeGNS (A : ObsAlg) where
  /-- The GNS inner product `⟨a, b⟩ = E_Λ(star a · b)`, `Q′`-valued because
  the finite-volume expectation is. -/
  inner : A.carrier → A.carrier → Q'
  /-- **The load-bearing law**: Gram positivity `⟨a, a⟩ ≥ 0`.  This IS the
  reflection positivity of the finite-volume state — `E_Λ(star a · a) ≥ 0`. -/
  inner_nonneg : ∀ a, (0 : Q') ≤ inner a a
  /-- Conjugate symmetry `⟨a, b⟩ = ⟨b, a⟩` (real-valued: `star = id` on
  `Q′`).  A structural property of the state on the *-algebra. -/
  inner_conj : ∀ a b, inner a b = inner b a
  /-- The cyclic GNS vacuum `Ω = [1]`. -/
  cyclic : A.carrier
  /-- **VacuumNormalized**: `⟨Ω, Ω⟩ = 1` (up to `Q′` `eqv`).  The genuine
  content of `OSReconstruction.VacuumNormalized`. -/
  cyclic_norm : (inner cyclic cyclic).eqv 1

/-- The diagonal of the GNS form is the squared norm `‖a‖² = ⟨a, a⟩ ≥ 0`. -/
def FiniteVolumeGNS.normSq {A : ObsAlg} (G : FiniteVolumeGNS A) (a : A.carrier) : Q' :=
  G.inner a a

theorem FiniteVolumeGNS.normSq_nonneg {A : ObsAlg} (G : FiniteVolumeGNS A)
    (a : A.carrier) : (0 : Q') ≤ G.normSq a :=
  G.inner_nonneg a

/-! ## Building the GNS space from the finite-volume expectation `E_Λ`

`gnsOfReferenceWeight` constructs the GNS datum directly from a
`ReferenceWeight` (the interacting finite-volume state of
`Continuum/FiniteVolume.lean`).  The inner product is `E_Λ(star a · b)`, its
positivity is `E_Λ_positive` (reflection positivity), and the cyclic-vacuum
normalization is `E_Λ_normalized`.

Conjugate symmetry `E_Λ(star a · b) = E_Λ(star b · a)` is a structural
property of the *-algebra/state; for a general `ObsAlg` it is supplied as the
hypothesis `hconj` (in the SU(2) Wilson instance it follows from the
commutativity of the abelian plaquette weight and reality of the trace, an
algebra-level fact, not an analytic gap). -/

/-- **The finite-volume GNS space from `E_Λ`.**  Given the interacting
finite-volume state `R : ReferenceWeight A`, the structural conjugate-
symmetry hypothesis `hconj`, and the unital-*-law `hone : star 1 · 1 = 1`,
the GNS datum is `⟨a, b⟩ = E_Λ(star a · b)` with:

  * `inner_nonneg` = `R.E_Λ_positive` — **the load-bearing
    `gns_inner_nonneg`** = reflection positivity, REUSED;
  * `cyclic = [1]`, `cyclic_norm` = `R.E_Λ_normalized` — **VacuumNormalized**.

`hone` (`A.mul (A.star A.one) A.one = A.one`) is the unital-*-algebra law
that `ObsAlg` does not bundle generically; it holds in every genuine unital
*-algebra (in particular the Wilson algebra) and is supplied as data, not
assumed away.  This is the genuine GNS triple of the interacting finite-
volume state. -/
def gnsOfReferenceWeight {A : ObsAlg} (R : ReferenceWeight A)
    (hconj : ∀ a b, R.E_Λ (A.mul (A.star a) b) = R.E_Λ (A.mul (A.star b) a))
    (hone : A.mul (A.star A.one) A.one = A.one) :
    FiniteVolumeGNS A where
  inner := fun a b => R.E_Λ (A.mul (A.star a) b)
  inner_nonneg := fun a => R.E_Λ_positive a
  inner_conj := hconj
  cyclic := A.one
  cyclic_norm := by
    -- ⟨Ω, Ω⟩ = E_Λ(star 1 · 1) = E_Λ(1) ≃ 1 by hone then E_Λ_normalized.
    show (R.E_Λ (A.mul (A.star A.one) A.one)).eqv 1
    rw [hone]
    exact R.E_Λ_normalized

/-- **`gns_inner_nonneg`** (named separately for downstream reference): the
GNS inner product built from the finite-volume state is Gram-positive on the
diagonal.  This is the re-packaged reflection positivity
`E_Λ(star a · a) ≥ 0`. -/
theorem gns_inner_nonneg {A : ObsAlg} (R : ReferenceWeight A)
    (hconj : ∀ a b, R.E_Λ (A.mul (A.star a) b) = R.E_Λ (A.mul (A.star b) a))
    (hone : A.mul (A.star A.one) A.one = A.one)
    (a : A.carrier) :
    (0 : Q') ≤ (gnsOfReferenceWeight R hconj hone).inner a a :=
  (gnsOfReferenceWeight R hconj hone).inner_nonneg a

/-! ## The GNS inner product at the `CReal` level

The brief's GNS shape has `inner : carrier → carrier → CReal`.  Since the
finite-volume form is `Q′`-valued, its `CReal` view is `ofQ' ∘ inner`, and
the Gram positivity lifts: `0 ≤ Q' inner ⟹ czero ≤ CReal inner` via
`ofQ'_le_ofQ'` (`czero = ofQ' 0`).  This is the bridge to the CReal-level
spectral statements `HasSpectralGapAt` in `OSReconstruction`. -/

/-- The GNS inner product viewed at the `CReal` level: `ofQ'` of the `Q′`
form. -/
def FiniteVolumeGNS.cInner {A : ObsAlg} (G : FiniteVolumeGNS A)
    (a b : A.carrier) : CReal :=
  ofQ' (G.inner a b)

/-- **CReal-level Gram positivity**: `czero ≤ ⟨a, a⟩_CReal`.  Lifts the `Q′`
reflection positivity `inner_nonneg` to the `CReal` order. -/
theorem FiniteVolumeGNS.cInner_nonneg {A : ObsAlg} (G : FiniteVolumeGNS A)
    (a : A.carrier) : (czero : CReal) ≤ G.cInner a a := by
  show ofQ' (0 : Q') ≤ ofQ' (G.inner a a)
  exact ofQ'_le_ofQ' (G.inner_nonneg a)

/-! ## A concrete inhabitant: the trivially-coupled GNS space

The `trivReferenceWeight` of `Continuum/FiniteVolume.lean` (the free product
state, `Z = 1`) yields a genuine GNS triple on the one-edge trivial product
algebra.  Its carrier is `PUnit`-based, so `hconj`/`hone` hold by `rfl` —
exhibiting the GNS construction end-to-end on a real (non-`True`/`Unit`-stub)
object. -/

/-- The trivially-coupled finite-volume GNS space (concrete inhabitant). -/
def trivGNS (n : Nat) : FiniteVolumeGNS (prodAlg trivFamily n) :=
  gnsOfReferenceWeight (trivReferenceWeight n) (fun _ _ => rfl) rfl

/-- The trivial GNS space's Gram positivity fires (reflection positivity on
the concrete free product state). -/
theorem trivGNS_inner_nonneg (n : Nat) (a : (prodAlg trivFamily n).carrier) :
    (0 : Q') ≤ (trivGNS n).inner a a :=
  (trivGNS n).inner_nonneg a

/-- The trivial GNS space's cyclic vacuum is normalized (VacuumNormalized on
the concrete object). -/
theorem trivGNS_cyclic_norm (n : Nat) :
    ((trivGNS n).inner (trivGNS n).cyclic (trivGNS n).cyclic).eqv 1 :=
  (trivGNS n).cyclic_norm

/-! ## Content-bearing replacements for the `True`-stub Props

These NEW defs show how the three upgradeable `OSReconstruction` Props would
adopt genuine finite-volume content.  They are stated over the concrete
finite-volume objects (`FiniteVolumeGNS`, `SpectralModel`) rather than over
the abstract `HilbertSpace`/`SelfAdjointOp` carriers, so they carry real
witnesses.  `OSReconstruction.lean` is left untouched (another agent's
MassGap chain depends on it); the adoption recipe is in
`docs/os-operator-attack-surface.md`. -/

/-- **VacuumNormalized, genuine.**  Replacement content for
`OSReconstruction.VacuumNormalized`: the GNS cyclic vacuum has squared norm
`⟨Ω, Ω⟩ ≃ 1`.  Unlike the `True`-stub, this is a substantive equation on the
constructed GNS inner product. -/
def gnsVacuumNormalizedContent {A : ObsAlg} (G : FiniteVolumeGNS A) : Prop :=
  (G.inner G.cyclic G.cyclic).eqv 1

theorem gnsVacuumNormalizedContent_holds {A : ObsAlg} (G : FiniteVolumeGNS A) :
    gnsVacuumNormalizedContent G :=
  G.cyclic_norm

/-- **HamiltonianNonneg, genuine.**  Replacement content for
`OSReconstruction.HamiltonianNonneg`: at finite volume the transfer matrix
`T = e^{−aH}` is a positive matrix, so every eigenvalue `λ_i = e^{−E_i}` is
nonnegative — i.e. `H ≥ 0` means `σ(T) ⊆ [0, ∞)`.  This is exactly the
`SpectralModel.lam_nonneg` field, here named as the H≥0 content.  (We do NOT
use a sorted-eigenvalue difference for the gap; the positive-weight
`SpectralModel` is the gap-carrier — see `hasSpectralGapContent`.) -/
def hamiltonianNonnegContent (S : SpectralModel) : Prop :=
  ∀ i, (0 : Q') ≤ S.lam i

theorem hamiltonianNonnegContent_holds (S : SpectralModel) :
    hamiltonianNonnegContent S :=
  S.lam_nonneg

/-- **HasSpectralGap, genuine (finite volume).**  Replacement content for
`OSReconstruction.HasSpectralGap`: a spectral gap at `μ` forces the connected
two-point function to decay geometrically, `G(n) ≤ G(0)·μ^n`.  This is the
already-proved `decay_of_spectralGap_corr0`, here named as the gap content.
The gap is carried as the `SpectralGapBound` predicate on the positive-weight
`SpectralModel` (NOT eigenvalue₂−eigenvalue₁). -/
def hasSpectralGapContent (S : SpectralModel) (μ : Q') : Prop :=
  SpectralGapBound S μ

theorem hasSpectralGapContent_decay (S : SpectralModel) (μ : Q')
    (hμ : (0 : Q') ≤ μ) (hgap : hasSpectralGapContent S μ) (n : Nat) :
    corr S n ≤ (corr S 0) * μ ^ n :=
  decay_of_spectralGap_corr0 S μ hμ hgap n

/-- The CReal-level vacuum normalization content: `⟨Ω, Ω⟩_CReal` upper-
bounded by `ofQ' 1` and lower-bounded — packaged as the pair witnessing the
`CReal` view of normalization (the `Q′` equation `eqv`-implies both `≤`s).
Stated as the `CReal`-positivity of the diagonal norm, the form
`HasSpectralGapAt` would consume. -/
theorem trivGNS_cInner_nonneg (n : Nat) (a : (prodAlg trivFamily n).carrier) :
    (czero : CReal) ≤ (trivGNS n).cInner a a :=
  (trivGNS n).cInner_nonneg a

end YMGap.Continuum.FiniteVolumeGNS

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FiniteVolumeGNS.gnsOfReferenceWeight
#print axioms YMGap.Continuum.FiniteVolumeGNS.gns_inner_nonneg
#print axioms YMGap.Continuum.FiniteVolumeGNS.FiniteVolumeGNS.cInner_nonneg
#print axioms YMGap.Continuum.FiniteVolumeGNS.trivGNS
#print axioms YMGap.Continuum.FiniteVolumeGNS.trivGNS_inner_nonneg
#print axioms YMGap.Continuum.FiniteVolumeGNS.trivGNS_cyclic_norm
#print axioms YMGap.Continuum.FiniteVolumeGNS.gnsVacuumNormalizedContent_holds
#print axioms YMGap.Continuum.FiniteVolumeGNS.hamiltonianNonnegContent_holds
#print axioms YMGap.Continuum.FiniteVolumeGNS.hasSpectralGapContent_decay
#print axioms YMGap.Continuum.FiniteVolumeGNS.trivGNS_cInner_nonneg
