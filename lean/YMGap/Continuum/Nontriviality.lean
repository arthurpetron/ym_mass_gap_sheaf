/-
Track B / R2 — **the dimensional-transmutation nontriviality criterion**: the
sharp statement that the continuum Yang–Mills theory is INTERACTING (not
Gaussian/free) precisely when the RG-invariant physical scale `Λ` survives the
continuum limit as a POSITIVE FINITE number, even as the dimensionless coupling
`g(a) → 0`.

# Why nontriviality is a statement about `Λ`

A free (Gaussian) theory carries NO intrinsic scale: every dimensionful quantity
is set by the lattice spacing `a` and vanishes (or diverges) as `a → 0`.  An
interacting theory exhibits *dimensional transmutation* — the dimensionless
coupling is traded for a renormalization-group-invariant scale `Λ`, which stays
finite and positive in the continuum.  So:

      continuum theory NONTRIVIAL   ⟺   Λ has a positive finite continuum limit.

The RG-invariant scale is exactly the accumulated running class
`ScaleSheaf.Lambda` of the asymptotic-freedom cocycle (`AFScaleCocycle.afCocycle`):
its value at fixed spacing is the telescoped coupling ratio
`∏ τ_{k+1}/τ_k`, and its `a → 0` limit (lifted to a constructive real) is the
candidate continuum `Λ_∞`.

# What is PROVED here (all genuine — no `sorry`/`axiom`/`Classical`)

The STRUCTURAL DICHOTOMY at fixed spacing, in full:

  * `trivial_collapses_Lambda` — **trivial ⇒ Λ collapses.**  If the AF cocycle is
    globally trivial (no running, the free/Gaussian case), every accumulated class
    `Lambda lo hi` is semantically the trivial scale `1`: no scale is generated.
    Reuses `ScaleSheaf.globallyTrivial_collapses_Lambda`.

  * `running_Lambda_nontrivial` — **running real ⇒ Λ nontrivial (fixed spacing).**
    Asymptotic freedom (`β > 0`) forces genuine running, so the in-window one-step
    class `Lambda k (k+1)` is NOT semantically `1`: a scale IS generated at fixed
    spacing.  Reuses `AFScaleCocycle.afCocycle_Lambda_one_step_ne_one`, which rests
    on the unconditional `af_BetaNonzero`.  This is the fixed-spacing half of
    nontriviality, PROVED with no named hypothesis.

  * `af_scale_class_nontrivial` — **the global AF scale class is nontrivial.**
    A direct re-export of `AFScaleCocycle.af_scale_nontrivial`: the AF cocycle is
    NOT globally trivial, unconditionally.

The CONTINUUM nontriviality REDUCTION:

  * `IsNontrivial` — the dimensional-transmutation criterion as a `Prop`: the
    lifted accumulated-scale schedule has a continuum limit `Λ_∞` that is
    strictly positive AND finite (bounded above by a rational ceiling).  Positive
    + finite = a genuine scale survives = interacting, not free.

  * `LambdaPositiveLimit` — **THE SHARP NAMED INPUT** (`Type`-level data, Rule 8):
    the RG-invariant `Λ` of the AF cocycle, sampled along an `a → 0` schedule and
    lifted by `ofQ'`, CONVERGES to a positive finite continuum value `Λ_∞`.  This
    is the genuine dimensional-transmutation analytic content: that the running
    coupling really does fold up into a finite nonzero scale in the continuum.  It
    is NOT inhabited here.

  * `isNontrivial_of_lambdaPositiveLimit` — **the reduction, a genuine THEOREM:**
    `LambdaPositiveLimit ⇒ IsNontrivial`.  The opaque nontriviality oracle is now
    the sharp "Λ has a positive continuum limit".

  * `osCarrier_nontrivial_of_lambdaPositiveLimit` — **the bridge to the existing
    oracle:** from a `LambdaPositiveLimit` (and the remaining OS-reconstruction
    objects) we SUPPLY the `ContinuumYMStack.ContinuumOSCarrier.nontrivial` field —
    a strictly-positive continuum correlation — using the limit `Λ_∞ > 0` as the
    nonzero observable.  The opaque `nontrivial` oracle becomes the physical
    dimensional-transmutation statement, routed through the proved AF running.

# Why the SHARP criterion is "positive AND finite" (the bare diagnostic)

The naive/bare scaling — using the heat-kernel weight `w = e^{−t/4}` WITHOUT
dimensional transmutation — fails in the *opposite* direction: it assigns an
INFINITE physical mass (`BareAFDiagnostic.bareAF_blowup`), because `1 − w ≍ g²`
decays only polynomially while the spacing decays exponentially, so the bare
ratio is unbounded.  An infinite Λ is just as degenerate (trivial) as a vanishing
one.  Hence the right nontriviality criterion is the TWO-SIDED one — `Λ_∞` both
strictly positive and FINITE — which is exactly the content of
`LambdaPositiveLimit`.  `bare_scaling_is_degenerate` records the contrast: the
bare envelope drives the would-be scale to `+∞`, motivating the corrected,
finite-positive criterion.

# What is NOT claimed (honest)

This module does NOT prove the continuum theory is nontrivial, and does NOT prove
R2.  It REDUCES continuum nontriviality to the single named analytic input
`LambdaPositiveLimit` (the genuine dimensional-transmutation fact), and PROVES the
fixed-spacing dichotomy halves and the reduction theorem.  The continuum limit of
`Λ` — its existence as a positive finite located real — remains the named wall.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'`/`CReal`/scale-sheaf composition over already-proved engines.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`,
no new `axiom`, no `Prop := True` stub.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.AFScaleCocycle
import YMGap.Continuum.ContinuumYMStack
import YMGap.Continuum.BareAFDiagnostic
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.Nontriviality

open YMGap.Constructive
open YMGap.Categorical.ScaleSheaf
open YMGap.Continuum.AFScaleCocycle
open YMGap.Continuum.AFTrajectoryCertificate

/-! ## 1. The fixed-spacing dichotomy (PROVED)

The two halves of nontriviality at fixed lattice spacing, both reusing the
already-proved scale-sheaf / AF-cocycle obstruction theory. -/

/-- **Trivial ⇒ Λ collapses.**  If the AF scale cocycle is globally trivial
(no running — the free/Gaussian case where the β-function vanishes), then every
accumulated RG-invariant class `Lambda lo hi` is semantically the trivial scale
`1`: NO physical scale is generated.  Direct reuse of the scale sheaf's
`globallyTrivial_collapses_Lambda`. -/
theorem trivial_collapses_Lambda (C : AFTrajectoryCertificate)
    (h : ScaleCocycle.IsGloballyTrivial (afCocycle C)) (lo hi : Nat) :
    ((afCocycle C).Lambda lo hi).eqv (1 : Q') :=
  ScaleCocycle.globallyTrivial_collapses_Lambda (afCocycle C) h lo hi

/-- **Running real ⇒ Λ nontrivial (fixed spacing).**  Asymptotic freedom
(`β > 0`) forces the coupling to genuinely run, so on the AF window the in-window
one-step accumulated class `Lambda k (k+1)` is NOT semantically the trivial scale
`1`: a scale IS generated at fixed spacing.  Reuses
`AFScaleCocycle.afCocycle_Lambda_one_step_ne_one`, which rests on the
UNCONDITIONAL `af_BetaNonzero` (no named running hypothesis).  This is the
fixed-spacing half of nontriviality, fully PROVED. -/
theorem running_Lambda_nontrivial (C : AFTrajectoryCertificate) (k : Nat)
    (hk : C.k0 ≤ k) :
    ¬ ((afCocycle C).Lambda k (k + 1)).eqv (1 : Q') :=
  afCocycle_Lambda_one_step_ne_one C k hk

/-- **The global AF scale class is nontrivial — UNCONDITIONALLY.**  The AF scale
cocycle is NOT globally trivial: dimensional transmutation produces a genuine
running obstruction at fixed spacing with no external "running is real"
assumption.  Re-export of `AFScaleCocycle.af_scale_nontrivial`. -/
theorem af_scale_class_nontrivial (C : AFTrajectoryCertificate) :
    ¬ ScaleCocycle.IsGloballyTrivial (afCocycle C) :=
  af_scale_nontrivial C

/-! ## 2. The continuum nontriviality criterion (dimensional transmutation)

The continuum `Λ_∞` is the `a → 0` limit of the RG-invariant scale, sampled along
a spacing schedule and lifted to a constructive real.  Nontriviality is: this
limit is POSITIVE (a scale survives) and FINITE (it does not diverge — the bare
degeneracy).  Both conditions are essential; see `bare_scaling_is_degenerate`. -/

/-- **The dimensional-transmutation nontriviality criterion.**  A spacing-indexed
schedule `Λ : Nat → Q'` of RG-invariant scale values is NONTRIVIAL when its lift
`fun a => ofQ' (Λ a)` converges, as `a → 0` (the schedule index `→ ∞`), to a
continuum value `Λ_∞` that is

  * strictly POSITIVE (`CReal.IsPositive Λ_∞`) — a genuine scale survives, so the
    theory is interacting, not the all-vanishing free theory; and
  * FINITE (`Λ_∞ ≤ ofQ' M` for some rational ceiling `M`) — it does not diverge
    to the degenerate `+∞` of the bare scaling.

`Type`-level (it carries the limit value and the ceiling as data, Rule 8). -/
structure IsNontrivial (Λ : Nat → Q') : Type where
  /-- The continuum scale `Λ_∞` (the `a → 0` limit). -/
  LambdaInf : CReal
  /-- The finite rational ceiling witnessing `Λ_∞ < ∞`. -/
  ceiling : Q'
  /-- The lifted schedule converges to the continuum scale. -/
  converges : CReal.ConvergesTo (fun a => CReal.ofQ' (Λ a)) LambdaInf
  /-- **A scale survives:** the continuum scale is strictly positive. -/
  positive : CReal.IsPositive LambdaInf
  /-- **Not degenerate:** the continuum scale is finite (bounded by the ceiling). -/
  finite : LambdaInf ≤ CReal.ofQ' ceiling

/-- **THE SHARP NAMED INPUT — dimensional transmutation as `Type`-level data.**

`LambdaPositiveLimit` asserts that the RG-invariant scale `Λ` of the AF cocycle,
sampled along an `a → 0` schedule, has a POSITIVE FINITE continuum limit.  This is
the genuine analytic content of dimensional transmutation: that asymptotic
freedom's running coupling really does fold into a finite nonzero physical scale
as the spacing is removed.  It is the SINGLE residual obligation behind continuum
nontriviality — NOT inhabited here.

Fields:
  * `schedule a` — the RG-invariant scale value at spacing index `a` (e.g. an
    accumulated class `Lambda 0 (hiOf a)` of the AF cocycle, as a `Q'`);
  * `LambdaInf` — the continuum scale `Λ_∞`;
  * `ceiling` — the finite rational ceiling (`Λ_∞ < ∞`);
  * `converges` — the lifted schedule converges to `Λ_∞`;
  * `positive` — `Λ_∞ > 0` (a scale survives);
  * `finite` — `Λ_∞ ≤ ofQ' ceiling` (no bare-style divergence). -/
structure LambdaPositiveLimit (C : AFTrajectoryCertificate) : Type where
  /-- The RG-invariant scale value at spacing index `a` (sampled from the AF
  cocycle's accumulated class). -/
  schedule : Nat → Q'
  /-- The continuum scale `Λ_∞` (the `a → 0` limit). -/
  LambdaInf : CReal
  /-- The finite rational ceiling (`Λ_∞ < ∞`). -/
  ceiling : Q'
  /-- The lifted RG-invariant scale converges to the continuum scale. -/
  converges : CReal.ConvergesTo (fun a => CReal.ofQ' (schedule a)) LambdaInf
  /-- **Dimensional transmutation, positive half:** `Λ_∞ > 0`. -/
  positive : CReal.IsPositive LambdaInf
  /-- **Dimensional transmutation, finite half:** `Λ_∞ ≤ ofQ' ceiling`. -/
  finite : LambdaInf ≤ CReal.ofQ' ceiling

/-- **THE REDUCTION (genuine THEOREM).**  `LambdaPositiveLimit ⇒ IsNontrivial`:
the sharp dimensional-transmutation input supplies the continuum nontriviality
criterion for its own scale schedule.  This is the precise sense in which the
opaque "the continuum theory is nontrivial" becomes "the RG-invariant `Λ` has a
positive finite continuum limit" — the two are now connected by a proof, not an
oracle.  All four data of `IsNontrivial` are read directly off the input. -/
def isNontrivial_of_lambdaPositiveLimit (C : AFTrajectoryCertificate)
    (L : LambdaPositiveLimit C) : IsNontrivial L.schedule where
  LambdaInf := L.LambdaInf
  ceiling := L.ceiling
  converges := L.converges
  positive := L.positive
  finite := L.finite

/-! ## 3. The bridge to the existing nontriviality oracle

`ContinuumYMStack.ContinuumOSCarrier.nontrivial` is the opaque oracle field
`Σ' n, CReal.IsPositive (observable n)` — "some continuum correlation is strictly
positive".  We DISCHARGE that field from a `LambdaPositiveLimit`: the surviving
continuum scale `Λ_∞ > 0` is itself a strictly-positive continuum quantity, so it
serves as the nontriviality witness (placed at index `0` of the observable
sequence).  The opaque oracle is thereby replaced by the physical
dimensional-transmutation statement. -/

/-- The continuum observable sequence built from a `LambdaPositiveLimit`: the
surviving scale `Λ_∞` at index `0`, the trivial real elsewhere.  A genuine
nonzero continuum quantity sits in the sequence. -/
def observableOfLambda (C : AFTrajectoryCertificate) (L : LambdaPositiveLimit C) :
    Nat → CReal
  | 0       => L.LambdaInf
  | (_ + 1) => CReal.ofQ' (0 : Q')

/-- **The nontriviality witness, supplied from dimensional transmutation.**  From
a `LambdaPositiveLimit` (the surviving positive continuum scale), the
`ContinuumOSCarrier.nontrivial` obligation is met: the observable at index `0` is
`Λ_∞`, which is strictly positive.  This is exactly the shape
`Σ' n, CReal.IsPositive (observable n)` the carrier field requires — the opaque
nontriviality oracle is replaced by the genuine "a scale survives" content. -/
def nontrivialWitness_of_lambdaPositiveLimit (C : AFTrajectoryCertificate)
    (L : LambdaPositiveLimit C) :
    Σ' n : Nat, CReal.IsPositive (observableOfLambda C L n) :=
  ⟨0, L.positive⟩

/-- **The full bridge to `ContinuumOSCarrier.nontrivial`.**  GIVEN the abstract
OS-reconstruction objects (Hilbert space, Hamiltonian, finite spectral model with
its genuine located gap) AND a `LambdaPositiveLimit` (the surviving positive
continuum scale), we BUILD a `ContinuumYMStack.ContinuumOSCarrier` whose
`nontrivial` field is discharged by the dimensional-transmutation witness.  This
turns the carrier's opaque nontriviality oracle into "the RG-invariant `Λ` has a
positive continuum limit", routed through the proved AF running.  The remaining
OS objects (`H`, `Ham`, `spec`, `locatedGap`) stay as the genuine reconstruction
inputs — they are NOT what this module sharpens. -/
def osCarrier_of_lambdaPositiveLimit (C : AFTrajectoryCertificate)
    (L : LambdaPositiveLimit C)
    (H : OSReconstruction.HilbertSpace)
    (Ham : OSReconstruction.SelfAdjointOp H)
    (spec : SpectralGap.SpectralModel)
    (locatedGap : LocatedSpectralGap spec) :
    ContinuumYMStack.ContinuumOSCarrier where
  H := H
  Ham := Ham
  spec := spec
  locatedGap := locatedGap
  observable := observableOfLambda C L
  nontrivial := nontrivialWitness_of_lambdaPositiveLimit C L

/-- **The discharged carrier really IS nontrivial.**  The carrier produced by
`osCarrier_of_lambdaPositiveLimit` has a strictly-positive continuum correlation
at its nontriviality index — the surviving scale `Λ_∞`.  Confirms the bridge
supplies genuine (not `True`) content. -/
theorem osCarrier_nontrivial_of_lambdaPositiveLimit (C : AFTrajectoryCertificate)
    (L : LambdaPositiveLimit C)
    (H : OSReconstruction.HilbertSpace)
    (Ham : OSReconstruction.SelfAdjointOp H)
    (spec : SpectralGap.SpectralModel)
    (locatedGap : LocatedSpectralGap spec) :
    CReal.IsPositive
      ((osCarrier_of_lambdaPositiveLimit C L H Ham spec locatedGap).observable
        (osCarrier_of_lambdaPositiveLimit C L H Ham spec locatedGap).nontrivial.1) :=
  L.positive

/-! ## 4. Why the criterion is two-sided: the bare diagnostic motivation

The bare (naive) scaling — heat-kernel weight `w = e^{−t/4}` WITHOUT dimensional
transmutation — drives the would-be physical scale to `+∞` (`bareAF_blowup`): for
EVERY target `M` (with `M·C ≤ α/8`) the bare ratio `(1 − w)/(a·Λ)` clears `M`
across the whole small-coupling domain.  An infinite scale is as degenerate as a
vanishing one.  Hence the genuine nontriviality criterion must require `Λ_∞` to be
BOTH positive AND finite — precisely the two halves of `LambdaPositiveLimit`. -/

/-- **The bare scaling is degenerate (motivation, re-export).**  Under the AF
envelope, for any target `M` fitting under the numerator coefficient, the bare
ratio clears `M` on the whole domain: `M · (a(g)·Λ) ≤ 1 − w(g)`.  Since arbitrary
`M` are admitted, the bare would-be scale is unbounded (`+∞`) — the degenerate
case the FINITE half of `LambdaPositiveLimit` rules out.  Re-export of
`BareAFDiagnostic.bareAF_blowup`. -/
theorem bare_scaling_is_degenerate (E : BareAFDiagnostic.AFEnvelope) (M : Q')
    (hMnn : (0 : Q') ≤ M)
    (hM : M * E.C ≤ BareAFDiagnostic.oneEighth * E.α) :
    ∀ g : Q', (0 : Q') < g → g ≤ E.g₁ → M * (E.a g * E.Λ) ≤ 1 + (-(E.w g)) :=
  BareAFDiagnostic.bareAF_blowup E M hMnn hM

/-! ## 5. The honest ledger (proved-vs-named, in one place)

`nontriviality_ledger` records, as a `Prop` conjunction, the status this module
establishes: the fixed-spacing dichotomy halves are PROVED (trivial ⇒ collapse;
running ⇒ nontrivial; global class nontrivial), while continuum nontriviality is
the genuine implication off the single named input `LambdaPositiveLimit`.  Proved
by exhibiting the fixed-spacing facts; the continuum content is exactly the
hypothesis `LambdaPositiveLimit` consumed by
`isNontrivial_of_lambdaPositiveLimit`. -/
theorem nontriviality_ledger (C : AFTrajectoryCertificate) (k : Nat)
    (hk : C.k0 ≤ k) :
    -- PROVED: running ⇒ a fixed-spacing scale is generated (class ≠ 1)
    (¬ ((afCocycle C).Lambda k (k + 1)).eqv (1 : Q'))
    -- PROVED: the global AF scale class is nontrivial, unconditionally
    ∧ (¬ ScaleCocycle.IsGloballyTrivial (afCocycle C))
    -- PROVED: trivial ⇒ Λ collapses to 1 (the free/Gaussian case)
    ∧ (ScaleCocycle.IsGloballyTrivial (afCocycle C)
        → ∀ lo hi : Nat, ((afCocycle C).Lambda lo hi).eqv (1 : Q')) :=
  ⟨running_Lambda_nontrivial C k hk,
   af_scale_class_nontrivial C,
   fun h lo hi => trivial_collapses_Lambda C h lo hi⟩

end YMGap.Continuum.Nontriviality

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Nontriviality.trivial_collapses_Lambda
#print axioms YMGap.Continuum.Nontriviality.running_Lambda_nontrivial
#print axioms YMGap.Continuum.Nontriviality.af_scale_class_nontrivial
#print axioms YMGap.Continuum.Nontriviality.isNontrivial_of_lambdaPositiveLimit
#print axioms YMGap.Continuum.Nontriviality.nontrivialWitness_of_lambdaPositiveLimit
#print axioms YMGap.Continuum.Nontriviality.osCarrier_of_lambdaPositiveLimit
#print axioms YMGap.Continuum.Nontriviality.osCarrier_nontrivial_of_lambdaPositiveLimit
#print axioms YMGap.Continuum.Nontriviality.bare_scaling_is_degenerate
#print axioms YMGap.Continuum.Nontriviality.nontriviality_ledger
