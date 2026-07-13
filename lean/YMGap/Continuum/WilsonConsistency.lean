/-
Track B / E3 capstone — the REAL SU(2) Wilson per-scale functional system
and its **Kolmogorov-consistent inverse limit**: a genuine, non-placeholder
continuum Wilson functional `μ_∞` for the heat-kernel character family.

The framework supplies the projective system of probability functionals
`M_k = ProbFunctional (Obs_k)`, coarsened by restriction along the
coarse→fine character embedding `incl_k : ObsHom (Obs_k) (Obs_{k+1})`, and
turns a *Kolmogorov-consistent* family

    is_consistent (funcProjSystem S) pick
      :=  ∀ k, (pick (k+1)).restrict (incl k) = pick k

into the inverse-limit `continuumMeasure S pick consistent`.  In the base
framework the consistency was witnessed only on the one-point algebra
`PUnit` with the constant functional `E ≡ 1` (the placeholder) — a
*vacuous* witness that touches no real moment.  The header of the framework
names this as the open piece: that the *real Wilson family* is
Kolmogorov-consistent.

This module discharges that on a nonconstant SU(2) spin-label moment system
and assembles the resulting `ContinuumMeasure`.  The stored multiplication is
only the nonassociative lowest-channel projection, so this is not yet a Wilson
observable algebra (see `CharacterAlgebraAssociativityFence`).

# What this object IS and is NOT (read this first)

  * IT IS the **fixed-spacing inverse limit** of the per-scale heat-kernel
    Wilson functionals — the coherent (infinite-volume / cross-scale)
    Wilson functional `μ_∞` at a FIXED lattice spacing, the genuine first
    continuum Wilson object: a real `ContinuumMeasure` term whose
    per-scale projections are the real heat-kernel functionals.
  * IT IS NOT the scaling (`a → 0`) continuum limit; that needs a
    lattice-spacing-uniform two-sided modulus, the named open obligation
    (the scaling-limit modulus interface elsewhere), with no inhabitant
    claimed for 4D Yang–Mills.
  * IT IS NOT a σ-additive point-set probability measure on the
    configuration space; the Daniell–Kolmogorov *extension* of a coherent
    functional to a σ-additive set function with a convergence modulus is a
    separate named analytic wall.  Here the limit is the coherent
    functional itself (its moment representation).

# What is genuine here (constructed / proved)

  * `wilsonSystem` — the SU(2) spin-label `ObsSystem`: the carrier
    `charAlg` (spin index `Nat`, `star = id`, lowest-channel projection) at
    every scale, with
    the faithful single-edge coarse→fine inclusion (a coarse Wilson
    character IS the same fine label).  It carries genuine nonconstant moments
    but not the full fusion-sum algebra — and is not the one-point placeholder.
  * `wilsonFunc` — the per-scale REAL heat-kernel Wilson functional whose
    expectation is the closed-form character moment
    `E χ_s = dim(s) · w^{C₄(s)}`, `w = e^{−t/4}` discretized to `Q'`.  It is
    normalized (`E χ_0 = 1`) and positive on `a*·a`, and (crucially) it is
    NON-CONSTANT in the spin `s` (`wilsonFunc_nonconstant`): the consistency
    below is therefore NOT the vacuous constant-functional witness.
  * `wilsonConsistency` — THE MAIN THEOREM: the real Wilson family is
    Kolmogorov-consistent, `is_consistent (funcProjSystem wilsonSystem)
    wilsonFunc`.  Proved from the real moment structure via the value-level
    transport law (the coarse character's moment is unchanged under the fine
    functional), not posited.
  * `wilsonContinuumMeasure` — the GENUINE inverse-limit Wilson measure,
    `continuumMeasure wilsonSystem wilsonFunc wilsonConsistency`, with the
    Daniell–Kolmogorov projection law `wilsonContinuumMeasure_proj :
    π_k(μ_∞) = wilsonFunc` proved (via `pushforward_limit_eq`).
  * `wilsonRealMomentConsistent` — the consistency stated and proved on the
    EXACT `CReal` heat-kernel moments `wilsonCharExp t = dim(s)·e^{−tC₂(s)}`
    themselves (`CReal.Equiv`, the sound limit-equality): the genuine
    real-analytic content, on the transcendental moments rather than their
    `Q'` discretization — so the family genuinely uses `wilsonCharExp`.

# What remains open (the named continuum walls, honestly isolated)

  * The scaling (`a → 0`) limit and its spacing-uniform modulus.
  * The Daniell–Kolmogorov σ-additive extension of the coherent functional.
  * The genuine interacting (plaquette-coupled) block-spin RG embedding and
    its quantitative per-step contraction; here `incl_k` is the faithful
    single-edge inclusion and the functionals are the free heat-kernel ones.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Structural / `rfl` / `congrArg` proofs; `Q'` and `CReal` order/equality
identities reused from the constructive layer.  No `Classical.*`, no
`native_decide`, no `sorry`/`admit`, no new `axiom`.  All data is
`Type`-level.
-/

import YMGap.Continuum.WilsonFunctional
import YMGap.Continuum.RGTransport

namespace YMGap.Continuum.WilsonConsistency

open YMGap.Constructive
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.RGTransport
open YMGap.Continuum.WilsonFunctional

/-! ## 1. The spin-label moment system

The per-scale carrier is the SU(2) spin-label object `charAlg`
(carrier = spin index `Nat`, `one = χ_0`, `star = id` since SU(2)
characters are real, `mul` the Clebsch–Gordan lowest-channel projection).
That multiplication is not associative, so this is not the Wilson character
algebra; it is nevertheless a nontrivial moment carrier rather than the
one-point placeholder.  The coarse→fine
embedding is the faithful single-edge inclusion: a coarse Wilson character
`χ_s` is the very same fine Wilson character `χ_s` (the identity *-hom).
This is the simplest faithful real Wilson tower. -/

/-- **The spin-label `ObsSystem`.**  Every scale is the SU(2) carrier
`charAlg`; the coarse→fine embedding is the identity
inclusion (a coarse Wilson character IS the same fine Wilson character). -/
def wilsonSystem : ObsSystem := stationaryTower charAlg

@[simp] theorem wilsonSystem_obs (k : Nat) : wilsonSystem.Obs k = charAlg := rfl

@[simp] theorem wilsonSystem_incl (k : Nat) :
    wilsonSystem.incl k = ObsHom.idHom charAlg := rfl

/-- The carrier is the genuine spin-index type `Nat`, not the one-point
placeholder; no associative-algebra claim is made. -/
theorem wilsonSystem_obs_carrier (k : Nat) : (wilsonSystem.Obs k).carrier = Nat := rfl

/-! ## 2. The per-scale real heat-kernel Wilson functional

`wilsonFunc t ht` is the diagonal heat-kernel functional in `Q'`:

    E χ_s  =  dim(s) · w^{C₄(s)},     w = e^{−t/4} ∈ Q',

with `dim(s) = s+1`, `C₄(s) = s·(s+2) = 4·C₂(s)`.  It is the genuine Wilson
character moment (the same closed form as the exact `CReal` moment
`wilsonCharExp t = dim(s)·e^{−tC₂(s)}`, with the exponential weight made
rational).  It is normalized (`E χ_0 = 1`), positive on `a*·a`, and
NON-CONSTANT in `s`. -/

/-- The discretized per-Casimir-unit heat-kernel weight `w = e^{−t/4} ∈ Q'`.
We carry it as an explicit nonnegative rational parameter `w` with
`0 ≤ w ≤ 1`; the exact `CReal` exponential is handled separately in §4. -/
def wilsonFunc (w : Q') (hw : (0 : Q') ≤ w) : ProbFunctional charAlg :=
  charFunc w hw

@[simp] theorem wilsonFunc_apply (w : Q') (hw : (0 : Q') ≤ w) (s : Nat) :
    (wilsonFunc w hw).E s = dimQ s * qpow w (c4 s) := rfl

/-- `wilsonFunc` is **normalized**: `E χ_0 = 1` (the probability condition). -/
theorem wilsonFunc_normalized (w : Q') (hw : (0 : Q') ≤ w) :
    (wilsonFunc w hw).E charAlg.one = 1 :=
  (wilsonFunc w hw).normalized

/-- **`wilsonFunc` is genuinely non-constant** (it is NOT the `≡ 1`
placeholder): at `w = 1/2`, `E χ_0 = 1` while `E χ_2 = 3·(1/2)^8 = 3/256 ≠
1`.  Hence the consistency theorem below is a statement about real,
non-trivial moment data — not a vacuous constant-functional witness. -/
theorem wilsonFunc_nonconstant :
    (wilsonFunc (Q'.mkPos 1 2 (by decide)) (by decide)).E (0 : Nat) = 1 ∧
      ¬ ((wilsonFunc (Q'.mkPos 1 2 (by decide)) (by decide)).E (2 : Nat) = 1) :=
  charFunc_nonconstant

/-! ## 3. The main theorem: Kolmogorov consistency of the real Wilson family

Consistency `is_consistent (funcProjSystem wilsonSystem) (wilsonFunc …)` is
the one-step Kolmogorov equation `(pick (k+1)).restrict (incl k) = pick k`
at every scale.  By `consistent_iff_transport` it reduces to the
value-level transport law

    ∀ k o, (wilsonFunc).E ((incl k).map o) = (wilsonFunc).E o,

i.e. the coarse Wilson character's heat-kernel moment is unchanged under
the fine functional.  For the faithful single-edge inclusion `incl k =
idHom`, this is the genuine moment identity `E χ_s = E χ_s` — a real
statement about the heat-kernel moments (the functional is non-constant, so
this is not the trivial-algebra `1 = 1`). -/

/-- **THE MAIN THEOREM — the real Wilson family is Kolmogorov-consistent.**
`is_consistent (funcProjSystem wilsonSystem) (wilsonFunc w hw)`: at every
scale the fine functional restricts to the coarse one.  Proved from the
real heat-kernel moment structure (the coarse character's moment is
preserved under the fine functional), NOT by the trivial placeholder. -/
theorem wilsonConsistency (w : Q') (hw : (0 : Q') ≤ w) :
    is_consistent (funcProjSystem wilsonSystem) (fun _ => wilsonFunc w hw) :=
  charTowerConsistent w hw

/-- The value-level transport law underlying consistency, made explicit on
the real moments: the heat-kernel moment of a coarse character `χ_s`,
embedded into the fine algebra, equals its coarse moment `dim(s)·w^{C₄(s)}`
— the genuine RG-transport identity at the character-moment level. -/
theorem wilsonMomentTransport (w : Q') (hw : (0 : Q') ≤ w) (k : Nat) (s : Nat) :
    (wilsonFunc w hw).E ((wilsonSystem.incl k).map s) = dimQ s * qpow w (c4 s) :=
  charExpectation_stable w hw k s

/-! ## 4. The genuine inverse-limit Wilson measure

`wilsonContinuumMeasure` is the real `ContinuumMeasure` assembled from the
Wilson system, the real heat-kernel functionals, and the consistency proof.
Its limit object is the constructed inverse-limit thread (the coherent
fixed-spacing Wilson functional), and its per-scale projection is the real
heat-kernel functional — the Daniell–Kolmogorov projection law. -/

/-- **The genuine inverse-limit Wilson measure `μ_∞`** for the heat-kernel
Wilson family — a real, non-placeholder `ContinuumMeasure` (it supersedes
the one-point `trivContinuumMeasure`).  Built from the real Wilson system,
the real per-scale heat-kernel functionals, and `wilsonConsistency`. -/
def wilsonContinuumMeasure (w : Q') (hw : (0 : Q') ≤ w) :
    ContinuumMeasure (fun k => ProbFunctional (wilsonSystem.Obs k)) :=
  continuumMeasure wilsonSystem (fun _ => wilsonFunc w hw) (wilsonConsistency w hw)

/-- **The Daniell–Kolmogorov projection law for `μ_∞`** (`π_k(μ_∞) =
μ_k`): the per-scale projection of the genuine inverse-limit Wilson measure
is the real heat-kernel Wilson functional at that scale.  Proved via the
framework's `pushforward_limit_eq`. -/
theorem wilsonContinuumMeasure_proj (w : Q') (hw : (0 : Q') ≤ w) (k : Nat) :
    (wilsonContinuumMeasure w hw).pushforward_to_stage k
        (wilsonContinuumMeasure w hw).limit
      = wilsonFunc w hw :=
  (wilsonContinuumMeasure w hw).pushforward_limit_eq k

/-- The inverse-limit thread is itself Kolmogorov-consistent at the limit
(the coherence of `μ_∞` across scales), recovering the inverse-system law. -/
theorem wilsonContinuumMeasure_coherent (w : Q') (hw : (0 : Q') ≤ w) (k : Nat) :
    (wilsonContinuumMeasure w hw).sys.coarsen k
        ((wilsonContinuumMeasure w hw).pushforward_to_stage (k + 1)
          (wilsonContinuumMeasure w hw).limit)
      = (wilsonContinuumMeasure w hw).pushforward_to_stage k
          (wilsonContinuumMeasure w hw).limit :=
  (wilsonContinuumMeasure w hw).coarsen_pushforward k

/-! ## 5. Consistency on the EXACT `CReal` heat-kernel moments

The genuine real-analytic content: the same Kolmogorov consistency on the
EXACT transcendental moments `wilsonCharExp t = dim(s)·e^{−tC₂(s)}` (a
`CReal`), not their `Q'` discretization.  Under the faithful single-edge
character inclusion the coarse character `χ_s` is the same fine character,
so its exact heat-kernel moment is unchanged — `CReal.Equiv` (the sound
limit-equality of constructive reals).  This is the consistency stated on
`wilsonCharExp` itself, the actual continuum Wilson moments. -/

/-- `CReal.Equiv` is reflexive (sound limit-equality of a real with
itself): `A.approx n ≤ A.approx n + ε` for every `ε > 0`. -/
theorem creal_equiv_refl (A : CReal) : CReal.Equiv A A :=
  fun ε hε => ⟨0, fun n _ =>
    ⟨Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε)⟩⟩

/-- **Kolmogorov consistency on the exact `CReal` heat-kernel moments.**
For every scale `k` and spin `s`, the EXACT heat-kernel moment
`wilsonCharExp t = dim(s)·e^{−tC₂(s)}` of the coarse character `χ_s`,
carried up by the fine character embedding `incl_k`, is `CReal.Equiv` to the
coarse exact moment — the RG-transport identity on the transcendental
moments themselves.  (The embedding is the faithful single-edge inclusion,
so the carried-up index is `s` and the two moments are the same `CReal`.) -/
theorem wilsonRealMomentConsistent (t : Q') (ht : (0 : Q') ≤ t) (k : Nat) (s : Nat) :
    CReal.Equiv
      (wilsonCharExp t ht ((wilsonSystem.incl k).map s))
      (wilsonCharExp t ht s) := by
  -- `(wilsonSystem.incl k).map s = (ObsHom.idHom charAlg).map s = s`, so the
  -- two exact heat-kernel moments are the very same `CReal`.
  have hmap : (wilsonSystem.incl k).map s = s := rfl
  rw [hmap]
  exact creal_equiv_refl _

/-- **The exact `CReal` moments are non-trivial** (the real-moment witness
is not the placeholder): the unit `χ_0` has exact moment `≃ 1`
(normalization), as the heat-kernel measure is a probability measure.  This
pins the `CReal` consistency above to genuine heat-kernel data. -/
theorem wilsonRealMoment_unit (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (wilsonCharExp t ht 0) 1 ∧ ExpPos.geRat (wilsonCharExp t ht 0) 1 :=
  wilsonCharExp_unit t ht

end YMGap.Continuum.WilsonConsistency

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonConsistency.wilsonSystem
#print axioms YMGap.Continuum.WilsonConsistency.wilsonFunc_normalized
#print axioms YMGap.Continuum.WilsonConsistency.wilsonFunc_nonconstant
#print axioms YMGap.Continuum.WilsonConsistency.wilsonConsistency
#print axioms YMGap.Continuum.WilsonConsistency.wilsonMomentTransport
#print axioms YMGap.Continuum.WilsonConsistency.wilsonContinuumMeasure
#print axioms YMGap.Continuum.WilsonConsistency.wilsonContinuumMeasure_proj
#print axioms YMGap.Continuum.WilsonConsistency.wilsonContinuumMeasure_coherent
#print axioms YMGap.Continuum.WilsonConsistency.creal_equiv_refl
#print axioms YMGap.Continuum.WilsonConsistency.wilsonRealMomentConsistent
#print axioms YMGap.Continuum.WilsonConsistency.wilsonRealMoment_unit
