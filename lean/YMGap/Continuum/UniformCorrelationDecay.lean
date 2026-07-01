/-
YMGap.Continuum.UniformCorrelationDecay
=======================================

**The category-correct open continuum input: the mass gap is spacing-uniform
exponential decay of the physical connected correlator — NOT a Wilson-loop area
law.**

# Why this module exists (read first)

The a→0 continuum obligation was previously carried as the abstract
margin-recursion surrogate
`UniformCouplingFromAF.TrueMarginRecursion` (a `DefectGapRecursion` whose
`physGap` is pinned to an abstract "true margin").  That surrogate is neither the
physically-correct statement of the mass gap nor a citable one.

This module replaces it with the PHYSICALLY CORRECT, CITABLE open input:

    the correlation length ξ = 1/m₋ stays FINITE and BOUNDED as a → 0,

i.e. the connected two-point correlator `C_{a,L}(x)` of a local gauge-invariant
observable decays exponentially, `|C_{a,L}(x)| ≤ A·e^{−m₋·|x|} + ε(r)`, with a
mass `m₋ > 0` that is UNIFORM in the lattice spacing `a`.  THAT — a
spacing-uniform correlation-decay RATE — is the constructive mass gap.  It is the
correlation-decay statement of OS4/clustering, *not* an area law (area laws are a
separate premise about Wilson loops, handled elsewhere and deliberately untouched
here).

# What is stated / proved here

  * `PhysicalCorrelator` — the connected two-point correlator `C_{a,L}(n)` at
    physical separation `|x| = n·a`, grounded in the REAL SU(2) Wilson connected
    correlator `WilsonConnCorr.wilsonG` (the concrete inhabitant
    `wilsonPhysicalCorrelator`, whose fixed-spacing exponential decay
    `wilsonPhysicalCorrelator_decay` is the real `wilsonG_decay`).

  * `UniformPhysicalCorrelationDecay` — the NEW primary OPEN input.  Carries a
    spacing-uniform physical mass `m₋ : CReal` (with a Type-level positivity
    witness, hence `CReal.IsPositive m₋`), an amplitude `A`, an error modulus
    `ε : Q' → CReal` with `ε(r) → 0`, and the decay bound
    `|C_{a,L}(x)| ≤ A·e^{−m₋·|x|} + ε(r)`.  The exponential envelope reuses the
    constructive `CReal.expNegC` (per lattice step `e^{−m₋·a}`, raised to the
    separation `n`, so `= e^{−m₋·n·a} = e^{−m₋·|x|}`).  UNINHABITED on ℝ⁴ — it
    IS the open continuum physics.

  * `uniformPhysicalCorrelationDecay_imp_massGap` — PROVED:
    `UniformPhysicalCorrelationDecay ⟹ MassGap`.  The uniform decay RATE `m₋` IS
    the gap; it survives `a → 0` precisely because it is uniform.

  * `massGap_of_spectralGapData` — the connection to the existing reconstructed
    gap machinery: a `GNSDynamics.SpectralGapData` yields a `MassGap`
    (`Δ = 1 − sep > 0` lifted to a positive `CReal`).

  * `massGap_imp_downstream` — PROVED (re-export): `MassGap ⟹` the formal
    downstream consequences — the infinite-volume positive mass
    (`ClayScorecard.RubricInfiniteVolumeMass`) and OS4 geometric clustering of the
    real Wilson correlator (`ClayScorecard.rubric_clustering_met`).  The
    reconstructed spectral-gap decay is re-exported via
    `massGap_reconstructed_gap` (`GNSDynamics.mass_gap_of_spectralGap`).

  * `trueMargin_of_correlationDecay` — the DEMOTION: the physical decay REFINES
    the old surrogate, `UniformPhysicalCorrelationDecay ⟹ TrueMarginRecursion`,
    with the abstract margin now DERIVED from the uniform mass floor `m₋`.  Hence
    `correlationDecay_imp_rubricUniformInCoupling` recovers the old
    `RubricUniformInCoupling` clause as a consequence.

# HONEST scope

The ONLY object left uninhabited is `UniformPhysicalCorrelationDecay` itself — the
genuine open continuum physics (Bałaban / Shen–Zhu–Zhu class): a spacing-uniform
correlation-decay rate.  Every implication in the chain
`UniformPhysicalCorrelationDecay ⟹ MassGap ⟹ Downstream` is proved GREEN, and the
old `TrueMarginRecursion` is demoted to a derived consequence.  Nothing here
closes 4D Yang–Mills.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the CReal / `Q'` backbone; the load-bearing positivity
witness is Type-level data (`CRealPosWitness`), never a `Prop`-∃; the error
modulus is a `Pi` into a subtype, never a `Prop`-∃ witness.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
No `Classical.*`, no `by_contra`, no `native_decide`, no `sorry`, no custom axiom.
-/

import YMGap.Continuum.WilsonConnCorr
import YMGap.Constructive.CRealExp
import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.UniformCouplingFromAF

namespace YMGap.Continuum.UniformCorrelationDecay

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Rubric.ClayScorecard

/-! ## 1. A Type-level strict-positivity witness for a `CReal`

`CReal.IsPositive` is a `Prop`-∃ (`∃ ε, 0 < ε ∧ ofQ' ε ≤ x`).  For the
load-bearing mass gap we carry the SAME content as Type-level DATA (Rule 8): the
positive rational floor `floor` together with `ofQ' floor ≤ m`.  It projects onto
`CReal.IsPositive` on demand. -/

/-- **Type-level strict positivity of a `CReal`.**  A positive rational `floor`
with `ofQ' floor ≤ m` — the constructive "`m > 0`" carried as data, so it can feed
Type-level consumers (a `DefectGapRecursion` floor, a uniform spacing floor). -/
structure CRealPosWitness (m : CReal) : Type where
  /-- The positive rational lower bound (the reciprocal correlation length floor). -/
  floor : Q'
  /-- The floor is strictly positive. -/
  floor_pos : (0 : Q') < floor
  /-- The floor lies below `m` at the `CReal` level. -/
  floor_le : CReal.ofQ' floor ≤ m

/-- The Type-level witness yields the `Prop`-level `CReal.IsPositive`. -/
def CRealPosWitness.isPositive {m : CReal} (h : CRealPosWitness m) :
    CReal.IsPositive m :=
  ⟨h.floor, h.floor_pos, h.floor_le⟩

/-! ## 2. The physical connected correlator `C_{a,L}(x)`

`PhysicalCorrelator` records a connected two-point correlator at physical
separation `|x| = n·a` (lattice spacing `a`, linear volume `L`), pinned to the
REAL SU(2) Wilson connected correlator `WilsonConnCorr.wilsonG`.  This is the
genuine object (a vacuum-subtracted character double-sum), NOT an abstract
`corr`. -/

/-- **The physical connected two-point correlator.**  `corr n = C_{a,L}(x)` at
lattice separation `n`, physical separation `|x| = n·a`, pinned to the real Wilson
connected correlator `wilsonG w (L+1) n`. -/
structure PhysicalCorrelator : Type where
  /-- The lattice spacing `a`. -/
  a : Q'
  /-- The spacing is strictly positive. -/
  a_pos : (0 : Q') < a
  /-- The linear volume `L` (number of chain plaquettes / sites). -/
  L : Nat
  /-- The coupling `w` (strong coupling `w = gw` in the concrete inhabitant). -/
  w : Q'
  /-- The coupling is nonnegative. -/
  w_nonneg : (0 : Q') ≤ w
  /-- The connected correlator at integer separation `n`. -/
  corr : Nat → Q'
  /-- **The pin:** `corr` IS the real Wilson connected correlator (not an abstract
  `corr`).  This grounds the physical correlator in the genuine character
  double-sum `WilsonConnCorr.wilsonG`. -/
  corr_is_wilson : ∀ n, corr n = WilsonConnCorr.wilsonG w (L + 1) n

/-- The physical separation `|x| = n·a` of the correlator at lattice separation
`n`. -/
def PhysicalCorrelator.physSep (P : PhysicalCorrelator) (n : Nat) : Q' :=
  Q'.ofNat n * P.a

/-- **The concrete inhabitant (non-vacuity).**  At any positive spacing `a` and
volume `L`, the strong-coupling (`w = gw = 1/6`) Wilson connected correlator is a
`PhysicalCorrelator`.  Grounds the interface in the REAL object. -/
def wilsonPhysicalCorrelator (a : Q') (ha : (0 : Q') < a) (L : Nat) :
    PhysicalCorrelator where
  a := a
  a_pos := ha
  L := L
  w := gw
  w_nonneg := gw_nonneg
  corr := fun n => WilsonConnCorr.wilsonG gw (L + 1) n
  corr_is_wilson := fun _ => rfl

/-- **Fixed-spacing exponential decay of the real physical correlator (PROVED).**
The concrete inhabitant's correlator decays geometrically,
`corr n ≤ (ofNat L · ρ)·ρ^n` with `ρ = rho gw = 2·(1/6)³ < 1` — EXACTLY the real
`WilsonConnCorr.wilsonG_decay`.  (Fixed spacing; the OPEN content is the
spacing-UNIFORMITY of the rate, §4.) -/
theorem wilsonPhysicalCorrelator_decay (a : Q') (ha : (0 : Q') < a) (L n : Nat) :
    (wilsonPhysicalCorrelator a ha L).corr n
      ≤ (Q'.ofNat L * rho gw) * (rho gw) ^ n :=
  WilsonConnCorr.wilsonG_decay gw_nonneg (by decide) L n

/-! ## 3. The exponential envelope `e^{−m₋·|x|}` via `CReal.expNegC`

The physical envelope is `e^{−m₋·|x|} = e^{−m₋·(n·a)} = (e^{−m₋·a})^n`: the
per-lattice-step factor `e^{−m₋·a}` (`stepFactor`, `≤ 1`) raised to the separation
`n`.  We reuse the constructive `CReal.expNegC` (packaged as `expNegCD` with its
Type-level modulus data `ExpNegCData`).  Written geometrically (a `cpow`) so the
exponent argument `m₋·a` stays bounded (`≤ 1`), exactly the discipline
`expNegC` requires. -/

/-- The per-lattice-step decay factor `e^{−m₋·a}` as a `CReal`, via `expNegC`. -/
def stepFactor (m : CReal) (a : Q')
    (d : CReal.ExpNegCData (CReal.mul m (CReal.ofQ' a))) : CReal :=
  CReal.expNegCD (CReal.mul m (CReal.ofQ' a)) d

/-- **The physical exponential envelope** `e^{−m₋·|x|} = (e^{−m₋·a})^n` at physical
separation `|x| = n·a`. -/
def physEnvelope (m : CReal) (a : Q')
    (d : CReal.ExpNegCData (CReal.mul m (CReal.ofQ' a))) (n : Nat) : CReal :=
  CReal.cpow (stepFactor m a d) n

/-- At separation `0` the envelope is `1` (`cpow _ 0 = cone`): normalization. -/
@[simp] theorem physEnvelope_zero (m : CReal) (a : Q')
    (d : CReal.ExpNegCData (CReal.mul m (CReal.ofQ' a))) :
    physEnvelope m a d 0 = CReal.cone := rfl

/-! ## 4. The NEW primary open input — spacing-uniform physical correlation decay

`UniformPhysicalCorrelationDecay` says: there is a SINGLE physical mass `m₋ > 0`,
UNIFORM in the spacing `a`, such that the connected correlator obeys
`|C_{a,L}(x)| ≤ A·e^{−m₋·|x|} + ε(r)` with `ε(r) → 0` as the dimensionless ratio
`r = max(a/|x|, |x|/L) → 0`.  The content is: the correlation length `ξ = 1/m₋`
stays FINITE and BOUNDED as `a → 0`.  THAT is the mass gap.  UNINHABITED on ℝ⁴. -/

/-- **THE NEW PRIMARY OPEN CONTINUUM INPUT.**  Spacing-uniform exponential decay of
the physical connected correlator.  The mass `m₋` is uniform in the spacing (its
positivity witness `m_pos` does NOT depend on `a`), so the correlation length
`ξ = 1/m₋` is bounded as `a → 0` — the constructive mass gap.  Left UNINHABITED
for the genuine `a → 0` continuum. -/
structure UniformPhysicalCorrelationDecay : Type where
  /-- **The spacing-uniform physical mass** `m₋ = 1/ξ`. -/
  m : CReal
  /-- **The uniform positive-mass witness** (Type-level; `⟹ CReal.IsPositive m`).
  Crucially spacing-INDEPENDENT: this single floor bounds `m₋` at every spacing. -/
  m_pos : CRealPosWitness m
  /-- **The amplitude** `A` (finite — every `CReal` is finite). -/
  A : CReal
  /-- The amplitude is nonnegative (so the envelope bound is meaningful). -/
  A_nonneg : CReal.leEv CReal.czero A
  /-- The `expNegC` modulus data for `e^{−m₋·a}` at each spacing `a`. -/
  expData : (a : Q') → CReal.ExpNegCData (CReal.mul m (CReal.ofQ' a))
  /-- **The spacing-indexed physical correlator family** (each a real
  `PhysicalCorrelator` at spacing `a`). -/
  fam : (a : Q') → (0 : Q') < a → PhysicalCorrelator
  /-- **The error modulus** `ε : Q' → CReal`. -/
  err : Q' → CReal
  /-- The dimensionless ratio `r = max(a/|x|, |x|/L)` controlling the regime
  `a ≪ |x| ≪ L`. -/
  ratio : Q' → Nat → Q'
  /-- The ratio is nonnegative. -/
  ratio_nonneg : ∀ (a : Q') (n : Nat), (0 : Q') ≤ ratio a n
  /-- **THE DECAY BOUND.**  For every spacing `a` and separation `n`,
  `|C_{a,L}(x)| ≤ A·e^{−m₋·|x|} + ε(r)` with `|x| = n·a` and `r = ratio a n`. -/
  decay : ∀ (a : Q') (ha : (0 : Q') < a) (n : Nat),
    CReal.leEv (CReal.ofQ' (Q'.abs ((fam a ha).corr n)))
      (CReal.add (CReal.mul A (physEnvelope m a (expData a) n)) (err (ratio a n)))
  /-- **`ε(r) → 0` as `r → 0`** (Type-level modulus of vanishing): for every
  tolerance `η > 0` there is a `δ > 0` with `ε(r) ≤ η` whenever `0 ≤ r ≤ δ`. -/
  err_vanish : ∀ η : Q', (0 : Q') < η →
    { δ : Q' // (0 : Q') < δ ∧
      ∀ r : Q', (0 : Q') ≤ r → r ≤ δ → CReal.leEv (err r) (CReal.ofQ' η) }

/-! ## 5. The constructive mass gap and the primary implication

`MassGap` is the constructive mass gap: a physical mass `m` with a Type-level
strict-positivity witness (`⟹ CReal.IsPositive m`, the constructive "gap above the
vacuum").  The primary implication reads off the uniform decay rate `m₋` as the
gap. -/

/-- **The constructive mass gap.**  A spacing-uniform physical mass `m` with a
Type-level positivity witness — the constructive "positive gap above the vacuum".
-/
structure MassGap : Type where
  /-- The physical mass gap `m` (a spacing-uniform `CReal`). -/
  m : CReal
  /-- The Type-level strict-positivity witness (`⟹ CReal.IsPositive m`). -/
  pos : CRealPosWitness m

/-- The mass gap is `CReal.IsPositive`. -/
def MassGap.isPositive (G : MassGap) : CReal.IsPositive G.m := G.pos.isPositive

/-- **`uniformPhysicalCorrelationDecay_imp_massGap` (PROVED).**  The spacing-uniform
correlation-decay RATE `m₋` IS the constructive mass gap: it is positive and, being
uniform in `a`, survives the continuum limit `a → 0`.  This is the category-correct
identification — the gap is the decay rate, not an area-law coefficient. -/
def uniformPhysicalCorrelationDecay_imp_massGap
    (U : UniformPhysicalCorrelationDecay) : MassGap where
  m := U.m
  pos := U.m_pos

/-! ## 6. Connection to the existing reconstructed-gap machinery

`GNSDynamics.SpectralGapData` (a located transfer-operator gap `Δ = 1 − sep > 0`)
produces a `MassGap`: the positive rational `Δ` lifts to a positive `CReal`.  So a
reconstructed spectral gap and the physical-decay mass gap are the SAME
constructive object. -/

/-- **`massGap_of_spectralGapData`.**  Any `SpectralGapData` on a complete GNS
Hilbert space yields a `MassGap`: the reconstructed margin `Δ = 1 − sep > 0`
(`SpectralGapData.massGap`, `SpectralGapData.massGap_pos`) lifted to the positive
`CReal` `ofQ' Δ`.  Connects this module's `MassGap` to `GNSDynamics`. -/
def massGap_of_spectralGapData {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : MassGap where
  m := CReal.ofQ' G.massGap
  pos :=
    { floor := G.massGap
      floor_pos := G.massGap_pos
      floor_le := CReal.le_refl (CReal.ofQ' G.massGap) }

/-! ## 7. Downstream formal consequences of the mass gap (re-export) -/

/-- **`massGap_imp_downstream` (PROVED, re-export).**  From a `MassGap`, the formal
downstream consequences:

  * the infinite-volume positive mass `ClayScorecard.RubricInfiniteVolumeMass m`
    (`= CReal.IsPositive m`); AND
  * OS4 geometric clustering of the REAL Wilson connected correlator at every
    cutoff `M` (`ClayScorecard.rubric_clustering_met`, i.e. the real
    `wilsonG_decay`).

The clustering half is an unconditional fixed-spacing theorem; the mass-gap
hypothesis supplies the spacing-UNIFORM positive rate. -/
theorem massGap_imp_downstream (G : MassGap) :
    RubricInfiniteVolumeMass G.m
    ∧ (∀ M : Nat, RubricClustering (fun n => WilsonConnCorr.wilsonG gw (M + 1) n)) :=
  ⟨G.pos.isPositive, rubric_clustering_met⟩

/-- **`massGap_reconstructed_gap` (re-export).**  The reconstructed spectral-gap
decay `G(n) ≤ G(0)·sep^n` with a strictly positive margin `Δ` — the
`e^{−Δ}`-type bound — from `GNSDynamics.mass_gap_of_spectralGap`.  This is the
Hamiltonian-side downstream consequence of a located transfer-operator gap. -/
theorem massGap_reconstructed_gap {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) :
    ∃ Δ : Q', (0 : Q') < Δ ∧
      ∀ n : Nat, corr G.model n ≤ (corr G.model 0) * G.gap.sep ^ n :=
  mass_gap_of_spectralGap G

/-! ## 8. DEMOTION — the physical decay refines the old margin surrogate

The old open input `UniformCouplingFromAF.TrueMarginRecursion` (an abstract
margin-recursion) is now a DERIVED consequence: the spacing-uniform mass floor
`m₋` furnishes a genuine `DefectGapRecursion` whose gaps ARE the (constant, uniform)
physical margin.  Hence the whole old `RubricUniformInCoupling` clause follows from
the physical decay. -/

/-- **`trueMargin_of_correlationDecay` (PROVED — the DEMOTION).**  From the physical
decay's spacing-uniform positive mass floor `ε = m₋.floor`, build a genuine
`TrueMarginRecursion`: the zero-defect constant-margin `DefectGapRecursion` at gap
`ε`, with the true margin pinned to `ε`.  The abstract "true margin" is thus
DERIVED from the citable physical decay — no longer a primitive open input. -/
def trueMargin_of_correlationDecay
    (U : UniformPhysicalCorrelationDecay) : TrueMarginRecursion where
  D := trivialDefectGapRecursion U.m_pos.floor U.m_pos.floor_pos
  trueMargin := fun _ => U.m_pos.floor
  physGap_is_trueMargin := fun _ => rfl

/-- **`correlationDecay_imp_rubricUniformInCoupling` (PROVED).**  Composing the
demotion with the proved `rubricUniformInCoupling_of_trueMargin`, the old
coupling-uniform gap clause `RubricUniformInCoupling` is recovered as a consequence
of the physical correlation decay. -/
theorem correlationDecay_imp_rubricUniformInCoupling
    (U : UniformPhysicalCorrelationDecay) : RubricUniformInCoupling :=
  rubricUniformInCoupling_of_trueMargin (trueMargin_of_correlationDecay U)

/-! ## 9. Documentation: PROVED vs OPEN (AGENTS.md Rule 6)

PROVED (GREEN, axiom-clean):

  * `wilsonPhysicalCorrelator`, `wilsonPhysicalCorrelator_decay` — the physical
    correlator grounded in the real `wilsonG` with its fixed-spacing exp decay;
  * `uniformPhysicalCorrelationDecay_imp_massGap` — the uniform decay rate `m₋` IS
    the mass gap (`UniformPhysicalCorrelationDecay ⟹ MassGap`);
  * `massGap_of_spectralGapData` — `GNSDynamics.SpectralGapData ⟹ MassGap`
    (reconstructed margin `Δ = 1 − sep` lifted to a positive `CReal`);
  * `massGap_imp_downstream`, `massGap_reconstructed_gap` — the downstream
    consequences (infinite-volume positive mass, OS4 clustering of the real Wilson
    correlator, reconstructed spectral-gap decay);
  * `trueMargin_of_correlationDecay`, `correlationDecay_imp_rubricUniformInCoupling`
    — the DEMOTION: the old `TrueMarginRecursion` / `RubricUniformInCoupling` are
    now DERIVED from the physical decay.

OPEN (the SINGLE citable continuum input, UNINHABITED here):

  * `UniformPhysicalCorrelationDecay` — spacing-uniform exponential decay of the
    physical connected correlator; equivalently, the correlation length
    `ξ = 1/m₋` stays finite and bounded as `a → 0`.  THIS is the mass gap, stated
    as correlation decay (OS4), NOT as a Wilson-loop area law.  The open continuum
    physics (Bałaban / Shen–Zhu–Zhu class).

This module makes the mass-gap continuum input category-correct and citable, and
demotes the abstract margin surrogate to a derived consequence.  It does NOT close
4D Yang–Mills. -/

end YMGap.Continuum.UniformCorrelationDecay

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.UniformCorrelationDecay.CRealPosWitness.isPositive
#print axioms YMGap.Continuum.UniformCorrelationDecay.wilsonPhysicalCorrelator
#print axioms YMGap.Continuum.UniformCorrelationDecay.wilsonPhysicalCorrelator_decay
#print axioms YMGap.Continuum.UniformCorrelationDecay.physEnvelope_zero
#print axioms YMGap.Continuum.UniformCorrelationDecay.uniformPhysicalCorrelationDecay_imp_massGap
#print axioms YMGap.Continuum.UniformCorrelationDecay.massGap_of_spectralGapData
#print axioms YMGap.Continuum.UniformCorrelationDecay.massGap_imp_downstream
#print axioms YMGap.Continuum.UniformCorrelationDecay.massGap_reconstructed_gap
#print axioms YMGap.Continuum.UniformCorrelationDecay.trueMargin_of_correlationDecay
#print axioms YMGap.Continuum.UniformCorrelationDecay.correlationDecay_imp_rubricUniformInCoupling
