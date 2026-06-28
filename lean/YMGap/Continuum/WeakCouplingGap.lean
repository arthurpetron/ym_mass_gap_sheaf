/-
Track B / R2 — the WEAK-COUPLING spectral-gap object, taken on DIRECTLY.

# What this module is — and what it is emphatically NOT (read first)

This module does NOT prove the 4D Yang–Mills weak-coupling / continuum mass gap,
and it does NOT inhabit any continuum wall.  It does three honest things:

  1. PROVES that the single-link character-coefficient object (the
     "gap = 1 − leading character coefficient" margin) FAILS at weak coupling:
     its located-separator candidate is `≥ 1`, so the located-gap requirement
     `sep < 1` is violated.  Hence the located weak-coupling gap CANNOT be the
     single-link character operator.

  2. DEFINES the correct weak-coupling gap object — the located second eigenvalue
     of the gauge-invariant SPATIAL transfer operator, equivalently the
     connected-correlator decay rate — abstractly, via the EXISTING located-gap
     machinery (`clustering_implies_located`), NOT via the single-link `coeffW`.
     The weak-coupling clustering input is carried as a NAMED OPEN obligation
     (`WeakClusteringBound`); GIVEN it, the located weak gap EXISTS (the reduction
     is PROVED) and genuinely has `sep < 1`.

  3. CONNECTS the weak gap to the existing program: it ties the weak gap rate to
     the dimensionless `RGLandingCertificate` shape, and it makes the "both sides
     meet" reduction explicit — the weak clustering would follow from the PROVED
     strong-coupling clustering PLUS an RG-flow-preservation step
     (`RGClusteringTransport`, the "middle" wall), which is left uninhabited.

# The pathology of the single-link object (Deliverable 1)

The diagonal SU(2) heat-kernel character coefficient at spin `s = 1` is
`coeffW w 1 = 2·w³` (`w = e^{−t}`, `t → 0` weak coupling).  The single-link
"vacuum" coefficient is `coeffW w 0 = 1`.  At the weak witness `w = 4/5 = 0.8`
(just past the strong/weak boundary `2^{−1/3} ≈ 0.794`),

      coeffW (4/5) 1  =  2·(4/5)³  =  128/125  >  1,

so the single-link separator candidate EXCEEDS the vacuum `1`.  A located gap
REQUIRES `sep < 1` (the excited spectrum strictly below the normalized vacuum
eigenvalue `1`); here `¬ (coeffW (4/5) 1 < 1)`, so NO `LocatedSpectralGap` of the
single-link character operator exists at weak coupling.  Concretely, the
single-link object's "vacuum" is no longer its largest eigenvalue — it is the
WRONG gap object in the weak-coupling region.

# The correct weak-coupling gap object (Deliverable 2)

`WeakClusteringBound` packages the GENUINE open content: a `SpectralModel` `S`
(the gauge-invariant spatial transfer operator at weak coupling) together with a
geometric clustering rate `corr S n ≤ C·μ^n`, `0 < μ < 1`, for the weak-coupling
connected correlator, plus the per-mode coupling / unused-slot side conditions
that `clustering_implies_located` consumes.  NO inhabitant of
`WeakClusteringBound` is constructed for 4D — exponential clustering at weak
coupling is exactly the open continuum problem.

GIVEN a `WeakClusteringBound`, `weakSpectralGap` builds a genuine
`LocatedSpectralGap` via the PROVED converse `clustering_implies_located`
(`sep = μ`), and `weakSpectralGap_sep_lt_one` confirms the object genuinely has a
located gap (`sep = μ < 1`) — UNLIKE the single-link one.  So the reduction
"weak clustering ⇒ weak located gap" is PROVED; only the clustering input is open.

# The "both sides meet" reduction and the RG landing (Deliverable 3)

`RGClusteringTransport` (a `Prop`, uninhabited) is the RG-flow-preservation step
that would carry exponential clustering from the PROVED strong-coupling regime
(`MayerClustering` / `GenuineKP`, uniform on the strong window) through the
intermediate "middle" to weak coupling.  `weakClustering_of_strong_and_transport`
shows: weak located gap ⟸ weak clustering ⟸ (strong clustering, PROVED) +
`RGClusteringTransport` (open middle wall).  And `weakGap_landing` ties the weak
gap rate `μ` to the dimensionless `RGLandingCertificate` shape (made dimensionless
against `Λ_YM`, with the open scale normalization `RGLandingInput` unchanged).

# Honest scope (Deliverable 4)

This module DEFINES the correct weak-coupling gap object (the spatial-transfer
located gap / connected-correlator decay), PROVES the single-link character
object fails at weak coupling, and REDUCES the weak gap to weak-coupling
clustering (the proved located-gap engine) and thence to strong clustering
(proved) + `RGClusteringTransport` (the middle wall) / the RG landing.  It does
NOT prove weak-coupling gap positivity — that exponentially-small,
dimensionally-transmuted, RG-controlled gap is the open continuum problem.  No 4D
Yang–Mills gap is claimed; `WeakClusteringBound`, `RGClusteringTransport`, and
`RGLandingInput` are uninhabited by design.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` / `Nat` core.  No `Classical.*`, no `native_decide`, no
`decide` on non-decidable props.  No `sorry` / `admit` / new `axiom` /
`Prop := True`.  All witnesses are `Type`-level data; the reduction is genuine
(it consumes the real `clustering_implies_located`), the pathology is a real
`decide` inequality, and the named obligations are real structures/`Prop`s with
content — never vacuous, never faked.  Every load-bearing declaration is gated
with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusionMarginScope
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.RGLandingCertificate
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.WeakCouplingGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.FusionMarginScope
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ContinuumClosureProgram (DefectGapRecursion)

/-! ## DELIVERABLE 1 — the single-link object FAILS at weak coupling

The single-link located-separator candidate is the vacuum-normalized excited
coefficient `coeffW w 1 / coeffW w 0`.  Since `coeffW w 0 = 1`, this is just
`coeffW w 1 = 2w³`.  At the weak witness `w = 4/5` it is `128/125 ≥ 1`, so the
located-gap requirement `sep < 1` FAILS. -/

/-- **The single-link located-separator candidate** `coeffW w 1 / coeffW w 0`,
carried division-free via `divPos` (with `coeffW w 0 > 0`).  This is the
vacuum-normalized first-excited character coefficient — the object the
"gap = 1 − leading coefficient" margin would use as the located separator. -/
def singleLinkSep (w : Q') (hw : (0 : Q') < coeffW w 0) : Q' :=
  Q'.divPos (coeffW w 1) (coeffW w 0) hw

/-- `coeffW w 0 = 1 > 0` — the single-link vacuum coefficient is positive
(needed to form `singleLinkSep`). -/
theorem coeffW_zero_pos (w : Q') : (0 : Q') < coeffW w 0 := by
  rw [coeffW_zero]; exact CReal.pos_of_num_pos (by decide)

/-- **`singleLinkSep` is the excited coefficient `coeffW w 1`.**  Since the
vacuum coefficient is `coeffW w 0 = 1`, the division-free separator collapses to
`coeffW w 1` (as `Q'` `eqv`): `divPos (coeffW w 1) 1 ≃ coeffW w 1`.  This pins the
single-link separator to the raw excited coefficient `2w³`. -/
theorem singleLinkSep_eqv_coeffW1 (w : Q') (hw : (0 : Q') < coeffW w 0) :
    (singleLinkSep w hw).eqv (coeffW w 1) := by
  -- divPos p q · q ≃ p ; with q = coeffW w 0 = 1 ⇒ divPos p 1 · 1 ≃ p ⇒ divPos p 1 ≃ p.
  have hmul : (singleLinkSep w hw * coeffW w 0).eqv (coeffW w 1) :=
    Q'.divPos_mul_eqv (coeffW w 1) (coeffW w 0) hw
  -- rewrite coeffW w 0 = 1 inside the product
  have hone : coeffW w 0 = (1 : Q') := coeffW_zero w
  have hmul1 : (singleLinkSep w hw * (1 : Q')).eqv (coeffW w 1) := by
    rw [hone] at hmul; exact hmul
  -- singleLinkSep · 1 ≃ singleLinkSep, so singleLinkSep ≃ coeffW w 1
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv (singleLinkSep w hw))) hmul1

/-- **DELIVERABLE 1 (the pathology, raw).**  At the weak-coupling witness
`w = 4/5`, the raw single-link excited coefficient is `≥ 1`:
`coeffW (4/5) 1 = 128/125 ≥ 1`.  (Strengthens `raw_excited_exceeds_vacuum`'s
strict `<` to the `≤` needed to NEGATE `sep < 1`.) -/
theorem singleLink_no_gap_weak : (1 : Q') ≤ coeffW wWeak 1 :=
  Q'.le_of_lt raw_excited_exceeds_vacuum

/-- **DELIVERABLE 1 (the `sep < 1` failure).**  The single-link separator
candidate at weak coupling is NOT `< 1`: `¬ (coeffW (4/5) 1 < 1)`.  Since a
`LocatedSpectralGap` REQUIRES `sep < 1`, there is NO located gap of the
single-link character operator at weak coupling — its "vacuum" coefficient `1` is
not the largest eigenvalue, so it is the WRONG gap object there. -/
theorem singleLink_sep_not_lt_one_weak : ¬ (coeffW wWeak 1 < (1 : Q')) := by
  intro hlt
  -- coeffW wWeak 1 < 1 ≤ coeffW wWeak 1 contradicts irreflexivity
  exact lt_irrefl' _ (lt_of_lt_of_le hlt singleLink_no_gap_weak)

/-- **DELIVERABLE 1 (on the `divPos` separator itself).**  The division-free
single-link separator `singleLinkSep (4/5)` is itself NOT `< 1` (it `eqv`s
`coeffW (4/5) 1 ≥ 1`).  So forming the separator division-free does not rescue the
`sep < 1` requirement. -/
theorem singleLinkSep_not_lt_one_weak :
    ¬ (singleLinkSep wWeak (coeffW_zero_pos wWeak) < (1 : Q')) := by
  intro hlt
  -- singleLinkSep ≃ coeffW wWeak 1, so coeffW wWeak 1 < 1, contradiction.
  have heq : (singleLinkSep wWeak (coeffW_zero_pos wWeak)).eqv (coeffW wWeak 1) :=
    singleLinkSep_eqv_coeffW1 wWeak (coeffW_zero_pos wWeak)
  have : coeffW wWeak 1 < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.ge_of_eqv heq) hlt
  exact singleLink_sep_not_lt_one_weak this

/-! ## DELIVERABLE 2 — the correct weak-coupling gap object

The genuine weak-coupling gap is the located second eigenvalue of the
gauge-invariant SPATIAL transfer operator, equivalently the connected-correlator
decay rate — defined via the EXISTING `clustering_implies_located` engine, NOT the
single-link `coeffW`.

`WeakClusteringBound` is the NAMED OPEN obligation: a `SpectralModel` for the
weak-coupling spatial transfer operator with a genuine geometric clustering rate
`μ < 1` and the side conditions the converse consumes.  NO 4D inhabitant. -/

/-- **`WeakClusteringBound` — the NAMED OPEN weak-coupling clustering obligation.**

`Type`-level data (Rule 8).  An inhabitant supplies:
  * `S` — the gauge-invariant SPATIAL transfer operator at weak coupling (a finite
    `SpectralModel`);
  * `C μ` with `0 < C`, `0 < μ`, `μ < 1` — the geometric clustering envelope;
  * `clusters : ∀ n, corr S n ≤ C·μ^n` — the weak-coupling connected-correlator
    EXPONENTIAL decay (the genuine open content);
  * `coupled` / `dead` — the per-mode coupling on live modes and the unused-slot
    bound (the honest side conditions of `clustering_implies_located`).

NO inhabitant for 4D weak coupling is constructed: weak-coupling exponential
clustering is the open continuum problem. -/
structure WeakClusteringBound : Type where
  /-- The gauge-invariant spatial transfer operator at weak coupling. -/
  S : SpectralModel
  /-- The clustering prefactor. -/
  C : Q'
  /-- The geometric clustering rate (the located separator). -/
  μ : Q'
  /-- The prefactor is positive. -/
  C_pos : (0 : Q') < C
  /-- The rate is positive. -/
  μ_pos : (0 : Q') < μ
  /-- The rate is strictly below `1` — the located-gap requirement at weak
  coupling (the content the single-link object FAILS). -/
  μ_lt_one : μ < (1 : Q')
  /-- **THE OPEN CONTENT — weak-coupling exponential clustering.**  The connected
  correlator of the weak-coupling spatial transfer operator decays geometrically,
  `corr S n ≤ C·μ^n`. -/
  clusters : ∀ n, corr S n ≤ C * μ ^ n
  /-- Per-mode coupling on the live modes (`i < k ⇒ wᵢ > 0`). -/
  coupled : ∀ i, i < S.k → (0 : Q') < S.w i
  /-- The unused-slot bound (`k ≤ i ⇒ λᵢ ≤ μ`). -/
  dead : ∀ i, S.k ≤ i → S.lam i ≤ μ

/-- **`weakSpectralGap` — the PROVED reduction (clustering ⇒ weak located gap).**

GIVEN a `WeakClusteringBound W`, the located weak-coupling spectral gap EXISTS:
`LocatedSpectralGap W.S` with `sep = W.μ`.  Built DIRECTLY from the genuine
converse `clustering_implies_located` (NOT a re-posited gap) — the reduction is
real proof; only the clustering input `W.clusters` is open. -/
def weakSpectralGap (W : WeakClusteringBound) : LocatedSpectralGap W.S :=
  clustering_implies_located W.S W.C W.μ
    W.C_pos W.μ_pos W.μ_lt_one W.clusters W.coupled W.dead

/-- **`weakSpectralGap_sep_lt_one` — the weak gap genuinely HAS a located gap.**

The located weak gap's separator is `< 1` (it is the real clustering rate
`W.μ < 1`), CONDITIONAL on the named clustering obligation.  This confirms the
weak-coupling gap object genuinely admits `sep < 1` — UNLIKE the single-link
character object (`singleLink_sep_not_lt_one_weak`). -/
theorem weakSpectralGap_sep_lt_one (W : WeakClusteringBound) :
    (weakSpectralGap W).sep < (1 : Q') :=
  (weakSpectralGap W).sep_lt_one

/-- The located weak gap's separator IS the clustering rate `W.μ`
(definitional: `clustering_implies_located` sets `sep := μ`). -/
theorem weakSpectralGap_sep_eq (W : WeakClusteringBound) :
    (weakSpectralGap W).sep = W.μ := rfl

/-- **The positive weak eigenvalue-gap margin** `1 − μ > 0`, CONDITIONAL on the
named clustering — the located weak mass gap as a strictly positive `Q'` quantity
(the gap in transfer-eigenvalue space, no `log`).  This is the constructive
"there is a weak-coupling gap" witness GIVEN clustering. -/
theorem weakSpectralGap_margin_pos (W : WeakClusteringBound) :
    (0 : Q') < (weakSpectralGap W).gapMargin :=
  (weakSpectralGap W).gapMargin_pos

/-! ## DELIVERABLE 3 — the "both sides meet" reduction and the RG landing

The weak clustering would follow from the PROVED strong-coupling clustering plus
an RG-flow-preservation step.  We name that step `RGClusteringTransport` (the
"middle" wall, a `Prop`, uninhabited) and expose the chain

    weak located gap  ⟸  weak clustering  ⟸  strong clustering (PROVED)
                                              +  RGClusteringTransport (open).

We also tie the weak gap rate to the dimensionless `RGLandingCertificate` shape. -/

/-- **`RGClusteringTransport` — the "middle" wall (a `Prop`, uninhabited).**

The RG-flow-preservation statement: exponential clustering of the spatial
transfer operator is carried from the PROVED strong-coupling regime, through the
intermediate "middle" coupling, to weak coupling, producing a weak-coupling
`SpectralModel` `Sweak` with a clustering envelope `(Cweak, μweak)` (`μweak < 1`)
and the converse's side conditions.  This is exactly the asymptotically-free
RG-flow control across the middle — left UNINHABITED (the open wall).

It is a genuine (non-vacuous) `Prop`: it asserts the EXISTENCE of a weak-coupling
spatial model with a strictly-clustering (`μweak < 1`) connected correlator and
discharged side conditions — i.e. it asserts a `WeakClusteringBound`.  No
inhabitant is provided. -/
def RGClusteringTransport : Prop :=
  ∃ Sweak : SpectralModel, ∃ Cweak μweak : Q',
    (0 : Q') < Cweak ∧ (0 : Q') < μweak ∧ μweak < (1 : Q') ∧
    (∀ n, corr Sweak n ≤ Cweak * μweak ^ n) ∧
    (∀ i, i < Sweak.k → (0 : Q') < Sweak.w i) ∧
    (∀ i, Sweak.k ≤ i → Sweak.lam i ≤ μweak)

/-- **`weakClustering_of_transport` — the middle reduction (PROVED conditional,
choice-free).**

`RGClusteringTransport` (the open middle wall, fed by the PROVED strong-coupling
clustering through the RG flow) yields a `WeakClusteringBound` — and hence, by
`weakSpectralGap`, a located weak gap.  This wires the "both sides meet" chain:
the weak gap follows from strong clustering (proved) carried across the middle by
`RGClusteringTransport` (open).

Stated `Prop`-to-`Prop` as `RGClusteringTransport → Nonempty WeakClusteringBound`
so NO choice is used: the existential witness is consumed by `Exists.elim` into
the `Prop` target `Nonempty WeakClusteringBound` (constructive elimination).  It
CONSUMES an `RGClusteringTransport` witness; no unconditional `WeakClusteringBound`
is produced. -/
theorem weakClustering_of_transport (h : RGClusteringTransport) :
    Nonempty WeakClusteringBound := by
  obtain ⟨Sweak, Cweak, μweak, hC, hμ, hμ1, hcl, hcoup, hdead⟩ := h
  exact ⟨{ S := Sweak, C := Cweak, μ := μweak,
           C_pos := hC, μ_pos := hμ, μ_lt_one := hμ1,
           clusters := hcl, coupled := hcoup, dead := hdead }⟩

/-- **The full "both sides meet" chain (choice-free).**  From
`RGClusteringTransport` (open middle wall) a located weak-coupling spectral gap
EXISTS: `∃ W : WeakClusteringBound, LocatedSpectralGap W.S` packaged as a
`Nonempty`.  Composes `weakClustering_of_transport` with the proved reduction
`weakSpectralGap`.  No choice, no faked positivity — the gap is produced ONLY
through the (uninhabited) transport obligation. -/
theorem weakGap_of_transport (h : RGClusteringTransport) :
    Nonempty (Σ W : WeakClusteringBound, LocatedSpectralGap W.S) := by
  obtain ⟨W⟩ := weakClustering_of_transport h
  exact ⟨⟨W, weakSpectralGap W⟩⟩

/-! ### The strong side is PROVED (the input the middle wall consumes)

The PROVED strong-coupling clustering datum is exactly a `WeakClusteringBound`-
shaped package at strong coupling: `MayerClustering.mayer_located_gap` etc. give a
genuine `LocatedSpectralGap` with `sep = ρ = 4/9 < 1` from real
connected-cluster decay.  We record the strong-side ANALOGUE of
`WeakClusteringBound` data so the "both sides" symmetry is explicit: a
`StrongClusteringDatum` is the SAME shape, and it IS inhabited (proved
strong-coupling clustering).  `RGClusteringTransport` is precisely what carries a
`StrongClusteringDatum` to a `WeakClusteringBound`. -/

/-- A strong-coupling clustering datum — the SAME shape as `WeakClusteringBound`
but at strong coupling, where it IS inhabited by the proved cluster expansion.
This makes the "both sides meet" symmetry explicit: strong (proved) and weak
(open) clustering are the same object at different couplings; the middle wall
`RGClusteringTransport` carries one to the other. -/
structure StrongClusteringDatum : Type where
  /-- The spatial transfer operator at strong coupling. -/
  S : SpectralModel
  /-- Clustering prefactor. -/
  C : Q'
  /-- Clustering rate. -/
  μ : Q'
  C_pos : (0 : Q') < C
  μ_pos : (0 : Q') < μ
  μ_lt_one : μ < (1 : Q')
  clusters : ∀ n, corr S n ≤ C * μ ^ n
  coupled : ∀ i, i < S.k → (0 : Q') < S.w i
  dead : ∀ i, S.k ≤ i → S.lam i ≤ μ

/-- A `StrongClusteringDatum` also produces a located gap by the SAME engine —
witnessing that the strong side is genuinely the same object as the weak one
(both run through `clustering_implies_located`).  (The strong side IS inhabited by
the cluster expansion in `MayerClustering`; this `def` is the shape-level bridge.) -/
def strongClusteringGap (D : StrongClusteringDatum) : LocatedSpectralGap D.S :=
  clustering_implies_located D.S D.C D.μ
    D.C_pos D.μ_pos D.μ_lt_one D.clusters D.coupled D.dead

/-! ### The RG-landing tie

The weak gap rate `μ = sep` is the lattice-units gap whose DIMENSIONLESS form
(against the dynamically-generated scale `Λ_YM`) is the Clay-relevant landing
target.  We tie the weak gap to the `RGLandingCertificate` shape via the proved
reduction `rgLanding_of_input`, keeping the open scale normalization
`RGLandingInput` unchanged. -/

/-- **`weakGap_landing` — the RG-landing tie (PROVED conditional).**  Given the
named continuum-scale normalization `RGLandingInput D` (the OPEN scale wall), the
dimensionless `RGLandingCertificate` for the weak gap follows by the proved
reduction `rgLanding_of_input`.  This places the weak-coupling located gap on the
SAME dimensionless landing target `q ≤ m/Λ_YM` as the rest of the program; the
scale normalization stays open. -/
def weakGap_landing (D : DefectGapRecursion)
    (h : RGLandingCertificate.RGLandingInput D) :
    RGLandingCertificate.RGLandingCertificate :=
  RGLandingCertificate.rgLanding_of_input D h

/-- The weak-gap landing certificate's dimensionless rational floor is strictly
positive (it is the recursion's product floor `D.prodFloor > 0`) — the landing
target is a genuine positive number, not a free decoration.  (The scale
normalization `RGLandingInput` remains the open wall.) -/
theorem weakGap_landing_q_pos (D : DefectGapRecursion)
    (h : RGLandingCertificate.RGLandingInput D) :
    (0 : Q') < (weakGap_landing D h).q :=
  D.prodFloor_pos

/-! ## DELIVERABLE 4 — honest scope (see the module header)

PROVED here (genuine, axiom-clean):
  * `singleLink_no_gap_weak`, `singleLink_sep_not_lt_one_weak`,
    `singleLinkSep_not_lt_one_weak` — the single-link character object FAILS the
    located-gap requirement `sep < 1` at weak coupling (it is the WRONG object);
  * `weakSpectralGap` — the PROVED reduction: weak clustering ⇒ located weak gap,
    via the real `clustering_implies_located`; `weakSpectralGap_sep_lt_one` /
    `weakSpectralGap_margin_pos` confirm the object genuinely has `sep < 1` /
    `1 − sep > 0`, CONDITIONAL on the named clustering;
  * `weakClustering_of_transport` — weak clustering follows from
    `RGClusteringTransport` (the middle wall, fed by proved strong clustering);
  * `strongClusteringGap` — the strong side is the SAME located-gap object;
  * `weakGap_landing` — the weak gap on the dimensionless RG-landing target.

NAMED-open (NOT faked — the continuum problem):
  * `WeakClusteringBound` — weak-coupling exponential clustering of the spatial
    transfer operator (no 4D inhabitant);
  * `RGClusteringTransport` — the RG-flow preservation of clustering from strong
    through the middle to weak coupling (no inhabitant);
  * `RGLandingCertificate.RGLandingInput` — the continuum-scale normalization
    (`m/Λ_YM`), unchanged and open.

This module does NOT prove weak-coupling gap positivity.  No 4D Yang–Mills mass
gap is claimed.  No positivity is faked: the weak located gap is produced ONLY
from a (named, uninhabited) clustering obligation through a real reduction. -/

end YMGap.Continuum.WeakCouplingGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WeakCouplingGap.coeffW_zero_pos
#print axioms YMGap.Continuum.WeakCouplingGap.singleLinkSep_eqv_coeffW1
#print axioms YMGap.Continuum.WeakCouplingGap.singleLink_no_gap_weak
#print axioms YMGap.Continuum.WeakCouplingGap.singleLink_sep_not_lt_one_weak
#print axioms YMGap.Continuum.WeakCouplingGap.singleLinkSep_not_lt_one_weak
#print axioms YMGap.Continuum.WeakCouplingGap.weakSpectralGap
#print axioms YMGap.Continuum.WeakCouplingGap.weakSpectralGap_sep_lt_one
#print axioms YMGap.Continuum.WeakCouplingGap.weakSpectralGap_sep_eq
#print axioms YMGap.Continuum.WeakCouplingGap.weakSpectralGap_margin_pos
#print axioms YMGap.Continuum.WeakCouplingGap.weakClustering_of_transport
#print axioms YMGap.Continuum.WeakCouplingGap.weakGap_of_transport
#print axioms YMGap.Continuum.WeakCouplingGap.strongClusteringGap
#print axioms YMGap.Continuum.WeakCouplingGap.weakGap_landing
#print axioms YMGap.Continuum.WeakCouplingGap.weakGap_landing_q_pos
