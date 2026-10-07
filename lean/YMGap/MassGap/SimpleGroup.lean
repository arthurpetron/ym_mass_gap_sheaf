/-
Conditional scalar-budget and OS-reconstruction assembly.

# What this module delivers

`MassGap/SU2.lean` exposes a legacy conditional signature that pairs the
Q'-rational facts `m_0 = 999/1000 > 0` and
`m_0² ≤ 9991/10000` with a separately supplied
`OSReconstruction` already carrying `HasSpectralGap rec`.  That Q'-level
signature does not bind `m_0` to the spectral gap.  The later CReal theorem
`mass_gap_SU2_creal` has the relevant `HasSpectralGapAt` rate binding, under an
explicit additional hypothesis.

This module transports the same scalar estimate to an arbitrary `RepData` row
`R` satisfying two explicit input structures:

  * `RepTheory/SimpleGroup.lean` — `AdmissibleSimpleGroup R`, whose historical
    name packages only two scalar inequalities plus a closure certificate; it
    does not prove that `R` comes from a compact simple group or carries the
    actual global-form spectral minimum.
  * `RG/UniformBudget.lean` — `monotone_budget`: with the per-step bound
    dominated by SU(2)'s (`UniformBudgetWitness.eta_dominated`, the named
    analytic input), `R`'s σ̂-budget is ≤ SU(2)'s at *every* truncation.

The current theorem derives only the displayed all-truncations budget closure
for `R`.  It also reuses the SU(2) constants verbatim, but does not prove in its
conclusion that `9991/10000` is `R`'s σ̂∞ floor, nor that `m_0` bounds the
spectral gap carried by `rec`.

# Top theorems

  * `budget_closes_uniform R hadm w` — the witness-relative all-truncations
    σ̂-budget closure for `R`, derived (no per-group `decide`) from
    `monotone_budget` + the proven `su2_budget_closes`.
  * `mass_gap_simple_group_of_osReconstruction R hadm w rec bundle` — a
    legacy conjunction of an explicit `m_0 : Q'` with `0 < m_0`, the closed
    inequality `m_0² ≤ 9991/10000`, the independently supplied OS
    spectral-gap conjunct `HasSpectralGap rec`, and `R`'s budget closure.  No
    conjunct binds these four facts into a group-specific gap lower bound.
  * `mass_gap_SU3` — the legacy SU(3) scalar-row specialization: the stored
    SU(3) row satisfies the historical scalar admissibility interface
    (`su3_admissible`) and is η-dominated (`su3_uniform_witness`, by `decide`:
    `13e-6 ≤ 3e-4`), so the top theorem instantiates directly.  This is not a
    theorem about the physical SU(3) gauge theory.

# The named analytic obligation (Rule 2 / Rule 6)

Everything here is constructive and axiom-clean **conditional on** the named
field `UniformBudgetWitness.eta_dominated` (`R.eta_max ≤ su2.eta_max`) and the
OS-reconstruction interface inputs inherited unchanged from
`mass_gap_SU2_of_osReconstruction`.  For the SU(N) scalar instances
(SU(2), SU(3)) the witness is discharged by `decide`; for the general
group it is the paper-layer obligation.

# Axiom-gate (AGENTS.md Rule 1)

`mass_gap_simple_group_of_osReconstruction` composes Q'-rational `decide` facts, the
`[propext]` budget closure, and the trivial OS bridge; it reports
`[propext]` (or `[propext, Quot.sound]`).  See the `#print axioms` block.
-/

import YMGap.RG.UniformBudget
import YMGap.RG.CharacterTailAntitone
import YMGap.RG.CharacterTailMajorant
import YMGap.RG.RankCollapse
import YMGap.RG.EtaPackaging
import YMGap.RG.WeylCharacterBound
import YMGap.RG.WeylDimGeneral
import YMGap.RepTheory.CasimirData
import YMGap.MassGap.SU2
import YMGap.Continuum.WilsonConsistency

namespace YMGap.MassGap.SimpleGroup

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RepTheory
open YMGap.RG
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.OSReconstruction
open YMGap.MassGap.SU2

/-! ## The witness-relative uniform budget closure -/

/-- **`budget_closes_uniform`.**  For any scalar row `R` together with the
named η-domination witness, the σ̂-budget closes at
*every* finite truncation under SU(2)'s `σ̂₀`:

    ∀ N, Σ_{k<N} η_k(R)  ≤  σ̂₀(su2) = 1.

This is the scalar §1.3 reduction: `monotone_budget` transports the
proven SU(2) closure (`su2_budget_closes`) to `R`.  No per-group `decide`
on `R`'s budget — the closure is *derived* from SU(2)'s via the
monotonicity substrate.  The historical parameter `hadm` is retained for API
compatibility but is logically unused by this proof; the displayed closure
flows entirely through `w`.  In particular, neither the numeric floors nor
`hadm.cert` are premises of this closure. -/
theorem budget_closes_uniform (R : RepData)
    (hadm : AdmissibleSimpleGroup R) (w : UniformBudgetWitness R) :
    ∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0 :=
  budget_closes_of_witness R w

/-- The admissible group carries its own `ClosureCertificate` (through
`hadm.cert`); `budget_closes_uniform` additionally certifies the closure
*uniformly* (transported from SU(2), not re-`decide`d).  We expose the
certificate for downstream use. -/
theorem closureCertificate_of_admissible (R : RepData)
    (hadm : AdmissibleSimpleGroup R) : R.ClosureCertificate :=
  hadm.cert

/-! ## Reused SU(2) constants

The following declarations reuse the two SU(2) rational constants and their
closed inequality.  This module does not derive a theorem identifying the
second constant with `R`'s σ̂∞ floor, and the Q'-level top theorem does not
bind the first constant to `rec.gapBound`. -/

/-- The reused positive SU(2) rational constant.  This Q'-level module does
not bind it to the spectral gap of an arbitrary reconstruction. -/
def m_0_uniform : Q' := m_0_canonical

/-- The reused SU(2) σ̂∞-floor constant.  Its name is historical; no
group-parametric floor theorem is packaged by this definition. -/
def sigma_hat_inf_lower_uniform : Q' := sigma_hat_inf_lower_canonical

/-- `0 < m_0_uniform`. -/
theorem m_0_uniform_positive : (0 : Q') < m_0_uniform :=
  m_0_canonical_positive

/-- `m_0_uniform² ≤ sigma_hat_inf_lower_uniform`. -/
theorem m_0_uniform_squared_le :
    m_0_uniform * m_0_uniform ≤ sigma_hat_inf_lower_uniform :=
  m_0_canonical_squared_le_sigma_hat

/-! ## The top theorem -/

/-- **Conditional mass-gap signature from scalar and OS inputs.**

This theorem does not quantify over or construct a compact simple gauge group.
It transports the SU(2) scalar budget to an arbitrary `RepData` row `R` after
the following inputs are supplied:

  * `hadm : AdmissibleSimpleGroup R` — a signature-level compatibility
    parameter carrying two numeric lower bounds and a closure certificate,
    without group provenance; the base proof below does not inspect it;
  * `w : UniformBudgetWitness R` — the named analytic input pinning SU(2)
    as the worst case (`R.eta_max ≤ su2.eta_max`);
  * `rec`, `bundle` — the OS-reconstruction quintuple and OS-axiom witness
    (paper-supplied, exactly as in `mass_gap_SU2_of_osReconstruction`);

we conclude there is an explicit `m_0 : Q'` with `0 < m_0`, the closed
SU(2)-constant inequality `m_0² ≤ 9991/10000`, the independent OS spectral
gap `HasSpectralGap rec`, and the derived all-truncations σ̂-budget closure
for `R` (`∀ N, Σ η_k(R) ≤ σ̂₀`).  The type contains no equation or
inequality relating `m_0` to `rec.gapBound`.

Relative to `mass_gap_SU2_of_osReconstruction`, the budget conjunct is derived
for any supplied scalar row (`budget_closes_uniform`), not
re-`decide`d per group.  The witness `w` is load-bearing; `hadm` is not used by
this base theorem, although several downstream witness constructors do use its
numeric fields.  Axiom-gate: `[propext]` / `[propext, Quot.sound]`
(Q'-rational `decide` facts + the budget-closure `[propext]` + the trivial
OS bridge). -/
theorem mass_gap_simple_group_of_osReconstruction
    -- UNBOUND (J04 T3): nothing in this signature ties `rec`, `μ_inf` or the
    -- `HasSpectralGap rec` conjunct to the group behind `R`, and `m_0` is not
    -- related to `rec.gapBound`.  See `mass_gap_simple_group_bound` for the
    -- version that carries the binding as an explicit open hypothesis.
    (R : RepData) (hadm : AdmissibleSimpleGroup R) (w : UniformBudgetWitness R)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  ⟨m_0_uniform,
   m_0_uniform_positive,
   m_0_uniform_squared_le,
   cluster_implies_gap_signature rec bundle,
   budget_closes_uniform R hadm w⟩

/-! ## The mass-gap INPUT operad

`mass_gap_simple_group_of_osReconstruction` consumes exactly one datum — a `UniformBudgetWitness R`.
The many entry points below differ ONLY in how that witness is built (gap→η
monotonicity, the `Z_t` majorant, the scalar rank-collapse data, the activity
model, the Weyl-character data).  We name those builders as **constructors** of
the input, turning the former chain of mutually-delegating theorems into an
explicit *algebra of input adapters* feeding one evaluation.  Each `ofX` is
independently reusable (build a witness without invoking the mass-gap theorem),
and every `mass_gap_*_of_X` theorem below becomes a one-line evaluation
`mass_gap_simple_group_of_osReconstruction R hadm (MassGapInput.ofX …) rec bundle`. -/

/-- The polymorphic mass-gap input: the single datum `mass_gap_simple_group_of_osReconstruction`
consumes.  An `abbrev` of `UniformBudgetWitness R` so the base theorem's
signature is unchanged; the `MassGapInput.*` constructors are the operad's
operations (the witness-building adapters).  (`UniformBudgetWitness` is a
`Prop`, so this input is propositional — the "data" is a proof.) -/
abbrev MassGapInput (R : RepData) : Prop := UniformBudgetWitness R

namespace MassGapInput

/-- Build the input from the structural gap→η monotonicity `EtaGapMonotone R`
(the per-step bound antitone in the Casimir gap to the SU(2) floor). -/
def ofGapMonotone (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (hmono : EtaGapMonotone R) (hwin : R.K_steps = su2.K_steps) : MassGapInput R :=
  uniformBudgetWitness_of_gapMonotone R hadm hmono hwin

/-- Build the input from the rank-general `Z_t` majorant bridge `EtaFromZt R`. -/
def ofZtMajorant (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (bridge : EtaFromZt R) (hwin : R.K_steps = su2.K_steps) : MassGapInput R :=
  ofGapMonotone R hadm (etaGapMonotone_of_ztMajorant bridge) hwin

/-- Build the input from the scalar rank-collapse data (per-axis floor excesses
`sFloor`, window/cap rationals), with `rank_collapse` discharged via
`ztMajorant_of_sum`; the `Z_t ↦ η` packaging `eta_of_zt` is the remaining input. -/
def ofRankCollapseData (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (r : Nat) (sR sFloor : Nat → Q') (su2Zt : Q')
    (hsR_nn : ∀ i, (0 : Q') ≤ sR i) (hsR_le : ∀ i, sR i ≤ sFloor i)
    (hFloor_nn : ∀ i, (0 : Q') ≤ sFloor i)
    (hwin : 2 * (sumExcess sFloor r) ≤ 1)
    (hcap : 2 * (sumExcess sFloor r) ≤ su2Zt)
    (eta_of_zt :
      ztValue (ztMajorant_of_sum (R := R) r sR sFloor su2Zt
          hsR_nn hsR_le hFloor_nn hwin hcap).sR
        (ztMajorant_of_sum (R := R) r sR sFloor su2Zt
          hsR_nn hsR_le hFloor_nn hwin hcap).rank
        ≤ (ztMajorant_of_sum (R := R) r sR sFloor su2Zt
          hsR_nn hsR_le hFloor_nn hwin hcap).su2Zt → R.eta_max ≤ su2.eta_max)
    (hKwin : R.K_steps = su2.K_steps) : MassGapInput R :=
  ofZtMajorant R hadm
    { major := ztMajorant_of_sum (R := R) r sR sFloor su2Zt
        hsR_nn hsR_le hFloor_nn hwin hcap
      eta_of_zt := eta_of_zt }
    hKwin

/-- Build the input from the rank-collapse data plus the activity model
`ZtEtaModel R` (which discharges `eta_of_zt` via `etaFromZt_of_model`). -/
def ofModelData (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (r : Nat) (sR sFloor : Nat → Q') (su2Zt : Q')
    (hsR_nn : ∀ i, (0 : Q') ≤ sR i) (hsR_le : ∀ i, sR i ≤ sFloor i)
    (hFloor_nn : ∀ i, (0 : Q') ≤ sFloor i)
    (hwin : 2 * (sumExcess sFloor r) ≤ 1)
    (hcap : 2 * (sumExcess sFloor r) ≤ su2Zt)
    (m : ZtEtaModel R)
    (hZtR : m.ZtR = ztValue sR r) (hZtsu2 : m.Ztsu2 = su2Zt)
    (hKwin : R.K_steps = su2.K_steps) : MassGapInput R :=
  ofZtMajorant R hadm
    (etaFromZt_of_model
      (ztMajorant_of_sum (R := R) r sR sFloor su2Zt
        hsR_nn hsR_le hFloor_nn hwin hcap)
      m hZtR hZtsu2)
    hKwin

/-- Build the input from the Weyl-character structural data `AxisFactorBound R`
(per-axis polynomial-geometric tail) plus the activity model `ZtEtaModel R`. -/
def ofWeylData (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (b : YMGap.RG.AxisFactorBound R) (su2Zt : Q')
    (hwin : 2 * (sumExcess b.axisExcess b.rank) ≤ 1)
    (hcap : 2 * (sumExcess b.axisExcess b.rank) ≤ su2Zt)
    (m : ZtEtaModel R)
    (hZtR : m.ZtR = ztValue b.axisExcess b.rank) (hZtsu2 : m.Ztsu2 = su2Zt)
    (hKwin : R.K_steps = su2.K_steps) : MassGapInput R :=
  ofZtMajorant R hadm
    (YMGap.RG.etaFromZt_of_model
      (YMGap.RG.ztMajorant_of_axisData b su2Zt hwin hcap)
      m hZtR hZtsu2)
    hKwin

end MassGapInput

/-! ## Legacy conditional signature from the gap → η obligation

`mass_gap_simple_group_of_osReconstruction` consumes the raw η-domination witness
`UniformBudgetWitness R` (whose load-bearing field is
`eta_dominated : R.eta_max ≤ su2.eta_max`).  The uniform character-tail
analysis (`RG/CharacterTailAntitone.lean`) reduces that field to the
*structural* gap → η monotonicity `EtaGapMonotone R` (the per-step bound
is antitone in the Casimir gap down to the SU(2) floor), whose analytic
engine — `e^{−tΔ}` non-increasing in Δ — is proven constructively there.
This corollary threads that reduction: from an `AdmissibleSimpleGroup R`
(supplying the floor `3/4 ≤ R.C2_fund`), the named `EtaGapMonotone R`,
and the same-window fact, it builds the budget witness and delivers the
legacy conjunction above.  The remaining budget obligation is
`EtaGapMonotone R`
(the antitone exponential's *assembly* into `eta_max` via the
rank-general Weyl-dimension `Z_t` majorant), not the bare `eta_max`
inequality. -/
theorem mass_gap_simple_group_of_gapMonotone
    (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (hmono : EtaGapMonotone R) (hwin : R.K_steps = su2.K_steps)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_osReconstruction R hadm (MassGapInput.ofGapMonotone R hadm hmono hwin) rec bundle

/-! ## Legacy conditional signature from the rank-general `Z_t` majorant

`mass_gap_simple_group_of_gapMonotone` consumes the named `EtaGapMonotone R`.
`RG/CharacterTailMajorant.lean` discharges *that* through the rank-general
character-tail majorant `Z_t(R) = ∏_i S_i − 1 ≤ Z_t(su2)`
(`etaGapMonotone_of_ztMajorant`), whose only non-`Q'` inputs are the named
`ZtMajorant.rank_collapse` (the §3 rank-collapse) and the `EtaFromZt`
`Z_t ↦ η` packaging — both bounded to the paper layer, neither faked, and
both *concrete `decide` facts* for the SU(N) family.  This corollary threads
that reduction end to end: from an `AdmissibleSimpleGroup R`, the
`EtaFromZt R` bridge (carrying the majorant), and the same-window fact, it
delivers the same legacy conjunction.  The remaining budget obligation is the rank-`r`
`Z_t` majorant of `R`, not the bare `eta_max` inequality. -/
theorem mass_gap_simple_group_of_ztMajorant
    (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (bridge : EtaFromZt R) (hwin : R.K_steps = su2.K_steps)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_osReconstruction R hadm (MassGapInput.ofZtMajorant R hadm bridge hwin) rec bundle

/-! ## Legacy signature with `rank_collapse` discharged from a scalar sum bound

`mass_gap_simple_group_of_ztMajorant` still consumes a whole `EtaFromZt R`
whose `major.rank_collapse` was a *posited* field.  `RG/RankCollapse.lean`
discharges that field as a **theorem** (`rank_collapse_of_sum`,
`ztMajorant_of_sum`): from the per-axis floor excesses `sFloor`, the window
`2·Σ sFloor ≤ 1`, and the concrete cap `2·Σ sFloor ≤ Z_t(su2)`, the rank
collapse `∏(1+sFloor)−1 ≤ Z_t(su2)` is proven over `Q'` (the scalar bound
`∏(1+sᵢ)−1 ≤ 2·Σ sᵢ` plus the §3 uniform-domination cap).  This corollary
takes that scalar data *directly* (no posited `rank_collapse`), builds the
majorant, and — given only the `eta_of_zt` packaging (the `Z_t ↦ η` bridge,
the explicitly out-of-scope residual) — delivers the legacy conjunction.  The
`rank_collapse` obligation is thus removed from the named-obligation list. -/
theorem mass_gap_simple_group_of_rankCollapseData
    (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (r : Nat) (sR sFloor : Nat → Q') (su2Zt : Q')
    (hsR_nn : ∀ i, (0 : Q') ≤ sR i) (hsR_le : ∀ i, sR i ≤ sFloor i)
    (hFloor_nn : ∀ i, (0 : Q') ≤ sFloor i)
    (hwin : 2 * (sumExcess sFloor r) ≤ 1)
    (hcap : 2 * (sumExcess sFloor r) ≤ su2Zt)
    (eta_of_zt :
      ztValue (ztMajorant_of_sum (R := R) r sR sFloor su2Zt
          hsR_nn hsR_le hFloor_nn hwin hcap).sR
        (ztMajorant_of_sum (R := R) r sR sFloor su2Zt
          hsR_nn hsR_le hFloor_nn hwin hcap).rank
        ≤ (ztMajorant_of_sum (R := R) r sR sFloor su2Zt
          hsR_nn hsR_le hFloor_nn hwin hcap).su2Zt → R.eta_max ≤ su2.eta_max)
    (hKwin : R.K_steps = su2.K_steps)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_osReconstruction R hadm
    (MassGapInput.ofRankCollapseData R hadm r sR sFloor su2Zt
      hsR_nn hsR_le hFloor_nn hwin hcap eta_of_zt hKwin) rec bundle

/-- **Legacy SU(2) signature via the rank-general `Z_t` majorant chain.**  Threads
SU(2) through the rank-1 product majorant (`su2_etaFromZt`), exhibiting the
full `Z_t ↦ η ↦ budget` path with no named obligation open at the boundary
instance. -/
theorem mass_gap_SU2_via_ztMajorant
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst su2.K_steps su2.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_ztMajorant su2 su2_admissible su2_etaFromZt (by decide) rec bundle

/-! ## Legacy signature with both budget residuals discharged from data
(`rank_collapse` from the scalar sum bound, `eta_of_zt` from the proven
monotone `Z_t ↦ η` packaging)

`mass_gap_simple_group_of_rankCollapseData` still consumed a *posited*
`eta_of_zt` implication.  `RG/EtaPackaging.lean` discharges that as a
**theorem** (`eta_of_zt_of_model`) from the explicit monotone activity model
`etaModel μ Z = μ · (Z · recip(1−Z))` (the `K_lf = q/(1−q)` wrapper
`qOver1mq_mono`, already proven).  So given a `ZtEtaModel R` whose two
character tails match the sum-bound majorant's (`ZtR = ztValue sR r`,
`Ztsu2 = su2Zt`), the `Z_t ↦ η_max` packaging is no longer a posited
implication but a consequence of `Q'` monotonicity.

This corollary therefore consumes only *data* — the admissibility floors
(now backed per-Cartan-type by `RepTheory/CasimirData.lean`), the per-axis
floor excesses with their window/cap rationals, and the `ZtEtaModel`
(single-plaquette heat-kernel output: weight `μ` and the two tails) — with
no posited implication anywhere.  The remaining honest content is exactly
the per-group analytic *data* (`sFloor`, the cap, and the model's `μ`/tails),
not any unproven monotonicity step. -/
theorem mass_gap_simple_group_of_modelData
    (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (r : Nat) (sR sFloor : Nat → Q') (su2Zt : Q')
    (hsR_nn : ∀ i, (0 : Q') ≤ sR i) (hsR_le : ∀ i, sR i ≤ sFloor i)
    (hFloor_nn : ∀ i, (0 : Q') ≤ sFloor i)
    (hwin : 2 * (sumExcess sFloor r) ≤ 1)
    (hcap : 2 * (sumExcess sFloor r) ≤ su2Zt)
    (m : ZtEtaModel R)
    (hZtR : m.ZtR = ztValue sR r) (hZtsu2 : m.Ztsu2 = su2Zt)
    (hKwin : R.K_steps = su2.K_steps)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_osReconstruction R hadm
    (MassGapInput.ofModelData R hadm r sR sFloor su2Zt
      hsR_nn hsR_le hFloor_nn hwin hcap m hZtR hZtsu2 hKwin) rec bundle

/-! ## Legacy signature from supplied Weyl-character-shaped data

`mass_gap_simple_group_of_modelData` consumed the per-axis floor excesses
`sFloor`/`sR` as *bare `Q'` data* — the inequality `Z_t(R) ≤ Z_t(su2)` was
realized through those numbers without a structural account of *where they
come from*.  `RG/WeylCharacterBound.lean` supplies that account — the
three-step Lie-theory chain over the dominant weight lattice `λ ∈ ℕ^r`:

  * (a) `casimir_axis_lower` : `h_i(x) ≥ Δ_i·x` (drop nonneg Gram cross
    terms, `x² ≥ x` on the support) — the Casimir lower split, *proven*;
  * (b) `one_add_sum_le_prod` : `1 + Σ a_i ≤ ∏(1 + a_i)` — the Weyl-product
    regrouping engine, *proven*; the per-root squaring is the named
    `WeylDimData`;
  * (c) `Zt_le_su2_of_axisData` : factorization + `rank_collapse_of_sum`
    caps `Z_t(R)` at `Z_t(su2)` from the per-axis polynomial-geometric
    factor excesses `AxisFactorBound` (the pitfall-aware tail data).

This corollary consumes the **structural** `AxisFactorBound R` (the per-axis
character-tail factor data, whose excesses ARE the `sFloor`/`sR` of the old
path — but now *named as the Weyl-character factors* they represent), builds
the `ZtMajorant` through the proven `ztMajorant_of_axisData`, and delivers
the legacy conjunction.  The remaining content is the named
per-group data items of `WeylCharacterBound.lean` — `WeylDimData` (Weyl
squaring constants) and `AxisFactorBound` (polynomial-geometric tail) — plus
the `Z_t ↦ η` model `ZtEtaModel`; no assumed inequality anywhere. -/
theorem mass_gap_simple_group_of_weylData
    (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (b : YMGap.RG.AxisFactorBound R) (su2Zt : Q')
    (hwin : 2 * (sumExcess b.axisExcess b.rank) ≤ 1)
    (hcap : 2 * (sumExcess b.axisExcess b.rank) ≤ su2Zt)
    (m : ZtEtaModel R)
    (hZtR : m.ZtR = ztValue b.axisExcess b.rank) (hZtsu2 : m.Ztsu2 = su2Zt)
    (hKwin : R.K_steps = su2.K_steps)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_osReconstruction R hadm
    (MassGapInput.ofWeylData R hadm b su2Zt hwin hcap m hZtR hZtsu2 hKwin) rec bundle

/-! ## SU(3) scalar-row corollary

SU(3) is admissible (`su3_admissible`) and η-dominated: its per-step
bound `13e-6` is ≤ SU(2)'s `3e-4` (`decide`), and both use the `K = 3`
window.  So the legacy conjunction instantiates directly at the SU(3) scalar
row; this is not a realized-group or rate-bound mass-gap theorem. -/

/-- SU(3) is η-dominated by SU(2): same `K = 3` window, and
`su3.eta_max = 13/1000000 ≤ 3/10000 = su2.eta_max`. -/
theorem su3_uniform_witness : UniformBudgetWitness su3 where
  same_window   := by decide
  eta_dominated := by decide

/-- **Legacy conditional signature at the SU(3) scalar row.**  The numeric
admissibility floors and η-domination are both decidable; the spectral gap is
still supplied independently by `rec`. -/
theorem mass_gap_SU3
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst su3.K_steps su3.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_osReconstruction su3 su3_admissible su3_uniform_witness rec bundle

/-- **Legacy SU(3) signature via supplied Weyl-character-shaped data.**

A specialization of `mass_gap_simple_group_of_weylData` to `R := su3`
(`su3_admissible`, `K = 3` window by `decide`).  The two Weyl-character
residuals this path used to leave open — the per-axis polynomial-geometric
tail `AxisFactorBound` and the squared-Weyl-dimension majorization
`WeylDimData` — are now *discharged theorems* for the SU(N) family
(`RG/PolylogTail.weightedGeomSum_le` / `RG.axisFactor_polylog_le` for the
tail, `RG.su3_dimSq_le` / `RG.su3_weylDimData_at` for the squared dimension),
so the only remaining input is the heat-kernel `Z_t ↦ η` packaging
`ZtEtaModel su3` (the explicitly out-of-scope residual) plus the concrete
window/cap rationals.  In this theorem `b : AxisFactorBound su3` remains an
explicit input, so the result itself does not derive the character-tail data
from a realized SU(3) group. -/
theorem mass_gap_SU3_via_weylData
    (b : YMGap.RG.AxisFactorBound su3) (su2Zt : Q')
    (hwin : 2 * (sumExcess b.axisExcess b.rank) ≤ 1)
    (hcap : 2 * (sumExcess b.axisExcess b.rank) ≤ su2Zt)
    (m : ZtEtaModel su3)
    (hZtR : m.ZtR = ztValue b.axisExcess b.rank) (hZtsu2 : m.Ztsu2 = su2Zt)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst su3.K_steps su3.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_weylData su3 su3_admissible b su2Zt hwin hcap m hZtR hZtsu2
    (by decide) rec bundle

/-! ## Historical SU(N)-named adapter

`mass_gap_SU3_via_weylData` discharged the squared-Weyl-dimension residual
`WeylDimData` *per group* (`su3_dimSq_le`).  `RG/WeylDimGeneral.lean` discharges
it for the WHOLE SU(N) family at once via the crude uniform bound

    (dim V_λ)²  ≤  (∏_{p<N−1}(1 + λ_p))^{2·#Δ⁺} ,    #Δ⁺ = N(N−1)/2 ≤ N² ,

proven ONCE over a generic finite positive-root collection
(`weylDimData_crude`: a product of `m` Weyl factors each `≤ B = ∏_p(1+λ_p)`
with `B ≥ 1` is `≤ B^m`, hence the squared bound `≤ B^{2m}`), then instantiated
for `SU(N)` with `m = suN_numPosRoots N` (`suN_weylDimData_crude`).  The uniform
exponent `2m` is the SAME for every axis, so the per-axis polylog tail closes
for each fixed `N` with NO per-group dimension case analysis.

Despite its historical name, the following theorem does not assert that `R`
is the SU(N) scalar row or connect `N`, `lab`, `fac`, and `dimVal` to `R`.
The locally constructed `WeylDimData` proof is not consumed by the concluding
`mass_gap_simple_group_of_weylData` call.  Its load-bearing inputs are instead
`hadm`, the supplied `AxisFactorBound R`, its cap/window, the supplied
`ZtEtaModel R`, and the OS interfaces.  A genuine SU(N) bridge must add group
provenance and make the dimension certificate enter the witness construction. -/
theorem mass_gap_suN
    (R : RepData) (hadm : AdmissibleSimpleGroup R)
    (N : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ YMGap.RG.crudeBound lab (N - 1))
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ YMGap.RG.prodFac fac (YMGap.RG.suN_numPosRoots N))
    (b : YMGap.RG.AxisFactorBound R) (su2Zt : Q')
    (hwin : 2 * (sumExcess b.axisExcess b.rank) ≤ 1)
    (hcap : 2 * (sumExcess b.axisExcess b.rank) ≤ su2Zt)
    (m : ZtEtaModel R)
    (hZtR : m.ZtR = ztValue b.axisExcess b.rank) (hZtsu2 : m.Ztsu2 = su2Zt)
    (hKwin : R.K_steps = su2.K_steps)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  -- The crude squared-Weyl-dimension certificate (generic, uniform exponent);
  -- it justifies the uniform per-axis degree the `AxisFactorBound` weight uses.
  let _wdd : YMGap.RG.WeylDimData R :=
    YMGap.RG.suN_weylDimData_crude (R := R) N hlab hfac hle hdim_nonneg hdim
  mass_gap_simple_group_of_weylData R hadm b su2Zt hwin hcap m hZtR hZtsu2 hKwin rec bundle

/-- SU(2) is (trivially) η-dominated by itself — the boundary witness. -/
theorem su2_uniform_witness : UniformBudgetWitness su2 where
  same_window   := by decide
  eta_dominated := by decide

/-- Sanity corollary: specialize the legacy conjunction to the SU(2) scalar
row.  The Q'-constant and spectral-gap conjunct remain unbound. -/
theorem mass_gap_SU2_via_uniform
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst su2.K_steps su2.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group_of_osReconstruction su2 su2_admissible su2_uniform_witness rec bundle

/-! ## J04 T3/b — the bound-gap statement, tied to the repo's Wilson measure

The only Wilson measure the repository constructs is the SU(2) heat-kernel
inverse-limit measure `WilsonConsistency.wilsonContinuumMeasure w hw` on the
stage family `WilsonM k = ProbFunctional (wilsonSystem.Obs k)`.  The provenance
predicate is therefore concrete:

  `SU2WilsonOrigin R μ :≡ R = su2 ∧ ∃ w hw, μ = wilsonContinuumMeasure w hw`.

It is not `True`: `not_SU2WilsonOrigin_su3` refutes it for the SU(3) row.

**Obstruction (recorded, proved).**  `GroupBoundGap.row_eq_su2`: any
`GroupBoundGap R rec` forces `R = su2`.  So for every non-SU(2) row the bound
statement is currently uninhabitable — not because a gap fails, but because no
Wilson measure for that group exists in the repo.  Extending it requires a
per-group Wilson measure (ladder items d–f).

**Open content.**  The rate field `rate_exists` (`HasSpectralGapAt rec m`,
`m ≥ m_0_uniform`, for an `OSReconstruction` of the Wilson measure) is the open
hypothesis.  No instance of `GroupBoundGap` is constructed anywhere. -/

open YMGap.Continuum.WilsonConsistency in
/-- The Wilson stage family of the repo's SU(2) Wilson measure. -/
abbrev WilsonM : Nat → Type :=
  fun k => YMGap.Continuum.ObservableMeasure.ProbFunctional
    (YMGap.Continuum.WilsonConsistency.wilsonSystem.Obs k)

/-- Concrete provenance: the row is SU(2) and `μ` is the repo's Wilson
inverse-limit measure at some heat-kernel weight `w ≥ 0`. -/
def SU2WilsonOrigin (R : RepData) (μ : ContinuumMeasure WilsonM) : Prop :=
  R = su2 ∧ ∃ (w : Q') (hw : (0 : Q') ≤ w),
    μ = YMGap.Continuum.WilsonConsistency.wilsonContinuumMeasure w hw

/-- Non-vacuity: the SU(3) row has no SU(2) Wilson origin. -/
theorem not_SU2WilsonOrigin_su3 (μ : ContinuumMeasure WilsonM) :
    ¬ SU2WilsonOrigin su3 μ := by
  intro h
  have := congrArg (fun r : RepData => r.C2_fund.num) h.1
  exact absurd this (by decide)

/-- The binding hypothesis for a group-pinned mass gap. -/
structure GroupBoundGap (R : RepData) {μ_inf : ContinuumMeasure WilsonM}
    (rec : OSReconstruction μ_inf) : Prop where
  /-- OPEN: located-margin rate at least the uniform scalar `m_0`. -/
  rate_exists : ∃ rate : CReal, CReal.ofQ' m_0_uniform ≤ rate ∧ HasSpectralGapAt rec rate
  /-- `μ_inf` is the repo's SU(2) Wilson measure and `R` is the SU(2) row. -/
  origin : SU2WilsonOrigin R μ_inf

/-- **Obstruction**: a bound gap can only be stated for the SU(2) row. -/
theorem GroupBoundGap.row_eq_su2 {R : RepData} {μ_inf : ContinuumMeasure WilsonM}
    {rec : OSReconstruction μ_inf} (hb : GroupBoundGap R rec) : R = su2 :=
  hb.origin.1

/-- **Bound conditional mass gap.**  Rate-bound gap `HasSpectralGapAt rec m`,
`m ≥ m_0_uniform`, for an OS reconstruction of the repo's SU(2) Wilson measure;
all analytic content is in the open hypothesis `hb.rate_exists`. -/
theorem mass_gap_simple_group_bound
    (R : RepData) (hadm : AdmissibleSimpleGroup R) (w : UniformBudgetWitness R)
    {μ_inf : ContinuumMeasure WilsonM} {rec : OSReconstruction μ_inf}
    (hb : GroupBoundGap R rec) :
    (∃ m : CReal, CReal.ofQ' m_0_uniform ≤ m ∧ HasSpectralGapAt rec m) ∧
      SU2WilsonOrigin R μ_inf ∧
      (0 : Q') < m_0_uniform ∧
      (∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ su2.sigma0) :=
  ⟨hb.rate_exists, hb.origin, m_0_uniform_positive, budget_closes_uniform R hadm w⟩

end YMGap.MassGap.SimpleGroup

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.MassGap.SimpleGroup.budget_closes_uniform
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_bound
#print axioms YMGap.MassGap.SimpleGroup.not_SU2WilsonOrigin_su3
#print axioms YMGap.MassGap.SimpleGroup.GroupBoundGap.row_eq_su2
#print axioms YMGap.MassGap.SimpleGroup.closureCertificate_of_admissible
#print axioms YMGap.MassGap.SimpleGroup.m_0_uniform_positive
#print axioms YMGap.MassGap.SimpleGroup.m_0_uniform_squared_le
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_osReconstruction
#print axioms YMGap.MassGap.SimpleGroup.MassGapInput.ofGapMonotone
#print axioms YMGap.MassGap.SimpleGroup.MassGapInput.ofZtMajorant
#print axioms YMGap.MassGap.SimpleGroup.MassGapInput.ofRankCollapseData
#print axioms YMGap.MassGap.SimpleGroup.MassGapInput.ofModelData
#print axioms YMGap.MassGap.SimpleGroup.MassGapInput.ofWeylData
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_gapMonotone
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_ztMajorant
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_rankCollapseData
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_modelData
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_weylData
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_SU2_via_ztMajorant
#print axioms YMGap.MassGap.SimpleGroup.su3_uniform_witness
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_SU3
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_SU3_via_weylData
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_suN
#print axioms YMGap.MassGap.SimpleGroup.su2_uniform_witness
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_SU2_via_uniform
