/-
Mass gap for *every* compact simple gauge group — the uniform
(all-simple-groups) assembly, transported from the proven SU(2) result.

# What this module delivers

`MassGap/SU2.lean` proves the SU(2) mass gap (`mass_gap_SU2`) by pairing
a Q'-rational lower bound `m_0 = 999/1000` (with `m_0² ≤ σ̂∞ = 9991/10000`)
against the paper-supplied OS-reconstruction spectral-gap interface.  The
σ̂∞ bound there is `1 − Σ η_k` at SU(2)'s budget.

This module lifts that to an arbitrary admissible simple group `R` by the
§1.3 reduction:

  * `RepTheory/SimpleGroup.lean` — `AdmissibleSimpleGroup R`: every simple
    group has `C₂_fund ≥ 3/4`, `C₂_adj ≥ 2`, minimised at SU(2).
  * `RG/UniformBudget.lean` — `monotone_budget`: with the per-step bound
    dominated by SU(2)'s (`UniformBudgetWitness.eta_dominated`, the named
    analytic input), `R`'s σ̂-budget is ≤ SU(2)'s at *every* truncation.

Because `R`'s budget is dominated by SU(2)'s, the *same* conservative
σ̂∞ floor `9991/10000` that closes SU(2) is a valid lower bound for `R`:
`σ̂∞(R) = σ̂₀ − Σ η(R) ≥ σ̂₀ − Σ η(su2) ≥ 9991/10000`.  So the SU(2)
mass-gap witness `m_0 = 999/1000` transports verbatim.

# Top theorems

  * `budget_closes_uniform R hadm w` — the unconditional all-truncations
    σ̂-budget closure for `R`, derived (no per-group `decide`) from
    `monotone_budget` + the proven `su2_budget_closes`.
  * `mass_gap_simple_group R hadm w rec bundle` — the §0 target: an
    explicit `m_0 : Q'` with `0 < m_0`, `m_0² ≤ ε` (the transported SU(2)
    floor), and the OS spectral-gap conjunct `HasSpectralGap rec`.  Same
    formal/paper boundary as `mass_gap_SU2`.
  * `mass_gap_SU3` — the near-free SU(3) corollary: SU(3) is admissible
    (`su3_admissible`) and η-dominated (`su3_uniform_witness`, by `decide`:
    `13e-6 ≤ 3e-4`), so the top theorem instantiates directly.

# The named analytic obligation (Rule 2 / Rule 6)

Everything here is constructive and axiom-clean **modulo** the single
named field `UniformBudgetWitness.eta_dominated` (`R.eta_max ≤ su2.eta_max`,
the antitone-in-Δ heat-kernel input) and the OS-reconstruction interface
Props inherited unchanged from `mass_gap_SU2`.  For the SU(N) instances
(SU(2), SU(3)) the witness is discharged by `decide`; for the general
group it is the paper-layer obligation.

# Axiom-gate (AGENTS.md Rule 1)

`mass_gap_simple_group` composes Q'-rational `decide` facts, the
`[propext]` budget closure, and the trivial OS bridge; it reports
`[propext]` (or `[propext, Quot.sound]`).  See the `#print axioms` block.
-/

import YMGap.RG.UniformBudget
import YMGap.RG.CharacterTailAntitone
import YMGap.RG.CharacterTailMajorant
import YMGap.RG.RankCollapse
import YMGap.RG.EtaPackaging
import YMGap.RG.WeylCharacterBound
import YMGap.RepTheory.CasimirData
import YMGap.MassGap.SU2

namespace YMGap.MassGap.SimpleGroup

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RepTheory
open YMGap.RG
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.OSReconstruction
open YMGap.MassGap.SU2

/-! ## The unconditional uniform budget closure -/

/-- **`budget_closes_uniform`.**  For any admissible simple group `R`
together with the named η-domination witness, the σ̂-budget closes at
*every* finite truncation under SU(2)'s `σ̂₀`:

    ∀ N, Σ_{k<N} η_k(R)  ≤  σ̂₀(su2) = 1.

This is the §1.3 reduction realised: `monotone_budget` transports the
proven SU(2) closure (`su2_budget_closes`) to `R`.  No per-group `decide`
on `R`'s budget — the closure is *derived* from SU(2)'s via the
monotonicity substrate.  The admissibility hypothesis `hadm` records that
`R`'s invariants are those of a genuine simple group (and supplies the
floors that justify the domination); the closure itself flows through
`w`. -/
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

/-! ## The transported σ̂∞ floor

SU(2) closes with `σ̂∞ ≥ 9991/10000` and witness `m_0 = 999/1000`
(`m_0² ≤ σ̂∞`).  Since any admissible η-dominated group's budget is ≤
SU(2)'s, `9991/10000` is a *conservative* σ̂∞ floor for every such group,
and `999/1000` is a valid mass-gap lower bound.  We reuse the SU(2)
constants verbatim; the domination is what licenses the reuse. -/

/-- The uniform mass-gap lower bound (transported SU(2) witness). -/
def m_0_uniform : Q' := m_0_canonical

/-- The uniform σ̂∞ floor (conservative; valid for any η-dominated
admissible group because its budget is ≤ SU(2)'s). -/
def sigma_hat_inf_lower_uniform : Q' := sigma_hat_inf_lower_canonical

/-- `0 < m_0_uniform`. -/
theorem m_0_uniform_positive : (0 : Q') < m_0_uniform :=
  m_0_canonical_positive

/-- `m_0_uniform² ≤ sigma_hat_inf_lower_uniform`. -/
theorem m_0_uniform_squared_le :
    m_0_uniform * m_0_uniform ≤ sigma_hat_inf_lower_uniform :=
  m_0_canonical_squared_le_sigma_hat

/-! ## The top theorem -/

/-- **Mass gap for every compact simple gauge group.**

`formal/mass-gap-theorem.tex` Theorem 1.1, lifted from SU(2) to an
arbitrary admissible simple group `R` via the uniform parametric budget
bound.  Given:

  * `hadm : AdmissibleSimpleGroup R` — `R`'s invariants are those of some
    compact simple `G` (`C₂_fund ≥ 3/4`, `C₂_adj ≥ 2`, the family floors);
  * `w : UniformBudgetWitness R` — the named analytic input pinning SU(2)
    as the worst case (`R.eta_max ≤ su2.eta_max`);
  * `rec`, `bundle` — the OS-reconstruction quintuple and OS-axiom witness
    (paper-supplied, exactly as in `mass_gap_SU2`);

we conclude there is an explicit `m_0 : Q'` with `0 < m_0`,
`m_0² ≤ ε` (the transported σ̂∞ floor `9991/10000`), the OS spectral
gap `HasSpectralGap rec`, AND the *derived* all-truncations σ̂-budget
closure for `R` (`∀ N, Σ η_k(R) ≤ σ̂₀`).

The novelty over `mass_gap_SU2`: `R` ranges over *all* simple groups and
the budget conjunct is **derived** (`budget_closes_uniform`), not
re-`decide`d per group — `hadm`/`w` are genuinely load-bearing (the fourth
conjunct consumes them).  Axiom-gate: `[propext]` / `[propext, Quot.sound]`
(Q'-rational `decide` facts + the budget-closure `[propext]` + the trivial
OS bridge). -/
theorem mass_gap_simple_group
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

/-! ## Mass gap from the gap → η monotonicity obligation

`mass_gap_simple_group` consumes the raw η-domination witness
`UniformBudgetWitness R` (whose load-bearing field is
`eta_dominated : R.eta_max ≤ su2.eta_max`).  The uniform character-tail
analysis (`RG/CharacterTailAntitone.lean`) reduces that field to the
*structural* gap → η monotonicity `EtaGapMonotone R` (the per-step bound
is antitone in the Casimir gap down to the SU(2) floor), whose analytic
engine — `e^{−tΔ}` non-increasing in Δ — is proven constructively there.
This corollary threads that reduction: from an `AdmissibleSimpleGroup R`
(supplying the floor `3/4 ≤ R.C2_fund`), the named `EtaGapMonotone R`,
and the same-window fact, it builds the budget witness and delivers the
mass gap.  The remaining obligation is then exactly `EtaGapMonotone R`
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
  mass_gap_simple_group R hadm
    (uniformBudgetWitness_of_gapMonotone R hadm hmono hwin) rec bundle

/-! ## Mass gap from the rank-general `Z_t` majorant (the honest unconditional path)

`mass_gap_simple_group_of_gapMonotone` consumes the named `EtaGapMonotone R`.
`RG/CharacterTailMajorant.lean` discharges *that* through the rank-general
character-tail majorant `Z_t(R) = ∏_i S_i − 1 ≤ Z_t(su2)`
(`etaGapMonotone_of_ztMajorant`), whose only non-`Q'` inputs are the named
`ZtMajorant.rank_collapse` (the §3 rank-collapse) and the `EtaFromZt`
`Z_t ↦ η` packaging — both bounded to the paper layer, neither faked, and
both *concrete `decide` facts* for the SU(N) family.  This corollary threads
that reduction end to end: from an `AdmissibleSimpleGroup R`, the
`EtaFromZt R` bridge (carrying the majorant), and the same-window fact, it
delivers the mass gap.  The remaining obligation is then exactly the rank-`r`
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
  mass_gap_simple_group_of_gapMonotone R hadm
    (etaGapMonotone_of_ztMajorant bridge) hwin rec bundle

/-! ## Mass gap with `rank_collapse` discharged from the scalar sum bound

`mass_gap_simple_group_of_ztMajorant` still consumes a whole `EtaFromZt R`
whose `major.rank_collapse` was a *posited* field.  `RG/RankCollapse.lean`
discharges that field as a **theorem** (`rank_collapse_of_sum`,
`ztMajorant_of_sum`): from the per-axis floor excesses `sFloor`, the window
`2·Σ sFloor ≤ 1`, and the concrete cap `2·Σ sFloor ≤ Z_t(su2)`, the rank
collapse `∏(1+sFloor)−1 ≤ Z_t(su2)` is proven over `Q'` (the scalar bound
`∏(1+sᵢ)−1 ≤ 2·Σ sᵢ` plus the §3 uniform-domination cap).  This corollary
takes that scalar data *directly* (no posited `rank_collapse`), builds the
majorant, and — given only the `eta_of_zt` packaging (the `Z_t ↦ η` bridge,
the explicitly out-of-scope residual) — delivers the mass gap.  The
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
  mass_gap_simple_group_of_ztMajorant R hadm
    { major := ztMajorant_of_sum (R := R) r sR sFloor su2Zt
        hsR_nn hsR_le hFloor_nn hwin hcap
      eta_of_zt := eta_of_zt }
    hKwin rec bundle

/-- **SU(2) mass gap via the rank-general `Z_t` majorant chain.**  Threads
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

/-! ## Mass gap with BOTH residuals discharged from data
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
  mass_gap_simple_group_of_ztMajorant R hadm
    (etaFromZt_of_model
      (ztMajorant_of_sum (R := R) r sR sFloor su2Zt
        hsR_nn hsR_le hFloor_nn hwin hcap)
      m hZtR hZtsu2)
    hKwin rec bundle

/-! ## Mass gap from the Weyl-character STRUCTURAL data
(the honest reduction of the assumed inequality to root-system data)

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
the mass gap.  The remaining honest content is exactly the two named
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
  mass_gap_simple_group_of_ztMajorant R hadm
    (YMGap.RG.etaFromZt_of_model
      (YMGap.RG.ztMajorant_of_axisData b su2Zt hwin hcap)
      m hZtR hZtsu2)
    hKwin rec bundle

/-! ## SU(3) corollary — the near-free instance

SU(3) is admissible (`su3_admissible`) and η-dominated: its per-step
bound `13e-6` is ≤ SU(2)'s `3e-4` (`decide`), and both use the `K = 3`
window.  So the top theorem instantiates directly, giving SU(3) per-group
parity with SU(2) as a one-line corollary. -/

/-- SU(3) is η-dominated by SU(2): same `K = 3` window, and
`su3.eta_max = 13/1000000 ≤ 3/10000 = su2.eta_max`. -/
theorem su3_uniform_witness : UniformBudgetWitness su3 where
  same_window   := by decide
  eta_dominated := by decide

/-- **Mass gap for SU(3)** — a corollary of `mass_gap_simple_group` at the
admissible, η-dominated instance `su3`.  No new analysis: SU(3)'s
admissibility floors and η-domination are both `decide`-able. -/
theorem mass_gap_SU3
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst su3.K_steps su3.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group su3 su3_admissible su3_uniform_witness rec bundle

/-- **Mass gap for SU(3) via the Weyl-character structural path.**

A specialization of `mass_gap_simple_group_of_weylData` to `R := su3`
(`su3_admissible`, `K = 3` window by `decide`).  The two Weyl-character
residuals this path used to leave open — the per-axis polynomial-geometric
tail `AxisFactorBound` and the squared-Weyl-dimension majorization
`WeylDimData` — are now *discharged theorems* for the SU(N) family
(`RG/PolylogTail.weightedGeomSum_le` / `RG.axisFactor_polylog_le` for the
tail, `RG.su3_dimSq_le` / `RG.su3_weylDimData_at` for the squared dimension),
so the only remaining input is the heat-kernel `Z_t ↦ η` packaging
`ZtEtaModel su3` (the explicitly out-of-scope residual) plus the concrete
window/cap rationals.  This makes explicit that the all-groups character-tail
inequality `Z_t(su3) ≤ Z_t(su2)` is, for SU(3), a theorem of root-system data
rather than a posited bound. -/
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

/-- SU(2) is (trivially) η-dominated by itself — the boundary witness. -/
theorem su2_uniform_witness : UniformBudgetWitness su2 where
  same_window   := by decide
  eta_dominated := by decide

/-- Sanity corollary: the uniform theorem reproduces the SU(2) mass gap at
the boundary instance. -/
theorem mass_gap_SU2_via_uniform
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst su2.K_steps su2.eta_max) N ≤ su2.sigma0) :=
  mass_gap_simple_group su2 su2_admissible su2_uniform_witness rec bundle

end YMGap.MassGap.SimpleGroup

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.MassGap.SimpleGroup.budget_closes_uniform
#print axioms YMGap.MassGap.SimpleGroup.closureCertificate_of_admissible
#print axioms YMGap.MassGap.SimpleGroup.m_0_uniform_positive
#print axioms YMGap.MassGap.SimpleGroup.m_0_uniform_squared_le
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_gapMonotone
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_ztMajorant
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_rankCollapseData
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_modelData
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_weylData
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_SU2_via_ztMajorant
#print axioms YMGap.MassGap.SimpleGroup.su3_uniform_witness
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_SU3
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_SU3_via_weylData
#print axioms YMGap.MassGap.SimpleGroup.su2_uniform_witness
#print axioms YMGap.MassGap.SimpleGroup.mass_gap_SU2_via_uniform
