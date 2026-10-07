/-
Legacy `CartanType`-indexed scalar representatives for the abstract uniform
mass-gap reduction.

# Mathematical-honesty quarantine

`CartanType` is a raw family/rank code; new code should validate it with
`IsCanonicalSimpleCode`.  The historical `IsSimpleRank` name used by the
declarations below is only a compatibility alias for that canonical-code
predicate, not a literal test of Lie simplicity.

`repDataOf` and its field name `C₂_fund` are retained as a **legacy
representative scalar table**.  This file constructs no compact group, global
form `G_sc/Gamma`, faithful lattice action, representation descent, or Haar
theory, and it does not prove that the stored representation is the smallest
allowed nontrivial Casimir for a chosen global form.  The global-form/descent
repair and the known `D_n` vector-Casimir normalization defect are tracked in
`work_plan.md` §8.9.  Accordingly, the results below are scalar-interface
compositions, not a faithful realization of all compact simple gauge groups.

# What this module delivers (Milestone 11.12, items 2–5)

`RepTheory/CartanType.lean` supplies the raw `CartanType` inductive
(A/B/C/D + G₂/F₄/E₆/E₇/E₈) and the crude squared-Weyl-dimension `WeylDimData`
per type.  This module consumes the *proven* per-type Casimir/dual-Coxeter
floors (`RepTheory/CasimirData.lean`) and the *proven* uniform reduction
(`MassGap/SimpleGroup.lean`) to realize:

  * **`repDataOf T`** — a legacy representative `RepData` row for every raw
    code, copying the scalar entries named `C₂_fund` and `C₂_adj = h^∨` from
    `CasimirData.lean` at a conservative,
    admissibility-respecting operating point (`g² = conv = 1`, `ρ_sf = C₂_fund`
    so the Bałaban tie is exact, `η_max = 13·10⁻⁶`, `K = 3`).

  * **`admissible_of_cartanType` (item 5, scalar-interface admissibility)** —
    every canonical code (expressed through the legacy alias) yields an
    `RepTheory.SimpleGroup.AdmissibleSimpleGroup (repDataOf T)`.  Both
    admissibility floors — the Casimir gap `C₂_fund ≥ 3/4` and the dual
    Coxeter `h^∨ = C₂_adj ≥ 2`, each minimized at A₁ inside this legacy table — are the
    current `CasimirData` lemmas, and the closure certificate is exact inside
    that scalar interface.  It does not realize a group or faithful action.

  * **`uniformBudgetWitness_of_cartanType` (item 4)** — a `UniformBudgetWitness
    (repDataOf T)` for every code, assembled through the abstract character-
    tail capstone `RG.uniformBudgetWitness_of_characterTail` in the
    strict-monotone regime (following the PROVEN `su3_uniform_witness_via_tail`
    pattern: the rank-1 majorant carrying the per-axis excess `13/313`,
    `rank_collapse` dominated by SU(2)'s `1/2`, driving `η_max ≤ su2.η_max`
    through the proven `K_lf` monotone bridge).

  * **`AxisFactorBound (repDataOf T)`** (items 2–3, the structural Weyl-
    character data) — realized per representative at the polynomial-geometric
    excess `13/313`; the `ZtEtaModel` model equalities are `decide`-facts.

  * **`mass_gap_of_cartanType` + per-type `mass_gap_A/B/C/D/G2/F4/E6/E7/E8`**
    — conditional scalar compositions with caller-supplied OS data, plus a
    `G₂`-labelled demonstration of the abstract Weyl-data path.

# What the representative budget layer does and does not establish

The BUDGET/η layer uses a *representative operating point*: `η_max = 13·10⁻⁶`
is a conservative value (the proven-admissible SU(3) per-step bound), NOT the
PHYSICAL per-step degradation derived from each group's own heat-kernel
character tail.  Deriving that physical `η_max(G)` — in particular for the
non-simply-laced `G₂`/`F₄`, where the short-root Killing-form normalization
enters (Milestone 1.1 precedent) — is exactly the SAME named analytic residual
already isolated as `UniformBudget.UniformBudgetWitness.eta_dominated` (the
antitone-in-Δ heat-kernel input, a `CReal` statement outside `Q'`).  It is NOT
discharged here: the representatives exercise the abstract scalar reduction;
the physical character-tail analysis per realized global group remains open.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing fact is a `Q'`-rational `decide`, an explicit `Q'`
order/`eqv` proof, or an assembly of the proven reduction; each reports
`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `native_decide`,
no `sorryAx`, no custom axiom.  See the `#print axioms` block at the end.
-/

import YMGap.RepTheory.CartanType
import YMGap.MassGap.SimpleGroup
import YMGap.RG.WeylDimGeneralData
import YMGap.BudgetConstants

namespace YMGap.MassGap.AllSimpleTypes

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RepTheory
open YMGap.RG
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.OSReconstruction
open YMGap.MassGap.SimpleGroup

/-! ## The legacy representative `RepData` from two stored scalars

`repOfCasimir c2f c2a` packages the two legacy scalar fields
`C₂_fund = c2f`, `C₂_adj = c2a` at a conservative operating point.  The
Bałaban tie `ρ_sf·g² ≃ C₂_fund·conv` holds *exactly* by construction
(`ρ_sf := c2f`, `g² := conv := 1`), so the closure certificate is real, and
`η_max := 13·10⁻⁶` (the proven-admissible SU(3) per-step bound) with `K = 3`
closes the budget and is dominated by SU(2)'s `3·10⁻⁴`. -/

/-- The representative `RepData` carrying the stored scalars `c2f`, `c2a`. -/
def repOfCasimir (c2f c2a : Q') : RepData where
  C2_fund := c2f
  C2_adj  := c2a
  g_sq    := 1
  conv    := 1
  rho_sf  := c2f
  eta_max := YMGap.BudgetConstants.bcEtaMaxSimple
  K_steps := 3
  sigma0  := 1

/-! The operating-point projections are constant (independent of the Casimirs),
recorded as `rfl`-lemmas so downstream `decide` goals can be reduced to a
variable-free form (the `decide` tactic refuses goals containing the free
Casimir variables). -/

/-- The representative's per-step degradation is the constant `13·10⁻⁶`. -/
theorem repOfCasimir_eta_max (c2f c2a : Q') :
    (repOfCasimir c2f c2a).eta_max = su3.eta_max := rfl

/-- The representative's RG window is the constant `3`. -/
theorem repOfCasimir_K (c2f c2a : Q') : (repOfCasimir c2f c2a).K_steps = 3 := rfl

/-- The representative's initial string tension is the constant `1`. -/
theorem repOfCasimir_sigma0 (c2f c2a : Q') : (repOfCasimir c2f c2a).sigma0 = 1 := rfl

/-- The representative discharges its closure certificate: the Bałaban tie is
exact (`c2f·1 ≃ c2f·1`, reflexive), `η_max ≥ 0`, and the 3-step budget
`39·10⁻⁶ ≤ 1`. -/
theorem repOfCasimir_cert (c2f c2a : Q') : (repOfCasimir c2f c2a).ClosureCertificate where
  balaban    := Q'.eqv_refl _
  eta_nonneg := by rw [repOfCasimir_eta_max]; decide
  budget     := by
    rw [repOfCasimir_eta_max c2f c2a, repOfCasimir_K c2f c2a, repOfCasimir_sigma0 c2f c2a]
    decide

/-! ## The legacy canonical-code predicate name

`IsSimpleRank` now comes from the cycle-free
`RepTheory/CartanType.lean` leaf and retains its original fully qualified name
`YMGap.MassGap.AllSimpleTypes.IsSimpleRank`.  It removes low-rank Lie-type
redundancies only; it does not choose a compact group's global form. -/

/-! ## The legacy representative row for every raw Cartan code

`repDataOf T` plugs the table's exact-ℚ representation/dual-Coxeter scalars
(`RepTheory/CasimirData.lean`, anchored to the repo normalization so
`A₁ → C₂_fund = 3/4`, `h^∨ = 2`) into `repOfCasimir`.  Type A reuses the
SU(N) formula; `B/C/D` use the legacy `soOdd/sp/soEven` rows; the five
exceptionals use closed literals.  This does not select or realize a global
form, and §8.9 of the work plan records why these rows are not yet a physical
minimum-Casimir table. -/

/-- The legacy representative `RepData` row for each raw Cartan code. -/
def repDataOf : CartanType → RepData
  | .A n => repOfCasimir (suN_C2_fund (n + 1) (Nat.succ_pos n)) (suN_C2_adj (n + 1))
  | .B n => repOfCasimir (soOdd_C2_fund n) (soOdd_C2_adj n)
  | .C n => repOfCasimir (sp_C2_fund n) (sp_C2_adj n)
  | .D n => repOfCasimir (soEven_vector_C2 n) (soEven_C2_adj n)  -- J04 T1: corrected vector value; min(vector, half-spin) for n ≥ 4
  | .G2 => repOfCasimir g2_C2_fund g2_C2_adj
  | .F4 => repOfCasimir f4_C2_fund f4_C2_adj
  | .E6 => repOfCasimir e6_C2_fund e6_C2_adj
  | .E7 => repOfCasimir e7_C2_fund e7_C2_adj
  | .E8 => repOfCasimir e8_C2_fund e8_C2_adj

/-! ## Item 5 — scalar-interface admissibility for canonical codes

For every canonical nonredundant code, the legacy representative row satisfies
the abstract structure `AdmissibleSimpleGroup`.  Both scalar floors come from
the current `CasimirData` lemmas and the closure certificate is
`repOfCasimir_cert`.  The structure's historical name does not turn this row
into a realized group, faithful action, or global-form representation table. -/

/-- **Every canonical Cartan code yields an admissible legacy scalar row.**
The two admissibility floors are the current `CasimirData` lemmas
(`suN_/soOdd_/sp_/soEven_/g2_/…_gap_lb` and `_hvee_lb`), each minimized only at
A₁ inside this table; the closure certificate is exact.  This is an
interface-admissibility theorem only. -/
theorem admissible_of_cartanType (T : CartanType) (h : IsSimpleRank T) :
    AdmissibleSimpleGroup (repDataOf T) := by
  cases T with
  | A n =>
      have hn : 1 ≤ n := h
      exact ⟨suN_gap_lb (n + 1) (by omega), suN_hvee_lb (n + 1) (by omega),
             repOfCasimir_cert _ _⟩
  | B n =>
      have hn : 2 ≤ n := h
      exact ⟨soOdd_gap_lb n (by omega), soOdd_hvee_lb n (by omega),
             repOfCasimir_cert _ _⟩
  | C n =>
      have hn : 3 ≤ n := h
      exact ⟨sp_gap_lb n (by omega), sp_hvee_lb n (by omega),
             repOfCasimir_cert _ _⟩
  | D n =>
      have hn : 4 ≤ n := h
      exact ⟨soEven_vector_gap_lb n (by omega), soEven_hvee_lb n (by omega),
             repOfCasimir_cert _ _⟩
  | G2 => exact ⟨g2_gap_lb, g2_hvee_lb, repOfCasimir_cert _ _⟩
  | F4 => exact ⟨f4_gap_lb, f4_hvee_lb, repOfCasimir_cert _ _⟩
  | E6 => exact ⟨e6_gap_lb, e6_hvee_lb, repOfCasimir_cert _ _⟩
  | E7 => exact ⟨e7_gap_lb, e7_hvee_lb, repOfCasimir_cert _ _⟩
  | E8 => exact ⟨e8_gap_lb, e8_hvee_lb, repOfCasimir_cert _ _⟩

/-! ## Items 2–4 — abstract representative tail data + budget witness

The `ZtMajorant`, `ZtEtaModel`, and `AxisFactorBound` for `repOfCasimir` are
uniform in the Casimirs (they involve only the operating-point constants), so a
single generic realization serves every type.  We follow the PROVEN
`su3_uniform_witness_via_tail` strict-monotone regime: rank-1 majorant at
per-axis excess `13/313`, `rank_collapse` dominated by SU(2)'s `1/2`, the
η-model at weight `μ = su2.η_max` reproducing `η_max = 13·10⁻⁶`. -/

/-- The representative rank-1 `Z_t` majorant at the strict-monotone excess
`13/313` (`rank_collapse` : `13/313 ≤ 1/2`). -/
def repOfCasimir_ztMajorant (c2f c2a : Q') : ZtMajorant (repOfCasimir c2f c2a) where
  rank      := 1
  sR        := fun _ => Q'.mkPos 13 313 (by decide)
  sFloor    := fun _ => Q'.mkPos 13 313 (by decide)
  su2Zt     := Q'.mkPos 1 2 (by decide)
  sR_nonneg := fun _ => by decide
  sR_le     := fun _ => Q'.le_refl' _
  rank_collapse := by decide

/-- The representative `Z_t ↦ η` model: weight `μ = su2.η_max`, `R`-tail
`13/313`, SU(2)-tail `1/2`.  Both model equalities hold by `decide`
(`etaModel (3/10⁴) (13/313) ≃ 13/10⁶ = η_max`, `etaModel (3/10⁴) (1/2) ≃
3/10⁴ = su2.η_max`), following `su3_ztEtaModel_matched`. -/
def repOfCasimir_ztEtaModel (c2f c2a : Q') : ZtEtaModel (repOfCasimir c2f c2a) where
  μ         := su2.eta_max
  ZtR       := ztValue (fun _ => Q'.mkPos 13 313 (by decide)) 1
  Ztsu2     := Q'.mkPos 1 2 (by decide)
  μ_nonneg  := by decide
  ZtR_nn    := by decide
  conv_su2  := by decide
  etaR_eq   := by rw [repOfCasimir_eta_max]; decide
  etasu2_eq := by decide

/-- The representative per-axis Weyl-character factor data (items 2–3): rank-1,
polynomial-geometric excess `13/313`.  A genuine `AxisFactorBound` at the
representative operating point. -/
def repOfCasimir_axisFactorBound (c2f c2a : Q') : AxisFactorBound (repOfCasimir c2f c2a) where
  rank       := 1
  axisExcess := fun _ => Q'.mkPos 13 313 (by decide)
  exc_nonneg := fun _ => by decide

/-- **The representative budget witness through the abstract tail
capstone.**  Assembled by `uniformBudgetWitness_of_characterTail` from the
matched majorant + model; the tail compatibilities are `rfl` and the window
equality is `decide`.  `η_max ≤ su2.η_max` is *derived* from the strict tail
domination `13/313 < 1/2` through the proven `K_lf`-monotone bridge — the same
real-work regime as `su3_uniform_witness_via_tail`. -/
theorem repOfCasimir_uniformWitness (c2f c2a : Q') :
    UniformBudgetWitness (repOfCasimir c2f c2a) :=
  uniformBudgetWitness_of_characterTail
    (repOfCasimir_ztMajorant c2f c2a)
    (repOfCasimir_ztEtaModel c2f c2a)
    rfl rfl rfl

/-- **Item 4: a budget witness for every raw Cartan-code row.** -/
theorem uniformBudgetWitness_of_cartanType (T : CartanType) :
    UniformBudgetWitness (repDataOf T) := by
  cases T <;> exact repOfCasimir_uniformWitness _ _

/-! ## Item 5 — conditional mass-gap composition for each legacy row

Combining scalar-interface admissibility (`admissible_of_cartanType`) with the
representative budget witness (`uniformBudgetWitness_of_cartanType`) and the
paper-supplied OS-reconstruction interface, `mass_gap_simple_group_of_osReconstruction`
returns the existing conditional mass-gap conclusion for each row.  This does
not construct the corresponding group, measure, or reconstruction input. -/

/-- **Conditional mass-gap composition for a validated Cartan code's legacy
row.** A one-line evaluation of the uniform theorem at `repDataOf T`, its
scalar-interface admissibility, its budget witness, and caller-supplied OS
reconstruction data. -/
theorem mass_gap_of_cartanType (T : CartanType) (h : IsSimpleRank T)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf T).K_steps (repDataOf T).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_simple_group_of_osReconstruction (repDataOf T)
    (admissible_of_cartanType T h) (uniformBudgetWitness_of_cartanType T) rec bundle

/-! ### Per-code conditional mass-gap corollaries

Thin aliases of `mass_gap_of_cartanType` at each family/exceptional.  The
classical families carry the canonical-code hypothesis; the exceptionals need
none.  Each remains conditional on the same caller-supplied OS data. -/

/-- Conditional result for the legacy `A_n` row (`n ≥ 1`). -/
theorem mass_gap_A (n : Nat) (hn : 1 ≤ n)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf (.A n)).K_steps (repDataOf (.A n)).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType (.A n) hn rec bundle

/-- Conditional result for the legacy `B_n` row (`n ≥ 2`). -/
theorem mass_gap_B (n : Nat) (hn : 2 ≤ n)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf (.B n)).K_steps (repDataOf (.B n)).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType (.B n) hn rec bundle

/-- Conditional result for the legacy `C_n` row (`n ≥ 3`). -/
theorem mass_gap_C (n : Nat) (hn : 3 ≤ n)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf (.C n)).K_steps (repDataOf (.C n)).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType (.C n) hn rec bundle

/-- Conditional result for the `D_n` row (`n ≥ 4`).  Since J04 T1 the row
uses the corrected vector Casimir `soEven_vector_C2 n = (2n−1)/2`, which is the
minimum of vector and half-spin values for `n ≥ 4` in any global form where the
vector descends (`soEven_halfSpin_eq_vector_D4`, `soEven_vector_lt_halfSpin_D5`). -/
theorem mass_gap_D (n : Nat) (hn : 4 ≤ n)
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf (.D n)).K_steps (repDataOf (.D n)).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType (.D n) hn rec bundle

/-- Mass gap for the `G₂` representative. -/
theorem mass_gap_G2
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf .G2).K_steps (repDataOf .G2).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType .G2 trivial rec bundle

/-- Mass gap for the `F₄` representative. -/
theorem mass_gap_F4
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf .F4).K_steps (repDataOf .F4).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType .F4 trivial rec bundle

/-- Mass gap for the `E₆` representative. -/
theorem mass_gap_E6
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf .E6).K_steps (repDataOf .E6).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType .E6 trivial rec bundle

/-- Mass gap for the `E₇` representative. -/
theorem mass_gap_E7
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf .E7).K_steps (repDataOf .E7).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType .E7 trivial rec bundle

/-- Mass gap for the `E₈` representative. -/
theorem mass_gap_E8
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf .E8).K_steps (repDataOf .E8).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_of_cartanType .E8 trivial rec bundle

/-! ## Items 2–3 demonstrated: the Weyl-character structural path on G₂

`mass_gap_simple_group_of_weylData` routes the mass gap through the
`AxisFactorBound` structural data (the per-axis polynomial-geometric tail)
rather than the raw budget witness.  We exhibit it on the concrete `G₂`
representative: the character-tail inequality `Z_t(repDataOf G₂) ≤ Z_t(su2)`
is a theorem of the per-axis excess data (`13/313 < 1/2` via the proven
rank-collapse), and the `ZtEtaModel` supplies the heat-kernel `Z_t ↦ η`
packaging.  This shows the items 2–3 data closing the reduction through the
structural route, not merely the direct witness. -/

/-- **G₂ mass gap via the Weyl-character structural path.**  Consumes the
representative `AxisFactorBound` (per-axis excess `13/313`) and the matching
`ZtEtaModel`; the window/cap facts (`26/313 ≤ 1`, `26/313 ≤ 1/2`) and the tail
compatibilities discharge by `decide`/`rfl`. -/
theorem mass_gap_G2_via_weylData
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q',
      (0 : Q') < m_0 ∧
      m_0 * m_0 ≤ sigma_hat_inf_lower_uniform ∧
      HasSpectralGap rec ∧
      (∀ N, finSum (truncatedConst (repDataOf .G2).K_steps (repDataOf .G2).eta_max) N
              ≤ su2.sigma0) :=
  mass_gap_simple_group_of_weylData (repDataOf .G2)
    (admissible_of_cartanType .G2 trivial)
    (repOfCasimir_axisFactorBound g2_C2_fund g2_C2_adj)
    (Q'.mkPos 1 2 (by decide))
    (by decide) (by decide)
    (repOfCasimir_ztEtaModel g2_C2_fund g2_C2_adj)
    rfl rfl (by decide) rec bundle

end YMGap.MassGap.AllSimpleTypes

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.MassGap.AllSimpleTypes.repOfCasimir_cert
#print axioms YMGap.MassGap.AllSimpleTypes.admissible_of_cartanType
#print axioms YMGap.MassGap.AllSimpleTypes.repOfCasimir_ztMajorant
#print axioms YMGap.MassGap.AllSimpleTypes.repOfCasimir_ztEtaModel
#print axioms YMGap.MassGap.AllSimpleTypes.repOfCasimir_axisFactorBound
#print axioms YMGap.MassGap.AllSimpleTypes.repOfCasimir_uniformWitness
#print axioms YMGap.MassGap.AllSimpleTypes.uniformBudgetWitness_of_cartanType
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_of_cartanType
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_A
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_B
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_C
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_D
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_G2
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_F4
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_E6
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_E7
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_E8
#print axioms YMGap.MassGap.AllSimpleTypes.mass_gap_G2_via_weylData
