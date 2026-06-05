/-
Group-invariant interface for the σ̂-budget closure — the *conditional
symbolic closure* over an arbitrary compact simple gauge group.

# Why this module exists

The Clay statement asks for a mass gap for *any* compact simple gauge
group `G` — i.e. for all of them: the four classical families
`A_n = SU(n+1)`, `B_n = SO(2n+1)`, `C_n = Sp(n)`, `D_n = SO(2n)`, and the
five exceptionals `G₂, F₄, E₆, E₇, E₈`.  A per-group `decide` witness
(as in `MassGap/SU2.lean`) re-instantiates the closure for one group; it
does not establish it for an arbitrary group.

The closure machinery, however, never inspects the group itself — only a
handful of *scalar invariants* derived from its representation theory:

  * `C2_fund` — the fundamental(-rep) quadratic Casimir.  Sets the
    small-field activity-decay scale (`c_λ`); larger ⇒ stronger
    small-field suppression.  For `SU(N)`, `C2_fund = (N²−1)/(2N)`.
  * `C2_adj`  — the adjoint Casimir, equal to the dual Coxeter number
    `h^∨`.  Drives the one-loop running `b₀ = (11/3)·C2_adj`; larger ⇒
    faster running ⇒ a *headwind* on the budget over many RG steps.
    For `SU(N)`, `C2_adj = N`.

So the honest general target is to parametrize the closure by those
invariants rather than by `N` (which would only reach the `A_n` family).
Every simple group instantiates `RepData` by plugging in its own
Casimirs; the closure theorem `RepData.budget_closes` then holds
*uniformly* in the group, conditional on the per-group analytic budget.

# What this module proves (and what it does not)

`RepData.budget_closes` is the **conditional** symbolic closure:

    for ANY `RepData R` admitting a `ClosureCertificate`,
        ∀ N, Σ_{k<N} η_k(R)  ≤  σ̂₀(R).

The certificate bundles the obligations a concrete group must discharge:

  1. `balaban` — the small-field rate is *derived from the group's
     fundamental Casimir* via the Bałaban relation
     `ρ_sf · g² ≃ C2_fund · conv`.  This is the structural tie between
     the closure and representation theory; it is what makes `ρ_sf` a
     group quantity rather than a free fiducial.
  2. `eta_nonneg`, `budget` — the per-step degradation is nonnegative and
     its `K`-step total fits under σ̂₀.

What this module does **not** do — and what remains genuinely open for an
*unconditional* SU(N)/all-groups result — is prove the `budget` field
holds *uniformly over the admissible invariant range*.  That is the
parametric analytic bound: showing `η_max(C2_fund, C2_adj, g₀)` summed
over the window stays under σ̂₀ for every simple group at once.  It is
where the `C2_adj`-driven running headwind competes with the
`C2_fund`-driven small-field tailwind, it needs the rigorous large-field
character-tail bound (which uses `exp`/`sin` and lives outside `Q'`), and
it is the same deferred constructive step as in the per-group case.  This
module makes that obligation *precise and group-uniform*; it does not
discharge it.

# Instances

`su2` and `su3` instantiate the interface and discharge their
certificates by `decide` at the documented operating point
(`g₀ = 0.30`, `K = 3`).  Both `balaban` relations hold exactly:
`(25/3)·(9/100) = 3/4 = C2_fund(SU2)` and
`(400/27)·(9/100) = 4/3 = C2_fund(SU3)`.  SU(3) closes with far more
margin (a ~20× smaller per-step bound), matching the closure-spike
finding that the larger fundamental Casimir suppresses small-field
activity harder.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` (inherited from the `Q'`
order via `prefix_plus_tail_closure`) or empty (the `decide` facts).  No
`Classical.*`, no `Quot.sound`, no `sorryAx`.  See the `#print axioms`
block at the end.
-/

import YMGap.Constructive.RationalTail

namespace YMGap.RepTheory

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## Generic finite-window closure engine

A `K`-step constant-budget η-sequence: `η_max` for the first `K` RG
steps, `0` thereafter.  Generalizes `RationalTail.truncated_const_3`
(hard-coded `K = 3`) to an arbitrary window length, so the closure no
longer bakes in the SU(2) pilot's three-step window. -/

/-- η-sequence that is `η_max` for indices `k < K` and `0` from `K` on. -/
def truncatedConst (K : Nat) (η_max : Q') : QSeq :=
  fun k => if k < K then η_max else 0

/-- Past the window cut-off `K`, the sequence is identically zero. -/
theorem truncatedConst_zero_of_ge (K : Nat) (η_max : Q') :
    ∀ k, K ≤ k → truncatedConst K η_max k = 0 := by
  intro k hk
  show (if k < K then η_max else 0) = 0
  have hnlt : ¬ k < K := fun hlt => Nat.lt_irrefl k (Nat.lt_of_lt_of_le hlt hk)
  rw [if_neg hnlt]

/-- Every term is nonnegative when `η_max` is. -/
theorem truncatedConst_nonneg (K : Nat) (η_max : Q') (h : (0 : Q') ≤ η_max) :
    ∀ k, (0 : Q') ≤ truncatedConst K η_max k := by
  intro k
  show (0 : Q') ≤ if k < K then η_max else 0
  by_cases hk : k < K
  · rw [if_pos hk]; exact h
  · rw [if_neg hk]; exact Q'.le_refl' _

/-- **Generic constant-window closure.**

If the per-step budget `η_max` is nonnegative and its `K`-step partial
sum fits under `σ₀`, then *every* finite partial sum fits under `σ₀`.

The tail past the window is exactly zero (`truncatedConst_zero_of_ge`),
so the uniform-past-`K` bound is just the `K`-step sum, and
`prefix_plus_tail_closure` supplies nonneg-monotonicity for `N < K`.
This is the window-length-agnostic core that every group reuses. -/
theorem constWindow_closes (K : Nat) (η_max σ₀ : Q')
    (h_nonneg : (0 : Q') ≤ η_max)
    (h_budget : finSum (truncatedConst K η_max) K ≤ σ₀) :
    ∀ N, finSum (truncatedConst K η_max) N ≤ σ₀ := by
  apply prefix_plus_tail_closure (truncatedConst K η_max) K
        (finSum (truncatedConst K η_max) K) σ₀
  · exact truncatedConst_nonneg K η_max h_nonneg
  · intro M
    rw [finSum_stabilizes_after_K (truncatedConst K η_max) K
          (truncatedConst_zero_of_ge K η_max) M]
    exact Q'.le_refl' _
  · exact h_budget

/-! ## The group-invariant interface -/

/-- Scalar representation-theoretic data the σ̂-budget closure depends
on, for one compact simple gauge group at one operating point.

Group-agnostic by construction: the fields are arbitrary `Q'` (and one
`Nat`), so `SU(N)`, `SO(N)`, `Sp(N)`, and the exceptionals all
instantiate it by supplying their own Casimirs. -/
structure RepData where
  /-- Fundamental quadratic Casimir `C₂(fund)`.  `SU(N): (N²−1)/(2N)`. -/
  C2_fund : Q'
  /-- Adjoint Casimir `C₂(adj) = h^∨` (dual Coxeter).  `SU(N): N`. -/
  C2_adj  : Q'
  /-- The squared gauge coupling `g₀²` at the operating point. -/
  g_sq    : Q'
  /-- Heat-kernel normalization convention factor (`t = conv / g²`). -/
  conv    : Q'
  /-- Small-field rate `ρ_sf`, derived from `C2_fund` via Bałaban. -/
  rho_sf  : Q'
  /-- Uniform per-step σ̂-degradation upper bound `η_max`. -/
  eta_max : Q'
  /-- Number of RG steps in the finite closure window `K`. -/
  K_steps : Nat
  /-- Initial dimensionless string tension `σ̂₀`. -/
  sigma0  : Q'

/-- The obligations a concrete group must exhibit for the closure to
apply.  Bundling them as a structure (rather than loose hypotheses)
keeps `budget_closes` universally quantified over groups and records
exactly what a valid instance owes.

`balaban` is the structural tie to representation theory: it forces
`ρ_sf` to be the Bałaban solution against the group's fundamental
Casimir, not a free constant.  `eta_nonneg`/`budget` are the analytic
content (the deferred parametric bound, per the module header). -/
structure RepData.ClosureCertificate (R : RepData) : Prop where
  /-- Small-field Bałaban relation `ρ_sf · g² ≃ C2_fund · conv`. -/
  balaban    : (R.rho_sf * R.g_sq).eqv (R.C2_fund * R.conv)
  /-- Per-step degradation is nonnegative. -/
  eta_nonneg : (0 : Q') ≤ R.eta_max
  /-- The `K`-step budget fits under σ̂₀. -/
  budget     : finSum (truncatedConst R.K_steps R.eta_max) R.K_steps ≤ R.sigma0

/-- **Conditional symbolic closure (all simple groups, via invariants).**

For ANY `RepData R` that admits a `ClosureCertificate`, the σ̂-budget
closes at every finite truncation:

    ∀ N, Σ_{k<N} η_k  ≤  σ̂₀.

The proof is the generic engine `constWindow_closes`; the group enters
only through `R`'s invariants and the certificate.  An *unconditional*
result requires proving `cert.budget` holds uniformly over the admissible
invariant range — the open parametric-analytic step (see module header),
NOT a consequence of this theorem. -/
theorem RepData.budget_closes (R : RepData) (cert : R.ClosureCertificate) :
    ∀ N, finSum (truncatedConst R.K_steps R.eta_max) N ≤ R.sigma0 :=
  constWindow_closes R.K_steps R.eta_max R.sigma0 cert.eta_nonneg cert.budget

/-! ## The SU(N) family: invariants as functions of `N`

For `SU(N)` in the standard normalization (`T(fund) = 1/2`):

  * `C₂(fund) = (N² − 1) / (2N)` — grows like `N/2`; the small-field
    suppression *tailwind* (larger ⇒ smaller per-step η).
  * `C₂(adj)  = N` = the dual Coxeter number `h^∨` — the RG-running
    *headwind* via `b₀ = (11/3)·N`.

These give the `A_{N−1}` family.  `SO(N)`, `Sp(N)`, and the exceptionals
instantiate `RepData` with their own Casimirs identically; the closure
theorem `budget_closes` is blind to which group supplied the scalars. -/

/-- `C₂(fund)` for `SU(N)`: `(N² − 1)/(2N)`.  Needs `0 < N` for the
denominator.  `N = 2 ↦ 3/4`, `N = 3 ↦ 8/6 ≃ 4/3`. -/
def suN_C2_fund (N : Nat) (hN : 0 < N) : Q' :=
  Q'.mkPos ((N : Int) * (N : Int) - 1) (2 * N) (Nat.mul_pos (by decide) hN)

/-- `C₂(adj) = h^∨` for `SU(N)`: simply `N`. -/
def suN_C2_adj (N : Nat) : Q' := Q'.ofNat N

/-! ## Instances: SU(2) and SU(3) at the canonical operating point

Both at `g₀ = 0.30` (`g² = 9/100`), canonical convention (`conv = 1`),
`K = 3`.  Provenance mirrors `Sheaf/SU2KP.lean` and
`docs/su3-campaign-plan.md` §0. -/

/-- SU(2): `C₂(fund) = 3/4`, `C₂(adj) = 2`, `ρ_sf = 25/3`.
`η_max = 3e-4` dominates each canonical per-step η_k ≈ 2.7e-4
(`Sheaf/SU2KP.lean` / `RG/SigmaHatPilot.lean`). -/
def su2 : RepData where
  C2_fund := Q'.mkPos 3 4 (by decide)
  C2_adj  := 2
  g_sq    := Q'.mkPos 9 100 (by decide)
  conv    := 1
  rho_sf  := Q'.mkPos 25 3 (by decide)
  eta_max := Q'.mkPos 3 10000 (by decide)
  K_steps := 3
  sigma0  := 1

/-- SU(3): `C₂(fund) = 4/3`, `C₂(adj) = 3`, `ρ_sf = 400/27`.
`η_max = 13e-6` is ≥ the documented SU(3) closure-spike total
`Σ η = 1.2149e-5` (`docs/su3-campaign-plan.md` §0, g₀=0.30, K=3), hence
dominates each per-step η_k; the ~20× smaller per-step bound vs SU(2) is
the larger-Casimir small-field suppression. -/
def su3 : RepData where
  C2_fund := Q'.mkPos 4 3 (by decide)
  C2_adj  := 3
  g_sq    := Q'.mkPos 9 100 (by decide)
  conv    := 1
  rho_sf  := Q'.mkPos 400 27 (by decide)
  eta_max := Q'.mkPos 13 1000000 (by decide)
  K_steps := 3
  sigma0  := 1

/-- SU(2) discharges its certificate: Bałaban `(25/3)·(9/100) = 3/4`,
nonneg, and the 3-step total `9/10000 ≤ 1`. -/
theorem su2_cert : su2.ClosureCertificate where
  balaban    := by decide
  eta_nonneg := by decide
  budget     := by decide

/-- SU(3) discharges its certificate: Bałaban `(400/27)·(9/100) = 4/3`,
nonneg, and the 3-step total `39e-6 ≤ 1` (closes with large margin). -/
theorem su3_cert : su3.ClosureCertificate where
  balaban    := by decide
  eta_nonneg := by decide
  budget     := by decide

/-- SU(2) σ̂-budget closes for every truncation, via the generic engine. -/
theorem su2_budget_closes :
    ∀ N, finSum (truncatedConst su2.K_steps su2.eta_max) N ≤ su2.sigma0 :=
  su2.budget_closes su2_cert

/-- SU(3) σ̂-budget closes for every truncation, via the generic engine. -/
theorem su3_budget_closes :
    ∀ N, finSum (truncatedConst su3.K_steps su3.eta_max) N ≤ su3.sigma0 :=
  su3.budget_closes su3_cert

/-! ### The instance Casimirs are the SU(N) formula at N = 2, 3

Certifies that `su2`/`su3` are not ad-hoc fiducials but the `SU(N)`
invariant formula evaluated at `N = 2, 3` (semantic `Q'` equivalence). -/

/-- `su2`'s Casimirs equal `suN(2)`: `C₂(fund) = 3/4`, `C₂(adj) = 2`. -/
theorem su2_matches_suN :
    su2.C2_fund.eqv (suN_C2_fund 2 (by decide)) ∧
    su2.C2_adj.eqv (suN_C2_adj 2) :=
  ⟨by decide, by decide⟩

/-- `su3`'s Casimirs equal `suN(3)`: `C₂(fund) = 8/6 ≃ 4/3`, `C₂(adj) = 3`. -/
theorem su3_matches_suN :
    su3.C2_fund.eqv (suN_C2_fund 3 (by decide)) ∧
    su3.C2_adj.eqv (suN_C2_adj 3) :=
  ⟨by decide, by decide⟩

end YMGap.RepTheory

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.truncatedConst_zero_of_ge
#print axioms YMGap.RepTheory.truncatedConst_nonneg
#print axioms YMGap.RepTheory.constWindow_closes
#print axioms YMGap.RepTheory.RepData.budget_closes
#print axioms YMGap.RepTheory.su2_cert
#print axioms YMGap.RepTheory.su3_cert
#print axioms YMGap.RepTheory.su2_budget_closes
#print axioms YMGap.RepTheory.su3_budget_closes
#print axioms YMGap.RepTheory.suN_C2_fund
#print axioms YMGap.RepTheory.suN_C2_adj
#print axioms YMGap.RepTheory.su2_matches_suN
#print axioms YMGap.RepTheory.su3_matches_suN
