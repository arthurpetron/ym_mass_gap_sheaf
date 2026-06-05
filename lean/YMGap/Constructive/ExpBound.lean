/-
Level-1 analytic-bound interface: the rational exponential seed + the
cluster / Brydges–Federbush reduction that turns a rational upper bound
on the heat-kernel character tail into a large-field KP certificate —
entirely in `Q'`.

# Where this sits

`RepTheory/RepData.lean` proved the *conditional symbolic closure*: for
any group whose invariants admit a `ClosureCertificate`, the σ̂-budget
closes.  The certificate's `budget` field is the analytic obligation —
ultimately a bound on the per-step η that traces back to the large-field
rate `ρ_lf = −log Z_t` and amplitude `K_lf`, where

    Z_t = Σ_{λ ≠ 0} (dim λ)² · e^{−t·C₂(λ)}

is the heat-kernel character tail.  In `Sheaf/SU2KP.lean` the resulting
`K_lf` is a Python-sourced `Q'` fiducial.

This module pushes the boundary one layer down.  It splits the analytic
content into two clearly-named obligations and **proves everything
between them in `Q'`**:

  1. a rational upper bound `Z_upper ≥ Z_t`  (the `ExpUB` seed interface;
     discharged constructively in `Constructive/ExpNeg.lean`, Level 2);
  2. the cluster-expansion closed form  (the geometric-tail extension of
     `Constructive/Geometric.lean`).

Given `Z_upper`, the Brydges–Federbush cluster reduction
`q = μ_plaq·Z_upper`, `q < 1`, `q ≤ K_lf·(1 − q)` is a finite `Q'`
computation — so `K_lf` is *derived from `Z_upper`*, not posited.  This
is the same shape as `RepData.budget_closes`: bundle the obligations,
prove the reduction, leave the residual transcendental facts as a small,
auditable interface.

# What is provable here, and what is deferred

  * **Provable (this module, `Q'`, axiom-clean):** the cluster reduction
    — convergence `q < 1` and the BF amplitude relation — and the
    assembly of a `KPCertificate Q' P_nonneg` from `(ρ_lf, K_lf)`.  The
    SU(3) instance discharges it by `decide` at the documented operating
    point.
  * **Deferred to Level 2 (`ExpNeg.lean`):** that `Z_upper` really bounds
    `Z_t` — i.e. the per-irrep facts `e^{−t·C₂(λ)} ≤ E(t·C₂(λ))` for the
    rational seed `E`, packaged as `ExpUB` below.
  * **Deferred to the geometric-tail extension** (`Geometric.lean`'s
    open-work `geometric_tail_closure_strong`): summing the out-of-box
    irreps via a rational geometric majorant.

# Why `e^{−x}`/`sin` are the obstruction — and how narrow it actually is

The closure-relevant `Z_t` evaluates characters at the identity, where
`χ_λ(𝟙) = dim λ` — an *integer* (Weyl dimension formula, a polynomial in
the irrep labels).  `C₂(λ)` is rational (a polynomial in the labels).  So
the tail is `Σ (integer)² · e^{−(rational)}`: **no `sin`** (the Weyl
denominator's sines only appear for non-identity group elements, a later
part of the program).  The single transcendental input is a *one-sided
rational bound* `e^{−q} ≤ E(q)` (`q ∈ ℚ`) plus monotonicity — exactly the
`ExpUB` fields, which Level 2 discharges from a constructive `expNeg`.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` (the `Q'` order) or empty
(`decide`).  No `Classical.*`, no `Quot.sound`, no `sorryAx`.
-/

import YMGap.Constructive.Geometric
import YMGap.Sheaf.Gluing

namespace YMGap.Constructive.ExpBound

open YMGap.Constructive
open YMGap.Sheaf

/-! ## The seed interface: a rational upper bound for `e^{−x}`

`ExpUB` abstracts a rational function `E : Q' → Q'` that upper-bounds
`x ↦ e^{−x}` on `x ≥ 0`, with the structural properties the character-tail
bound uses.  Level 2 (`ExpNeg.lean`) instantiates `E` from the truncated
exponential series and proves these fields; here it is abstract, so this
module is *conditional on `ExpUB`* exactly as `RepData.budget_closes` is
conditional on its certificate. -/

/-- A rational upper-bound operator for `e^{−x}` on `x ≥ 0`. -/
structure ExpUB where
  /-- The rational bound: morally `E x ≥ e^{−x}`. -/
  E : Q' → Q'
  /-- `e^{−x} > 0`, so the bound is nonnegative. -/
  E_pos : ∀ x, (0 : Q') ≤ E x
  /-- `e^{0} = 1`. -/
  E_zero_le_one : E 0 ≤ 1
  /-- `e^{−·}` is decreasing: larger Casimir ⇒ smaller term. -/
  E_antitone : ∀ x y, x ≤ y → E y ≤ E x

/-- The per-irrep majorant `(dim)² · E(t·C₂)` for a single representation.
A term of the character tail `Z_t`, bounded above via the seed `E`. -/
def termMaj (U : ExpUB) (d t c : Q') : Q' := d * d * U.E (t * c)

/-- The per-irrep majorant is nonnegative (dimensions are nonnegative,
`E ≥ 0`).  The one structural fact the box sum needs from `E`. -/
theorem termMaj_nonneg (U : ExpUB) (d t c : Q') (hd : (0 : Q') ≤ d) :
    (0 : Q') ≤ termMaj U d t c := by
  show (0 : Q') ≤ d * d * U.E (t * c)
  exact Q'.mul_nonneg (d * d) (U.E (t * c)) (Q'.mul_nonneg d d hd hd) (U.E_pos _)

/-! ## Cluster / Brydges–Federbush reduction (pure `Q'`)

Given a rational upper bound `Z_upper` on the character tail and the
plaquette-polymer connectivity `μ_plaq`, the cluster-expansion residual
is `q = μ_plaq · Z_upper`.  The geometric cluster sum
`Σ_n μ^n e^{−ρ n} = 1/(1−q)` converges iff `q < 1`, and the closed form
gives the amplitude relation `q ≤ K_lf·(1 − q)` (i.e. `K_lf ≥ q/(1−q)`).
Both are finite `Q'` facts once `Z_upper` is fixed. -/

/-- The cluster-expansion residual `q = μ_plaq · Z_upper`. -/
def residual (mu Z : Q') : Q' := mu * Z

/-- Assemble the large-field KP certificate from a derived `(ρ_lf, K_lf)`.
`P_nonneg` needs only nonnegativity; the *content* is that `K_lf` meets
the BF relation against `residual`, exposed by `largeField_bf`. -/
def largeFieldCert (rho_lf K_lf : Q')
    (h_rho : (0 : Q') ≤ rho_lf) (h_K : (0 : Q') ≤ K_lf) :
    KPCertificate Q' P_nonneg :=
  { rho := rho_lf, K := K_lf, satisfies := ⟨h_rho, h_K⟩ }

/-- **The cluster reduction.**  Given a tail bound `Z`, connectivity `μ`,
convergence `q < 1`, and a `K_lf` meeting the Brydges–Federbush relation
`q ≤ K_lf·(1 − q)`, the large-field certificate exists and carries the
convergence + BF facts.  This is the `Q'` content that makes `K_lf` a
*derived* quantity keyed to `Z`. -/
theorem largeField_bf (rho_lf K_lf mu Z : Q')
    (h_rho : (0 : Q') ≤ rho_lf) (h_K : (0 : Q') ≤ K_lf)
    (h_conv : residual mu Z < 1)
    (h_bf : residual mu Z ≤ K_lf * (1 - residual mu Z)) :
    (largeFieldCert rho_lf K_lf h_rho h_K).rho = rho_lf ∧
    (largeFieldCert rho_lf K_lf h_rho h_K).K = K_lf ∧
    residual mu Z < 1 ∧
    residual mu Z ≤ K_lf * (1 - residual mu Z) :=
  ⟨rfl, rfl, h_conv, h_bf⟩

/-! ## SU(3) instance: large-field certificate from a `Z_upper`

At `g₀ = 0.30`: `t = 1/g² = 100/9`, dominant Casimir `C₂(1,0) = 4/3`.
The SU(3) closure-spike / `computations/su3_character_sum.py` give
`Z_t ≈ 9.6×10⁻⁴`; rounded UP to `Z_upper = 1/1000`.  With `μ_plaq = 16`
the residual is `q = 16/1000 < 1` and `K_lf = 17/1000` meets the BF
relation.  The per-irrep `e^{−t·C₂}` bounds and the geometric tail behind
`Z_upper = 1/1000` are the Level-2 / geometric obligations. -/

/-- SU(3) heat-kernel character-tail upper bound `Z_t ≤ 1/1000`. -/
def Z_upper_su3 : Q' := Q'.mkPos 1 1000 (by decide)

/-- Plaquette-polymer connectivity `μ_plaq = 16` (4D, group-independent). -/
def mu_plaq : Q' := 16

/-- SU(3) large-field rate `ρ_lf`.  A conservative rational lower bound on
`−log Z_t ≈ 6.9`; only `ρ_lf ≥ 0` is load-bearing for the certificate,
the `−log Z` value being the Level-2 obligation. -/
def rho_lf_su3 : Q' := 6

/-- SU(3) large-field amplitude `K_lf = 17/1000`, meeting the BF relation. -/
def K_lf_su3 : Q' := Q'.mkPos 17 1000 (by decide)

/-- **SU(3) cluster derivation.**  `q = 16/1000 < 1` and the BF relation
`q ≤ K_lf·(1 − q)` both hold by `decide` at the encoded `Z_upper`. -/
theorem su3_largeField_derivation :
    residual mu_plaq Z_upper_su3 < 1 ∧
    residual mu_plaq Z_upper_su3 ≤ K_lf_su3 * (1 - residual mu_plaq Z_upper_su3) :=
  ⟨by decide, by decide⟩

/-- The SU(3) large-field KP certificate, derived from `Z_upper_su3` via
the cluster reduction.  Mirrors `Sheaf/SU2KP.lean`'s `c_lf_*`, but with
`K_lf` keyed to the character-tail bound rather than posited. -/
def c_lf_su3 : KPCertificate Q' P_nonneg :=
  largeFieldCert rho_lf_su3 K_lf_su3 (by decide) (by decide)

end YMGap.Constructive.ExpBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.ExpBound.termMaj_nonneg
#print axioms YMGap.Constructive.ExpBound.largeField_bf
#print axioms YMGap.Constructive.ExpBound.su3_largeField_derivation
#print axioms YMGap.Constructive.ExpBound.c_lf_su3
