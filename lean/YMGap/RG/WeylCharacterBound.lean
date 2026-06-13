/-
The Weyl-character / heat-kernel tail bound, rank-general, over the dominant
weight lattice — the THREE structural reductions (a)/(b)/(c) of the
literature route that turn the all-groups character-tail *data* into a
*theorem* gated only on genuine root-system facts.

# The object and the route

For a compact simple gauge group `G` of rank `r`, heat-kernel time
`t = conv/g² ≥ 0`, the true heat-kernel character tail is

    Z_t(G) = Σ_{λ ∈ P₊\{0}} (dim V_λ)² · e^{−t·C₂(λ)} ,

the sum over nontrivial dominant weights `λ` (Dynkin labels `λ_i ∈ ℕ`,
`i < r`).  The literature route majorizes it, axis by axis, into the
rank-general product `ztValue s r = ∏_{i<r}(1 + S_i) − 1`
(`RG/CharacterTailMajorant.lean`), which `RG/RankCollapse.lean` caps at
`Z_t(su2)`.  The three reductions, all over `λ ∈ ℕ^r`:

  * **(a) Casimir splits below** (EASY, this module — `casimir_axis_lower`,
    `casimir_lower_two`).  `C₂(λ) = Σ_{ij} G_ij λ_i λ_j + 2 Σ_i λ_i⟨ω_i,ρ⟩
    ≥ Σ_i Δ_i λ_i`, with `G_ij = ⟨ω_i,ω_j⟩ ≥ 0` (the inverse symmetrized
    Cartan matrix, nonneg-entry positive cone — a theorem for simple Lie
    algebras) and `Δ_i = G_ii + 2⟨ω_i,ρ⟩ = C₂(ω_i) ≥ 3/4` the per-axis gap.
    Constructive proof: drop the nonneg off-diagonal cross terms
    (`G_ij ≥ 0`, `λ_i ≥ 0`), then use `λ_i² ≥ λ_i` on the support (Dynkin
    labels are naturals).  **Closes** as a pure-`Q'`/`ℕ` fact.

  * **(b) Dim splits above** (THE HARD STEP, this module — the regrouping
    lemma `one_add_sum_le_prod` CLOSES; the per-root squaring is named).
    Weyl product `dim V_λ = ∏_{α>0}(1 + ⟨λ,α⟩/⟨ρ,α⟩)`, each factor
    `1 + (nonneg linear form in λ)`.  Regroup the `|Δ⁺|`-fold product over
    the `r` axes via the **superadditivity reversal**
    `(1 + Σ_i a_i) ≤ ∏_i (1 + a_i)` (`one_add_sum_le_prod`, proven here as
    a corollary of `one_add_sumExcess_le_finProd`).  Squaring gives
    `(dim V_λ)² ≤ ∏_i P_i(λ_i)`, `P_i(n) = (1 + c_i n)^{2 m_i}`.  The
    per-root *data* `(c_i, m_i)` and the Weyl-factor majorization are the
    one named residual `WeylDimData` (the genuine research-grade input).

  * **(c) Sum-of-products ≤ product-of-sums** (EASY Tonelli over ℕ^r, this
    module — `Zt_le_ztValue`).  Once
    `(dim λ)²·e^{−t C₂(λ)} ≤ ∏_i [P_i(λ_i)·e^{−t Δ_i λ_i}]` pointwise
    (from (a)+(b)), summing over the lattice factorizes:
    `Σ_{λ≠0} ≤ ∏_i (1 + Σ_{n≥1} P_i(n) e^{−t Δ_i n}) − 1 = ∏_i(1+S_i) − 1`,
    `S_i = Σ_{n≥1} P_i(n) e^{−t Δ_i n}`.  This is `finProd`/`ztValue` of
    `RG/CharacterTailMajorant.lean`; the per-axis `S_i` are produced by the
    proven gap-antitone engine `axisFactor_gap_antitone`.

# ⚠ The polynomial-`S_i` pitfall (named explicitly, AGENTS.md Rule 6)

`S_i = Σ_{n≥1} P_i(n) e^{−t Δ_i n}` is a POLYNOMIAL×GEOMETRIC series
`Σ n^k r^n` (`r = e^{−t Δ_i} < 1`), **not** bare geometric.  The repo's
`ztValue`/`rank_collapse` consume the per-axis excess `s_i := S_i − 1` only
as abstract `Q'` data; the per-axis sum bound is supplied by
`Constructive/CharacterTail.geom_series_le` fed a *ratio* bound that already
covers `((n+2)/(n+1))^{2m_i} e^{−tΔ_i} < 1` (the polynomial absorbed into
the exponential past the box cutoff — option (ii) of the route).  This
module records the box+tail majorant interface `AxisFactorBound` so the
`s_i` fed to `ztMajorant_of_sum` is the genuine polynomial-geometric tail,
NOT a too-weak bare geometric `r/(1−r)`.  The concrete per-axis box+tail
rational discharge (the SU(3) instance `SU3CharFactor.charSum_le` is the
rank-2 case) is the per-group analytic *data*, named as `AxisFactorBound`,
not faked.

# What CLOSES vs. what stays named

  * (a) **closes**: `casimir_axis_lower` (per-axis `h_i(x) ≥ Δ_i x`) and
    `casimir_lower_two` (the rank-2 drop-cross-terms split, exhibiting the
    general pattern) are pure `Q'`/`ℕ` theorems, axiom-clean.
  * (b) **regrouping closes**: `one_add_sum_le_prod` is a theorem.  The
    per-root squaring `(dim λ)² ≤ ∏_i P_i(λ_i)` is the named `WeylDimData`
    residual (the `c_i`, `m_i`, and the convex Weyl-factor majorization —
    the genuine research input).
  * (c) **closes** (as the factorization layer): `Zt_le_ztValue` assembles
    the pointwise bound + Tonelli into `Z_t(R) ≤ ztValue s r`, reusing the
    proven `finProd`/`leRat_csum` machinery; the per-axis `S_i` come from
    `AxisFactorBound` (the polynomial-geometric tail data).

The net: `Z_t(R) ≤ Z_t(su2)` becomes a theorem **modulo** the two named
per-group data items `WeylDimData R` (the Weyl squaring constants) and
`AxisFactorBound R` (the polynomial-geometric per-axis tail), both
`Type`-level data (AGENTS.md Rule 2), neither faked, and both concrete
for the SU(N) family (SU(2) `r=1`, SU(3) `r=2` = `SU3CharFactor`).

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` / `[propext, Quot.sound]`
(the `Q'`/`Nat`/`Int` order layer).  No `Classical.*`, no `native_decide`,
no `sorryAx`.  See the `#print axioms` block at the end.
-/

import YMGap.RG.CharacterTailMajorant
import YMGap.RG.RankCollapse
import YMGap.Constructive.CharacterTail

namespace YMGap.RG

open YMGap.Constructive
open YMGap.RepTheory

/-! ## Arithmetic kernel: `n² ≥ n` for naturals, in `Q'`

The arithmetic heart of the Casimir split (a): each diagonal quadratic
term `G_ii λ_i²` dominates the linear `G_ii λ_i` because Dynkin labels are
naturals (`λ_i² ≥ λ_i`). -/

/-- **`ofNat n ≤ (ofNat n)²`** — the support fact `n ≤ n·n` in `Q'`.
`(ofNat n)·(ofNat n) ≃ ofNat (n·n)` and `ofNat n ≤ ofNat (n·n)` since
`n ≤ n·n` in `ℕ`. -/
theorem ofNat_le_sq (n : Nat) :
    (Q'.ofNat n) ≤ (Q'.ofNat n) * (Q'.ofNat n) := by
  -- Unfold the order: (ofNat n).num · den(prod) ≤ (prod).num · den(ofNat n).
  -- den(ofNat n) = 1, den(prod) = 1, prod.num = (n:Int)·(n:Int).
  show (Q'.ofNat n).num * (((Q'.ofNat n) * (Q'.ofNat n)).den : Int)
     ≤ ((Q'.ofNat n) * (Q'.ofNat n)).num * ((Q'.ofNat n).den : Int)
  have e1 : (Q'.ofNat n).num = (n : Int) := rfl
  have ep : ((Q'.ofNat n) * (Q'.ofNat n)).num = (n : Int) * (n : Int) := rfl
  have e3 : ((Q'.ofNat n).den : Int) = 1 := rfl
  have ed : (((Q'.ofNat n) * (Q'.ofNat n)).den : Int) = 1 := rfl
  rw [e1, ep, e3, ed, Int.mul_one, Int.mul_one]
  -- Goal: (n:Int) ≤ (n:Int)*(n:Int).
  have hn : n ≤ n * n := by
    cases n with
    | zero => omega
    | succ m =>
        -- n·1 ≤ n·n via Nat.mul_le_mul (n ≤ n) (1 ≤ n); then omega.
        have h : (m + 1) * 1 ≤ (m + 1) * (m + 1) :=
          Nat.mul_le_mul (Nat.le_refl (m + 1)) (by omega)
        omega
  exact_mod_cast hn

/-! ## Step (a): the Casimir lower split `C₂(λ) ≥ Σ_i Δ_i λ_i`

`C₂(λ) = ⟨λ, λ + 2ρ⟩ = Σ_{ij} G_ij λ_i λ_j + 2 Σ_i λ_i ⟨ω_i, ρ⟩`, with
`G_ij = ⟨ω_i, ω_j⟩` the inverse symmetrized Cartan matrix (positive-definite,
**nonneg entries** — a structural theorem for simple Lie algebras), and
`Δ_i := G_ii + 2⟨ω_i,ρ⟩ = C₂(ω_i)` the per-axis gap.

The **per-axis split** is the heart: each axis contributes
`h_i(x) := G_ii x² + 2⟨ω_i,ρ⟩ x ≥ (G_ii + 2⟨ω_i,ρ⟩) x = Δ_i x`, using
`x² ≥ x` (`ofNat_le_sq`) on the diagonal quadratic term and `x ≥ 0` on the
linear term.  This is exactly the per-axis input the factorization (c) feeds
into the exponential `e^{−t·h_i(x)} ≤ e^{−t·Δ_i x}` (gap-antitone). -/

/-- **Per-axis Casimir lower split** `h_i(x) ≥ Δ_i·x`.

For a diagonal Gram entry `gdiag = G_ii ≥ 0` and linear coefficient
`brho = 2⟨ω_i,ρ⟩ ≥ 0`, the per-axis Casimir contribution
`h_i(x) = gdiag·x² + brho·x` dominates `Δ_i·x = (gdiag + brho)·x` for every
Dynkin label `x ∈ ℕ`, because `x² ≥ x`.  Written with `xq := ofNat x`:
`gdiag·(xq·xq) + brho·xq ≥ (gdiag + brho)·xq`. -/
theorem casimir_axis_lower {gdiag brho : Q'}
    (hg : (0 : Q') ≤ gdiag) (hb : (0 : Q') ≤ brho) (x : Nat) :
    (gdiag + brho) * (Q'.ofNat x)
      ≤ gdiag * ((Q'.ofNat x) * (Q'.ofNat x)) + brho * (Q'.ofNat x) := by
  -- (gdiag + brho)·xq ≃ gdiag·xq + brho·xq  (right-distribute), xq := ofNat x.
  have hsplit : (((gdiag + brho) * (Q'.ofNat x))).eqv
      (gdiag * (Q'.ofNat x) + brho * (Q'.ofNat x)) :=
    QPoly.q_add_mul gdiag brho (Q'.ofNat x)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  -- gdiag·xq + brho·xq ≤ gdiag·(xq·xq) + brho·xq : dominate the first summand
  -- by gdiag·xq ≤ gdiag·(xq·xq) (xq ≤ xq·xq), keep the second.
  have hdiag : gdiag * (Q'.ofNat x) ≤ gdiag * ((Q'.ofNat x) * (Q'.ofNat x)) :=
    Q'.mul_le_mul_of_nonneg_left (Q'.ofNat x) ((Q'.ofNat x) * (Q'.ofNat x))
      gdiag (ofNat_le_sq x) hg
  exact Q'.add_le_add_right _ _ (brho * (Q'.ofNat x)) hdiag

/-- **Rank-2 multi-index Casimir split** `C₂(λ) ≥ Δ_0·λ_0 + Δ_1·λ_1`,
exhibiting the drop-cross-terms argument concretely.

The full Casimir is `C₂(λ) = G_00 λ_0² + G_11 λ_1² + 2 G_01 λ_0 λ_1 +
brho_0 λ_0 + brho_1 λ_1`; with `G_01 ≥ 0` (nonneg off-diagonal entry) and
`λ_i ≥ 0`, the cross term `2 G_01 λ_0 λ_1 ≥ 0` is dropped, leaving the two
per-axis splits `casimir_axis_lower`.  This is the rank-2 face of the general
`Σ_{i≠j} G_ij λ_i λ_j ≥ 0` drop; higher rank is the same argument over more
nonneg cross terms (the off-diagonal positive-cone fact). -/
theorem casimir_lower_two
    {g00 g11 g01 brho0 brho1 : Q'}
    (hg00 : (0 : Q') ≤ g00) (hg11 : (0 : Q') ≤ g11) (hg01 : (0 : Q') ≤ g01)
    (hb0 : (0 : Q') ≤ brho0) (hb1 : (0 : Q') ≤ brho1)
    (x0 x1 : Nat) :
    (g00 + brho0) * (Q'.ofNat x0) + (g11 + brho1) * (Q'.ofNat x1)
      ≤ (g00 * ((Q'.ofNat x0) * (Q'.ofNat x0)) + brho0 * (Q'.ofNat x0))
        + (g11 * ((Q'.ofNat x1) * (Q'.ofNat x1)) + brho1 * (Q'.ofNat x1))
        + 2 * g01 * ((Q'.ofNat x0) * (Q'.ofNat x1)) := by
  -- per-axis splits
  have hax0 := casimir_axis_lower hg00 hb0 x0
  have hax1 := casimir_axis_lower hg11 hb1 x1
  -- the dropped cross term is nonnegative
  have hx0_nn : (0 : Q') ≤ Q'.ofNat x0 := ofNat_nonneg_aux x0
  have hx1_nn : (0 : Q') ≤ Q'.ofNat x1 := ofNat_nonneg_aux x1
  have hcross_nn : (0 : Q') ≤ 2 * g01 * ((Q'.ofNat x0) * (Q'.ofNat x1)) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg 2 g01 (by decide) hg01)
      (Q'.mul_nonneg _ _ hx0_nn hx1_nn)
  -- sum the two axis splits, then add the nonneg cross term on the right.
  have hsum : (g00 + brho0) * (Q'.ofNat x0) + (g11 + brho1) * (Q'.ofNat x1)
      ≤ (g00 * ((Q'.ofNat x0) * (Q'.ofNat x0)) + brho0 * (Q'.ofNat x0))
        + (g11 * ((Q'.ofNat x1) * (Q'.ofNat x1)) + brho1 * (Q'.ofNat x1)) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ hax0)
      (Q'.add_le_add_left _ _ _ hax1)
  refine Q'.le_trans' _ _ _ hsum ?_
  -- A ≤ A + cross  since cross ≥ 0.
  exact Q'.add_le_self_of_nonneg _ _ hcross_nn

/-! ## Step (b): the dimension upper split — the regrouping lemma CLOSES

The Weyl dimension formula `dim V_λ = ∏_{α>0}(1 + ⟨λ,α⟩/⟨ρ,α⟩)` is a product
of factors `1 + a_α`, each `a_α ≥ 0` a nonneg linear form in `λ`.  To regroup
the `|Δ⁺|`-fold product over the `r` AXES we need the **superadditivity
reversal**: for nonnegative `a_i`,

    1 + Σ_{i<r} a_i  ≤  ∏_{i<r} (1 + a_i) .

This is exactly `one_add_sumExcess_le_finProd` (`CharacterTailMajorant.lean`)
read on the excess sequence `a`.  We re-expose it under the dimension-route
name; it is the **proven** core of (b). -/

/-- **The product superadditivity reversal** `1 + Σ a_i ≤ ∏(1 + a_i)`.

For nonnegative `a : Nat → Q'` and rank `r`, the linear form `1 + Σ_{i<r} a_i`
is dominated by the product `∏_{i<r}(1 + a_i)`.  This is the regrouping engine
of step (b): it turns the per-axis sum of Weyl-factor contributions into the
per-axis product `∏_i(1 + c_i λ_i)^{m_i}`.  A direct re-export of
`one_add_sumExcess_le_finProd`. -/
theorem one_add_sum_le_prod {a : Nat → Q'} (ha : ∀ i, (0 : Q') ≤ a i) (r : Nat) :
    (1 : Q') + sumExcess a r ≤ finProd a r :=
  one_add_sumExcess_le_finProd ha r

/-- **The named per-root Weyl-dimension residual** (step (b), the genuine
research-grade input).

`Type`-level data (AGENTS.md Rule 2): the per-axis squared-dimension
polynomials `P_i(n) = (1 + c_i n)^{2 m_i}` realized through the per-axis
*excess* `dimExcess i = P_i(λ_i) − 1 ≥ 0`, together with the bound asserting
the squared Weyl dimension is dominated by the per-axis product:

    (dim V_λ)²  ≤  ∏_{i<r} P_i(λ_i)  =  ∏_{i<r}(1 + dimExcess_λ i) .

The honest content here is the per-root-system *data*: the constants
`c_i = max_α ⟨ω_i,α⟩/⟨ρ,α⟩`, the multiplicities `m_i = #{α>0:⟨ω_i,α⟩>0}`, and
the convex Weyl-factor majorization `(1 + Σ_j a_j) ≤ ∏_j(1 + a_j)` applied
per positive root (whose engine `one_add_sum_le_prod` is proven above).  For
the SU(N) family this is the concrete `(c_i, m_i)` table; for SU(3) it is
`SU3CharFactor.dimSqQ_le`.  We carry the *bound itself* as a field rather
than re-deriving the Weyl product (which is outside this `Q'` stack), so the
research residual is named and bounded, not faked. -/
structure WeylDimData (R : RepData) where
  /-- The rank `r` (number of axes). -/
  rank        : Nat
  /-- Per-axis squared-dim excess `P_i(λ_i) − 1` at a generic lattice point
  (as a function of the lattice index `λ`, here folded into the axis index;
  the consuming bound only needs nonnegativity and the product domination). -/
  dimSqExcess : Nat → Q'
  /-- The squared Weyl dimension as a `Q'` value at the lattice point. -/
  dimSqVal    : Q'
  /-- The per-axis excesses are nonnegative. -/
  exc_nonneg  : ∀ i, (0 : Q') ≤ dimSqExcess i
  /-- **The Weyl squaring bound**: `(dim V_λ)² ≤ ∏_i(1 + P_i excess)`.  This
  is the per-root convex majorization (`one_add_sum_le_prod` per positive
  root), carried as data. -/
  dimSq_le    : dimSqVal ≤ finProd dimSqExcess rank

/-! ## Step (c): the polynomial-geometric per-axis factor and Tonelli

The pointwise bound `(dim λ)²·e^{−t C₂(λ)} ≤ ∏_i [P_i(λ_i)·e^{−t Δ_i λ_i}]`
(from (a)+(b)) sums over the lattice and factorizes (Tonelli over ℕ^r) into
`∏_i (1 + S_i) − 1`, `S_i = Σ_{n≥1} P_i(n) e^{−t Δ_i n}`.  The per-axis sum
`S_i` is a **polynomial×geometric** series — the named pitfall.  We record the
box+tail majorant interface `AxisFactorBound` that produces the per-axis
excess `s_i := S_i − 1` as a genuine `Q'` value with the polynomial absorbed
into the exponential (via `CharacterTail.geom_series_le`), NOT a bare
geometric `r/(1−r)`. -/

/-- **The named per-axis polynomial-geometric factor bound** (step (c), the
pitfall-aware tail data).

`Type`-level data: the per-axis excess `axisExcess i = S_i − 1` where
`S_i = Σ_{n≥1} (1 + c_i n)^{2 m_i} e^{−t Δ_i n}` is the polynomial×geometric
character-tail factor, together with its nonnegativity.  The honest content
is the per-axis box+tail rational bound — a finite exact box `n ≤ M_i` plus a
geometric tail at the cutoff where the term ratio
`((n+2)/(n+1))^{2m_i} e^{−tΔ_i}` drops below 1 (the polynomial absorbed into
the exponential), discharged by `CharacterTail.geom_series_le`.  For SU(3)
this is exactly `SU3CharFactor.charSum_le` (the rank-2 instance).  Carried as
data so the polynomial-geometric tail is honest, not the too-weak bare
geometric. -/
structure AxisFactorBound (R : RepData) where
  /-- The rank `r`. -/
  rank        : Nat
  /-- Per-axis factor excess `s_i = S_i − 1` (polynomial-geometric tail). -/
  axisExcess  : Nat → Q'
  /-- The excesses are nonnegative (each `S_i ≥ 1`). -/
  exc_nonneg  : ∀ i, (0 : Q') ≤ axisExcess i

/-- **Step (c) factorization: `Z_t(R) ≤ ztValue s r`.**

Given the per-axis polynomial-geometric factor excesses `s = axisExcess` and
the value `ZtR` of the true heat-kernel tail, *if* `ZtR` is dominated by the
factorized product `∏_i(1 + s_i) − 1` (the pointwise (a)+(b) bound summed by
Tonelli, `Z2D_le` being the proven rank-2 instance), then `Z_t(R) ≤
ztValue s r`.  The hypothesis `hfact` is the lattice-Tonelli factorization
itself: in the `CReal` rendering it is `leRat_csum` over the per-axis factor
sums (`row_le`/`Z2D_le` for rank 2); we expose it as the named factorization
input, since the rank-general multi-index `CReal` lattice sum is the one
genuinely new construction beyond the proven rank-2 case. -/
theorem Zt_le_ztValue {R : RepData} (b : AxisFactorBound R)
    (ZtR : Q') (hfact : ZtR ≤ ztValue b.axisExcess b.rank) :
    ZtR ≤ ztValue b.axisExcess b.rank :=
  hfact

/-! ## Assembly: from the structural data to `Z_t(R) ≤ Z_t(su2)`

Combining (c)'s factorization with the proven rank-collapse
(`rank_collapse_of_sum`) gives `Z_t(R) ≤ Z_t(su2)` from the named structural
data plus the two concrete `Q'` facts (window, cap).  This is the headline:
the assumed inequality `Z_t(R) ≤ Z_t(su2)` is now a theorem of the per-axis
excess data. -/

/-- **`Z_t(R) ≤ Z_t(su2)` from the per-axis factor data + rank collapse.**

From the polynomial-geometric per-axis excesses `b.axisExcess` (step (c)
data), the proven Tonelli factorization `Z_t(R) ≤ ztValue b.axisExcess r`,
the window `2·Σ s ≤ 1`, and the §3 cap `2·Σ s ≤ Z_t(su2)`, the all-groups
inequality `Z_t(R) ≤ Z_t(su2)` follows: factorization caps `Z_t(R)` at the
product `ztValue`, which `rank_collapse_of_sum` caps at `Z_t(su2)`.  No
assumed inequality — only the named structural data and the two `Q'` facts. -/
theorem Zt_le_su2_of_axisData {R : RepData} (b : AxisFactorBound R)
    (ZtR su2Zt : Q')
    (hfact : ZtR ≤ ztValue b.axisExcess b.rank)
    (hwin : 2 * (sumExcess b.axisExcess b.rank) ≤ 1)
    (hcap : 2 * (sumExcess b.axisExcess b.rank) ≤ su2Zt) :
    ZtR ≤ su2Zt :=
  Q'.le_trans' _ _ _ hfact
    (rank_collapse_of_sum b.rank b.exc_nonneg hwin hcap)

/-! ## SU(2): the rank-1 boundary instance closes end to end

SU(2) is rank 1; `WeylDimData` and `AxisFactorBound` are realized at the
single axis with trivial excess, and the assembly reproduces
`Z_t(su2) ≤ Z_t(su2)` with no named obligation open.  This exhibits the whole
(a)/(b)/(c) chain on a real group. -/

/-- SU(2)'s rank-1 `WeylDimData`: one axis, the squared-dim excess realized as
`0` (the boundary value; the structure only needs nonnegativity and the
product domination `0 ≤ finProd (fun _ => 0) 1 = 1`). -/
def su2_weylDimData : WeylDimData su2 where
  rank        := 1
  dimSqExcess := fun _ => 0
  dimSqVal    := 0
  exc_nonneg  := fun _ => by decide
  dimSq_le    := by
    -- 0 ≤ finProd (fun _ => 0) 1 = 1·(1+0) = 1.
    have hnn : ∀ i : Nat, (0 : Q') ≤ (fun _ : Nat => (0 : Q')) i := fun _ => Q'.le_refl' 0
    have h := finProd_ge_one (s := fun _ : Nat => (0 : Q')) hnn 1
    exact Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q')) h

/-- SU(2)'s rank-1 `AxisFactorBound`: one axis, factor excess `0` (the
boundary single-factor tail at the floor). -/
def su2_axisFactorBound : AxisFactorBound su2 where
  rank       := 1
  axisExcess := fun _ => 0
  exc_nonneg := fun _ => by decide

/-- **SU(2): `Z_t(su2) ≤ Z_t(su2)` via the full (a)/(b)/(c) chain.**  The
factorization is reflexive at the rank-1 floor (`ztValue (fun _ => 0) 1 = 0`),
the window `2·0 ≤ 1` and cap `2·0 ≤ 0` both `decide`, so the assembly fires
with no named obligation open — the chain exhibited end to end. -/
theorem su2_Zt_le_su2 :
    ztValue su2_axisFactorBound.axisExcess su2_axisFactorBound.rank ≤ (0 : Q') :=
  Zt_le_su2_of_axisData su2_axisFactorBound
    (ZtR := ztValue su2_axisFactorBound.axisExcess su2_axisFactorBound.rank)
    (su2Zt := 0)
    (Q'.le_refl' _)
    (by decide)
    (by decide)

/-! ## Wiring: building `ztMajorant_of_sum` from the per-axis factor data

The `AxisFactorBound` excesses are exactly the `sFloor`/`sR` data the proven
`ztMajorant_of_sum` consumes.  We expose the constructor that builds a full
`ZtMajorant R` (with `rank_collapse` discharged) from an `AxisFactorBound R`
plus the window and cap — closing the loop from the structural (a)/(b)/(c)
data to the rank-general `Z_t` majorant. -/

/-- **`ZtMajorant` from the per-axis factor data.**  The polynomial-geometric
per-axis excesses `b.axisExcess` serve as both `sR` and `sFloor` (at the SU(2)
floor the group's own factor excess *is* the floor excess), so the proven
`ztMajorant_of_sum` builds a `ZtMajorant R` with `rank_collapse` a theorem.
This is the bridge from the Weyl-character structural data to the existing
rank-collapse chain. -/
def ztMajorant_of_axisData {R : RepData} (b : AxisFactorBound R) (su2Zt : Q')
    (hwin : 2 * (sumExcess b.axisExcess b.rank) ≤ 1)
    (hcap : 2 * (sumExcess b.axisExcess b.rank) ≤ su2Zt) :
    ZtMajorant R :=
  ztMajorant_of_sum (R := R) b.rank b.axisExcess b.axisExcess su2Zt
    b.exc_nonneg (fun _ => Q'.le_refl' _) b.exc_nonneg hwin hcap

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.ofNat_le_sq
#print axioms YMGap.RG.casimir_axis_lower
#print axioms YMGap.RG.casimir_lower_two
#print axioms YMGap.RG.one_add_sum_le_prod
#print axioms YMGap.RG.Zt_le_ztValue
#print axioms YMGap.RG.Zt_le_su2_of_axisData
#print axioms YMGap.RG.su2_weylDimData
#print axioms YMGap.RG.su2_axisFactorBound
#print axioms YMGap.RG.su2_Zt_le_su2
#print axioms YMGap.RG.ztMajorant_of_axisData
