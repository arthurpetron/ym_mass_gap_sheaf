# Uniform Parametric σ̂-Budget Bound — Plan to Takeoff

Authoritative plan for closing the one load-bearing open step in the
"mass gap for *any* compact simple gauge group" program: replacing the
**per-group, pointwise-`decide`d** `ClosureCertificate.budget` with an
**unconditional bound that holds uniformly over the invariant range of
all compact simple groups**.

Status of record (entering this plan):

- SU(2) σ̂-budget closure: **proven, axiom-clean** (`su2_budget_closes`,
  `mass_gap_SU2`).
- Group-uniform *interface*: **done** — `RepData` parametrizes the
  closure by scalar invariants `(C₂_fund, C₂_adj, g², conv, ρ_sf, η_max,
  K, σ̂₀)`; `RepData.budget_closes` is the conditional closure.
- SU(3) instance + certificate: **done** at one operating point
  (`su3_cert`, `decide`).
- **Open (this plan):** prove `cert.budget` *parametrically*, uniformly
  over the admissible invariant range, so no per-group `decide` is
  needed and the result covers all simple groups at once.

This plan does **not** change the formal/paper boundary inherited from
SU(2): OS reconstruction, the cluster→gap bridge, and the √-bridge O(1)
constant remain paper-level interface Props (`Continuum/OSAxioms.lean`,
`Continuum/OSReconstruction.lean`). "Takeoff" here means **parity with
the SU(2) result, for every simple group simultaneously** — i.e. the
constructive σ̂-budget closure and a `mass_gap_simple_group` theorem at
the same boundary `mass_gap_SU2` sits at today.

---

## 0. The target theorem

The end state is a single Lean theorem, axiom-clean per AGENTS.md Rule 1:

```lean
theorem mass_gap_simple_group
    (R : RepData)
    (hadm : AdmissibleSimpleGroup R)          -- R's invariants are those of *some* compact simple G
    {M : Nat → Type} {μ_inf : ContinuumMeasure M}
    (rec : OSReconstruction μ_inf) (bundle : OSAxiomBundle μ_inf) :
    ∃ m_0 : Q', 0 < m_0 ∧ m_0 * m_0 ≤ R.sigma0 ⊖ totalEta R ∧ HasSpectralGap rec
```

where `totalEta R := finSum (truncatedConst R.K_steps R.eta_max) R.K_steps`
and `⊖` is truncated Q' subtraction. The novelty over `mass_gap_SU2` is
that `hadm` ranges over *all* simple groups and the budget conjunct is
**derived**, not assumed per group.

The whole plan reduces to producing, axiom-clean:

```lean
theorem budget_closes_uniform (R : RepData) (hadm : AdmissibleSimpleGroup R) :
    R.ClosureCertificate
```

Everything downstream (`mass_gap_simple_group`) is the SU(2) assembly
re-run against `R` instead of `su2`.

---

## 1. Strategy: reduce the family to its worst case (SU(2))

The infinite family A_n, B_n, C_n, D_n, G₂, F₄, E₆, E₇, E₈ collapses to a
single inequality because **every budget channel is monotone in the
smallest nonzero quadratic Casimir `Δ := C₂_min` (the spectral gap), and
`Δ` is globally minimized at SU(2).**

### 1.1 Why SU(2) is the worst case

The per-step degradation is `η_k = ½·Δ_∩(g_k, g_{k+1})`, with
`Δ_∩` the increment of `K_∩ = K_sf + K_lf`. Each piece:

| Channel | Formula | Dependence on the Casimir gap Δ | Direction |
|---|---|---|---|
| Small-field | `ρ_sf = C₂_fund/g²`, converges iff `ρ_sf > log(8e)`; `K_sf ↓` as `C₂_fund ↑` | larger `C₂_fund` ⇒ stronger suppression ⇒ smaller `K_sf` | **tailwind** |
| Large-field | `Z_t = Σ_{R≠0} dim(R)²e^{−tC₂(R)}`, `K_lf = q/(1−q)`, `q = μ_plaq·Z_t` | larger gap `Δ` ⇒ faster tail decay ⇒ smaller `Z_t` ⇒ smaller `K_lf` | **tailwind** |
| RG running | `b₀ = (11/3)·C₂_adj`; larger `b₀` ⇒ `g_k` decays faster ⇒ fewer expensive steps | larger `C₂_adj` ⇒ *smaller* Σ η | favorable; **slowest running (smallest h∨) is conservative** |

So decreasing `C₂_fund`, decreasing the gap `Δ`, and decreasing `C₂_adj`
all **increase** the budget. The budget is maximized at the group that
*jointly minimizes* these invariants.

### 1.2 The rep-theory facts that pin the minimum at SU(2)

In the normalization where `C₂_adj = h∨` (dual Coxeter number):

- **Dual Coxeter numbers.** A_n: n+1; B_n: 2n−1; C_n: n+1; D_n: 2n−2;
  G₂: 4; F₄: 9; E₆: 12; E₇: 18; E₈: 30. The minimum over *all* simple
  Lie algebras is `h∨ = 2`, attained only by **A₁ = su(2)**. Hence
  `C₂_adj ≥ 2` for every simple G.
- **Smallest nonzero Casimir.** The smallest fundamental/defining-rep
  Casimir over all simple groups is `C₂ = 3/4`, attained by the spin-½
  of su(2). For every other simple group the smallest nontrivial irrep
  has a strictly larger Casimir gap. Hence `Δ ≥ 3/4` and `C₂_fund ≥ 3/4`,
  with equality only at su(2).

These two facts are the **`AdmissibleSimpleGroup` lower bounds**. They
are finite, decidable inputs (a table for the classical-family formulas
+ nine exceptional constants), provable in Q' by `decide`/explicit
formula — *no analysis*.

### 1.3 The reduction

```
budget_closes_uniform R hadm
  := monotone_budget  (Δ_min = 3/4, h∨_min = 2)  (hadm.gap_lb) (hadm.hvee_lb)
        |> transport along  su2_cert  (already proven)
```

In words: the SU(2) certificate already proves the budget at the
minimizing invariants; the monotonicity lemma says any larger invariants
give a *smaller* budget; therefore the budget closes for every simple G.
**One monotonicity lemma + the existing SU(2) closure ⇒ all groups.**

> ⚠️ Honest caveat. The monotonicity is *physically* robust (the spike
> shows SU(3) closing ~66× tighter than SU(2)), but it is the analytic
> heart of the plan and must be made rigorous, not assumed. §2 is where
> that work lives. If global monotonicity has a non-monotone pocket
> (e.g. the `K_lf = q/(1−q)` nonlinearity near the convergence edge),
> the fallback (§2.4) is a finite cover of the invariant range with a
> per-cell `decide`d bound — still finite, still axiom-clean.

---

## 2. The analytic core (the real mathematics)

The monotonicity claim of §1 rests on three sub-bounds, currently
realized only numerically/pointwise in Python. Each must become a
*rigorous parametric inequality in the invariants*, then port to Q'/CReal.

### 2.1 Small-field monotonicity — `K_sf` non-increasing in `C₂_fund`

Source: `computations/small_field_kp.py`. `ρ_sf = c_λ/g²` with
`c_λ = C₂_fund` (Bałaban/Casimir-gap, already the `balaban` field of the
certificate). Need: `K_sf` (the cluster-expansion constant) is
non-increasing in `ρ_sf`, hence in `C₂_fund`, on the convergent regime
`ρ_sf > log(8e)`. This is the easiest piece — `K_sf` is a decreasing
elementary function of `ρ_sf`; monotonicity is algebraic once the
convergence threshold is met. **Mostly already structured in Lean**
(`Sheaf/SU2KP.lean` `rho_sf_*`, `K_sf_*`).

### 2.2 Large-field monotonicity — the group-uniform character-tail bound

**This is the hard piece.** Source: `computations/su3_character_sum.py`
(SU(3)) and `large_field_kp.py` (SU(2)). Required: a *rigorous upper
bound on `Z_t` valid for an arbitrary simple group*, monotone
non-increasing in the Casimir gap Δ.

The SU(3) bound already has the right shape and ports directly:

1. **Dimension/Casimir factorization.** For SU(3),
   `dim(p,q)² ≤ (p+1)⁴(q+1)⁴` and
   `C₂(p,q) ≥ f(p)+f(q)`, `f(x) = (x²+3x)/3` (drop the cross term).
   So `a(p,q) ≤ g(p)g(q)`, `g(x) = (x+1)⁴ e^{−t f(x)}`.
2. **1-D geometric tail.** ratio `ρ(x) = g(x+1)/g(x) < 1` past a box of
   half-width M ⇒ `Σ_{x>M} g(x) ≤ g(M+1)/(1−ρ(M+1))`.
3. **2-D union bound.** `Σ_{(p,q)∉box} a(p,q) ≤ 2·tail₁D·g_full`.
4. **`Z_t = exact-box-sum + tail`** — a finite Q' computation plus a
   closed-form geometric remainder.

For the **general** simple group the analogue is: irreps labelled by a
dominant-weight lattice of rank `r`, `dim(λ)` a Weyl-dimension product,
`C₂(λ) = ⟨λ, λ+2ρ⟩`. The uniform bound is an `r`-dimensional version of
the same factorized-majorant + geometric-tail argument, with the key
monotone input that **`C₂(λ) ≥ Δ·(height of λ)`** so larger Δ uniformly
accelerates the decay. The deliverable is a paper lemma:

> **Lemma (uniform character-tail).** For every compact simple G with
> Casimir gap `Δ ≥ 3/4` and heat-kernel time `t = conv/g²`,
> `Z_t(G) ≤ Z_t^{su(2)}(Δ=3/4)`, and `Z_t(G)` is non-increasing in Δ.

This is the lemma that, combined with `K_lf = q/(1−q)` monotone in `Z_t`,
gives large-field monotonicity. It is the same `exp`/`sin`-bearing object
that forced the constructive-reals detour; see §3.

### 2.3 The η assembly — `Δ_∩` and the K=3 → ∞ window

`η_k = ½·Δ_∩(g_k,g_{k+1})`, `Δ_∩ = ΔK_sf + ΔK_lf`. With §2.1 + §2.2 the
per-step η_max is monotone in the invariants. The finite window K and the
K→∞ tail are *already handled group-agnostically* by
`constWindow_closes` / `prefix_plus_tail_closure` / the geometric tail
in `GeometricTail.lean` — no new analysis, the same deferred
constructive-limit step as SU(2).

### 2.4 Fallback if monotonicity is not globally clean

Partition the admissible `(C₂_fund, C₂_adj)` rectangle
`[3/4, C_max] × [2, h_max]` into finitely many cells; on each cell bound
η_max by its corner value and `decide` the budget. Since only finitely
many groups have small invariants and the families are eventually
deep in the convergent interior, a coarse cover suffices. This trades
one elegant lemma for a finite (still axiom-clean) case split.

---

## 3. The constructive substrate (Lean port)

What the CReal/Q' layer must gain to express §2 inside Lean. Current
frontier (from `Constructive/`): `expNeg : Q' → CReal` exists with a
sound rational upper bound `expNeg_leRat`; `GeometricTail.geometric_tail_closure`
gives the closed-form geometric remainder; `ExpBound.termMaj`/`largeField_bf`
give the character-majorant + Brydges–Federbush reduction; `ExpBound.ExpUB`
is the abstract `E : Q' → Q'` interface. Missing pieces, in dependency order:

| # | Piece | Where | Notes |
|---|---|---|---|
| S1 | **Instantiate `ExpUB` from `expNeg`** — assemble `E : Q' → Q'` (a rational upper bound for `e^{−x}`) and prove `E_pos`, `E_zero_le_one`, `E_antitone`. | `Constructive/ExpNeg.lean` → `ExpBound.lean` | Unblocks `termMaj` with a *concrete* E. `E_antitone` is the monotone input §2.2 needs. The `leRat` certificate already gives the upper bound; antitonicity needs the bracket facts (currently the listed open work in ExpNeg). |
| S2 | **Finite character-tail bound in Q'** — port §2.2 steps 1–4: a `Q'` `finSum` of `termMaj` over a box + a `geometric_tail_closure` remainder ⇒ `Z_upper : Q'`. | new `Constructive/CharacterTail.lean` | The geometric tail closed form exists; this is assembly. SU(2)/SU(3) recovered as `decide` instances (regression-lock vs Python). |
| S3 | **Monotonicity of `Z_upper` in Δ** — `Δ ≤ Δ' → Z_upper(Δ') ≤ Z_upper(Δ)`. | `CharacterTail.lean` | Follows from `E_antitone` (S1) termwise + `finSum` monotonicity (`RationalTail.finSum_monotone_of_nonneg`, exists). |
| S4 | **`K_lf` and `K_sf` monotone wrappers** — `q = μ·Z_upper`, `K_lf = q/(1−q)` monotone in `Z_upper`; `K_sf` monotone in `ρ_sf`. | `Sheaf/SU2KP.lean` generalized → `Sheaf/KPParametric.lean` | Needs Q' division lemma for `q/(1−q)` (monotone increasing on `[0,1)`). |
| S5 | **`eta_max_param : RepData → Q'`** — the parametric per-step bound from S2–S4, replacing the hardcoded `eta_max` field. | `RepTheory/RepData.lean` | The function the certificate's `budget` is then checked against, *symbolically* not per-instance. |
| S6 | **`monotone_budget`** — `Δ ≤ Δ', h∨ ≤ h∨' → totalEta(Δ',h∨') ≤ totalEta(Δ,h∨)`. | `RepTheory/RepData.lean` | Composes S3+S4 over the K-window. The §1.3 reduction lemma. |

All six must end `#print axioms … = [propext]` (or empty) and be entered
in `SORRY_LEDGER.md`/`AXIOM_AUDIT.md` per Rules 1 & 6. S1's `E_antitone`
is the single most load-bearing constructive obligation; if it resists,
quarantine the analytic content as an explicit hypothesis (the pattern
already used for `domGlue_preserves_KP`'s `P_glue`) and discharge it at
the paper layer — keeping the Lean chain axiom-clean and the analytic
debt *named*.

---

## 4. Milestones

Dependencies in parentheses. ★ = on the critical path. (P) = paper-level
analytic obligation; (L) = Lean.

### Pillar A — Analytic (paper)

- **U.1 — Casimir-invariant table & lower bounds** (P). Record `C₂_fund`,
  `C₂_adj = h∨`, and the smallest nonzero Casimir Δ for A/B/C/D + the 5
  exceptionals; prove `Δ ≥ 3/4`, `h∨ ≥ 2`, minima only at su(2). Largely
  a literature table + two min arguments. Feeds `AdmissibleSimpleGroup`.
- **★ U.2 — Uniform character-tail lemma** (P, U.1). **Core established
  2026-06-07.** Derivation + verified implementation in
  `computations/general_character_sum.py`; writeup in
  `notes/uniform-character-tail-bound.md`. The rigorous majorant
  `Z_t(G) ≤ ∏_i S_i(t) − 1` (Casimir splits below via the nonnegative
  off-diagonal Gram entries; dimension splits above via the Weyl-factor
  convexity; each `S_i` = exact box + geometric tail) **specializes
  verbatim to `su3_character_sum.py`** for SU(3). Validated: it dominates
  the engine's exact `Z_t` for all 19 groups, and **`Z_upper(G) ≤
  Z_upper(SU(2))` for every group on the operating window** `t ≥ t₀≈6.25`
  (`g ≤ 0.40`), which the canonical trajectory (`g₀=0.30`, RG flow only
  raises `t`) stays inside. *Remaining*: tighten `t₀` (sharper dimension
  bound), the written product-≤-sum proof for `formal-suN/`, and the Lean
  port (U.6). The earlier "non-increasing in Δ" framing is superseded by
  the stronger **direct domination by SU(2)** (the loose majorant is not
  Δ-monotone — G₂ slightly exceeds A₃ — but is uniformly ≤ SU(2)).
- **U.3 — Small/large-field & η monotonicity** (P, U.2). §2.1+§2.3:
  assemble `η_max(C₂_fund, C₂_adj, g₀)` monotone non-increasing in both
  invariants on the admissible range; state the worst-case reduction.
- **U.4 — Numerical corroboration sweep** (computations). **DONE
  2026-06-07 — STRONG GO.** `computations/lie_algebras.py` (a general
  simple-Lie-algebra engine: Cartan data → Weyl dims + Casimirs →
  character sum `Z_t`, calibrated so `C₂(adj)=h∨` and `dim(adj)=dim(G)`
  exactly for all 19 tested groups) + `scripts/uniform_bound_sweep.py`
  drive the existing KP/RG pipeline per group. Results
  (`visualizations/pilot/general/uniform-bound-sweep.{json,svg}`):
  * SU(2) reproduces the documented baseline `Σ η = 7.951e-4` (validates
    the engine+pipeline chain end-to-end).
  * **Every** simple type has `Σ η(G) ≤ Σ η(SU(2))`, strictly, and `Σ η`
    is **monotone decreasing in the spectral gap Δ** (the global minimum
    Δ=3/4 is SU(2)'s, the next is B₂'s 5/4 already 31× smaller budget).
  * **SU(2) is the worst case across the entire `g₀` window [0.20, 0.45]**
    — at `g₀=0.45` SU(2)'s budget diverges (`Σ η = ∞`) while every other
    group stays finite. The risk-register "non-monotone pocket near the
    convergence edge" did **not** materialize.

  The worst-case-reduction strategy (§1) is numerically de-risked: the
  uniform bound reduces to monotonicity in Δ + the proven SU(2) closure.

### Pillar B — Lean substrate

- **★ U.5 — `ExpUB` from `expNeg`** (L). **Structural core done
  2026-06-08; soundness + a design correction remain.**
  `Constructive/ExpUBInstance.lean` provides the concrete instance
  `recipExpUB : ExpUB` with `E(x) = 1/(1+x)` (the `[0/1]` Padé bound),
  defined via `Int.toNat` clamping so it is literally `1/(1+max(0,x))` and
  hence **antitone on all of `Q'`**; `E_pos`, `E_zero_le_one`,
  `E_antitone` proven in pure `Q'`, axiom-clean. This de-abstracts
  `ExpBound.ExpUB`.
  - **Design correction (important):** a *rational* `E` cannot carry the
    character-tail convergence — substituting `1/(1+x)` for `e^{-x}` makes
    `S_i = Σ_x (x+1)^{2n_i}E(t h_i(x))` **diverge** (terms grow like
    `x^{2n_i-2}`; verified numerically). So `ExpUB.E` can only bound the
    **finite box** terms of `Z_t`; the infinite tail is irreducibly
    exponential and U.6 must bound it with `expNeg`'s geometric ratio
    (`e^{-t·linear} < 1`, a `CReal` fact via `expNeg_leRat`), not a
    rational `E`. The plan's S2 is amended accordingly.
  - **Soundness — DONE 2026-06-09** (`Soundness.lean`,
    `expNeg_le_oneOver1p`, axiom-clean). The chain
    `(1+x) ≤ e^x` ⟹ `(1+x)e^{-x} ≤ e^x·e^{-x} = 1` ⟹ `e^{-x} ≤ 1/(1+x)`
    is fully built. The product law `e^x·e^{-x} = 1` was discharged by the
    full Cauchy-product proof (F.4, L1–L4a) — the binomial
    `Σ_{k+j=m}(−1)ʲC(m,j)=0` was *avoided* via the binomial-free recurrence
    `(m+1)·c_{m+1} = x·cₘ − x·cₘ = 0`, and the corner-term tail by a
    single-cutoff Mertens estimate. `e^{-x} ≥ 0` (needed for the multiply
    step) falls out of `e^x·e^{-x} ≥ ½ > 0` + `e^x > 0`. So
    `recipExpUB` is now a *proven* sound `ExpUB`, not a named obligation.
- **★ U.6 — Constructive character-tail module** (L, U.5). **Tail core
  DONE 2026-06-08** (`Constructive/CharacterTail.lean`, axiom-clean):
  `geom_dom` (term-ratio ⇒ geometric domination `f k ≤ f₀·rᵏ`) and
  `geom_series_le` (a ratio-dominated nonneg series sums under `H`, via
  `geom_dom` + termwise-`finSum` + `geometric_tail_closure`). This is the
  reusable engine for each factor `S_i`'s **exponential tail**,
  parametrized by the ratio bound — so it reduces "bound `S_i`" to "show
  `((x+2)/(x+1))^{2n}·e^{−t·(linear)} ≤ r < 1`", the analytic input
  supplied by `expNeg`'s geometric ratio (not a rational `E` — the tail is
  irreducibly exponential, per the U.5 design correction).
  **Box-term soundness DONE 2026-06-09** (`CharacterTermBound.lean`,
  `charTerm_leRat`): with U.5 proven, `dim²·e^{−t·c} ≤ termMaj recipExpUB
  dim t c` (`= dim²/(1+t·c)`) as a sound `leRat` — the `termMaj` per-point
  bound (ExpBound's "deferred to Level 2" obligation) is now proven, the box
  half of each `S_i`.
  *Remaining*: (i) the **exp-ratio input** `term(x+1) ≤ r·term(x)` for the
  character terms — the irreducibly-exponential **tail**, needing a rational
  geometric majorant for `e^{−t·h(x)}`.  This rests on the exponential
  *addition* law `e^{−(a+b)} = e^{−a}·e^{−b}` (and `e^{−ak} = (e^{−a})ᵏ`),
  the general case of the just-built product law — buildable on the same
  L1–L3 Cauchy-product infrastructure (`FinSumAlg`/`CauchyConv`/
  `ProductDecomp`/`CornerBound`).  (ii) the finite **box** sum
  `Σ_{x<M} termMaj …` (rational, `decide`) over `charTerm_leRat`.  (iii)
  assemble `Z_upper` (`∏ S_i − 1`) with SU(2)/SU(3) `decide` regression locks
  vs `computations/general_character_sum.py`.
- **U.7 — Parametric KP wrappers** (L, U.6). S4: generalize
  `Sheaf/SU2KP.lean` → `KPParametric.lean`; `K_sf`/`K_lf` monotone.
- **★ U.8 — `eta_max_param` + `monotone_budget`** (L, U.7). S5+S6 in
  `RepData.lean`; the §1.3 reduction.
- **★ U.9 — `budget_closes_uniform`** (L, U.8, U.1). Compose
  `monotone_budget` with `su2_cert` + `AdmissibleSimpleGroup` ⇒ the
  unconditional certificate for every simple G.

### Pillar C — Per-group wire-ins & top theorem

- **U.10 — `mass_gap_simple_group`** (L, U.9). Re-run the SU(2) assembly
  (`MassGap/SU2.lean`) against arbitrary `R`; produce the top theorem of
  §0. Axiom-clean.
- **U.11 — SU(3) wire-in files** (L, U.9). The four missing files
  (`RepTheory/SU3.lean`, `Sheaf/SU3KP.lean`, `RG/SigmaHatPilotSU3.lean`,
  `MassGap/SU3.lean`) become *thin instances* of the parametric result —
  a `decide` of `AdmissibleSimpleGroup su3` + a call to
  `mass_gap_simple_group`. (Drops out almost free once U.9/U.10 land;
  gives SU(3) per-group parity with SU(2) as a corollary.)
- **U.12 — Ledger + audit + paper** (P+L). New `formal-suN/` chapter for
  U.1–U.3; update `SORRY_LEDGER.md`, `AXIOM_AUDIT.md`, regenerate
  `make lean-audit-update`; record the formal/paper boundary (unchanged
  from SU(2): OS-reconstruction/cluster-to-gap/√-bridge still paper).

---

## 5. Sequencing

```
U.4 (sweep, cheap, FIRST) ─┐
U.1 (table) ───────────────┼─► U.2 ★ (uniform tail, hard) ─► U.3 (η monotone)
                           │                                      │
U.5 ★ (ExpUB) ─► U.6 ★ ────┴─► U.7 ─► U.8 ★ ─► U.9 ★ ─► U.10 ★ ─► U.11
   (Lean substrate)                  (reduction)  (top thm)  (SU3 corollary)
                                                              └─► U.12 (ledger/paper)
```

Two near-independent fronts: the **analytic** front (U.1→U.2→U.3) and the
**Lean substrate** front (U.5→U.6→U.7), converging at U.8. Start U.4
(numerical monotonicity sweep) and U.5 (ExpUB) immediately — U.4 de-risks
the hard analytic lemma U.2 before any proof effort, and U.5 is the
substrate bottleneck everything else waits on.

---

## 6. Risk register

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| `K_lf = q/(1−q)` non-monotone pocket near the convergence edge breaks global monotonicity | Med | High | U.4 sweep finds it *before* proof; fallback §2.4 finite cover; or restrict admissible g₀ to the deep-interior window where q ≪ 1. |
| Rank-`r` character-tail bound (U.2) much harder than SU(3)'s rank-2 | Med | High | Bound via the *gap* Δ and total weight-height only (1-D geometric in height), not the full `r`-D lattice — collapses rank dependence. |
| `E_antitone` (U.5) needs alternating-series bracket facts not yet built | Med | Med | Already scoped as ExpNeg open work; if it stalls, supply antitonicity as an explicit hypothesis (quarantine pattern) and discharge at paper layer. |
| Some exceptional group violates a normalization assumption in the table | Low | Med | U.1 cross-checks every entry against two independent Casimir conventions; `decide` the nine constants. |
| Reduction proves "≤ su(2) budget" but su(2) margin too thin for some derived σ̂∞ | Low | Low | su(2) closes with `9/10000 ≪ 1`; >100× headroom. Larger groups only improve it. |
| Infinite-K tail still deferred (same as SU(2)) | — | — | Out of scope by design; identical constructive-limit step, tracked separately. |

---

## 7. Definition of done (takeoff)

1. `budget_closes_uniform R (hadm : AdmissibleSimpleGroup R) : R.ClosureCertificate`
   — proven, `#print axioms` clean (Rule 1).
2. `mass_gap_simple_group` (§0) — proven for arbitrary admissible `R`,
   clean-axiom, at the SU(2) formal/paper boundary.
3. SU(3) (U.11) reduced to a one-line corollary; `mass_gap_SU3` exists.
4. U.4 numerical sweep confirms `Σ η(G) ≤ Σ η(su2)` for all nine
   group types; chart committed.
5. `SORRY_LEDGER.md` + `AXIOM_AUDIT.md` updated; analytic obligations
   (U.2 uniform tail, and any quarantined hypothesis) named and bounded
   to the paper layer, not hidden.

What this does **not** deliver (unchanged from SU(2), explicitly out of
scope): the operator-theoretic OS-reconstruction / cluster→gap / √-bridge
content, which stays paper-level. Takeoff = *constructive σ̂-budget
closure + mass-gap statement, uniform over all compact simple gauge
groups, at SU(2)-parity rigor.*

---

## Appendix: invariants of record (for U.1)

Normalization: `C₂_adj = h∨` (dual Coxeter), `T(fund) = 1/2` long-root.

| G | rank | `h∨ = C₂_adj` | `C₂_fund` (defining) | smallest gap Δ |
|---|---|---|---|---|
| A₁ = SU(2) | 1 | **2** | **3/4** | **3/4** |
| A_{N−1} = SU(N) | N−1 | N | (N²−1)/(2N) | (N²−1)/(2N) |
| B_n = SO(2n+1) | n | 2n−1 | n | n |
| C_n = Sp(n) | n | n+1 | (2n+1)/4·… | ≳ (n+1)/2 |
| D_n = SO(2n) | n | 2n−2 | n | n−… |
| G₂ | 2 | 4 | 2 | 2 |
| F₄ | 4 | 9 | 7 | 7 |
| E₆ | 6 | 12 | 26/3 | 26/3 |
| E₇ | 7 | 18 | 57/4 | 57/4 |
| E₈ | 8 | 30 | 30 | 30 |

Minima over all simple G: `h∨ = 2` and `Δ = 3/4`, both **only at SU(2)**.
(Exact `C_n`/`D_n`/exceptional fundamental Casimirs to be pinned to a
single convention in U.1; the *minimum is SU(2)* regardless of
convention, which is all the reduction needs.)

---

# Part II — Folding the operator-theoretic obligations into Lean

Goal (per the 2026-06-07 directive): push the three obligations that
`mass_gap_SU2` currently carries as **paper-level `True`-valued interface
Props** — OS reconstruction, cluster→gap, the √-bridge — as far into Lean
as constructively possible, so each holds with **redundancy across paper,
code, and Lean** rather than paper-only. Partial is acceptable; the aim is
maximal overlap.

## II.0 The governing constraint: the stack is Mathlib-free

`lean/lakefile.toml` depends on **nothing but Lean core** — *"Mathlib's
`Real` is forbidden by Rule 3."* There is therefore **no classical
analysis library to import**: Hilbert spaces, Stone's theorem, the
spectral theorem, functional calculus all would have to be *built*, and
built **constructively** (AGENTS.md Rule 1: no `Classical.choice`). This
is the deep cost — and the reason the obligations were shelved to paper.
Two consequences:

1. We cannot "fold in" by reusing Mathlib; every folded statement is new
   constructive mathematics over the `Q'`/`CReal` substrate.
2. Where the genuine object is irreducibly classical/infinitary (the
   *continuum* spectral theorem for unbounded self-adjoint operators),
   the realistic move is to fold in the **finite-dimensional / discrete
   shadow** (which is constructive and is what the lattice actually
   realizes) and keep the continuum lift as a named interface — not to
   quarantine a classical island (Rule 4), which we avoid.

## II.1 The redundancy triangle, per obligation

| Obligation | Paper | Code | Lean (before) | Lean (now) |
|---|---|---|---|---|
| **cluster→gap** | ✅ `os-reconstruction.tex` Thm 7.2 | ✅ GEVP effective mass = measured `−log λ₀` | ❌ `True` | 🟡 **gap⇒clustering proved** (finite vol), converse scoped |
| **√-bridge** `m ≥ √σ̂∞` | ✅ area-law-to-gap, O(1)=1 | ✅ `mass_gap_bound.py` | 🟡 `m₀²≤σ̂∞` (Q′) | 🟡 unchanged; needs `CReal.sqrt` |
| **OS reconstruction** | ✅ `os-reconstruction.tex` §3–6 | n/a | ❌ `True` quintuple | ❌ types still `Unit`/`True` |

Foldability ranking (easiest → hardest): **cluster→gap** > **√-bridge** >
**full OS reconstruction**.

## II.2 Delivered this session — `Continuum/SpectralGap.lean`

A new module, **built and axiom-clean (`#print axioms` = `[propext]`
only, no `sorryAx`)**, folding the *gap ⇒ clustering* direction:

- Finite Källén–Lehmann model `SpectralModel` (k modes, nonneg weights
  `w_i`, nonneg transfer-matrix eigenvalues `λ_i`); `corr S n = Σ_i w_i λ_iⁿ`
  is exactly the connected two-point function the lattice transfer matrix
  realizes at finite volume — *not a surrogate*.
- `pow_le_pow_left` — `Q'` power monotone in the base (a reusable gap the
  stack lacked; only the half-base case existed).
- `corr_zero` — `corr(0) = Σ_i w_i` (total spectral weight).
- `finSum_mul_const_le` — distributivity `Σ_i (f_i·c) ≤ (Σ_i f_i)·c`
  (also the lemma `Geometric.lean` flagged as missing).
- **`decay_of_spectralGap`** / `decay_of_spectralGap_corr0` — the payoff:
  a spectral gap at `μ` forces `corr S n ≤ corr(0)·μⁿ`, i.e. exponential
  clustering at rate `−log μ`. This is `OSReconstruction.ClusterImpliesGap`'s
  gap⇒clustering content, now a *theorem* over the finite spectrum.

Net effect: the cluster↔gap link moves from paper-only to the full
paper/code/Lean triangle, at finite volume.

## II.3 Plan — cluster→gap (finish the converse, then lift)

- **★ F.1 — Converse: clustering ⇒ gap (finite volume)** (L).
  **Status 2026-06-07: DONE & verified, axiom-clean.** The unconditional
  `gap_of_decay` (`Continuum/SpectralGapGrowth.lean`) proves: measured
  exponential clustering `corr S n ≤ C·μⁿ` ⇒ every populated mode
  `λ_j ≤ μ`. `#print axioms` = `[propext]` / `[propext, Quot.sound]`
  (the `Quot.sound` is from `omega`; no `Classical.choice`). Two layers:
  - `SpectralGapConverse.lean` — the logical reduction
    `gap_of_decay_of_growth` (single-term domination + contradiction) plus
    the Q′ strict-order layer the stack lacked (`pos_iff_num_pos`,
    `mul_pos`, `pow_pos`, `lt_of_not_le`, `not_lt_of_le`, `finSum_ge_term`,
    `term_le_corr`).
  - `SpectralGapGrowth.lean` — the geometric-growth kernel
    `pow_dominates : 0<μ → μ<λ → 0<w → 0≤C → ∃ n, C·μⁿ < w·λⁿ`, discharged
    division-free by reducing the Q′ inequality through the `num/den`
    representation to a `Nat` fact `nat_geom_dominates`, itself proved from
    a `Nat` Bernoulli bound (`nat_bernoulli`). Reusable bridge lemmas:
    `num_pow`, `den_cast_pow`, `int_mul_pow`, `int_geom_dominates`.

  *(Historical proof sketch retained below.)* Division-free proof
  (Q′ has no reciprocal), three new lemmas:
  1. `term_le_corr` — a single nonnegative term is ≤ the finite sum
     (`w_j λ_jⁿ ≤ corr S n`); from `finSum` nonneg-monotonicity.
  2. `pair_bernoulli` — for `0 ≤ μ ≤ λ`, `λⁿ ≥ μⁿ + n·μⁿ⁻¹·(λ−μ)`
     (induction; no division). Hence `λⁿ ≥ n·μⁿ⁻¹·(λ−μ)`.
  3. `Q'.archimedean` — `∀ q c, 0 < c → ∃ n, q < (ofNat n)·c` (from the
     numerator/denominator of `q`). 
     Combine: assume `μ < λ`; then `w_j·n·μⁿ⁻¹·(λ−μ) ≤ w_j λ_jⁿ ≤ C·μⁿ =
     C·μ·μⁿ⁻¹`; cancel the positive `μⁿ⁻¹` to get `w_j·n·(λ−μ) ≤ C·μ`
     for all `n`, contradicting Archimedean. The `μ = 0` corner is the
     easy `λⁿ→0 ⇒ λ = 0` sub-case. Acceptance: axiom-clean; SU(2) GEVP
     numbers as a `decide` regression instance.
- **F.2 — `SpectralModel` ← transfer matrix interface** (L). Connect
  `SpectralModel` to the OS `HilbertSpace`/`SelfAdjointOp` at finite
  volume: define the finite transfer matrix's spectral data and show it
  inhabits `SpectralModel`. Replaces the `Unit` carriers with real
  finite-dimensional content. Continuum lift (k → ∞, the genuine
  spectral theorem) stays a named interface.
- **F.3 — Rewire `ClusterImpliesGap`** (L). Make
  `OSReconstruction.HasSpectralGap`/`ClusterImpliesGap` *defined in terms
  of* `SpectralGap.decay_of_spectralGap` + F.1 at finite volume, so the
  Prop is no longer `True` but the real finite-volume statement, with the
  continuum step the only remaining interface hypothesis.

## II.4 Plan — √-bridge (constructive square root)

Currently `m_0² ≤ σ̂∞` is proved in `Q'`. The honest upgrade is to make
`m_0` *be* `√σ̂∞` as a constructive real.

- **F.4 — `CReal` arithmetic** (L). **`CReal.mul` DONE 2026-06-08**
  (`Constructive/CRealMul.lean`, axiom-clean `[propext, Quot.sound]`):
  pointwise product, choice-free (moduli used only in the `cauchy` proof),
  with the `Q'` substrate `AbsQ` (abs + `mul_le_of_bounds`), `CReal.localBound`
  (boundedness), and `exists_mul_le` (division-free product modulus).
  **`CReal.add`/`neg` DONE 2026-06-09** (`Constructive/CRealAdd.lean`,
  axiom-clean `[propext]`): pointwise `add`/`neg` with Cauchy proofs
  (`neg` preserves the modulus; `add` splits `ε = half·ε + half·ε` via the
  `Q'.regroup` rearrangement + `ExpNeg.two_halves`), the `ofQ'` homomorphisms
  (`ofQ'_add`/`ofQ'_neg`, by proof irrelevance), and `leRat_add` (sound
  upper bound of a sum). **`mul` monotonicity DONE 2026-06-09**
  (`Constructive/CRealMulMono.lean`): `mul_nonneg` (product of nonnegatives),
  `leRat_smul_nonneg`, `geRat_add_neg`, via the sign-cased `Q'.mul_ge_of_bounds`.
  **Product law `e^x·e^{-x}=1` DONE 2026-06-09** — the full Cauchy-product
  proof, axiom-clean, *without* binomial coefficients:
  * L1 `FinSumAlg.lean` — `finSum` distributivity/additivity.
  * L2 `CauchyConv.lean` — the convolution coefficient vanishes
    (`conv_succ_eqv_zero`, `cₘ=[m=0]`) via the recurrence
    `(m+1)·c_{m+1} = x·cₘ − x·cₘ = 0` + the weighted term-recurrences
    `(k+1)·a_{k+1}=x·aₖ`, `(k+1)·b_{k+1}=−x·bₖ`.
  * L3a `ProductDecomp.lean` — row-split `P⁺_{n+1}·P⁻_{n+1} ≃ 1 + corner`
    (triangle = `Σ cₘ` = 1).
  * L3b `CornerBound.lean` — Mertens estimate `cornerₘ → 0` (single-cutoff
    split at `max(halfRatioCutoff, termAbsModulus(½δ))`, uniform
    `expNeg_tail_bound`).
  * L4a `ProductLaw.lean` — `expProd_leRat`/`expProd_geRat` (eˣ·e⁻ˣ = 1).
  **U.5 soundness `e^{-x} ≤ 1/(1+x)` DONE 2026-06-09**
  (`Soundness.lean`, `expNeg_le_oneOver1p`): `eˣ·e⁻ˣ=1` + `e⁻ˣ≥0` ⇒
  `(1+x)·e⁻ˣ ≤ 1` ⇒ divide. So `ExpUBInstance.recipExpUB` is a *proven*
  sound bound for `expNeg`. F.4/U.5 closed; all axiom-clean
  (`[propext]` / `[propext, Quot.sound]`).
- **F.5 — `CReal.sqrt`** (L, F.4). Heron/Newton iteration with explicit
  Cauchy modulus (constructive, no choice — same shape as `expNeg`).
  Prove `(sqrt x)·(sqrt x) ≈ x` and `0 < sqrt x` for `0 < x`. Then
  define `m_0 := CReal.sqrt σ̂∞` and recover the existing `m_0² ≤ σ̂∞` as
  an equality-up-to-`CReal`, with the conservative O(1) constant 1
  explicit. The dimensional identification (mass-dimension of `m_0`)
  remains the paper's province, but the *square-root content* becomes a
  Lean theorem, not an assumption.

## II.5 Plan — OS reconstruction (the hard, partial one)

- **F.6 — Substantiate the Hilbert-space types** (L). Replace the `Unit`
  carriers in `OSReconstruction.lean` with a real constructive
  inner-product space: a `CReal`-valued sesquilinear form on the
  test-function algebra, with reflection positivity as a real `0 ≤ ⟨·,·⟩`
  hypothesis. Makes `VacuumNormalized`/`HamiltonianNonneg`/… real
  equations rather than `True`.
- **F.7 — GNS quotient + completion** (L, F.4/F.6). The
  `E₊/N`-quotient-then-complete construction is constructively available
  (Bishop-style completion of a `CReal`-pre-Hilbert space). Yields a
  genuine `HilbertSpace` carrier.
- **Out of constructive reach this program (named, not folded):**
  **Stone's theorem** and the **unbounded self-adjoint spectral
  theorem**. These are the genuine constructive-analysis frontier; with
  no Mathlib they would each be a multi-month build, and the constructive
  spectral theorem for *unbounded* operators is subtle even in principle
  (Bishop's spectral theory covers the bounded/located case). The plan
  keeps `SemigroupGenerated` (the `U(t)=e^{−tH}` Stone statement) as an
  interface hypothesis. The finite-volume transfer matrix (F.2) is the
  bounded, constructive stand-in that carries the actual gap content.

## II.6 Honest scorecard after Part II

- **cluster→gap**: foldable to a real Lean theorem at finite volume
  (gap⇒clustering ✅ now; clustering⇒gap via F.1) — the continuum lift
  stays interface. **Strong redundancy achieved.**
- **√-bridge**: fully foldable (F.4–F.5); only the units interpretation
  stays paper. **Strong redundancy achievable.**
- **OS reconstruction**: partially foldable (types + GNS, F.6–F.7);
  Stone + unbounded spectral theorem remain named interfaces — the one
  place "imagine doing this in Agda" really bites, and where Lean's
  (future) Mathlib bridge or a dedicated constructive-analysis build is
  the only way to full redundancy. **Partial by necessity, honestly
  bounded.**

The lattice (code leg) already measures the gap directly via the GEVP
correlator decay — so even where Lean stops at the interface, the
paper+code legs cover it, and `SpectralGap.lean` ties the Lean leg to the
same finite-spectral object the code measures.
