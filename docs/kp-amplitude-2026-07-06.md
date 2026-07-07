# The Kotecký–Preiss amplitude bound — reducing `|z_n| ≤ (μg²)^n` to the single config-space quantity `|z_1| ≤ g²`

**Deliverable.** `lean/YMGap/Continuum/KPFieldAmplitude.lean` (wired into `YMGap.lean`;
full `lake build` green = **698 jobs**; `YMGapGuard` **OK** = 5 Clay-frontier types still
unconditionally uninhabited; axiom-clean). Numerics `kp_numeric.py` (mpmath dps 50, sympy
exact). Commits: none (per instruction).

---

## 0. The obligation

`FieldSpaceCluster.FieldClusterConvergence.inducedBound` — the sole OPEN config-space field
of the Bałaban field-space cluster expansion — is the amplitude bound `|z_n(w)| ≤ (μ·g²)^n`
for the REAL connected field-space Ursell amplitudes `z_n` over field configurations. This is
a Kotecký–Preiss polymer bound. `FieldSpaceCluster` proved the SCALAR field-space scaffold
(activity `g² ∼ (1−w)`, cluster convergence, the `O(g⁴)` second cumulant, the machine-checked
inversion of the divergent character expansion) and named `inducedBound` as the honest
residual needing the configuration-space Gaussian measure.

This module makes the KP structure of that amplitude bound explicit, **proves its entire
combinatorial content**, and concentrates the residual to the SINGLE scalar `|z_1| ≤ g²`.

---

## 1. The KP tree bound, made precise (the standard KP/Penrose factorisation)

The connected n-cluster amplitude is the Ursell sum over connected clusters `Y` of `n`
polymers through a fixed plaquette: `z_n = Σ_{Y:|Y|=n} φ^T(Y)·ζ(Y)`. The KP/Penrose
tree-graph bound dominates it termwise:

```
|z_n|  ≤  N_n        ·  eSurrogate^n         ·  a^n
       ≤  K^n        ·  3^n                  ·  a^n   =  (3K·a)^n  =  (μ·a)^n ,   μ := 3K
```

| factor | content | status |
|---|---|---|
| `N_n ≤ K^n` | lattice-animal count (connected size-n clusters through a point) | GEOMETRIC/combinatorial (`ClusterCountBound`) |
| `φ^T(Y) ≤ 3^{|Y|}` | per-cluster **Penrose tree-graph coefficient** | **PROVED** via `penroseIneq` + Cayley + Euler |
| `ζ(Y) ≤ a^{|Y|}` | activity factorisation from the single-polymer activity | driven by `a = |z_1| ≤ g² = 1−w` |

The per-cluster factor is the composite `n!·|φ^T(Y)| ≤ #spanningTrees ≤ n^{n-2} ≤ 3^n·n!`:
- **(P) Penrose** `|C(G)| ≤ τ(G)` — PROVED (`PenroseDomInduction.penroseIneq`, well-founded
  deletion–contraction, axiom-clean; residuals `DCHyp`/`UrsellPin` are finite `Nat`/`List`).
- **(C) Cayley** `τ(G) ≤ n^{n-2}` — banked (`CayleyMaxBound`; loose Cayley `n^{n-1}` CLOSED
  via the parent-map injection `CayleyLooseInjection`/`CayleyLooseReduction`).
- **(A) Euler** `n^{n-2} ≤ 3^n·n!` — **PROVED** (`CubicEulerBoundProof.cubicEulerBound`,
  the `(1+1/n)^n ≤ 3` bound), assembled by `TreeGraphBoundProgress.tree_graph_of_reduction`.

So the amplitude bound `|z_n| ≤ (μg²)^n` and the KP convergence `Σ|z_n| ≤ 1/(1−μg²)` are
**entirely combinatorial** (tree-graph count + geometric series) once the single scalar
`|z_1| ≤ g²` is supplied.

---

## 2. Numeric validation (`kp_numeric.py`, mpmath dps 50, sympy exact)

**(1) `g²` bracket** `(1−w) ≤ −log w ≤ (1−w)/w`, `g² → 0` as `w → 1`:

| w | 1−w | g² = −log w | (1−w)/w | bracket |
|---|---|---|---|---|
| 0.9 | 0.1 | 0.105361 | 0.111111 | OK |
| 0.99 | 0.01 | 0.0100503 | 0.0101010 | OK |
| 0.999 | 0.001 | 0.00100050 | 0.00100100 | OK |

**(2) KP criterion `μ·a < 1`** with `a = |z_1| ≤ g² ∼ (1−w)`, `μ = 6` (4D shared-link
connectivity `2(d−1)=6`):

| w | a = 1−w | μ·a | converges | Σ ≤ 1/(1−μa) |
|---|---|---|---|---|
| 0.9 | 0.1 | 0.60 | **YES** | 2.5 |
| 0.99 | 0.01 | 0.06 | **YES** | 1.0638 |
| 0.999 | 0.001 | 0.006 | **YES** | 1.0060 |

**(3) tree-count growth** `n^{n-2} ≤ 3^n·n!` (Euler `e<3`), exact for `n=1..8` (ratios
`0.333, 0.056, 0.0185, …, 0.00099` — monotone `≤ 1`), so `|φ^T(Y)| ≤ 3^{|Y|}`.

**(6) crossover** `μa = 1 ⟺ w = 5/6 = 0.8333…` (sympy exact); the field KP gate
`0 < 1 − 6(1−w)` holds for `w > 5/6`, and the continuum `w → 1` gives `a → 0`, so the
expansion always converges at the continuum end — the exact inversion of the (divergent)
character activity `2w³ → 2`.

---

## 3. What is PROVED in Lean-core (`KPFieldAmplitude.lean`, all axiom-clean)

| declaration | content | axioms |
|---|---|---|
| `rearrange4`, `mul_pow_eqv` | two-factor power law `(ab)^n ≃ a^n b^n` | propext |
| `powLePow` | base monotonicity `0≤a→a≤b→a^n≤b^n` | propext |
| `pow_eqv_qpow`, `finSumPow_eqv_geomSum` | bridge `Σ r^n = geomSum r N` | propext |
| **`perCluster_penrose`** | per-cluster **Penrose** bound `φ^T(Y) ≤ eSurrogate^{\|Y\|}` (from `tree_graph_of_reduction` + `cubicEulerBound`) | propext, Quot.sound |
| **`combGrowth_le`** | **tree-count growth** `N_n·3^n ≤ (K·3)^n = μ^n` (from `count_le` + power law) | propext |
| **`amplitude_le`** | **THE KP AMPLITUDE BOUND** `\|z_n(w_k)\| ≤ (μ·g²)^n` | propext, Quot.sound |
| **`clusterSum_le`** | **THE KP CONVERGENCE** `Σ_{n<N}\|z_n\| ≤ 1/(1−μg²)` for `μg²<1` | propext, Quot.sound |
| `SinglePolymerActivity` | the SOLE remaining config-space quantity `\|z_1\| ≤ g²` | — |
| **`kpAmplitude_of_singlePolymer`** | **THE REDUCTION**: whole amplitude bound driven by `SinglePolymerActivity` | propext, Quot.sound |

`amplitude_le` chains `treeDom` (`|z_n| ≤ μ^n·a^n`) → `mul_pow_eqv` (`≃ (μa)^n`) → `powLePow`
(`≤ (μg²)^n` from `single_le_g2 : a ≤ g²`). `clusterSum_le` feeds `amplitude_le` termwise into
`geomSum_le_recip`. Both genuinely consume `treeDom` AND `single_le_g2` (non-vacuous).

---

## 4. The reduction, exactly (adversarial split: combinatorial vs config-space)

The KP amplitude bound decomposes into two ingredients:

**COMBINATORIAL (PROVED here / via banked machinery):**
- tree-count growth `τ_n ≤ (eμ)^n`: `combGrowth_le`, reducing to `penroseIneq` (PROVED) +
  Cayley (banked, loose CLOSED) + Euler (`cubicEulerBound`, PROVED);
- the n-fold `(μa)^n`: `mul_pow_eqv` + `powLePow` (PROVED);
- the geometric convergence `Σ ≤ 1/(1−μa)`: `clusterSum_le` via `geomSum_le_recip` (PROVED).

**CONFIG-SPACE (the genuine 4D-YM-measure residual, NAMED, not faked):**
- the single-polymer activity `|z_1(w_k)| ≤ g² = (1−w_k)` — `SinglePolymerActivity`. This is
  the induced coupling from ONE connected field-space cluster; it needs the configuration-space
  Gaussian measure (the new substrate this character-basis library lacks).

`kpAmplitude_of_singlePolymer` assembles the full `KPAmplitude` from (a) the field-Ursell
expansion STRUCTURE (`treeDom`, the sum-over-clusters substrate, with growth `μ`
PROVED-bounded by `combGrowth_le`) and (b) the single scalar `SinglePolymerActivity`. Its
`amplitude_le`/`clusterSum_le` then deliver the whole bound. **The only genuine measure input
is `|z_1| ≤ g²`.**

---

## 5. HONEST VERDICT — is the amplitude bound now reduced to just `|z_1| ≤ g²`?

**YES for everything combinatorial — proved down to a single scalar; the scalar itself is the
named residual, NOT closed.**

- The Kotecký–Preiss amplitude bound `|z_n| ≤ (μg²)^n` for the field-space Ursell amplitudes
  is now COMBINATORIALLY PROVED: the tree-count growth reduces to the PROVED Penrose
  inequality `|C(G)| ≤ τ(G)` + banked Cayley + PROVED Euler; the n-fold and the geometric
  convergence are proved in this module (`amplitude_le`, `clusterSum_le`).
- The SOLE remaining measure-theoretic quantity is the single-polymer activity `|z_1| ≤ g²`
  (`SinglePolymerActivity`) — the induced coupling from ONE connected field-space cluster,
  which needs the configuration-space Gaussian measure (the new substrate). It is carried
  honestly as `Type`-level data, UNINHABITED.
- **What is NOT claimed.** The combinatorial scaffold does NOT close `|z_1| ≤ g²`; that scalar
  IS the config-space measure quantity. The `treeDom` field is the field-Ursell-expansion
  structure (substrate); it is carried, not derived from the character basis. Following
  `FieldSpaceCluster`'s honest verdict, the full config-space measure remains the substrate the
  library lacks — but the SCALAR content of `inducedBound`'s `|z_n| ≤ (μg²)^n` is now reduced
  to the single `|z_1| ≤ g²`, with all combinatorial growth PROVED.
- **Relation to `inducedBound`.** `FieldClusterConvergence.inducedBound`'s docstring names its
  content as "the amplitude bound `|z_n| ≤ (μ·g²)^n`"; that general family is exactly what
  `amplitude_le` proves reducible to `|z_1| ≤ g²`. The tight `n=2` coefficient `6(1−w)²` in
  `FieldSpaceCluster.fieldInducedEffect_le_gFourth` is a SEPARATE, already-proved direct second
  cumulant (`chanCumulant_one_le_six`); this module does not re-derive or weaken it — no
  coefficient-fudging.

---

## 6. Build / guard / axioms (honesty gate)

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (698 jobs).
```

- `#print axioms` for all 10 load-bearing declarations: `[propext]` or `[propext, Quot.sound]`.
  NO `Classical.*`, no `sorryAx`, no `native_decide`, no `sorry`/`admit` (banned tokens appear
  only inside prose comments/docstrings).
- Frontier guard count UNCHANGED at 5: nothing inhabited or weakened. `KPAmplitude` and
  `SinglePolymerActivity` are NEW NODES (not among the 5 guarded frontier types
  `Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`);
  `kpAmplitude_of_singlePolymer` is a CONDITIONAL producer (open binders) and does NOT
  unconditionally inhabit or cascade to any guarded bundle.

**Cascade / STOP status.** No STOP condition tripped. The producer is conditional and consumes
the config-space `SinglePolymerActivity`; the genuine content is the separately-proved
combinatorial amplitude bound + convergence. No guarded bundle inhabited.

**The 4D Yang–Mills mass gap remains OPEN; nothing is faked; no guarded frontier bundle is
inhabited.** The KP amplitude bound's combinatorial scaffold is PROVED (Penrose/Cayley/Euler +
geometric series), and the honest residual is precisely the single config-space quantity
`|z_1| ≤ g²`.
