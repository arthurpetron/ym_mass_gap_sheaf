# Codynamic-uplift survey — Constructive/ (68) · RG/ (16) · RepTheory/ (8)

Read-only walk. Tools: T1 reflection-unit defect (`Metric.unit-defect`/`εX`), T2 nonlinear
monotone modulus (`Lipschitz.scale`), T3 compositional error law (`eqBound-◅◅`), T4 n-step
Grönwall fold (`nstep-d`), T5 islands (`island-free`), T6 evolution monad (`extendsBy`), T7
complexity budget (`cert-budget`).

**Framing (from the three context docs).** The whole proved continuum floor already IS the
codynamic `nstep-d` fold, hand-rolled twice (`DefectGapRecursion.prodPrefix_le_physGap`
product form, `InductiveBoundWitnessSystem.terminal_invariant_bound` additive form). The one
open atom `singleStep` is exactly the `lip`/`unit-defect` hypothesis the fold *consumes and
never proves*. So a fresh top-level port = a forbidden `:= SingleStepDefectBound` loop. The
tools' honest value in THIS subtree is therefore: **(a) supply the `Costs`/`MetricVal`
instance the tools need** (a genuine reuse of the Q'/CReal substrate), and **(b) provide the
T1 reflection-unit home (`BlockSpin`) and the concrete T2 monotone-modulus witnesses
(`EtaPackaging`)** — but the defect these price out equi-inhabits `singleStep` and is not
shrunk here.

---

## `Costs` / `MetricVal` supplier map (the concrete reuse — see summary §A)

The Agda `Costs` record needs: carrier `Q`, `0#`, `_+#_`, `_⊔#_` (join), `_≤#_`, `≤#-refl`,
`≤#-trans`, `+#-mono`, `+#-assoc`, `+#-identityˡ`, `≤#-⊔ˡ/ʳ`, `⊔#-lub`; and `MetricVal` needs
a `d` with `triangle`, `d-sym`, `nonneg`. Over the substrate `Q'`:

| `Costs`/`MetricVal` field | Supplied by | Lean name |
|---|---|---|
| carrier `Q`, `0#`, `_+#_`, `_≤#_`, `≤#-refl`, `≤#-trans`, `+#-identityˡ` | **Rationals.lean** | `Q'`, `Zero`, `HAdd`, `LE`, `le_refl'`, `le_trans'`, `add_zero'` |
| `+#-assoc` (as `.eqv`), `+#`-comm | **RationalsMul.lean** | `add_assoc_eqv`, `add_comm_eqv` |
| `+#-mono` | **CRealAdd.lean** (Q'-level) / Rationals | `add_le_add` |
| `_⊔#_` = `max'` (def) | **Rationals.lean** | `Q'.max'`, `Q'.min'` |
| `≤#-⊔ˡ`, `≤#-⊔ʳ`, `⊔#-lub`, plus `maxOver`-ub analog | **RegularCRealArith.lean** | `le_max'_left`, `le_max'_right`, `max'_le_iff'`, `runningMax_le_of_le` |
| `MetricVal.d` + `triangle` + `nonneg` (Q' abs) | **AbsQ.lean** | `abs`, `abs_add_le'`? (triangle in CRealAbs), `abs_nonneg`, `abs_le` |
| `MetricVal.d` + `triangle` + `nonneg` (CReal abs) | **CRealAbs.lean** | `CReal.abs`, `abs_add_le'`, `abs_le_of_bounds` |

**Verdict on the instance:** the `Costs` instance for the tools is supplied jointly by
**Rationals.lean (carrier + add + order + `max'` def) and RegularCRealArith.lean (the join
`lub` laws — the crux `max'_le_iff'` = `⊔#-lub`)**; the `MetricVal` by **AbsQ.lean / CRealAbs.lean**.
These are GENUINE reuse targets (the tools should import them, not rebuild them).

---

## Constructive/ (68 modules)

| module | role | tool(s) | verdict | note |
|---|---|---|---|---|
| Rationals | the `Q'` carrier + `0/1/+/≤`, `le_refl'/le_trans'`, `add_zero'`, `max'/min'` defs | Costs T1-T7 base | **GENUINE-GAIN** | SUPPLIES most Costs fields (carrier, `0#`,`+#`,`≤#`,`≤#-refl/trans`,`+#-identityˡ`, `⊔#` def). Root of the instance. |
| RationalsMul | `Q'` multiplicative + `add_assoc_eqv`, `add_comm_eqv` at `.eqv` | Costs `+#-assoc` | **GENUINE-GAIN** | Supplies `+#-assoc`/comm the fold's associativity juggling (`eqBound-◅◅`) needs. |
| RegularCRealArith | canonical-modulus real arith + `le_max'_left/right`, `max'_le_iff'`, `runningMax_le_of_le` | Costs `⊔#`-lub | **GENUINE-GAIN** | SUPPLIES the join semilattice laws (`≤#-⊔ˡ/ʳ`, `⊔#-lub`) + the `maxOver`/`dAll` running-max analog. The crux join supplier. |
| AbsQ | constructive `|·|` on `Q'`, sign-cased product bound, `abs_le` | MetricVal (Q') | **GENUINE-GAIN** | Supplies the `Q'`-level metric `d=|u−v|`, `nonneg`, `abs_le` (two-sided). |
| CRealAbs | `CReal.abs` index-wise + `abs_add_le'` (triangle), `abs_le_of_bounds` | MetricVal (CReal) | **GENUINE-GAIN** | Supplies the CReal metric `triangle` inequality — the `MetricVal` on the real substrate. |
| CRealAdd | pointwise `add/neg`, `add_le_add`, `leRat_add` | Costs `+#-mono` | **GENUINE-GAIN** | Supplies `+#-mono` and additive congruence used in every `nstep-d` step. |
| CRealAlg | shared CReal ring/`csum`/`ofQ'` algebra (`cmul_assoc`, `csum_add`, `amgm_two`) | T3/T4 plumbing | DEDUP/BOOKKEEPING | Ring identities the fold reuses; not a Costs field, pure plumbing. |
| CRealLe | sound rational upper bound `leRat` | MetricVal order | DEDUP/BOOKKEEPING | The `≤#` at CReal level; supports the metric but is order-only. |
| CRealMul, CRealMulLe, CRealMulMono | CReal `*`, product upper bound, monotone/nonneg | modulus arith | DEDUP/BOOKKEEPING | Multiplicative — needed for the *product* fold (SITE-2) `scale=ρ·(−)`; supports but is not a Costs additive field. |
| CRealSum | finite sums of CReals `csum`, `leRat_csum` | T3/T4 Σ | DEDUP/BOOKKEEPING | The `Σ` behind `derivBound`/`eqBound`; bookkeeping for the fold. |
| CRealComplete, CRealCompleteCauchy, CRealCompleteIdx, CRealCompleteRate | Bishop completeness backbones (explicit-modulus limits) | T4 (limit of trajectory) | MISMATCH | Completion of a Cauchy sequence of CReals ≠ the finite `nstep-d` fold; these are the a→∞ limit machinery, orthogonal to per-step defect/modulus. |
| CauchyConv | product-law L2 convolution vanishing (`m·cₘ=0`) | — | N/A | Exp-add analytic identity; no fold/defect/modulus content. |
| CharacterTail | geometric bound for ratio-dominated `Q'` series (`geom_series_le`) | T2/T5 modulus input | DEDUP/BOOKKEEPING | Character-tail = the per-step η_max modulus INPUT / island tail; already proved, re-expressible as a modulus. |
| CharacterTermBound | `termMaj` per-irrep bound soundness | T2 modulus input | DEDUP/BOOKKEEPING | Feeds the tail modulus; analytic. |
| CornerBound, CornerBoundAdd | Mertens corner-vanishing for product/add exp laws | — | N/A | Analytic exp-law residual; orthogonal. |
| CRealExp | `expNegC` — `e^{−w}` for a CReal exponent | T2 modulus building block | DEDUP/BOOKKEEPING | The `sep_k=exp(logR/(b+1)^k)` self-similar step map; is a candidate `scale` component but analytic content only. |
| CRealLog | constructive `log` (artanh route) | T2 building block | N/A | Needed for `exp(logR/…)`; analytic, no codynamic structure. |
| CRealSqrtCReal | √ of a CReal radicand (`csqrt`) | — | N/A | Chebyshev half-angle analytic; uses `max'` (consumer, not supplier). |
| CRealTrig, CRealTrigFull | `cosC/sinC` of a CReal angle + range reduction | — | N/A | Trig analytic content. |
| CubeRoot | `cbrtFrom` for positive rationals; `min_le_left/right` | (min lemmas) | N/A | The min lemmas duplicate RegularCRealArith's; analytic root otherwise. |
| ExpAdd, ExpAddConv | `e^{−a}e^{−b}=e^{−(a+b)}` + convolution identity | — | N/A | Exp-add analytic. |
| ExpBound | Level-1 `ExpUB` interface + Brydges–Federbush large-field cert | T2 modulus input | DEDUP/BOOKKEEPING | `termMaj` = the modulus seed of the tail; analytic. |
| ExpGeomBound, ExpGeomMaj, ExpGeomSum | geometric domination of `e^{−a·m}≤ρ^m` and its sum | T2/T5 | DEDUP/BOOKKEEPING | The geometric majorant = the island-tail cost-collapse (T5) / modulus; already proved. |
| ExpNeg, ExpNegCongr, ExpPos | rational `e^{−x}`/`e^{+x}` partial sums + `.eqv` congruence | — | N/A | Analytic exp substrate. |
| ExpUBInstance | concrete `E(x)=1/(1+x)` `ExpUB` | T2 modulus input | DEDUP/BOOKKEEPING | Concrete modulus seed; analytic. |
| FinSumAlg | `finSum` distributivity/additivity `.eqv` laws | T3/T4 Σ algebra | DEDUP/BOOKKEEPING | The additivity `eqBound-◅◅` mirrors (`finSum_add`); bookkeeping for the fold's sum. |
| FinSumGeom | uniform box + geometric-tail `finSum` bound | T5 island | DEDUP/BOOKKEEPING | Box + geometric tail = the finite-core ⊕ island-tail split shape; already proved. |
| GeomBeatsLinear | `k·s^k ≤ 1` for `2s≤1` | T5 | N/A | Elementary SU(N) scalar; island-tail summability input, not codynamic structure. |
| Geometric, GeometricTail | `Q'.pow` + geometric-tail closed form | T4/T5 | DEDUP/BOOKKEEPING | The geometric-tail closure = the summable-budget (T7) / island (T5) closed form. |
| HalfPow | `(1/2)^k → 0` with explicit modulus | T7 budget | DEDUP/BOOKKEEPING | Explicit convergence modulus = a `cert-budget` datum; bookkeeping. |
| Pi | constructive `π` (arctan) | — | N/A | Analytic constant. |
| ProductDecomp, ProductDecompAdd | rectangle/corner split of exp partial products | — | N/A | Exp-law analytic. |
| ProductLaw | `eˣe⁻ˣ=1` sound bounds | — | N/A | Analytic. |
| PythFull | series-level `cos²+sin²=1` | — | N/A | Trig analytic. |
| QDivArctanSeries | `arctan(1/5)` coefficient model (`SeriesData`) | — | N/A | Analytic series data. |
| QPoly | reflective univariate `Q'`-polynomial ring (`ring`-substitute) | T3 (SOS) | N/A | Polynomial-identity engine for SOS pivots; not a Costs field. |
| RationalTail | `QSeq`, `finSum`, `sigma_hat_budget_closure`, `prefix_plus_tail_closure` | **T4 + T7** | DEDUP/BOOKKEEPING | THE additive Grönwall/budget fold already in Lean (`Σδ ≤ budget` at every truncation) = the additive `nstep-d`/`cert-budget`. Faithful match; the tools would dedup it, no new content. Highest-relevance non-Costs node. |
| RatNat | `Q'`→`Nat` bridges, `halfRatioCutoff` | T7 | N/A | Cutoff data; minor. |
| Reals | Bishop regular Cauchy `CReal` base | MetricVal base | DEDUP/BOOKKEEPING | Defines `CReal` (the metric's `Val`); the one-slack `≤` is deliberately NOT the metric order. |
| RegularCReal | canonical-modulus regular real | MetricVal base | DEDUP/BOOKKEEPING | Alternative real carrier; the arith/join lemmas live in RegularCRealArith (above). |
| SelfSimilarFlow | general-`b` CReal power law + self-similar flow (`scaleN`, `ExpNegCData`) | **T2/T4** | DEDUP/BOOKKEEPING | The `b`-th-root self-similar RG step = a concrete monotone `scale` trajectory; `scaleN` iterates it. Closest Constructive analogue of the codynamic modulus-fold, but analytic/already-built. |
| SinAddNonneg | `Q'`-angle sine addition core | — | N/A | Trig analytic. |
| Soundness | `e⁻ˣ ≤ 1/(1+x)` | T2 modulus input | N/A | Analytic bound feeding the tail modulus. |
| Sqrt, SqrtSubadd | `CReal.sqrt` + √-subadditivity/Hölder modulus | T2 modulus | DEDUP/BOOKKEEPING | `holder_oneMinusSq` = a genuine nonlinear uniform-continuity modulus (√ is the archetypal nonlinear `scale`) — a real T2 EXAMPLE, but analytic content, not core-shrinking. |
| SU3CharFactor | SU(3) irrep data + prefactor of tail majorant | T2 input | N/A | Rep-data modulus input. |
| SumOfSquares | SOS/PSD positivity primitives (`geRat_add`, `geRat_csum_nonneg`) | MetricVal nonneg | DEDUP/BOOKKEEPING | `nonneg` of the metric/costs via SOS; supports `Costs.nonneg`-style facts but for OS2 not the fold. |
| Trig, TrigAdd, TrigAddCReal, TrigBound, TrigSignedAdd, TrigSignedAddFull, TrigSineAddCReal | constructive cos/sin, addition laws, second-difference bound | — | N/A | Trig analytic layer (Wall-2 / OS2 content); orthogonal to the codynamic fold/defect/modulus. `TrigBound.cos_second_diff_abs_le` is a curvature bound, not a modulus. |

## RG/ (16 modules)  — the T1/T2/T4 hot zone

| module | role | tool(s) | verdict | note |
|---|---|---|---|---|
| BlockSpin | block-spin step `TwoCellTheta` (`σ_in−η_k ≤ σ_out`), `StepTypeWithBudget` (S1–S4), `Obligation_*` | **T1 + T4 (+T2)** | **GENUINE-GAIN** | THE home of the reflection unit: the block map = the coarse-graining `φ`; `TwoCellTheta.decrease` IS the additive `nstep-d` step (`scale=id`, defect `η_k`); S4 = the reflection-unit defect step. The tools land here verbatim. HONEST CAVEAT: the defect they price out (`η_k` = per-block RG loss) equi-inhabits `singleStep` — the gain is the correct T1 *framing/home*, not a new bound. |
| CharacterTailAntitone | `e^{−tΔ}` antitone in Casimir gap (`expNeg_scaled_antitone_leRat`) | **T2 modulus** | DEDUP/BOOKKEEPING | The per-step degradation as a monotone map of the gap = a genuine `scale`-mono INSTANCE; analytic, already proved. |
| CharacterTailMajorant | `Z_t ≤ ∏S_i − 1`, `finProd_one_add_mono`, `EtaGapMonotone` | T2 modulus | DEDUP/BOOKKEEPING | Product-of-factors monotone assembly = the multiplicative modulus of the tail; already proved. |
| EtaPackaging | `etaModel μ Z = μ·Z/(1−Z)`, **`etaModel_mono`**, `ZtEtaModel` | **T2** | **GENUINE-GAIN** | `etaModel_mono` is a CONCRETE `Lipschitz.scale`-mono witness (`Z↦η` monotone) — a ready-made `MonotoneModulus` instance the tools can consume directly. Cleanest T2 supplier in RG. |
| InductiveState | carried state `ℐ_k`, `Valid`, `StepType`, `ValidWitness` | T4/T6 trajectory | DEDUP/BOOKKEEPING | The trajectory STATE the fold transports; `StepType` = one evolution step. T6 monad candidate but defect-free (mismatch for magnitude). |
| PerAxisTail | polynomial×geometric per-axis tail `≤ B₀H^{d+1}` | T2/T5 | DEDUP/BOOKKEEPING | Per-axis modulus / island-tail closure; analytic. |
| PolylogTail | polylog `Σ(1+cn)^{2m}r^n` majorant, `recurrence_closure` | T5/T7 | DEDUP/BOOKKEEPING | Summable polylog tail = island cost-collapse (T5) + budget (T7); analytic. |
| RankCollapse | `(1+s)^r−1 ≤ 2rs`, `rank_collapse_of_sum` | T2 | DEDUP/BOOKKEEPING | Rank-general modulus linearization; analytic. |
| SigmaHatPilot | SU(2) pilot: concrete `η_max`, `eta_pilot_budget_closes` | T4/T7 instance | DEDUP/BOOKKEEPING | A concrete INSTANCE of the additive budget fold at pilot data; instance, not new tool. |
| SigmaHatPilotUV | genuine infinite-trajectory closure, `eta_pilot_uv = 0` | **T5 island** | DEDUP/BOOKKEEPING | `η≡0` deep-UV = the FREE ISLAND (cost collapses, defect 0) — a clean `island-free` instance, but already proved as such. |
| SUNWeylData | SU(N) fundamental-weight Casimir/gap data, `suN_C2_fundweight_gap_lb` | T2 input | N/A | Modulus INPUT (gap floor feeds the antitone modulus); rep-data. |
| TonelliFactor | reusable Tonelli `Z_t ≤ ∏S_i` (`csum2/3_prod_le`) | T3 | DEDUP/BOOKKEEPING | Factorization plumbing; supports the product modulus. |
| UniformBudget | uniform σ̂-budget monotonicity, `monotone_budget`, `qOver1mq_mono`, `truncatedConst_le` | **T2 + T4** | DEDUP/BOOKKEEPING | Monotonicity of the budget over the K-step window = `nstep-d` + `scale`-mono; SU(2)=worst-case reduction. Faithful match, already proved. |
| WeylCharacterBound | rank-general Weyl/heat-kernel tail, `one_add_sum_le_prod`, `AxisFactorBound` | T2/T3 | DEDUP/BOOKKEEPING | The `1+Σ ≤ ∏` step = the additive-vs-product modulus relation the tools formalize; analytic. |
| WeylDimGeneral, WeylDimGeneralData | crude squared-Weyl-dim majorant `≤ B^{2m}`, Cartan-type `numPosRoots` | T2 input | N/A | Dimension prefactor of the modulus; rep-data/combinatorics. |

## RepTheory/ (8 modules)

| module | role | tool(s) | verdict | note |
|---|---|---|---|---|
| CasimirData | per-type exact-ℚ Casimir/dual-Coxeter data, family floors | T2 input | N/A | Numeric modulus inputs pinning SU(2) worst-case. |
| RepData | group-invariant σ̂-closure interface, `budget_closes`, `ClosureCertificate` | T4 interface | DEDUP/BOOKKEEPING | The abstract per-group budget-fold interface; T4 shape but purely the conditional wrapper. |
| SimpleGroup | admissible simple-group interface, `gapFloor=3/4`, `AdmissibleSimpleGroup` | T2 input | N/A | Rep-theory lower-bound interface; modulus floor. |
| SU2 | SU(2) irreps, `fourTimesCasimir`, dimension | T2 input | N/A | Rep data (worst case). |
| SU3 | SU(3) irreps + two termwise tail inequalities | T2 input | N/A | Rep data. |
| Spin4 | `Spin(4)=SU(2)_L×SU(2)_R`, `spin4Gap_of_chiral` | — | N/A | O(4)-restoration finite reduction; orthogonal to defect/modulus. |
| Spin4Reflection | ℤ₂ chiral-reflection margin, `ModeInvolution`, `evenSector_margin_pos` | — | N/A | Finite parity margin; not codynamic. |
| LatticeAnisotropy | D₄/24-cell rotation-restoration invariant theory, `Q2_swap01` etc. | — | N/A | Finite invariant-theory crux for O(4); orthogonal. |

---

## Summary

### §A. The `Costs`/`MetricVal` instance suppliers (the concrete, defensible reuse)

The new codynamic tools require a `Costs` (ordered additive monoid with joins) and a
`MetricVal`. In THIS subtree they are already fully present and should be imported, not
rebuilt:

- **`Costs` over `Q'`** = **Rationals.lean** (carrier `Q'`; `0#`,`+#`,`≤#`; `≤#-refl`=`le_refl'`,
  `≤#-trans`=`le_trans'`; `+#-identityˡ`=`add_zero'`; `⊔#`=`max'` def) **+ RationalsMul.lean**
  (`+#-assoc`=`add_assoc_eqv`) **+ CRealAdd.lean** (`+#-mono`=`add_le_add`) **+
  RegularCRealArith.lean** (the join `lub` laws: `le_max'_left`, `le_max'_right`,
  `max'_le_iff'` = `⊔#-lub`, plus `runningMax_le_of_le` = the `maxOver`/`dAll` running-max).
  **The single most load-bearing pair is `Rationals.lean` + `RegularCRealArith.lean`** — the
  former is the additive-ordered base, the latter is the ONLY supplier of the join-semilattice
  (`⊔#`) laws the `dAll`/`maxOver` metric plumbing needs.
- **`MetricVal`** = **AbsQ.lean** (Q'-level `d=|·|`, `nonneg`, `abs_le` two-sided) and
  **CRealAbs.lean** (CReal `d`, `triangle`=`abs_add_le'`, `abs_le_of_bounds`).

### §B. GENUINE-GAIN nodes, ranked by value

1. **Rationals.lean + RegularCRealArith.lean** — supply the `Costs` instance (additive-ordered
   base + the join `lub` laws). Without these the tools have no cost object over `Q'`. Top value:
   this is the reuse that lets the tools exist in this codebase at all.
2. **AbsQ.lean / CRealAbs.lean** — supply the `MetricVal` (`d` + `triangle`). The metric the
   `unit-defect`/`εX` and `nstep-d` are defined against.
3. **BlockSpin.lean** — the T1 reflection-unit HOME: the block-spin map = the coarse-graining
   `φ`; `TwoCellTheta.decrease` (`σ_in−η_k ≤ σ_out`) IS the additive `nstep-d` step; S4 = the
   defect step. Genuine framing gain — BUT the defect priced out equi-inhabits `singleStep`
   (the wall), so it is a correct *home*, not a new bound. This is exactly the SITE-1 route
   the application-map flags as the sole ledger-legal attack surface.
4. **EtaPackaging.lean** — `etaModel_mono` is a ready-made concrete `MonotoneModulus`
   (`Lipschitz.scale`-mono) witness the tools can consume directly. Cleanest T2 instance.
5. **RationalsMul.lean, CRealAdd.lean** — supply `+#-assoc`/`+#-mono` (secondary Costs fields).

### §C. Honest verdict on uplift

No node in this subtree yields a *new* top-level reduction — consistent with the ledger and
the two codynamic-recast docs: composition/propagation is free (T2/T3/T4), the `2w³→2` wall
was a linear-modulus artifact, and the sole binding obstruction is the per-block DEFECT, which
is orthogonal to the modulus and equi-inhabits the atomic `singleStep`. Concretely in this
subtree:

- **Constructive/** is overwhelmingly the analytic substrate. Its genuine codynamic role is to
  **SUPPLY the `Costs`/`MetricVal` instance** (Rationals, RegularCRealArith, RationalsMul,
  CRealAdd, AbsQ, CRealAbs — GENUINE-GAIN as reuse). Everything else (exp/trig/sqrt/log/π/exp-law
  modules) is N/A or DEDUP: it is per-bound analytic content, not fold/defect/modulus structure.
  `RationalTail.sigma_hat_budget_closure` is the one non-Costs node that IS the additive
  `nstep-d`/`cert-budget` fold already, hand-rolled — a faithful T4+T7 match the tools would
  dedup, not extend.
- **RG/** is where T1/T2/T4 land: **BlockSpin** (T1 reflection unit + T4 step), **EtaPackaging**
  (T2 monotone-modulus witness), UniformBudget/CharacterTail* (T2 tail moduli), SigmaHatPilotUV
  (T5 free island). All are correct *placements* of the tools, but every one is either already
  proved (DEDUP) or prices the `singleStep`-equivalent defect (BlockSpin) — no F-move.
- **RepTheory/** is N/A: rep-data / modulus inputs (Casimir floors pinning SU(2)) and the
  finite O(4)-restoration reductions (Spin4/LatticeAnisotropy), none carrying codynamic
  fold/defect/modulus structure.

**Net:** the tools should be BUILT ON `Rationals.lean` + `RegularCRealArith.lean` (Costs) and
`AbsQ.lean`/`CRealAbs.lean` (MetricVal), INSTANTIATED at `BlockSpin.TwoCellTheta`/
`EtaPackaging.etaModel_mono`, and pointed at the SITE-1 intra-block per-move decomposition of
`BlockSpin`'s `η_k` — the only ledger-legal (clause-b) attack. Uplift here is real reuse +
correct T1 framing, NOT a frontier-shrinking reduction.
