# Codynamic-tool UPLIFT survey — Continuum modules F–O (node-by-node)

**Scope.** All 184 `lean/YMGap/Continuum/[F-O]*.lean` modules, walked node-by-node
(header + main signatures, no full proofs). Read-only; no Lean touched.
**Date.** 2026-07-07. **Coverage.** 184/184 read, 0 skipped, 0 unreadable
(F = 51, G/H/I = 49, J/K/L/N = 35, M/O = 49).

**Tools.** T1 reflection-unit defect · T2 nonlinear monotone modulus · T3 compositional
error law · T4 n-step Grönwall fold · T5 islands (free/discrete/Gaussian) · T6 evolution
monad (defect-free) · T7 complexity-budget.

**Calibration (from `docs/codynamic-application-map-2026-07-07.md` + `-recast-`).** The ONLY
core-moving site is **SITE-1**: intra-block per-move/per-mode decomposition of the atomic
defect `singleStep` (`realδ_k ≤ 6(1−w)²`) into summable local-heat-kernel-move defects
(T1+T3+T4). The whole-gap Grönwall fold (T2/T4) is already hand-rolled twice
(`DefectGapRecursion` product + `InductiveBoundWitnessSystem` additive) — any fold/erosion/
summability module re-expresses proved content ⇒ **DEDUP**. T5 islands are borderline-genuine
*organizational*. T6/monad/GNS/OS/spectral/measure plumbing is defect-free ⇒ **MISMATCH/N/A**.
**Loop trap (applies to every GENUINE-GAIN below):** a per-move handle is only a legal
clause-(b) move if the per-move defect is certified *strictly weaker* AND `(⋀ per-move) →
singleStep` is proved; if the local defects merely re-sum to the same block object it
collapses back to `singleStep` (a forbidden loop).

---

## Batch F (51 modules)

| module | role (1 line) | applicable tool(s) | verdict | note |
|---|---|---|---|---|
| Favard | Favard 3-term-recurrence route to uniform-in-N heat-kernel Gram positivity (P_N nonneg-coeff) | — | N/A | Gram-determinant positivity (P_N wall), not a defect-fold surface. |
| FavardRec | closed form of Favard coefficient β_k via S_N²·P_N factorization | — | N/A | Recurrence-coefficient positivity, same P_N wall; no per-move defect. |
| FavardUniform | all-k telescoping induction for perfect-square factor S_N | — | N/A | Inductive determinant identity, not an RG-defect fold. |
| FCLimitContinuity | inner-product limit-continuity on the constructive GNS completion | — | N/A | GNS/pre-Hilbert plumbing; defect-free. |
| FCNormBoundLimit | operator norm-bound `‖f(T)x‖²≤M‖x‖²` as diagonal spectral limit | — | N/A | Spectral/GNS reconstruction plumbing. |
| FieldMeasureUrsell | config-space free-field measure + Mayer–Ursell tree-dom substrate | T5 | DEDUP/BOOKKEEPING | `freeConnected2=0` is one free-field zero-cost island instance, not the finite core. |
| FieldSpaceCluster | Bałaban field-space cluster expansion, per-k defect ≤ g⁴, summable | T4,T5 | DEDUP/BOOKKEEPING | Weak-coupling island + cluster-sum re-sum to the block form-preservation object. |
| FieldSpaceRenormalized | physDefect=afDefectSeq, accumContraction=∏(survival), singleStep alias | T4 | DEDUP/BOOKKEEPING | Explicit RG survival product = the already hand-rolled Grönwall fold. |
| FinEuclCompletionCoordsClose | inhabits RC^N completion coords, 1-Lipschitz coordinate projection | — | N/A | Completion/Hilbert plumbing; no defect fold. |
| FiniteProductFDDeriv | iterated C¹ product-rule finite-difference derivative combinator | — | MISMATCH | Defect-free derivative (DiffJTP) combinator; product rule ≠ defect composition. |
| FiniteSMarginWorstcase | reduces per-mode margin to one cross-ratio w²-monotonicity | T2 | DEDUP/BOOKKEEPING | Per-mode margin-ratio monotonicity, but re-collapses to same worst-case object. |
| FiniteSMarginWorstcaseProof | verdict: scout two-factor route is strict regression / uninhabited | — | MISMATCH | Refutation/audit module; no defect-fold surface. |
| FiniteVolume | interacting finite-volume expectation E_Λ as positive normalized functional | — | N/A | Bishop–Bridges measure/functional reconstruction; not a defect site. |
| FiniteVolumeGNS | finite-volume GNS space, Gram positivity, spectral-gap content | — | N/A | GNS/OS reconstruction plumbing. |
| FormPreservationCluster | Bałaban SingleCouplingFormPreservation via induced coupling 4w⁶ ≤ afDefect | T1,T3 | DEDUP/BOOKKEEPING | Per-step induced-coupling defect re-sums to block form-preservation; refuted at weak coupling. |
| FourDExistence | states the 4D continuum OS existence hypothesis as an explicit structure | — | N/A | The Clay hypothesis itself, assumed; OS/existence plumbing. |
| FPClusterIdentity | Fernández–Procacci connecting-cluster `≤` bound on off-diag correlator | T3 | DEDUP/BOOKKEEPING | Per-line rate in a KP majorant that re-sums; correlator decay, not singleStep decomp. |
| FullModeAssembly | composes per-mode envelope + Casimir moment into O((1−w)²), then product floor | T3,T4 | DEDUP/BOOKKEEPING | scalar→inv-square→summable→exp-product-floor chain = the already hand-rolled fold. |
| **FullModeQuadratic** | per-mode renormalized defect δ_s ≤ dimQ s·C₄(s)²·(1−w)², bond-move linked | T1,T2 | **GENUINE-GAIN** | Map-named per-mode quadratic SITE-1 handle; `modeDefect_one = bondMovingDeltaRen`. |
| FusionChannelIneq | per-channel (s=0,1,2) pure-Q' log-concavity inequalities | T2 | DEDUP/BOOKKEEPING | Per-channel algebraic lemmas feeding the box core; re-sum to same object. |
| FusionCoreInduction | N-induction of box log-concavity core, reduced to per-step CoreStep | T4 | DEDUP/BOOKKEEPING | Induction of one core (CoreStep refuted downstream); shape, not defect. |
| FusionCoreStepRoundA | proves CoreStep UNSATISFIABLE for N≥2; packages UniformBoxLogConcave | — | MISMATCH | Machine refutation of a dead route; no live defect handle. |
| FusionCoreStepRoundB | direct box Cauchy–Binet at N=5,6; packages UniformBoxQuadCertificate | — | DEDUP/BOOKKEEPING | Concrete instances + residual repackaging of the same box core. |
| FusionCoreStepRoundC | Gaussian magnitude atom coeffW super-log-concavity (factor-4 slack, all s) | T2 | DEDUP/BOOKKEEPING | Reusable per-mode magnitude atom but only factors the same box certificate. |
| FusionCoreStepRoundD | strand/Clebsch reindexing; splits QuadGershgorinClosure into A1/A2/A3 | — | DEDUP/BOOKKEEPING | Structural reduction/relabeling of one residual. |
| FusionCoreStepRoundE | Hankel rectangle log-concavity atom + per-pair minor positivity | T2 | DEDUP/BOOKKEEPING | Symbolic structural atom feeding the same TP₂ core. |
| FusionCoreStepRoundF | Andréief/Cauchy–Binet half-sum identity; closes common-range TP₂ | — | DEDUP/BOOKKEEPING | Algebraic identity + closure of a sub-residual; re-sums. |
| FusionCoreStepRoundG | discriminant engine reducing A3 to central-autoconv reserve δ≥ε²+2ε | T2 | DEDUP/BOOKKEEPING | Reduction to numeric reserve; per-mode geometric ratio re-sums. |
| FusionCoreStepRoundH | pins CentralAutoconvReserve to concrete H0auto/offAuto, proves decomp/nonneg | — | DEDUP/BOOKKEEPING | Concretizes + discharges finite fields of the same reserve residual. |
| FusionCoreStepRoundI | proves geometric shift-tail `dominate`; reduces to one reserve field | T5 | DEDUP/BOOKKEEPING | Geometric-tail domination (island-flavored) collapsing to same reserve. |
| FusionCoreStepRoundJ | diagonal (3/4) minor reserve atom + refutation of summand-wise route | — | DEDUP/BOOKKEEPING | Partial atom + machine correction on one residual. |
| FusionCoreStepRoundK | cross-strand localisation pinning where the reserve wall lives | — | DEDUP/BOOKKEEPING | Localization/relabel of the sole reserve residual. |
| FusionCoreStepRoundL | reserveM quadratic form; REFUTES Gershgorin/PSD closure routes | — | MISMATCH | Decisive refutation of matrix-PSD routes; dead-route pruning. |
| FusionCoreStepRoundM | exact Gaussian factorization reducing reserve to w-free coupling Turán | — | DEDUP/BOOKKEEPING | Re-expression isolating the reserve constant; same residual, new variable. |
| FusionGenFunction | gen-function reduction of s=1-dominance to heat-kernel log-concavity | T2 | DEDUP/BOOKKEEPING | Spectral peak-shape (unimodality) reduction, not defect magnitude. |
| **FusionKernelStatement** | discrete SU(2) fusion local-CLT residual in saddle form, wired to δ-loop; p=1 proved | T1,T2 | **GENUINE-GAIN** | Per-mode saddle eigenvalue-shift defect (bulk_shift≤1/12) on the binding δ-loop path. |
| FusionLogConcave | log-concave ⇒ unimodal ⇒ s=1-dominance implication | T2 | DEDUP/BOOKKEEPING | Structural unimodality plumbing; shape, not defect. |
| FusionMarginMono | discharges FusionMarginTailMonotone; physMargin monotone, floor unconditional | T2 | DEDUP/BOOKKEEPING | Monotone-margin fold re-summing to the dominant-mode floor. |
| FusionMarginMonotone | tilted first-moment retarget of cross-ratio monotonicity; refutes PF₂/MLR | T2 | DEDUP/BOOKKEEPING | Reduction to first-moment convexity (local-CLT datum); same residual. |
| FusionMarginScope | delimits scope of gap=1−leading-coeff margin (zero-crossing boundary) | — | MISMATCH | Scope-confirmation module; no defect content. |
| FusionPositivity | coefficientwise monotonicity of bond-moving fusion map (positive domination) | T2 | DEDUP/BOOKKEEPING | Monotonicity engine enabling per-mode envelope domination; not itself a defect. |
| FusionQuotientCollapse | quotient-collapse denominator anchor `fusion zeroCoeff = Zsum²` for n=2 | — | DEDUP/BOOKKEEPING | Vacuum-denominator support lemma for the same quotient defect. |
| FusionRDFactor | exact (r,d) factorization of p=2 self-fusion coefficient; σ=√ lever | — | DEDUP/BOOKKEEPING | Exact re-expression of one fusion coefficient; a local-CLT lever, not a new defect. |
| FusionResidualBound | genuine bond-moving fusion residual, per-mode quadratic frontier | T1 | DEDUP/BOOKKEEPING | `residualModeDefect = modeDefect` — same object as FullModeQuadratic, re-expressed. |
| FusionSaddleReduction | reduces p=2 bulkShiftBound onto Tier-0 curvature via two bridge residuals | T2 | DEDUP/BOOKKEEPING | Bridge/reduction of one shift residual onto an existing curvature datum. |
| FusionShiftMonotone | p-index monotonicity collapsing {bulkShiftBound_p}_{p≥2} onto p=2 | T2 | DEDUP/BOOKKEEPING | Telescoping collapse of a p-family = a fold on one new single-step atom. |
| FusionUTuranEnvelope | four elementary envelope bounds + finite geometric-sum lemma for coupling Turán | T5 | DEDUP/BOOKKEEPING | Finite geometric envelope algebra feeding the same Turán residual. |
| FusionUTuranFiniteS | finite-S truncated coupling Turán; general-w FiniteSMargin inhabitant | — | DEDUP/BOOKKEEPING | Sharper truncation of the same reserve residual. |
| FusionUTuranReindex | Q=1/w² inverse reindexing carrying Turán → reserve; inhabits SymMinorGershgorin | — | DEDUP/BOOKKEEPING | Variable-change bookkeeping between two forms of one residual. |
| FusionUTuranTrunc | truncated w-free coupling Turán, uniform-in-s | — | DEDUP/BOOKKEEPING | Reduction of the same reserve to a truncated inequality. |
| FusionUTuranWFree | w-free coupling Turán; refutes "transcendental" verdict (θ² cancels) | — | DEDUP/BOOKKEEPING | Simplification (theta cancels) of the same residual to leading-shell capture. |

## Batch G/H/I (49 modules)

| module | role (1 line) | applicable tool(s) | verdict | note |
|---|---|---|---|---|
| GapIsEigenvalue | resolves δ-loop: lattice gap = multiplicity-blind transfer eigenvalue, not weighted coeff | — | N/A | spectral gap-definition plumbing, no defect-fold surface. |
| GapStability | topological/integer `belowCount` gap protection, stability only | T6 | MISMATCH | explicitly magnitude-blind (integer invariant can't see margin shrink). |
| GaussQBinom | Gauss q-binomial finite identity for the theta Gaussian weight | — | N/A | pure finite combinatorial algebra. |
| GenuineClusterBound | clustering rate `sep=ρ=2w³` from proved correlator decay → located gap | — | N/A | OS/clustering→gap reconstruction, not a per-step defect fold. |
| GenuineCorrLink | ties real Wilson correlator to abstract clustering rate by domination | — | N/A | correlator-link OS plumbing. |
| GenuineKP | KP polymer-sum bound carried by genuine lattice-animal count | T7 | DEDUP/BOOKKEEPING | summable polymer count-budget, already covered by summability machinery. |
| GenuineResidualDefect | DEPRECATED per-mode relative-residual defect (found linear, route false) | T1 | MISMATCH | per-mode defect refuted (O(1−w) not quadratic ⇒ AF sum diverges); lemmas only. |
| GNSComplete | metric completeness of GNS completion (Cantor diagonal) | — | N/A | Hilbert-space plumbing. |
| GNSCompletion | CReal metric completion of GNS pre-Hilbert quotient | — | N/A | Hilbert-space plumbing. |
| GNSDynamics | transfer/time-translation operator + reconstructed-gap interface | T6 | N/A | evolution/dynamics + spectral plumbing, defect-free. |
| GNSHamiltonian | `H=−log T` eigenvalue-level gap interface | — | N/A | spectral/log plumbing. |
| GNSHilbertSpace | CReal-valued inner product on the completion | — | N/A | Hilbert-space plumbing. |
| GNSQuotient | GNS quotient `V/Radical` pre-Hilbert space | — | N/A | Hilbert-space plumbing. |
| **GradedBondMovingBudget** | C₄-graded (H⁻² Sobolev) per-mode bond-moving defect, uniform quadratic, summable | T1,T3,T4 | **GENUINE-GAIN** | Exposes per-mode graded defect `gradedDefect≤(1−w)²` as an independent strictly-weaker SITE-1 handle. |
| GramReduction | Gram PSD ⟸ functional positivity, uniform in N | — | N/A | moment-PSD plumbing. |
| GramReduction3 | N=3 Gram-form PSD via LDLᵀ | — | N/A | moment-PSD plumbing. |
| H4RotationAuto | O(4) rotation `*`-automorphism + anisotropy defect | T1,T2 | MISMATCH | symmetry-restoration defect, not the gap/reflection-unit defect. |
| HaarClassIntegral | SU(2) class-function Haar integral + character orthogonality | — | N/A | analytic-primitive plumbing. |
| HaddDischarge | wiring seam installing proved `hadd` into `SpectralMarginInput` | T4 | DEDUP/BOOKKEEPING | margin-recursion wiring, fold already hand-rolled. |
| HamiltonianAllSep | `Δ=−log sep` unconditional in the separator | — | N/A | spectral/log plumbing. |
| HamiltonianScalar | scalar-linearity brick + spectral-resolution bridge | — | N/A | Hilbert/spectral plumbing. |
| HamiltonianSpectrumInf | spectrum-inf = located gap at top excited eigenvalue | — | N/A | spectral plumbing. |
| HbridgeInputs | pinned `hbridge` feeds (`hLin` schedule / `hId` open) + summability tension | T4,T7 | DEDUP/BOOKKEEPING | shift/defect schedule + honest harmonic-divergence bookkeeping. |
| HdconvClose | split theta `Hdconv` into convergence + identity halves | — | MISMATCH | analytic C¹ double-limit interchange (theta K_t wall), off-path, no defect fold. |
| HdconvReroute | cancel shared Θ, isolate coefficient identity | — | MISMATCH | theta analytic identity, no defect fold. |
| HeatKernelConv | S-factor as convergent CReal (small `a`) | — | N/A | analytic heat-kernel positivity construction. |
| HeatKernelConvGen | S-factor lifted to all `a∈(0,1)` | — | N/A | analytic positivity construction. |
| HeatKernelCurvature | free diagonal generator `CD(K=3/4)` curvature magnitude | T5 | MISMATCH | curvature = separate magnitude route (free anchor), orthogonal to defect fold. |
| HeatKernelGap | closed-form transfer gap `sep=w³` | — | N/A | spectral gap construction. |
| HeatKernelGaussNode | CReal Gauss-node quadrature for `t>0` off-diag OS2 | — | N/A | moment-PSD/OS2 plumbing. |
| HeatKernelGramSOS | positive-weight Gram/SOS witness for off-diag OS2 | — | N/A | moment-matrix PSD plumbing. |
| HeatKernelLinearBound | reduce cubic `1−w³` margin to linear `1−w` | — | N/A | spectral margin algebra, no defect surface. |
| HeatKernelNodeQuad | inhabit off-diag OS2 `NodeQuadrature` (δ_e, atomic) | — | N/A | moment-PSD plumbing. |
| HeatKernelPersistence | continuum-gap obligation made concrete in `1−w³` | — | N/A | spectral gap reduction. |
| HeatKernelPos | pointwise SU(2) heat-kernel positivity, termwise algebra | — | N/A | analytic Bochner/Jacobi positivity. |
| HeatKernelPos2 | CReal positive object `R=Θ·S` | — | N/A | analytic positivity. |
| HeatKernelRGStep | one MK block step: exact decimation + bond-moving residual | T1,T3,T5 | MISMATCH | block-level split (not intra-block per-move); decimation-island dup of HierarchicalGap, bond-moving uncontrolled on ℝ⁴. |
| **HeatKernelSecondCumulant** | per-channel 2nd cumulant `chanCumulant(s,w)`, ch-1 = atomic bond-moving defect | T1,T3 | **GENUINE-GAIN** | per-mode second-cumulant defect, quadratic `≤6(1−w)²`, identified with the `singleStep` atom (SITE-1). |
| **HierarchicalGap** | δ=0 exact decimation-line unconditional continuum gap | T5 | **GENUINE-GAIN** | reusable free/exact zero-defect island (cost-collapse); honestly not 4D. |
| HinRunningCapClose | inhabit theta-product running-cap bundle | T4 | DEDUP/BOOKKEEPING | running-cap accumulation (telescope), theta off-path. |
| HptProductPtwiseClose | theta product-pointwise R1, compact-region retype | — | MISMATCH | theta analytic, off-path, no defect fold. |
| InstantonDiluteGas | instanton density IR-divergent; large-ρ tail = confinement = singleStep | T5 | MISMATCH | small-inst island convergent but large-inst IR = `singleStep` core; no cost-collapse. |
| InteractingMeasureReduction | connect 2 open measure fields to Penrose + telescoping erosion budget | T4,T7 | DEDUP/BOOKKEEPING | additive block-spin erosion `ε_k` budget + Wick-tree; connects, doesn't close. |
| **InteractingMFoldDefect** | exact m-fold fusion defect: `2−ρ_m=(6/m)ε` concentrates, remainder `O((1−w)⁴)` | T3 | **GENUINE-GAIN** | compositional finding — parallel bond-moving defect concentrates (refutes linear-in-m), strictly-weaker quartic handle. |
| InteractingSinglePolymerMeasure | non-Gaussian `z₁`: fixed-spacing definite `≤4w³` clears KP; continuum = singleStep | T5 | MISMATCH | fixed-spacing island genuine but continuum `z₁` = `singleStep` core. |
| InterchangeViaEngine | engine route to theta interchange given `Hdconv` | — | MISMATCH | theta double-limit interchange (relocates, not closes), off-path. |
| IRRegulatorAnalyticity | IR cutoff removes renormalon pole; verdict reduces to singleStep | — | MISMATCH | analyticity/dispersion probe reducing to `singleStep` core. |
| **IsserlisGaussianBase** | genuine Isserlis Gaussian base (`⟨x⁴⟩=3s⁴`), determines `z_n` finite-order, refutes free dodge | T5 | **GENUINE-GAIN** | reusable free-Wick/Gaussian reference island; finite-order only, resummation + a→0 continuum open. |
| IsserlisPenroseReduction | reduce `isserlisBound` via proved Penrose `|C(G)|≤τ(G)` to `pertRep` | T5,T7 | DEDUP/BOOKKEEPING | signed-Ursell tree-domination + count-budget reduction wrapper. |

## Batch J/K/L/N (35 modules)

| module | role (1 line) | applicable tool(s) | verdict | note |
|---|---|---|---|---|
| JacobiFactorFDDeriv | per-factor `FDDerivDataC` for the Jacobi theta product via quadratic-FD modulus | T4/T7 | DEDUP/BOOKKEEPING | Summable per-factor budget re-expresses the hand-rolled geometric fold; off OS2 path (Wall-2). |
| JacobiQuadResidualClose | CReal cosine addition law + `|cos|,|sin|≤1` amplitude bounds | — | MISMATCH | Pure trig identities/amplitude bounds; analytic identity, no defect surface. |
| JTPIdentity | differentiated-JTP residual: `Σ(n+1)²aⁿ²` geometric majorant + conditional `Kt≥0` | T4/T7 | DEDUP/BOOKKEEPING | Quadratic-geometric summability majorant = summability fold already hand-rolled. |
| JTPInstance | concrete per-factor M_k / N(ε) equicontinuity moduli for theta C¹-limit engine | T4/T7 | DEDUP/BOOKKEEPING | Per-factor geometric-tail modulus = same summable budget; no strictly-weaker handle. |
| KPCriterion | single-rep Haar collapse + Kotecký–Preiss criterion conditional on cluster-count | T4/T5 | DEDUP/BOOKKEEPING | KP convergence is a geometric summability fold; single-rep collapse is structural. |
| KPFieldAmplitude | KP amplitude `|z_n|≤(μg²)ⁿ` via Penrose tree, reduced to scalar `z_1≤g²` | T4/T5 | DEDUP/BOOKKEEPING | Termwise geometric cluster domination = fold; tool re-expresses summability. |
| KPIncrement | per-step increment `|S(Λ+1)−SΛ|≤aΛ` with geometric decay | T2/T4 | DEDUP/BOOKKEEPING | Textbook per-step geometric erosion — exactly the hand-rolled increment content. |
| KPLimit | engine turning geometric increment bound into a CReal limit with Cauchy modulus | T4 | DEDUP/BOOKKEEPING | This IS the geometric-tail→limit fold engine; tool would merely rename it. |
| KreinOS | Krein indefinite-metric OS reconstruction → positive physical sector + gap | — | N/A | Reconstruction/spectral plumbing; defect-free. |
| LaplaceMarginDeep | ρ=w² sharpening of theta-weight autoconvolution super-log-concavity (Hankel) | — | MISMATCH | Structural log-concavity inequality (R1), no reflection-unit-defect surface. |
| LaplaceRenormalonSelfSimilar | identifies Borel/Laplace renormalon ambiguity with self-similar condensate Λ | T6 | MISMATCH | Self-similar flow with conserved invariant but carries magnitude; defect-free. |
| LargeFieldSuppression | exponential large-field suppression → geometric-summable budget + additive erosion floor | T5/T4 | DEDUP/BOOKKEEPING | T5-flavored but content is a geometric budget/summability fold, not a free-boundary collapse. |
| LeakGeoDecay | runs Andréief half-sum identity backward → Gershgorin ⇔ single scalar reserve | — | MISMATCH | Determinant/log-concavity equivalence (R1); refutes leak route, no defect fold. |
| LGVPositivity | uniform-in-N column nonnegativity of `P_N=Δ_N/S_N²` (LGV) | — | MISMATCH | P_N-wall polynomial coefficient positivity; algebraic, off-path. |
| LinearTransferOperator | operator-linearity/diagonal-symbol layer of T on GNS completion (`|λ_i|≤1`) | — | N/A | Transfer-operator spectral plumbing; defect-free contraction. |
| LineSumLogConcave | reindexes antidiagonal line-sum log-concavity into a shift-family, reduces to one residual | T5 (watch) | DEDUP/BOOKKEEPING | SITE-1-flavored, but per-pair atoms merely re-sum to the block target → LOOP → dedup. |
| LocalCLTSteepestDescent | adjacent-band nonnegativity of symMinor, locates indefiniteness to `|m−n|≥2` tail | T1/T3 (watch) | DEDUP/BOOKKEEPING | Closest SITE-1 candidate, but bands re-sum, needs aggregate cancellation; object is R1 log-concavity not δ_k. |
| LocalCurvatureFields | typed curvature-word grammar + local-operator interfaces (stress/OPE) on a ProbFunctional | — | N/A | Finite operator-content grammar/existence hypothesis; no defect-fold surface. |
| LocatedBracketGen | discharges two Lipschitz fields of `LocatedBracketM` for all M via Markov majorant | — | N/A | Located-root/off-diag OS2 plumbing; reduces to RootEnclosure. |
| LocatedNodeDataGen | inhabits `LocatedNodeData M` by bisection + T-sign (general-M off-diag OS2) | — | N/A | Located-node spectral plumbing; residual is a decidable bracket. |
| LocatedReconstruction | located strict finite-volume gap (`sep<1`) on OS-reconstruction datum | — | N/A | Located/spectral reconstruction plumbing. |
| LocatedSpectralGap | located 2nd-eigenvalue gap of the compact finite transfer operator | — | N/A | Constructive-spectral plumbing; magnitude, no defect composition. |
| LogDerivSumCReal | sum-side log-derivative limit `S'` as base-q² geometric-modulus CReal | T4 | DEDUP/BOOKKEEPING | Per-term geometric increment = geometric summability fold (Wall-2), hand-rolled. |
| LoopyCorrelatorBound | off-diag multi-plaquette correlator decay (Fernández–Procacci) + residual reduction | T5/T4 | DEDUP/BOOKKEEPING | Connecting-cluster geometric decay = summability fold; no defect handle. |
| LoopyCorrelatorProgress | multi-loop Mayer/Ursell: loops add edges not nodes ⇒ decay rate unchanged | T5/T4 | DEDUP/BOOKKEEPING | Rep-pinning collapse + geometric decay; no per-move strictly-weaker defect. |
| LoopyLinkIntegral | m-fold shared-link Haar integral; m=3 triple-character fusion `∫χχχ=N_{abc}` | — | MISMATCH | Character/fusion-multiplicity algebra; multilink but no defect-fold surface. |
| LProductFactorClose | factorises log-derivative limit through the shared theta factor | — | MISMATCH | CReal ring-regrouping identity + residual naming; no summability/defect content. |
| NetDriftBudgetSplit | splits total additive-erosion budget at crossover K into finite window + 1/k² tail | T4/T7 | DEDUP/BOOKKEEPING | Explicit NetDrift budget-split — tool re-expresses the hand-rolled additive Σδ budget. |
| NetDriftInvSqBudget | derives Σδ budget from `δ_k≤D/(k+1)²` via `Σ1/(k+1)²≤2` telescope | T4/T5/T7 | DEDUP/BOOKKEEPING | AF 1/k² tail is a T5-island fact but the fold is the hand-rolled additive budget. |
| NewtonRecurrence | finite Newton/U-power-sum telescoping recurrence closing Wall-1 Gram PSD | — | MISMATCH | Finite Chebyshev power-sum algebra; defect-free identity, no composition. |
| NonAbelianGapChain | Route-B conditional chain: susceptibility→per-scale rate→dynamic⇒static | T4 | DEDUP/BOOKKEEPING | Reuses the hand-rolled product/Weierstrass floor; remainder is assembly. |
| NonpertActivityHeatKernel | non-perturbative test of `z_1` vs entire Wilson heat kernel `e^{−(3/4)t}` | — | MISMATCH | Analytic-magnitude activity test/refutation; defect-free, no fold. |
| NonSaturatedFloor | non-degenerate located gap at `sep=1−mFiducial` via √-bridge fiducial | — | N/A | Located-spectral + fiducial plumbing; magnitude witness, no defect surface. |
| Nontriviality | dimensional-transmutation criterion: interacting ⟺ Λ has positive finite continuum limit | T6 | MISMATCH | RG-invariant-scale existence dichotomy; defect-free flow, magnitude≠composition. |
| NormExcitedDrift | concrete `RGCoeffStep` from fusion-derived normalized excited coeff `E(w)=2c₁` | T1/T2 | DEDUP/BOOKKEEPING | Gives δ_k as one dominant-mode margin, not a per-move decomposition; re-expresses defect recursion. |

## Batch M/O (49 modules)

| module | role (1 line) | applicable tool(s) | verdict | note |
|---|---|---|---|---|
| MarkovLukacs | SOS/Positivstellensatz producer for `[−1,1]` heat-kernel-average positivity | — | N/A | Polynomial nonnegativity certificate producer; OS-positivity-adjacent, not a defect fold. |
| MatchedRetune | p=2 self-fusion per-mode matched-retune carrier + `∏(1+δ)` engine | T4 (T2) | DEDUP/BOOKKEEPING | Per-mode quotient telescoping fold; `∏(1+δ_k)`/`Σδ` already hand-rolled. |
| MatchedRetuneBridge | cube-root carrier inhabitation + rational-bracket bridge | — | N/A | Constructive CReal cube-root/bracket plumbing; analytic, no defect content. |
| MatchedRetuneFrontier | per-mode local-CLT step δ_k dominance + derivative telescoping into fusion quotient | T1/T3/T4 | DEDUP/BOOKKEEPING | Per-mode increment decomposition, but telescopes back to the SAME p=2 quotient — re-sum. |
| MayerBridgeDecomposition | z4 Mayer–Ursell bridge = KP connecting-cluster resummation reduction | T4/T7 | DEDUP/BOOKKEEPING | KP/Mayer cluster-span sum = summability fold. |
| MayerClustering | Mayer clustering bound + KP geometric tail → located gap | T4/T7 | DEDUP/BOOKKEEPING | KP geometric-tail summability fold; convergence engine already in the tree. |
| MayerTwoPlaquette | two-plaquette shared-link Haar-orthogonality diagonal collapse | T5 (flavor) | MISMATCH | Discrete Haar-orthogonality collapse (off-diag→0); structural, not a per-step defect fold. |
| MayerUrsellZ4 | z4 Mayer–Ursell verified reduction + d=0 unsat obstruction | T4 | DEDUP/BOOKKEEPING | Mayer/KP reduction to two named atoms; summability bookkeeping. |
| MayerUrsellZ4Restated | vacuum-normalized non-degenerate restatement of the z4 identity | T4 | DEDUP/BOOKKEEPING | Same KP atoms, diagonal renormalized. |
| MeanComplementClose | Casimir ledger + antidiagonal-variance curvature floor `Δ²⟨D²⟩≥−2` | — | MISMATCH | Local-CLT first-moment/variance-curvature magnitude; analytic. |
| MeanComplementCovariance | exact antidiagonal-variance covariance moment identity | — | MISMATCH | Exact moment identity recast; analytic magnitude, not a defect site. |
| MeanComplementLogConcave | line-sum log-concavity curvature-floor recast of the complement half | — | MISMATCH | Log-concavity/mean-curvature magnitude; analytic, no defect fold. |
| MeanExpConvexProgress | Casimir-normalized mean-exponent convexity reduction | — | MISMATCH | Midpoint mean-convexity magnitude; analytic, not composition. |
| MeanToCrossRatioClose | constructive FTC/increasing-function cross-ratio skeleton | — | MISMATCH | Monotone-function/FTC skeleton for first-moment gap; analytic, not RG degradation. |
| MeasureTransfer | OSforGFF cylinder→continuum measure transfer + Minlos lift | — | N/A | σ-additive measure-construction plumbing; not a defect. |
| MiddleClusteringFloor | 3-step `∏(1−δ)` character-clustering middle floor | T4/T5 | DEDUP/BOOKKEEPING | Finite 3-step survival product of proved clustering margins; a T4 fold instance. |
| **MKBondMovingControl** | MK per-bond-move defect ≤6(1−w)² + concentration; real-4D transfer assessment | T1/T3/T4/T5 | **GENUINE-GAIN** | Canonical SITE-1: the literal per-bond-move sequence where T1+T3+T4+T5 attach. CAVEAT: its own `mkVariational_bounds_freeEnergy_not_gapDefect` proves Jensen bounds FREE ENERGY not the gap defect; real-4D↔MK gap-defect transfer ≡ `singleStep`, still open. |
| MomentBridge | moment→Gram PSD bridge (`MomentSquarePos`) | — | N/A | OS2 moment-square PSD plumbing. |
| MomentIntegralPSD | all-order Gram PSD via R-projection + SOS moment-integral | — | N/A | Wall-1 all-order moment PSD; positivity, no defect content. |
| MomentMatrixPSD | moment-matrix-of-positive-measure PSD (Gauss node quadrature) | — | N/A | Off-diag OS2 moment-matrix PSD; positivity plumbing. |
| MomentPositivity | uniform-in-N heat-kernel Gram PSD (`S²·P_N` factorization) | — | N/A | Wall-1 uniform PSD certificate. |
| MomentSquarePSD | all-order `E(q²)≥0` assembly + finite-order LDLᵀ | — | N/A | OS2 Gram PSD; positivity plumbing. |
| MooreOsgoodB2 | arctan↔trig iterated double-limit interchange (B2) | T6 (mismatch) | MISMATCH | Analytic Moore–Osgood double-limit; defect-free analytic atom, not a fold site. |
| MovingCutoff | w-uniform scaled Casimir-square moment (moving cutoff, probabilistic) | — | MISMATCH | Analytic Gaussian-moment magnitude bound; moving cutoff is analytic. |
| MovingWindowEdgeClose | theta TP2 2×2-minor moving-window edge reconciliation | — | N/A | Total-positivity/theta minor reconciliation; OS2-adjacent bookkeeping, not a defect fold. |
| MulCombinatorClose | binary finite-difference C¹ product-rule combinator | — | MISMATCH | Constructive C¹ product-rule remainder; analytic derivative combinator, not an RG fold. |
| MultiComponentFactorization | disconnected joint correlator factorizes ⇒ Ursell cross-term ≡0 | T5 (flavor) | MISMATCH | Disconnected-region zero connected correlator (island-flavored) but a factorization theorem, not the RG defect. |
| MultiComponentKPProgress | Penrose–Ursell KP connecting-cluster re-factor + refutation | T4 | DEDUP/BOOKKEEPING | KP reduction/refutation; summability fold bookkeeping. |
| **MultiLinkFusionDefect** | direct m-fold SU(2) fusion defect ρ_m + sub-additivity/concentration ρ_m/m↓ | T4/T5 | **GENUINE-GAIN** | Route-C per-link fusion defect: log-concavity concentration puts ρ_m STRICTLY below naive `m·ρ_1` — a strictly-weaker-than-linear independent per-link island (T5 concentration beating T4 additive). |
| MultiPlaquetteMayer | branching-tree connected correlator collapse + geometric decay `ρ^{nodes}` | T4/T7 | DEDUP/BOOKKEEPING | Geometry-census correlator geometric decay; accumulation fold feeding clustering. |
| MultiScalePolymerAssembly | Bałaban multi-scale `∏(1−δ_k)` polymer product + summability floor | T4/T7 | DEDUP/BOOKKEEPING | The literal T4 Grönwall fold (already hand-rolled twice); isolates `singleStep` as input — assembly bookkeeping. |
| O4BetaSign | `betaDrop_nonneg` from AF sign β>0 (antitone trajectory) | T2 (flavor) | N/A | O(4) symmetry-restoration AF monotone flow; symmetry plumbing, not a gap-defect fold. |
| O4ClauseStrength | named non-trivial anisotropy defect for O(4) restoration | — | N/A | O(4) symmetry-restoration *-hom/anisotropy witness; symmetry plumbing. |
| O4DecayFromMargin | O(4) decay ratio ρ=blockRatio^margin from 24-cell degree margin | T2/T4 (flavor) | N/A | Geometric per-step contraction of the symmetry-breaking coeff; not the RG gap defect. |
| O4H4Homomorphism | AF trajectory-certificate → `betaDrop_nonneg` bridge | T2 (flavor) | N/A | O(4) restoration AF monotone-drop bridge; symmetry plumbing. |
| O4RestorationAF | AF geometric decay of breaking coefficient → RotationRestored | T4 (flavor) | N/A | Geometric decay of O(4)-breaking coeff; symmetry-restoration, not defect fold. |
| O4RestorationH4 | decay-to-zero strengthening + Clay-clause wiring | T4 (flavor) | N/A | O(4) restoration limit=0 wiring; symmetry plumbing. |
| O4RestorationH4Invariant | genuine H₄ axis-swap *-automorphism + functional invariance | — | N/A | H₄ symmetry *-automorphism; symmetry plumbing, no defect. |
| O4RestorationProgress | DimensionlessFlow / CouplingRunning monotone AF flow | T2 (flavor) | N/A | AF dimensionless monotone flow for O(4); not the gap defect. |
| O4RestorationReduction | OS1 (H₄ invariance + O4 clause) fired from one input | — | N/A | OS1/O(4) statement-layer symmetry plumbing. |
| ObservableMeasure | `ProbFunctional` positive normalized functional + `restrict` coarsening | — | N/A | Riesz/moment functional measure representation; measure/OS plumbing. |
| OffDiagShift | off-diagonal power-sum collapse `S_p=S_{p+2}` (Newton/Chebyshev) → Wall-1 PSD | — | N/A | Chebyshev-U orthogonality / Newton recurrence for Wall-1 Gram PSD; positivity plumbing. |
| OPECondensatePositivity | OPE condensate positivity sign-fixing the renormalon → singleStep | T6 (mismatch) | MISMATCH | Self-similar condensate magnitude/positivity; reduces to `singleStep` — magnitude≠composition. |
| OSAxiomAudit | OS-axiom GJ↔OS numbering cross-walk audit | — | N/A | OS-axiom cross-walk documentation/plumbing. |
| OSAxioms | OS axioms (reflection positivity, cluster) content interface | — | N/A | OS-axiom predicate interface; positivity plumbing. |
| OSConfinementAssessment | OS-reconstruction/confinement (area-law) route assessment → singleStep | — | N/A | OS/area-law route assessment reducing to `singleStep`; not a defect fold. |
| OSContent | OS-reconstruction finite-volume content + located gap | — | N/A | OS reconstruction finite-vol predicates/located gap; spectral plumbing. |
| OSReconstruction | OS reconstruction Hilbert/Hamiltonian type interface (paper-level) | T6 (mismatch) | N/A | Stone/spectral reconstruction interface; defect-free spectral plumbing. |
| OSReconstructionProgress | GNS pre-Hilbert Cauchy–Schwarz layer from OS2 positivity | — | N/A | Pre-inner-product Cauchy–Schwarz from reflection positivity; positivity plumbing. |

---

## Summary — GENUINE-GAIN nodes ranked by value

**Tally (184 nodes):** GENUINE-GAIN = 9 · DEDUP/BOOKKEEPING = 67 · MISMATCH = 34 · N/A = 74.

Every GENUINE-GAIN below is gated by the same ledger clause-(b) test: a legal core-move
ONLY if the per-move/per-mode defect is certified *strictly weaker* than the block defect
AND `(⋀ per-move) → singleStep` is proved. None discharges `singleStep` on its own; they are
the *materials* for the one legal SITE-1 attack.

### Tier A — SITE-1 intra-block per-move/per-mode defect candidates (the only core-movers)

1. **MKBondMovingControl** (M) — `T1/T3/T4/T5`. The **canonical SITE-1 object**: the literal
   Migdal–Kadanoff per-bond-move sequence, with `mkDefect_le_sixQuad` (per-move δ ≤ 6(1−w)²)
   and `mkFusion_concentration`. This is exactly the "decimation ∘ bond-moving, bond-moving =
   finite sequence of local moves" decomposition the application-map names as the highest-value
   site. **Sharpest honest caveat of the whole survey:** the module's own
   `mkVariational_bounds_freeEnergy_not_gapDefect` proves the Jensen/variational bound controls
   FREE ENERGY, not the gap defect — the real-4D ↔ MK gap-defect transfer is still ≡ `singleStep`.
   The per-move handle is real but does not by itself cross the binding residual.

2. **GradedBondMovingBudget** (G) — `T1/T3/T4`. Cleanest "independent strictly-weaker per-mode
   handle" claim: a C₄-graded (H⁻² Sobolev) per-mode bond-moving defect proved uniform-quadratic
   `gradedDefect ≤ (1−w)²` and summable. The grading is the concrete device that could make the
   per-mode pieces *independent* (not merely re-summing) — the most promising Lean substrate for
   the SITE-1 fold.

3. **HeatKernelSecondCumulant** (H) — `T1/T3`. Per-channel 2nd cumulant `chanCumulant(s,w)` with
   channel-1 = the atomic bond-moving defect, proved quadratic `≤ 6(1−w)²` and *identified with
   the `singleStep` atom*. A genuine single-local-heat-kernel per-mode object — but the explicit
   identification with `singleStep` is also the loop-risk flag (may re-sum to the same object).

4. **FullModeQuadratic** (F) — `T1/T2`. Map-named per-mode quadratic envelope
   `δ_s ≤ dimQ s·C₄(s)²·(1−w)²` with `modeDefect_one = bondMovingDeltaRen`. The per-mode envelope
   the application-map explicitly says SITE-1 "would reuse." (Note `FusionResidualBound` is the
   same object re-expressed — DEDUP.)

5. **FusionKernelStatement** (F) — `T1/T2`. Per-mode saddle eigenvalue-shift defect
   `bulk_shift ≤ 1/12`, wired to the binding δ-loop (p=1 proved). On the critical path; the defect
   is a genuine single-mode object but the p≥2 residual is the live wall.

### Tier B — compositional/concentration finding (strictly-weaker-than-linear teeth)

6. **MultiLinkFusionDefect** (M) — `T4/T5`. Direct m-fold SU(2) fusion defect with
   `ρ_m/m ↓` (log-concavity concentration puts `ρ_m` **strictly below** the naive additive
   `m·ρ_1`). This is the one place where a T5-concentration *beats* the T4 additive budget — the
   genuine mathematical content behind "product beats additive," and the strongest evidence that
   the per-link pieces are strictly weaker rather than re-summing.

7. **InteractingMFoldDefect** (I) — `T3`. Exact m-fold defect `2−ρ_m = (6/m)ε` concentrates with
   remainder `O((1−w)⁴)`; refutes the linear-in-m renormalon wall. Compositional-error-law
   finding that corroborates #6 (quartic strictly-weaker handle).

### Tier C — T5 islands (organizational / free-regime, NOT finite-core estimates)

8. **HierarchicalGap** (H) — `T5`. δ=0 *exact* zero-defect island (decimation line): a reusable
   "free boundary ⇒ zero defect / cost-collapse" instance. Honestly not 4D, but the canonical
   `no-step ⇒ unit-defect=0` anchor for the tail⊕core split.

9. **IsserlisGaussianBase** (H) — `T5`. Genuine free-Wick/Gaussian reference island
   (`⟨x⁴⟩=3s⁴`), fixes `z_n` at finite order and refutes the "free dodge." Reusable Gaussian
   zero-cost reference; finite-order only (resummation + a→0 continuum stay open).

### Honest bottom line

The F–O range contains the entire per-bond-move / per-mode / fusion frontier, and the survey
confirms the application-map's verdict at the module level: **the codynamic toolkit's genuine
uplift is concentrated in exactly one place — the SITE-1 intra-block defect decomposition —
and its best Lean substrates are MKBondMovingControl + GradedBondMovingBudget +
HeatKernelSecondCumulant + FullModeQuadratic (per-mode quadratic defects) plus MultiLinkFusionDefect
+ InteractingMFoldDefect (the concentration/strictly-sub-linear teeth).** The two dozen
Fusion*-core-round modules, all Mayer/KP/polymer/NetDrift/JTP folds, and the OS/GNS/moment-PSD/
O4-restoration plumbing supply **no new analytic input** — they are DEDUP (the fold, already
hand-rolled twice), MISMATCH (defect-free analytic/magnitude or dead-route refutations), or N/A
(spectral/reconstruction/positivity plumbing). Nothing in F–O discharges `singleStep`; the
GENUINE-GAIN nodes are the materials for the single legal clause-(b) attack, whose live risk
remains the loop trap (per-move defects re-summing to the block object), most acutely flagged by
MKBondMovingControl's own free-energy-vs-gap-defect caveat.
