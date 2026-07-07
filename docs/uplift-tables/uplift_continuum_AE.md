# Codynamic-tool uplift survey — Continuum modules A–E (214 nodes)

Read-only classification pass. Tools: **T1** reflection-unit defect (=realδ_k), **T2** nonlinear monotone modulus, **T3** compositional error law, **T4** n-step Grönwall fold (∏(1−δ_k)), **T5** islands (free/discrete δ=0 / δ~1/k²), **T6** evolution monad (defect-free → MISMATCH for defect work), **T7** complexity budget.
Verdict ∈ {GENUINE-GAIN, DEDUP/BOOKKEEPING, MISMATCH, N/A}. Grounding: PROGRESS-LEDGER (F=1 atomic core `singleStep : realδ_k ≤ 6(1−w)²`), application-map (**SITE-1** intra-block per-*bond-move* defect decomposition = the ONLY genuine core-mover; the RG-flow fold is already hand-rolled twice → DEDUP; monad/categorical = MISMATCH), recast (composition is FREE; the 2w³→2 wall was a linear-modulus artifact; **defect ⊥ modulus**, so any modulus-side work is provably not core-shrinking).

## GENUINE-GAIN summary (ranked by value)

The whole "gap ⇐ singleStep" fold is already in tree (DefectGapRecursion / InductiveBoundWitnessSystem), so porting T4 anywhere = a forbidden `:=SingleStepDefectBound` loop. The **only** codynamic construct that can legally move D/F is the **SITE-1 intra-block per-bond-move decomposition of the per-BLOCK defect** into strictly-weaker per-MOVE local heat-kernel defects, folded by T1+T3+T4 at the per-move scale, using the η_move=0 island. Three nodes host that and nothing else does:

1. **CodynamicBondMoving** — the designated SITE-1 host, but its *current* content is a per-**mode** (spin-tower `s`) summability budget, i.e. already a T4 fold on the block defect (DEDUP of the fold). The GENUINE-GAIN handle NOT yet built here is the per-**bond-move** fold `realδ_block ≤ Σ_moves (∏ρ_dec)·η_move`. Highest value *iff* the per-move η is a strictly-smaller object than the block δ (ledger clause-b gate).
2. **BondMovingStep** — supplies the actual per-move composition operator `fusionProduct`/`fusionPow` (the p-fold Clebsch–Gordan fusion = the intra-block move trajectory) and the per-move defect seed `coeffW_dev`/`bondMovingDelta_to_zero` (η_move → 0 linearly). This is where the per-move unit-defect (T1) literally lives; the T4 fold over `fusionPow`'s iterate is the missing assembly.
3. **CodynamicHierarchical** — inhabits `exactLoss = 0` (`hierarchical_residual_zero`), i.e. the **η_move = 0 free island** (T5) that anchors the SITE-1 per-move fold; decimation-is-favorable proved. Already built as an island instance; its uplift value is as the base case of the SITE-1 fold, not standalone.

**Honest caveat (the ledger trap):** if the per-move defects merely re-sum to the same whole-block object, SITE-1 collapses back to `singleStep` (exactly what `SingleStepDecompositionAdjudication` and the reflection-unit recast already caught). So even (1)–(3) are GENUINE-GAIN only conditionally; every other A–E node is DEDUP, MISMATCH, or N/A. No new *unconditional* core-mover exists in A–E.

Everything else clusters as: **DEDUP** = the hand-rolled RG fold / defect-identification / already-built codynamic layer (T4/T3/T7 re-expression, or T2 modulus whose "linear-artifact" lesson the recast already recorded); **MISMATCH** = categorical/monad (T6, defect-free); **N/A** = analytic real-analysis primitives (Chebyshev orthogonality, arctan/π, Bernstein/local-CLT variance, theta K_t, cluster/polymer combinatorics, transfer-operator spectral, continuum-measure construction) with no defect/flow/modulus/island structure.

---

## Full node-by-node table

| module | role (1 line) | tool(s) | verdict | note |
|---|---|---|---|---|
| AbstractPolymerXi | abstract polymer Ξ + Dobrushin/KP add-one bound | T7 | N/A | combinatorial hard-core gas; not the RG defect fold |
| AcNReserveAnalytic | theta autoconvolution log-concavity reserve → rational floor | — | N/A | analytic theta (R1/local-CLT), no defect structure |
| AdditiveErosionAdequacy | derives uniform floor from additive-erosion recursion | T4,T3,T7 | DEDUP/BOOKKEEPING | THE hand-rolled additive Grönwall fold; recast SITE-4 |
| AdjacentMLR | refutes pointwise adjacent-MLR for theta arrays | — | N/A | analytic TP₂ refutation |
| AdjSpanningBuild | spanning-tree/BFS count for cluster over-count | — | N/A | combinatorial (cluster expansion) |
| AFBetaStepCanonical | discharges two-loop β-step for canonical AF trajectory | T4 | DEDUP/BOOKKEEPING | supplies δ_k rate to the fold; no new handle |
| AFCertificateModel | concrete rational inhabitant of AF trajectory cert | T4 | DEDUP/BOOKKEEPING | witness for the flow schedule |
| AFDeepUVSummability | derives δ_ren,k ~ 1/k² deep-UV summability from 1-loop AF | T5,T4 | DEDUP/BOOKKEEPING | the AF-tail **island** (δ~1/k²) already proved; T5 instance |
| AFDeltaDecay | relaxes exact δ=0 descent to summable-δ | T5,T4 | DEDUP/BOOKKEEPING | island-relaxation; feeds the fold |
| AFEpsRideBudget | identifies+bounds additive ε_k ≤ Dε/k² | T4,T3 | DEDUP/BOOKKEEPING | ε-side of the additive fold; SITE-4 |
| AFExpLift | additive log-spacing → multiplicative block ratio ≥ b+1 | — | N/A | spacing/exp arithmetic |
| AFRateCalibration | AF-rate interface + harmonic-divergence kill of linear crack | T2 | DEDUP/BOOKKEEPING | shows linear modulus fails (= recast's linear-artifact lesson) |
| AFRateMatch | AF block-rate meets margin-decay RateMatch | T4 | DEDUP/BOOKKEEPING | rate-matching for the fold |
| AFReciprocalRate | 1/k rate from two-loop AF recurrence | T4 | DEDUP/BOOKKEEPING | supplies the summable δ_k schedule |
| AFScaleCocycle | AF cert → nontrivial scale cocycle (transmutation) | T6 | MISMATCH | categorical scale-sheaf; defect-free |
| AFSpacingRatio | continuum spacing-ratio floor from AF running | T4 | DEDUP/BOOKKEEPING | flow-schedule arithmetic |
| AFTrajectoryCertificate | two-loop AF as recurrence-with-remainder → 1/k modulus | T4 | DEDUP/BOOKKEEPING | the flow data the fold consumes |
| AnchorDominanceEigenvalueShift | ∑ε_k dominated by m_phys via telescoping eigenvalue-shift | T4,T3 | DEDUP/BOOKKEEPING | telescoping budget = additive fold (SITE-4) |
| AnchorFixedSpacingDischarge | deep-UV anchor discharged by fixed-spacing gap | T4 | DEDUP/BOOKKEEPING | anchor input to the fold |
| ArctanCompositionIdentity | dedup of arctan↔trig atom | — | N/A | Machin-π trig core (off critical path) |
| ArctanCompositionTail | Moore–Osgood factoring of arctan↔trig tail | — | N/A | analytic trig |
| ArctanSeriesTrigBridge | arctan-series ↔ trig-series at 1/5 | — | N/A | analytic trig |
| ArctanTangentLink | concentrates arctan atom onto single cosine | — | N/A | analytic trig |
| ArctanTanInversion | arctan↔trig inversion via Gaussian integers | — | N/A | analytic trig |
| ArctanTrigConverges | antitone-modulus residual for at5 | — | N/A | analytic trig |
| ArctanTrigConvergesProof | circularity theorem + composition reduction | — | N/A | analytic trig |
| ArctanValueIdentity | value-identity sval ≃ sinC(arctan 1/5) | — | N/A | analytic trig |
| ArrayMLR | telescoping engine for two-index coefficient MLR | — | N/A | analytic TP₂ |
| ArtanhMonotone | monotonicity of constructive artanh series | — | N/A | analytic primitive |
| AsymptoticSpectralLoc | discharges `recursion` field of spectral loc | T4 | DEDUP/BOOKKEEPING | per-scale recursion = fold |
| AutoconvGershgorin | Andréief half-sum expansion of autoconv defect | — | N/A | analytic theta (Gershgorin) |
| BakryEmery | discrete Bakry–Émery curvature ⇒ gap | T2 | DEDUP/BOOKKEEPING | curvature modulus; magnitude route, content proved; not core |
| BakryEmeryGap | finite-regulator Bakry–Émery ⇒ gap corroboration | T2 | DEDUP/BOOKKEEPING | as above; corroboration |
| BalabanExactProgress | rebases codynamic exact-identification off fixed pt | T1,T5 | DEDUP/BOOKKEEPING | re-expresses `CodynamicExactIdentification` |
| BalabanLargeFieldEntropy | large/small-field suppression vs entropy | T5 | DEDUP/BOOKKEEPING | large-field geometric tail = island; Route E |
| BareAFDiagnostic | diagnostic kill-test (not progress) | — | N/A | explicitly a diagnostic |
| BddLatticeAnimal | lattice-animal count on bounded-degree lattice | T7 | N/A | combinatorial counting |
| BernsteinModulusClose | discharges QuadSumVarianceStmt0 residual | — | N/A | Bernstein/local-CLT variance (uniform_in_m, off-core) |
| BernsteinSequenceWrap | Bernstein → SpectralUnifCauchy wrap | — | N/A | analytic uniform-convergence |
| BernsteinStageData | StageData from monotone vanishing | — | N/A | analytic |
| BernsteinUniformConvergence | Chebyshev/quadratic-majorant convergence | — | N/A | analytic majorant |
| BernsteinVariance | division-free Bernstein variance identity | — | N/A | analytic variance |
| BernsteinVarianceClose | closes the Bernstein moment chain | — | N/A | analytic variance |
| BinomialTheorem | general binomial theorem over Q' | — | N/A | algebraic primitive |
| BirkhoffContraction | Birkhoff/Hilbert-metric contraction of positive op | T2 | DEDUP/BOOKKEEPING | contraction = a linear modulus; recast's linear-artifact applies; content proved |
| BlockingStepFrontier | states the single open continuum input | T1 | DEDUP/BOOKKEEPING | restates the singleStep frontier |
| BlockSpinMarginConstruction | constructs REAL block-spin eigenvalue margin | — | DEDUP/BOOKKEEPING | builds the object δ acts on; not a per-move handle |
| BlockSpinModel | end-to-end self-similar block-spin capstone | T4 | DEDUP/BOOKKEEPING | assembly over the fold |
| BondMovingMoment | Gaussian/Casimir moment bound for scaled weight | — | DEDUP/BOOKKEEPING | analytic tail; supplies η envelope factor to SITE-1 |
| BondMovingQuadratic | renormalized block defect δ_ren ≤ 6p(1−w)² (quadratic) | T2,T1 | DEDUP/BOOKKEEPING | per-BLOCK defect = singleStep's model RHS; quadratic modulus but block-scale |
| BondMovingRelResidual | ⚠ DEPRECATED (FusionRelResidualBound FALSE) | — | N/A | dead route |
| BondMovingRetuneFix | corrected bond-moving retune to rational surrogate | T2 | DEDUP/BOOKKEEPING | retune arithmetic for δ_ren |
| BondMovingScaledNorm | scaled heat-kernel norm + Casimir tail modulus | — | DEDUP/BOOKKEEPING | analytic infra feeding the envelope |
| **BondMovingStep** | explicit 4D bond-moving δ; fusionPow p-fold fusion; δ→0 | **T1,T3,T4** | **GENUINE-GAIN** | hosts the per-**move** composition (`fusionPow`) + per-move defect seed (η_move); the SITE-1 per-move fold is buildable here (clause-b gated) |
| BorelRenormalonScaffold | Borel/renormalon assessment | — | N/A | diagnostic scaffold |
| BoundedFCRetired | ④-chain capstone `continuousFC_retired` | — | N/A | functional-calculus (retired) |
| BoundedHamiltonianFiniteVol | finite-vol bounded H as located-spectrum data | — | N/A | spectral |
| BoundedTransferCalculus | bounded transfer-operator functional calculus | — | N/A | spectral |
| BulkModeCrux | sharp order of heat-kernel-scaled bulk mode | — | N/A | analytic (local-CLT bulk) |
| CarrierPrecursors | lattice-level precursors for 4D existence | — | N/A | structural existence |
| CasimirMoment | scaled Casimir-square moment (α verdict) | — | N/A | analytic moment |
| CayleyInjection | leg-C SET→LIST lifting for Prüfer injectivity | — | N/A | combinatorial (tree count) |
| CayleyLooseInjection | de-risked loose Cayley parent-map injection | — | N/A | combinatorial |
| CayleyLooseReduction | tree-graph atom needs only loose count n^{n-1} | — | N/A | combinatorial |
| CayleyMaxBound | Cayley spanning-tree count bound | — | N/A | combinatorial |
| CayleyParentInj | injectivity of BFS parent-map encoder | — | N/A | combinatorial |
| CayleyPruferInjection | Cayley count via Prüfer injection | — | N/A | combinatorial |
| CenterSymmetry | center symmetry / N-ality / confinement order param | — | N/A | structural (phase, not gap magnitude) |
| CharacterDiagResolutionProof | inhabits CharacterDiagResolution | — | N/A | spectral/character |
| CharacterWindowCeiling | pushes strong character-clustering window up | — | N/A | analytic clustering |
| CharChainFree | free SU(2) heat-kernel character chain (Wave 1) | — | N/A | analytic character chain |
| CharChainWilson | interacting Wilson plaquette character chain (Wave 2) | — | N/A | analytic character chain |
| CharFunCumulantDefect | char-function/cumulant attack on single-scale defect | — | N/A | analytic (reduces to R1) |
| ChebBracketTaylor | centered-difference Taylor remainder bounds | — | N/A | analytic Chebyshev |
| ChebDiscreteOrtho | discrete Chebyshev orthogonality/power-sum | — | N/A | analytic Chebyshev |
| ChebGeneralOrtho | general-M discrete Chebyshev-U orthogonality | — | N/A | analytic Chebyshev |
| ChebHeatKernelExpansion | Chebyshev-U generating-function partial sum | — | N/A | analytic Chebyshev |
| ChebLocatedNodesGen | DeMoivreNode 5 at √(3/4) | — | N/A | analytic Chebyshev |
| ChebLocatedRoots | located U₃ nodes 0,±√(1/2) | — | N/A | analytic Chebyshev |
| ChebLocatedRoots4 | located U₄ nodes ±(√5±1)/4 | — | N/A | analytic Chebyshev |
| ChebLocatedRoots4Even | EvenLocatedPowerSums4 via √5-quadrature | — | N/A | analytic Chebyshev |
| ChebMarkovModulus | two Markov-modulus obligations for bracket bounds | — | N/A | analytic Chebyshev |
| ChebOrthoAssembly | interior radical-leg √-Hölder difference bound | — | N/A | analytic Chebyshev |
| ChebOrthoBracketDecay | bracket boundary-decay estimate | — | N/A | analytic Chebyshev |
| ChebOrthoBudget | per-resolution approx-budget reduction | — | N/A | analytic Chebyshev |
| ChebOrthoBudgetClose | closes even-order √-weighted off-diag ortho | — | N/A | analytic Chebyshev |
| ChebOrthoCancel | discrete leading-order cancellation | — | N/A | analytic Chebyshev |
| ChebOrthoCancelDiv | cancellation/division primitive AbsLeRat | — | N/A | analytic Chebyshev |
| ChebOrthoEvenFTC | Riemann–FTC scaffolding for even-order π-free | — | N/A | analytic Chebyshev |
| ChebOrthoFinal | final interior assembly | — | N/A | analytic Chebyshev |
| ChebOrthoFTCEstimate | √-weighted FTC estimate even-order | — | N/A | analytic Chebyshev |
| ChebOrthogonality | discrete second-kind Chebyshev orthogonality | — | N/A | analytic Chebyshev |
| ChebOrthoGraded | corrected non-uniform graded per-cell rate | — | N/A | analytic Chebyshev |
| ChebOrthoGradedClose | closes graded per-cell bound | — | N/A | analytic Chebyshev |
| ChebOrthoInterior | interior-cell reciprocal lower bound | — | N/A | analytic Chebyshev |
| ChebOrthoLeadingModel | concrete midpoint leading model LZ | — | N/A | analytic Chebyshev |
| ChebOrthoLegAssembly | per-cell eventual leg bounds | — | N/A | analytic Chebyshev |
| ChebOrthoLegClose | outer division for symmetric √ 2nd-difference | — | N/A | analytic Chebyshev |
| ChebOrthoLegProof | eventual smooth-bracket leg bound | — | N/A | analytic Chebyshev |
| ChebOrthoMatrix | π-free Chebyshev-U orthogonality matrix | — | N/A | analytic Chebyshev |
| ChebOrthoMatrixUncond | orthogonality matrix unconditionally | — | N/A | analytic Chebyshev |
| ChebOrthoMidpoint | real-boundary midpoint reformulation | — | N/A | analytic Chebyshev |
| ChebOrthoMidpointCore | corrected per-cell midpoint rate | — | N/A | analytic Chebyshev |
| ChebOrthoMidpointEst | midpoint-quadrature error budget | — | N/A | analytic Chebyshev |
| ChebOrthoOffDiag | π-free off-diagonal Chebyshev-U ortho | — | N/A | analytic Chebyshev |
| ChebOrthoOffDiagClose | off-diagonal finish-line assembly | — | N/A | analytic Chebyshev |
| ChebOrthoOffDiagFinal | unconditional even off-diagonal ortho | — | N/A | analytic Chebyshev |
| ChebOrthoRadLegProof | eventual radical-leg bound | — | N/A | analytic Chebyshev |
| ChebOrthoRadSecondDiff | reusable √ 2nd-difference bounds | — | N/A | analytic Chebyshev |
| ChebOrthoRadSecondDiffSq | √ 2nd-diff-of-squares cancellation | — | N/A | analytic Chebyshev |
| ChebOrthoRemainder | product-difference split of midpoint increment | — | N/A | analytic Chebyshev |
| ChebOrthoSecondDiff | leg split of centered midpoint-diff remainder | — | N/A | analytic Chebyshev |
| ChebOrthoSecondOrder | CReal.cancel_mul_left primitive | — | N/A | analytic Chebyshev |
| ChebOrthoTaylor | 2nd-difference Taylor reduction of interior remainder | — | N/A | analytic Chebyshev |
| ChebOrthoTightModulus | tight sub-2nd-difference √ cancellation | — | N/A | analytic Chebyshev |
| ChebOrthoWeightedFTC | π-free √-weighted FTC antiderivative | — | N/A | analytic Chebyshev |
| ChebRoot | located roots of Chebyshev-U as CReal | — | N/A | analytic Chebyshev |
| ChebRotationPair | de Moivre rotation node uniform-in-M | — | N/A | analytic Chebyshev |
| ChebRProjection | R-projection per edge via truncation | — | N/A | analytic Chebyshev |
| ChebTFwdBoundClose | FwdSummable leaf of theta C¹ inputs | — | N/A | analytic theta (Wall-2, off-core) |
| ChebTFwdRatioClose | forward-T Taylor bracket engine | — | N/A | analytic theta |
| ChebUDClosure | pure-algebra residuals of √-weighted FTC | — | N/A | analytic Chebyshev |
| ChebUniformOrtho | uniform-in-M roots-of-unity finite-sum engine | — | N/A | analytic Chebyshev |
| ChebyshevBound | \|T_n(x)\| ≤ 1 over Q' | — | N/A | analytic primitive |
| ChebyshevQuadPSD | all-order heat-kernel Gram PSD via Gauss–Chebyshev | — | N/A | analytic PSD (OS2-adjacent) |
| ChebyshevU | \|U_{n-1}(x)\| ≤ n over Q' | — | N/A | analytic primitive |
| CircleFourierPowerModel | additive-Fourier-circle reframing of position-variance | — | N/A | local-CLT variance (off-core) |
| CircleModelAssembly | CircleModel from direction-pair encoding | — | N/A | local-CLT variance |
| ClusterBoundInstance | degenerate placeholder cluster bound | — | N/A | placeholder (cluster) |
| ClusterCount | ⚠ FAKE inhabitant, superseded | — | N/A | dead route |
| ClusterCount4DProgress | genuine 4D plaquette-incidence BddLattice | T7 | N/A | combinatorial 4D counting |
| ClusterGapReduction | collapses two thermodynamic-limit obligations | — | N/A | cluster/thermodynamic |
| ClusteringImpliesGap | clustering ⇒ spectral gap (converse) | — | N/A | spectral/operator |
| CodynamicBondMoving | codynamic uplift of ℝ⁴ bond-moving wall (per-mode budget) | **T1,T2,T4** | **GENUINE-GAIN** | designated SITE-1 host; current content = per-**mode** summability (=DEDUP fold), but per-**bond-move** fold not yet built here = the one core-mover (clause-b gated) |
| CodynamicCRealFlow | codynamic flow law at CReal level | T2,T4 | DEDUP/BOOKKEEPING | already the codynamic layer in Lean |
| CodynamicGap | surviving floor as flow invariant | T4 | DEDUP/BOOKKEEPING | already-built codynamic fold |
| CodynamicHierarchical | codynamic gap meets exact decimation; δ=0 hierarchical | **T5,T1** | **GENUINE-GAIN** | inhabits `exactLoss=0` = η_move=0 **island** anchoring the SITE-1 per-move fold; standalone already proved |
| CodynamicPhysFloor | conserved CReal margin budget → physical floor | T4,T7 | DEDUP/BOOKKEEPING | already-built budget layer |
| CodynamicReflectionUnitRecast | reflection-unit recast of singleStep (defect⊥modulus) | T1,T2,T3 | DEDUP/BOOKKEEPING | the T1 recast itself; machine-checked HONEST COLLAPSE (no F-move) |
| CodynamicTransmutation | codynamic recast of dimensional transmutation (flow law) | T2 | DEDUP/BOOKKEEPING | recasts transmutation; not core |
| CoeffChebSineClose | sin-free x-derivative recast of CoeffHalfIdentity | — | N/A | analytic theta (Wall-2) |
| CoeffHalfIdentityClose | differentiated Gauss q-binomial engine | — | N/A | analytic theta |
| CompactTransferGNS | finite-vol transfer op as compact self-adjoint | — | N/A | spectral/operator |
| CompletionGenerator | FiniteVolumeBoundedH → genGap transport | — | N/A | spectral transport |
| CondensateGeometricErosion | non-perturbative condensate, geometric ε_k=K·r^k | T5,T4 | DEDUP/BOOKKEEPING | geometric-tail **island** feeding the fold; already proved |
| CondMomentReduction | R1 → conditional-second-moment relocation | — | N/A | local-CLT variance |
| ConfigSpaceMeasure | constructive configuration-space field measure | — | N/A | measure construction |
| ConnectedActivityAssembly | Ursell/connected reorganization terminal assembly | — | N/A | cluster/polymer combinatorics |
| ConstructiveShellBridge | external finite-resolution tick bridge | T6 | MISMATCH | shell/tick structure, defect-free |
| ContinuousFCCarrierLimit | carrier-side limit of continuous FC | — | N/A | functional calculus |
| ContinuousFunctionalCalculusForm | forms p(T)=ΣcₖTᵏ operator | — | N/A | functional calculus |
| ContinuousTransferCalculus | continuous FC for Wilson transfer op | — | N/A | functional calculus |
| ContinuumCertificate | Stage-2 synthesis capstone (R2+R3+O4) | T4 | DEDUP/BOOKKEEPING | top assembly over the fold |
| ContinuumClosureProgram | continuum closure as one per-scale program (DefectGapRecursion) | **T4,T2** | DEDUP/BOOKKEEPING | THE hand-rolled product fold (`prodPrefix_le_physGap`); recast SITE-2 |
| ContinuumExistence | μ_∞ existence attack-surface (statements) | — | N/A | existence scaffold |
| ContinuumFieldMeasure | a→0 field-space measure as inverse-limit | — | N/A | measure construction |
| ContinuumFrontierScorecard | one-open-input scorecard | T1 | DEDUP/BOOKKEEPING | restates the frontier |
| ContinuumFunctional | continuum theory as positive linear functional | — | N/A | functional/OS |
| ContinuumGapLimit | gap-persistence bridge (collapses to one input) | T4 | DEDUP/BOOKKEEPING | limit assembly over fold |
| ContinuumGapModulus | continuum-gap convergence modulus via AF | T4,T2 | DEDUP/BOOKKEEPING | modulus/schedule for the fold |
| ContinuumMeasure | continuum SU(2) Wilson measure interface | — | N/A | measure interface |
| ContinuumShadowFloor | continuum-shadow reframing of position-variance | — | N/A | local-CLT variance |
| ContinuumYMStack | minimum theorem stack factoring | T4 | DEDUP/BOOKKEEPING | organizational factoring of the fold |
| CosIntegralReduction | sharpening AngleCosineIntegral (2/π) primitive | — | N/A | analytic trig |
| CosNodeBracket | divided-difference→Lipschitz cos-node bundle | — | N/A | analytic Chebyshev/cos node |
| CosNodeFamilyClose | general-M off-diagonal OS2 walls for cos family | — | N/A | analytic Chebyshev/cos |
| CosPiEnclosure | (k+2)² divided-difference secant bound | — | N/A | analytic Chebyshev/cos |
| CoupledContinuumWeight | interacting plaquette-coupled continuum RG weight | — | N/A | measure/weight construction |
| CRealContinuumAlg | shared Pivot2 CReal algebra home | — | N/A | shared primitive |
| CrossoverAnchorFloor | anchors full continuum margin floor to proved crossover | T4 | DEDUP/BOOKKEEPING | anchor input to fold |
| CrossoverDefectUnification | unifies crossover window; Σδ≈2.54>1 | T2,T4 | DEDUP/BOOKKEEPING | proves additive budget fails → product/T2 needed; recast SITE-2 lesson already recorded |
| CrossoverFlowContraction | crossover defect sum as flow-contraction | T4,T2 | DEDUP/BOOKKEEPING | flow-contraction = the fold |
| CrossRatioMonotone | generic two-value total-positivity engine | — | N/A | analytic TP₂ |
| CrudeMomentBound | ⚠ DEPRECATED (rests on FALSE FusionRelResidual) | — | N/A | dead route |
| CubedDerivative | cubing trick for matched-retune derivative | T2 | DEDUP/BOOKKEEPING | retune arithmetic (δ_ren) |
| CubedDominance | cubing trick for matched-retune dominance | T2 | DEDUP/BOOKKEEPING | retune arithmetic |
| CubeRatioBounds | two rational bounds on self-fusion cube target | — | N/A | analytic fusion arithmetic |
| CubicEulerBound | leg-(A) crux of tree-graph reduction | — | N/A | combinatorial (tree graph) |
| CumulativeBulkShift | cumulative bulk eigenvalue shift over AF flow | T4 | DEDUP/BOOKKEEPING | cumulative = the accumulation fold |
| CurvatureFloorStatement | curvature floor route linking proved links | T2 | DEDUP/BOOKKEEPING | curvature-magnitude route; content proved |
| CurvatureSingleStepAssessment | Bakry–Émery angle on the open single-step field | T2 | DEDUP/BOOKKEEPING | curvature modulus on singleStep; not core-shrinking |
| CycleMayer | connected correlator on a single plaquette cycle | — | N/A | cluster/Mayer combinatorics |
| CyclotomicPositivity | constructive positivity atoms for LDLᵀ pivot | — | N/A | algebraic positivity |
| DDIdentity | divided-difference secant identity for first-kind | — | N/A | analytic Chebyshev |
| DecodeComplete | alphabet enumeration / decoder completeness | — | N/A | combinatorial (tree decode) |
| DecodeTourSound | decoder soundness on rooted-tree Euler tours | — | N/A | combinatorial |
| DefectGapRecursionProgress | reduces+refutes two `recursion` fields of defect-gap | T4 | DEDUP/BOOKKEEPING | works on the product-fold recursion directly |
| DeltaFrontierLedger | end-to-end MK bond-moving δ-loop capstone/ledger | T1,T4 | DEDUP/BOOKKEEPING | ledger over the δ fold; restates frontier |
| DeMoivreHalfGen | located branch collapse + uniform-in-M de Moivre half | — | N/A | analytic Chebyshev |
| DerivStepPropClose | differentiated q-Pascal step for all N | — | N/A | analytic theta |
| DiffJTPAssembly | DiffJTP capstone (Wall-2 K_t≥0 CReal-deriv layer) | — | N/A | theta K_t (off critical path) |
| DiffJTPClose | fires DiffJTP/K_t≥0 from two C¹ inputs | — | N/A | theta K_t |
| DiffJTPClosed | corrected Wall-2 capstone over flat modulus | — | N/A | theta K_t |
| DiffJTPFinal | collapses DiffJTP to six named leaves | — | N/A | theta K_t |
| DiffJTPResult | consolidated Wall-2 verdict (type-bug repaired) | — | N/A | theta K_t |
| DiffJTPWireFinal | supplies series side of Wall-2 capstone | — | N/A | theta K_t |
| DiffProduct | constructive finite-difference Leibniz rule | — | N/A | analytic primitive (Wall-2) |
| DimensionlessMarginTransmutation | dimensionless physical margin transmutation assembled | T2 | DEDUP/BOOKKEEPING | transmutation flow; recast by CodynamicTransmutation |
| DimensionlessRatio | gap as natural transformation into dimensionless | T6 | MISMATCH | categorical nat-transf, defect-free |
| DirectSingleStepReconGap | direct attack on singleStep via reconstruction; 2w³→2 | T2,T1 | DEDUP/BOOKKEEPING | source of the 2w³→2 wall = linear-modulus artifact (recast §2 already isolated it) |
| DiscreteLaplaceMargin | generic margin-from-ρ (discrete-Laplace) reframing | — | N/A | local-CLT variance |
| DiscreteLaplaceSaddle | steepest-descent cumulant form of fusion | — | N/A | local-CLT saddle |
| DkProducerClose | closes Dk leaf of Wall2FinalResiduals | — | N/A | theta (Wall-2) |
| DominantModeRecursion | genuine DefectGapRecursion instance for dominant mode | T4 | DEDUP/BOOKKEEPING | instance of the product fold |
| DynamicToStaticGap | Helffer–Sjöstrand dynamic⇒static gap | — | N/A | spectral bridge |
| E2ProductFunctional | decoupled E2 thermodynamic product functional | — | N/A | thermodynamic/functional |
| EffectiveActionMassFlow | Bałaban effective-action mass-term flow | T4 | DEDUP/BOOKKEEPING | per-scale mass recursion = fold |
| EffMassConvergence | correlator plateau → effective-mass convergence | — | N/A | spectral/correlator |
| EigenvalueShiftBound | Clay core input 1: real block-spin ε_k ≤ w³-diff, PINNED | T1 | DEDUP/BOOKKEEPING | the pinned per-BLOCK defect = the atomic core (equi-inhabits singleStep) |
| EigenvalueShiftBridge | weight-defect ⟹ eigenvalue-shift bridge | T1 | DEDUP/BOOKKEEPING | defect-identification; part of core |
| EigShiftOrder | sharp order of multiplicity-blind eigenvalue shift | T1 | DEDUP/BOOKKEEPING | sharpens the block-defect object |
| EnvelopeClosure | anchor lemmas for position-variance curvature floor | — | N/A | local-CLT variance |
| ExactSinglePolymerActivity | exact single-mode single-polymer activity \|z_1\|≤g² | — | N/A | polymer/activity |
| ExpProductFloor | all-R lower bound for exponential product floor | T4 | DEDUP/BOOKKEEPING | product-floor lower bound = fold arithmetic |

---

## Coverage

All **214** assigned A–E modules classified (A:31, B:28, C:124, D:22, E:9); none skipped. Deprecated/fake nodes (BondMovingRelResidual, CrudeMomentBound, ClusterCount) flagged N/A as dead routes.

## Distribution

- **GENUINE-GAIN: 3** — CodynamicBondMoving, BondMovingStep, CodynamicHierarchical — all three the SITE-1 intra-block per-bond-move-defect cluster, conditionally (clause-b gated; risk of collapse to `singleStep`).
- **DEDUP/BOOKKEEPING: ~48** — the hand-rolled RG Grönwall fold (AF*/Anchor*/Crossover*/Continuum*/DefectGap*/Dominant*/Cumulative*/AdditiveErosion, T4/T3/T7), the curvature/Birkhoff T2 modulus route (recast's "linear-artifact" lesson already recorded), the already-built codynamic layer (Codynamic{Gap,CRealFlow,PhysFloor,Transmutation,ReflectionUnitRecast}), and the defect-identification cluster (Eigenvalue*/BondMovingQuadratic/DirectSingleStepReconGap — all equi-inhabit or feed `singleStep`).
- **MISMATCH: 4** — AFScaleCocycle, ConstructiveShellBridge, DimensionlessRatio (categorical/nat-transf/tick, T6 defect-free), + monad-flavored.
- **N/A: ~159** — analytic real-analysis primitives with no defect/flow/modulus/island structure: the Chebyshev-orthogonality bulk (~60), Arctan/π (8), Bernstein/local-CLT variance (~14), theta K_t Wall-2 (DiffJTP*/Coeff*/Dk*, off critical path), cluster/polymer combinatorics (Cayley*/Cluster*/Cycle*/Decode*/AbstractPolymer/Connected), transfer-operator spectral (Bounded*/Continuous*/Compact*/Dynamic*/EffMass), and continuum-measure construction (Continuum{Measure,FieldMeasure,Existence}/ConfigSpace/Coupled).

## Bottom line for the caller

Within A–E, the codynamic toolkit's only core-moving surface is the **SITE-1 per-bond-move decomposition**, and it is already *scaffolded* (not yet folded) across exactly three adjacent modules: **BondMovingStep** already builds the per-move fusion operator `fusionPow` and the per-move defect seed; **CodynamicHierarchical** already gives the η_move=0 island base case; **CodynamicBondMoving** already gives the fold but at the wrong (per-mode, not per-move) granularity. The genuine-gain move is to assemble the T1+T3+T4 fold `realδ_block ≤ Σ_moves (∏ρ_dec)·η_move` over `fusionPow`'s move trajectory — and it is legal only if the per-move η is certified strictly weaker than the block δ (else it collapses to `singleStep`, the trap the ledger already sprang twice). Every other A–E node is a hand-rolled fold (DEDUP), a defect-magnitude re-derivation that equi-inhabits the core (DEDUP), a defect-free categorical construct (MISMATCH), or analytic real analysis untouched by the codynamic metric (N/A).
