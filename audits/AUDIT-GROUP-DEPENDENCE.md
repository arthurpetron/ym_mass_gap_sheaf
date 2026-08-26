# Group-dependence audit

Date: 2026-08-26

Scope: source-only audit of the worktree as inspected before commit `096a8d0`. No `.lean` file was edited and no proof obligation was changed during the audit. `CompactDualSlabFaceStrandComponentReconstruction.lean` and its ledger entry were uncommitted at audit time; this report marks that snapshot status `WORKTREE-ONLY` where used. They were subsequently committed unchanged in `096a8d0` after the audit was complete.

## Executive findings

1. **No Lean dependency path from the strand/component layer to `SingleStepDefectBound.singleStep` was found.** The component chain ends at accepted component reconstruction/weight comparison. `SingleStepDefectReduction.lean` imports only `CrossoverDefectUnification`, `RenDefectQuadFactor`, and `SummabilityCapstone` (`lean/YMGap/Continuum/SingleStepDefectReduction.lean:94`-`96`), and its `singleStep` field mentions only `AFRateModulus`, `Nat -> Q'`, and an inequality (`lean/YMGap/Continuum/SingleStepDefectReduction.lean:284`, declaration `SingleStepDefectBound`). No strand/component declaration is named in that type or its constructors.
2. The first load-bearing non-abelian declaration in the maximal source-backed strand chain is `fusionOK` (`lean/YMGap/Continuum/BondMovingStep.lean:119`). It is the hard-coded SU(2) Clebsch--Gordan triangle/parity rule (`lean/YMGap/Continuum/BondMovingStep.lean:104`-`120`).
3. The strand chain has **no gauge-group typeclass parameter at all**. It therefore cannot literally be instantiated with U(1) or Z_n; it is hard-coded to SU(2) natural-number twice-spin labels. Conversely, `SingleStepDefectBound` has no group parameter or non-abelian hypothesis, so its type does not exclude an abelian semantic interpretation.
4. The exact component payment is proved only at `anchorCoupling = 1/400`; the desired conditional-transition lower bound and uniform posterior-variance fraction are **NOT FOUND**. The completed `1/16` strict form theorem explicitly quantifies `0 <= coupling <= anchorCoupling`, but contains no beta or lattice-spacing parameter.
5. The finite BF4 gap bounds the row-normalized operator obtained from the symmetric reflected BF4/Choi joint law. It is an OS/reflection transfer represented as a reversible Markov kernel, **not** a link-variable heat-bath dynamics or its generator.

## A. Group dependence

### A.1 Actual dependency result

The requested end-to-end path is **NOT FOUND**.

The strand/component imports form the following source-backed branch:

```text
fusionOK (SU(2) Clebsch--Gordan rule)
  -> canonical trivalent resolution and local mate
  -> canonical same-slot internal continuation
  -> canonical stop/advance and ordered-path termination
  -> canonical physical-terminal partner/pairing
  -> corrected-slab face-strand edges
  -> rooted finite graph component and partner-closed pullback
  -> accepted component drop and global assignment
  -> exact component weight payment
  -> exact reconstruction of the source (WORKTREE-ONLY)
  -X-> NOT FOUND: component-to-posterior/defect/RG bridge

SingleStepDefectBound.singleStep
  <- CrossoverDefectUnification / RenDefectQuadFactor / SummabilityCapstone
```

The searched strand/component modules were:

- `lean/YMGap/Continuum/SU2TrivalentStrandPeeling.lean`
- `lean/YMGap/Continuum/SU2TrivalentStrandPortPairing.lean`
- `lean/YMGap/Continuum/CanonicalLinkInternalStrandContinuation.lean`
- `lean/YMGap/Continuum/CanonicalLinkStrandStep.lean`
- `lean/YMGap/Continuum/CanonicalLinkStrandMonotonePath.lean`
- `lean/YMGap/Continuum/CanonicalLinkStrandStrictProgress.lean`
- `lean/YMGap/Continuum/CanonicalLinkStrandTerminal.lean`
- `lean/YMGap/Continuum/CanonicalLinkPhysicalTerminalPartner.lean`
- `lean/YMGap/Continuum/CanonicalLinkPhysicalTerminalPairing.lean`
- `lean/YMGap/Continuum/CompactDualSlabLinkPhysicalStrandPairing.lean`
- `lean/YMGap/Continuum/CompactDualSlabGlobalFaceStrandEdges.lean`
- `lean/YMGap/Continuum/CompactDualSlabFaceStrandSeedComponent.lean`
- `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentDrop.lean`
- `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentAssignment.lean`
- `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentWeight.lean`
- `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentReconstruction.lean`
- `lean/YMGap/Continuum/SingleStepDefectReduction.lean`

Searches for `SingleStepDefectReduction`, `SingleStepDefectBound`, and `singleStep` in all strand/component modules returned no references. The exact requested declaration for a "closed/classified boundary strand component" is also **NOT FOUND** in those modules. The nearest declarations are the rooted graph component `SlabFaceStrandSeed.component` (`lean/YMGap/Continuum/CompactDualSlabFaceStrandSeedComponent.lean:130`) and the linkwise partner-closed selection `SlabFusionWitnessFaceStrandSeed.atLinkMateClosedSelection` (`lean/YMGap/Continuum/CompactDualSlabFaceStrandSeedComponent.lean:222`); neither classifies time-boundary components.

### A.2 Declaration classification on the maximal source-backed adjacent chain

Because the requested end-to-end path does not exist, the table below reports every principal declaration in the maximal source-backed chain matching the named stages, followed by the disconnected `singleStep` endpoint. It does not assert a dependency across the missing edge.

| declaration | module:line | classification | evidence |
|---|---|---|---|
| `fusionOK` | `lean/YMGap/Continuum/BondMovingStep.lean:119` | NON-ABELIAN | Definition is the SU(2) Clebsch--Gordan triangle/parity rule; the module identifies it as SU(2) character fusion at lines 104-120. U(1) fusion is not this rule. |
| `TrivalentStrandResolution` | `lean/YMGap/Continuum/SU2TrivalentStrandPeeling.lean:44` | GROUP-AGNOSTIC | Structure contains only six natural numbers/equalities and no group, Casimir, rank, or fusion hypothesis. |
| `canonicalTrivalentStrandResolution` | `lean/YMGap/Continuum/SU2TrivalentStrandPeeling.lean:83` | NON-ABELIAN | Its input is `fusionOK a b c = true` and it computes the SU(2) trivalent multiplicities. |
| `TrivalentStrandResolution.admissible` | `lean/YMGap/Continuum/SU2TrivalentStrandPeeling.lean:103` | NON-ABELIAN | Its conclusion is the hard-coded `fusionOK a b c = true`. |
| `TrivalentStrandPort` | `lean/YMGap/Continuum/SU2TrivalentStrandPortPairing.lean:54` | GROUP-AGNOSTIC | Pure sum of `Fin a`, `Fin b`, and `Fin c`; no group operation or representation rule. |
| `strandMate` | `lean/YMGap/Continuum/SU2TrivalentStrandPortPairing.lean:84` | GROUP-AGNOSTIC | Consumes an arbitrary `TrivalentStrandResolution`; implementation is bounded natural-number arithmetic. |
| `strandMate_involutive` | `lean/YMGap/Continuum/SU2TrivalentStrandPortPairing.lean:138` | GROUP-AGNOSTIC | The statement is only involutivity of `strandMate` for arbitrary resolution data. |
| `canonicalTrivalentPortMate` | `lean/YMGap/Continuum/SU2TrivalentStrandPortPairing.lean:218` | NON-ABELIAN | Requires `fusionOK a b c = true` and invokes `canonicalTrivalentStrandResolution`. |
| `CanonicalInternalStrandPort` | `lean/YMGap/Continuum/CanonicalLinkInternalStrandContinuation.lean:139` | NON-ABELIAN | Its carrier is `canonicalLinkResolvedStrandNetwork` under `canonicalLinkConditionalAllowedB`; this is the canonical SU(2) resolved-fusion network. |
| `canonicalInternalStrandHalfEdge` | `lean/YMGap/Continuum/CanonicalLinkInternalStrandContinuation.lean:151` | NON-ABELIAN | Domain is `CanonicalInternalStrandPort` on that canonical SU(2) network. |
| `canonicalInternalStrandContinue` | `lean/YMGap/Continuum/CanonicalLinkInternalStrandContinuation.lean:165` | NON-ABELIAN | Same-slot crossing is stated only on the canonical allowed/resolved link network. |
| `canonicalInternalStrandContinue_slot` | `lean/YMGap/Continuum/CanonicalLinkInternalStrandContinuation.lean:212` | NON-ABELIAN | The theorem consumes `canonicalLinkConditionalAllowedB` and the specialized continuation. |
| `canonicalInternalStrandContinue_involutive` | `lean/YMGap/Continuum/CanonicalLinkInternalStrandContinuation.lean:252` | NON-ABELIAN | The theorem is specialized to the same canonical network and its internal fusion edges. |
| `canonicalResolvedPortClassify` | `lean/YMGap/Continuum/CanonicalLinkStrandStep.lean:119` | NON-ABELIAN | Classifies ports of `canonicalLinkResolvedStrandNetwork` under `canonicalLinkConditionalAllowedB`. |
| `CanonicalPhysicalStrandPort` | `lean/YMGap/Continuum/CanonicalLinkStrandStep.lean:158` | NON-ABELIAN | Subtype of ports in the canonical resolved SU(2) link network. |
| `canonicalLinkStrandStep` | `lean/YMGap/Continuum/CanonicalLinkStrandStep.lean:171` | NON-ABELIAN | Combines the specialized canonical classification, internal crossing, and local mate. |
| `NatPathAdjacent` | `lean/YMGap/Continuum/CanonicalLinkStrandMonotonePath.lean:35` | GROUP-AGNOSTIC | Predicate on three natural-number equalities only. |
| `natPathAdjacent_nonbacktracking_direction` | `lean/YMGap/Continuum/CanonicalLinkStrandMonotonePath.lean:39` | GROUP-AGNOSTIC | Pure theorem about adjacent natural numbers. |
| `natPathRank` | `lean/YMGap/Continuum/CanonicalLinkStrandMonotonePath.lean:61` | GROUP-AGNOSTIC | Natural-number rank with no group data. |
| `natPathRank_strictly_decreases` | `lean/YMGap/Continuum/CanonicalLinkStrandMonotonePath.lean:66` | GROUP-AGNOSTIC | Pure bounded nonbacktracking path theorem. |
| `canonicalSuccessiveInternalCrossing_no_return` | `lean/YMGap/Continuum/CanonicalLinkStrandStrictProgress.lean:62` | NON-ABELIAN | Applied to the canonical allowed/resolved link and its internal fusion-edge set. |
| `canonicalSuccessiveInternalCrossing_rank_decreases` | `lean/YMGap/Continuum/CanonicalLinkStrandStrictProgress.lean:151` | NON-ABELIAN | Specializes the generic rank theorem to successive crossings in the canonical fusion network. |
| `CanonicalStrandTerminalWitness` | `lean/YMGap/Continuum/CanonicalLinkStrandTerminal.lean:87` | NON-ABELIAN | Sigma type over `CanonicalPhysicalStrandPort` and the canonical strand path. |
| `CanonicalOrientedInternalState` | `lean/YMGap/Continuum/CanonicalLinkStrandTerminal.lean:104` | NON-ABELIAN | State fields are ports and internal edges of the canonical allowed/resolved link. |
| `CanonicalOrientedInternalState.next_rank_lt` | `lean/YMGap/Continuum/CanonicalLinkStrandTerminal.lean:169` | NON-ABELIAN | Uses the specialized canonical crossing progress theorem. |
| `CanonicalOrientedInternalState.terminalWitness` | `lean/YMGap/Continuum/CanonicalLinkStrandTerminal.lean:210` | NON-ABELIAN | Recursive terminal extraction over the specialized canonical state. |
| `canonicalLinkStrandTerminalWitness` | `lean/YMGap/Continuum/CanonicalLinkStrandTerminal.lean:237` | NON-ABELIAN | Computes a physical terminal in the canonical allowed/resolved link network. |
| `canonicalLinkStrandTerminal` | `lean/YMGap/Continuum/CanonicalLinkStrandTerminal.lean:273` | NON-ABELIAN | Projection of the specialized canonical terminal witness. |
| `canonicalPhysicalStrandPartner` | `lean/YMGap/Continuum/CanonicalLinkPhysicalTerminalPartner.lean:373` | NON-ABELIAN | Partner is defined by local mate plus terminal extraction on the canonical fusion network. |
| `canonicalPhysicalStrandPartner_involutive` | `lean/YMGap/Continuum/CanonicalLinkPhysicalTerminalPartner.lean:417` | NON-ABELIAN | Involutivity theorem for the specialized partner. |
| `canonicalPhysicalStrandPartner_ne_self` | `lean/YMGap/Continuum/CanonicalLinkPhysicalTerminalPairing.lean:311` | NON-ABELIAN | Fixed-point-free theorem on canonical physical terminals. |
| `canonicalPhysicalStrandPartner_edgeId_ne` | `lean/YMGap/Continuum/CanonicalLinkPhysicalTerminalPairing.lean:400` | NON-ABELIAN | Uses the canonical link's one-element physical half-edge fiber and specialized partner. |
| `CanonicalPhysicalStrandPairing` | `lean/YMGap/Continuum/CanonicalLinkPhysicalTerminalPairing.lean:441` | NON-ABELIAN | Carrier is `CanonicalPhysicalStrandPort` under `canonicalLinkConditionalAllowedB`. |
| `canonicalPhysicalStrandPairing` | `lean/YMGap/Continuum/CanonicalLinkPhysicalTerminalPairing.lean:453` | NON-ABELIAN | Packages the specialized partner/involutivity/fixed-point-free results. |
| `SlabLinkFaceStrandOccurrence` | `lean/YMGap/Continuum/CompactDualSlabLinkPhysicalStrandPairing.lean:47` | NON-ABELIAN | Corrected-slab occurrence is built from the canonical SU(2) terminal carrier. |
| `slabLinkPhysicalTerminalOccurrence` | `lean/YMGap/Continuum/CompactDualSlabLinkPhysicalStrandPairing.lean:102` | NON-ABELIAN | Converts a canonical physical terminal into a slab face/slot occurrence. |
| `slabLinkPhysicalStrandPartner` | `lean/YMGap/Continuum/CompactDualSlabLinkPhysicalStrandPairing.lean:168` | NON-ABELIAN | Specializes `canonicalPhysicalStrandPartner` to an accepted slab link. |
| `SlabFaceStrandCopy` | `lean/YMGap/Continuum/CompactDualSlabGlobalFaceStrandEdges.lean:127` | NON-ABELIAN | Global copy is assembled from accepted slab-link physical terminals. |
| `SlabFaceStrandEdge` | `lean/YMGap/Continuum/CompactDualSlabGlobalFaceStrandEdges.lean:177` | NON-ABELIAN | Edge endpoints are the specialized slab face-strand copies. |
| `slabFusionWitnessAssignmentFaceStrandEdges` | `lean/YMGap/Continuum/CompactDualSlabGlobalFaceStrandEdges.lean:252` | NON-ABELIAN | Concatenates terminal-partner edges from a complete slab fusion-witness assignment. |
| `SlabFaceStrandSeed.component` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandSeedComponent.lean:130` | NON-ABELIAN | Root component is computed on the specialized global face-strand edge list. |
| `SlabFusionWitnessFaceStrandSeed.atLinkMateClosedSelection` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandSeedComponent.lean:222` | NON-ABELIAN | Pulls the specialized rooted component back to a linkwise mate-closed SU(2) selection. |
| `slabFaceStrandSelectionCount` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentDrop.lean:81` | NON-ABELIAN | Counts selected slots of the specialized slab face-strand component. |
| `SlabFusionWitnessFaceStrandSeed.lowerPhysical` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentDrop.lean:431` | NON-ABELIAN | Lowers the physical labels using the specialized component incidence. |
| `SlabFusionWitnessFaceStrandSeed.lower_auxiliary_mem_atLink` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentDrop.lean:443` | NON-ABELIAN | Produces an accepted lowered SU(2) fusion witness at a displayed link. |
| `SlabFusionWitnessFaceStrandSeed.lowerAssignment` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentAssignment.lean:131` | NON-ABELIAN | Assembles all specialized locally accepted lowered fusion witnesses. |
| `SlabFusionWitnessFaceStrandSeed.lowerAssignment_mem` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentAssignment.lean:144` | NON-ABELIAN | Membership is in `slabFusionWitnessAssignmentsOn`, the SU(2) fusion assignment list. |
| `SlabFusionWitnessFaceStrandSeed.peelPath` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentWeight.lean:538` | NON-ABELIAN | Serializes the specialized component into accepted physical face peels. |
| `SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_le` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentWeight.lean:566` | NON-ABELIAN | Bounds the actual SU(2) expanded fusion-fiber weight after the component peel. |
| `SlabFusionWitnessFaceStrandSeed.reconstructCompleteAssignment_eq` | `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentReconstruction.lean:362` | NON-ABELIAN | `WORKTREE-ONLY`; reconstructs the complete source fusion assignment from the specialized lower assignment and drop. |
| `SingleStepDefectBound` / field `singleStep` | `lean/YMGap/Continuum/SingleStepDefectReduction.lean:284` / `:296` | GROUP-AGNOSTIC | The type contains only `AFRateModulus`, `Nat -> Q'`, positivity, and a scalar recursion inequality. No group, representation, Casimir, rank, beta, lattice spacing, strand, or component datum occurs. |

**FIRST NON-ABELIAN declaration:** `fusionOK` at `lean/YMGap/Continuum/BondMovingStep.lean:119`.

There is no declaration connecting the final NON-ABELIAN component row to the GROUP-AGNOSTIC `SingleStepDefectBound.singleStep` row.

## B. Instantiation test

### B.1 Literal typeclass answer

The strand-layer hypothesis bundle/typeclass requested in the question is **NOT FOUND**. The searched strand modules contain no `Group`, `CompactGroup`, `NonAbelian`, U(1), or Z_n parameter or instance. They are not polymorphic in a gauge group: their fundamental labels are `Nat`, and their admissibility predicate is the fixed SU(2) `fusionOK` (`lean/YMGap/Continuum/BondMovingStep.lean:117`-`120`, declaration `fusionOK`). Therefore:

- literal Lean instantiation of the strand layer with U(1): **NOT FOUND / not applicable**, because there is no group parameter to instantiate;
- literal Lean instantiation with Z_n: **NOT FOUND / not applicable**, for the same reason;
- semantic exclusion of U(1) or Z_n from `SingleStepDefectBound`: **absent**, because that structure has no group parameter (`lean/YMGap/Continuum/SingleStepDefectReduction.lean:284`-`297`).

Modules searched for this question: all modules listed in A.1, plus `lean/YMGap/RepTheory/RepData.lean` and `lean/YMGap/RepTheory/SimpleGroup.lean`.

### B.2 Hypotheses required to make abelian exclusion load-bearing

The following source-level additions are all required for the present disconnected architecture to express and enforce exclusion of U(1) and Z_n:

| required hypothesis/pin | current location |
|---|---|
| An actual gauge-group carrier and group operations parameterizing the lattice/strand objects | **NOT FOUND** in the searched modules. |
| An explicit non-abelian witness attached to that carrier, such as noncommuting elements, or an equivalent compact-connected-simple hypothesis whose definition refers to the same carrier | **NOT FOUND**. The nearest name is `AdmissibleSimpleGroup` at `lean/YMGap/RepTheory/SimpleGroup.lean:88`, but it is a proposition over scalar `RepData`, not over a group carrier. |
| A representation/fusion pin proving that the strand rule used by the lattice object is the representation rule of that same gauge group | **NOT FOUND**. The current `fusionOK` is hard-coded SU(2), not a field of a group-indexed interface. |
| A pin threading the same group-indexed physical object into `SingleStepDefectBound.trueMargin` and `singleStep` | **NOT FOUND** in `SingleStepDefectReduction.lean` or the strand/component modules. |

`RepData` does not supply the missing exclusion. Its fields are arbitrary rationals/naturals, and its own documentation calls it “Group-agnostic by construction” (`lean/YMGap/RepTheory/RepData.lean:139`-`159`, declaration `RepData`). `AdmissibleSimpleGroup` requires only scalar lower bounds and a `RepData.ClosureCertificate` (`lean/YMGap/RepTheory/SimpleGroup.lean:82`-`97`); no group multiplication or noncommutativity witness is present in that declaration.

## C. Beta and lattice-spacing dependence

### C.1 Source naming convention

No declaration identifying the heat/nome parameter `w` or `coupling` with a function of beta and lattice spacing was found in the modules audited below. Accordingly, category (ii) below means “the heat/nome parameter is explicit in the type”; an explicit source equation `w = w(beta,a)` is **NOT FOUND**.

### C.2 Heat-weight ratio and requested conditional-transition lower bound

| symbol/value | defining declaration | category | source evidence |
|---|---|---|---|
| `coeffW w s = dimQ s * qpow w (c4 s)` | `coeffW` | (ii) beta/heat-dependent with `w` explicit in the type | `lean/YMGap/Continuum/BondMovingStep.lean:259`. No beta/a identification is stated there. |
| `anchorCoupling = 1/400` | `anchorCoupling` | (i) independent of beta syntactically; fixed operating point, not beta-uniform | `lean/YMGap/Continuum/Z4StrongCouplingParametricAnchor.lean:243`. |
| `anchorFaceCoefficient = 1/32,000,000` | `anchorFaceCoefficient` | (i) fixed anchor constant | `lean/YMGap/Continuum/Z4StrongCouplingParametricAnchor.lean:245`; `anchorFundamentalCoefficient` identifies it with `coeffW anchorCoupling 1` at `:247`. |
| successor ratio `1/32,000,000` | `anchorCoeffW_succ_le` | (i) fixed anchor theorem, not beta-uniform | `lean/YMGap/Continuum/CompactDualSlabExpandedFacePeelWeight.lean:63`; statement explicitly uses `anchorCoupling`. |
| packet successor ratio `1/32,000,000` | `anchorPacketCoefficient_succ_le` | (i) fixed anchor theorem | `lean/YMGap/Continuum/CompactDualSlabExpandedFacePeelWeight.lean:85`; cutoff is quantified, heat parameter is fixed. |
| one-face factor `1/32,000,000` | `slabPhysicalFaceFactor_anchor_lower_one_le` | (i) fixed anchor theorem | `lean/YMGap/Continuum/CompactDualSlabExpandedFacePeelWeight.lean:263`; cutoff, extent, label, and face are quantified, but beta/a are absent. |
| component/path factor `(1/32,000,000)^m` | `SlabFacePeelPath.faceFactor_le` | (i) fixed anchor theorem | `lean/YMGap/Continuum/CompactDualSlabExpandedFacePeelWeight.lean:309`; path length is explicit. |
| `animalK z4Chain = 625` | `animalK`, `z4Chain` | (i) combinatorial 4D lattice constant | `animalK` is `(D+1)^2` at `lean/YMGap/Continuum/BddLatticeAnimal.lean:280`; `z4Chain.D = 24` at `lean/YMGap/Continuum/ClusterCount4DProgress.lean:292`-`297`. |
| candidate component ratio `625/32,000,000 = 1/51,200` | `anchorExpandedFaceAnimalCandidateRatio` | (i) fixed anchor candidate | Definition at `lean/YMGap/Continuum/CompactDualSlabExpandedFacePeelWeight.lean:452`; exact equality at `:456`; `< 1` at `:464`. The source explicitly says it is only a candidate pending inverse encoding at `:447`-`463`. |
| requested conditional-transition lower bound | **NOT FOUND** | no category applies | Searched `CompactDualSlabExpandedFacePeelWeight.lean`, all `CompactDualSlabFaceStrandComponent*.lean`, and `BF4PhysicalVacuumSectorConditionalVariance.lean`. The ledger says the component weight still lacks the inverse code/count at `lean/SORRY_LEDGER.md:19154`-`19158`. |

No category-(iii) opaque beta-dependent constant was found in this heat/component inventory.

### C.3 Posterior-variance fraction

| symbol/value | defining declaration | category | source evidence |
|---|---|---|---|
| `weightedGramConditionalPairwiseVariance` | same-named definition | (ii) generic weights/amplitudes are explicit inputs | `lean/YMGap/Continuum/BF4PhysicalVacuumSectorConditionalVariance.lean:67`. |
| `centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance w hw cutoff half coefficient` | same-named definition | (ii) heat/nome `w`, cutoff, and half-extent are explicit in the type | `lean/YMGap/Continuum/BF4PhysicalVacuumSectorConditionalVariance.lean:211`. |
| factor `1/2` in `diagonal - transfer = (1/2) posteriorVariance` | `centralPhysicalFiniteVacuumSector_deficit_eqv_half_conditionalPairwiseVariance` | (i) arithmetic constant independent of heat/beta | `lean/YMGap/Continuum/BF4PhysicalVacuumSectorConditionalVariance.lean:262`-`271`. |
| positive cutoff-independent posterior-variance fraction | **NOT FOUND** | no category applies | The module states “No uniform variance fraction is asserted” at `lean/YMGap/Continuum/BF4PhysicalVacuumSectorConditionalVariance.lean:25`; the ledger leaves precisely this lower bound open at `lean/SORRY_LEDGER.md:18110`-`18114`. |

No posterior-variance modulus in beta or lattice spacing is declared in the searched module.

### C.4 Uniform strict form bound on the completed dense/OS vacuum complement

| symbol/value | defining declaration | category | source evidence |
|---|---|---|---|
| `anchorDecoratedFaceEnvelope = 1/7500` | `anchorDecoratedFaceEnvelope` | (i) fixed anchor constant | `lean/YMGap/Continuum/Z4SpinSummedFaceActivityBound.lean:76`. |
| `eSurrogate = 3` | `eSurrogate` | (i) fixed rational KP constant | `lean/YMGap/Continuum/KPCriterion.lean:237`. |
| `anchorDecoratedEffectiveRatio = animalK z4Chain * anchorDecoratedFaceEnvelope * eSurrogate = 1/4` | `anchorDecoratedEffectiveRatio` | (i) fixed strong-coupling rate | Definition at `lean/YMGap/Continuum/Z4SpinSummedFaceActivityBound.lean:700`; equality at `:703`. |
| `anchorDecoratedDoubledTimeRate = (anchorDecoratedEffectiveRatio)^2 = 1/16` | `anchorDecoratedDoubledTimeRate` | (i) fixed rate | Definition at `lean/YMGap/Continuum/Z4CouplingParametricSignedGeometricClustering.lean:44`; equality at `:47`; strictness at `:69`. |
| heat/coupling range `0 <= coupling <= anchorCoupling` | parameters of `strictJointCylinderCompletedTwoStepTransfer` and completed gap theorem | (ii) heat/nome parameter explicit in type | Operator type at `lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer.lean:39`-`44`; completed form gap theorem at `lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCenteredCompletedGap.lean:402`-`406`. |
| completed form separator `q = 1/16` | `anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap` | (i) separator itself fixed; (ii) coupling range explicit | `lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCenteredCompletedGap.lean:399`-`414`. |
| completed operator squared-norm rate `q^2 = (1/16)^2 = 1/256` | `anchorDecoratedDoubledTimeRate_completed_vacuum_operator_norm_gap` | (i) fixed rate; (ii) coupling range explicit | `lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap.lean:440`-`456`. |
| beta/a modulus | **NOT FOUND** | no category applies | No beta or lattice-spacing variable occurs in the two completed gap declarations. |

No category-(iii) opaque beta-dependent constant was found in this strict-gap inventory.

### C.5 Uniformity flags

- `slabPhysicalFaceFactor_anchor_lower_one_le` is genuinely uniform over the explicitly quantified cutoff, extent, selected spin/face, and other labels, but only at the fixed `anchorCoupling`; it is not a beta-uniform theorem (`lean/YMGap/Continuum/CompactDualSlabExpandedFacePeelWeight.lean:258`-`273`).
- `SlabFacePeelPath.faceFactor_le` is uniform over the explicitly quantified path data, again only at the fixed anchor (`lean/YMGap/Continuum/CompactDualSlabExpandedFacePeelWeight.lean:302`-`317`).
- `anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap` explicitly names its coupling range and all completed vacuum-orthogonal vectors (`lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCenteredCompletedGap.lean:402`-`414`). It does **not** name beta or lattice spacing. Any description of this theorem as uniform in beta or `a -> 0` is unsupported by its statement.
- The requested “uniform posterior-variance fraction” has no statement at all; it is an open ledger obligation (`lean/SORRY_LEDGER.md:18110`-`18114`).
- `SingleStepDefectBound.singleStep` quantifies scale `k` but does not name a group, beta, lattice spacing, volume, or relation of `trueMargin` to a physical transfer (`lean/YMGap/Continuum/SingleStepDefectReduction.lean:284`-`297`).

## D. Which spectral gap?

### D.1 Operator actually bounded

The fixed finite-volume/finite-cutoff gap in `BF4PhysicalFiniteVacuumSectorPoincareGap.lean` bounds the quadratic form of the **row-conditioned normalized reflected BF4 joint kernel** on its marginal-mean-zero vacuum sector:

- `centralPhysicalConditionalKernel` divides the normalized reflected joint entry by its positive row marginal (`lean/YMGap/Continuum/BF4SU2FixedMagneticPhysicalMarkov.lean:246`-`262`).
- `centralPhysicalMarkovApply` applies that row-conditional kernel (`lean/YMGap/Continuum/BF4SU2FixedMagneticPhysicalMarkov.lean:668`-`678`).
- `centralPhysicalWeightedInner` uses the same reflected-law row marginal (`lean/YMGap/Continuum/BF4SU2FixedMagneticPhysicalMarkov.lean:693`-`704`).
- `centralPhysicalFiniteVacuumSector_abs_matrix_le_poincareRate_mul_diagonal` gives the strict finite-sector form bound at the explicit cutoff-dependent rate (`lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPoincareGap.lean:470`-`486`). The module itself states that the rate is not claimed uniform in cutoff (`:14`-`:17`).

This is **not a generator of a Markov/heat-bath dynamics on link variables**. The word “Markov” denotes conditional normalization of the symmetric OS/reflection (Choi) joint law. The source states this distinction explicitly: the partition-normalized reflected BF4 kernel is a symmetric joint probability law, and row conditioning produces the physical conditional operator (`lean/YMGap/Continuum/BF4SU2FixedMagneticPhysicalMarkov.lean:2`-`18`).

### D.2 Exact bridge from Markov notation to the OS/reflection joint form

The bridge exists and is algebraic, not a decay-of-correlations bridge:

- `centralPhysicalMarginal_mul_conditional_eqv_joint` recovers the normalized reflected joint entry from stationary marginal times conditional kernel (`lean/YMGap/Continuum/BF4WeightedJointPerronPerturbation.lean:707`-`746`).
- `centralPhysicalWeightedMarkovQuadratic_eq_joint` identifies the weighted Markov quadratic exactly with the symmetric physical joint quadratic (`lean/YMGap/Continuum/BF4WeightedJointPerronPerturbation.lean:751`-`760`).
- `centralPhysicalFiniteKernel` is definitionally the indexed normalized physical reflected kernel (`lean/YMGap/Continuum/BF4PhysicalCutoffFiniteIndexBridge.lean:62`-`66`).
- `centralPhysicalFiniteMatrixQuadratic_eqv_jointQuadratic` identifies its finite matrix quadratic with the normalized reflected joint quadratic (`lean/YMGap/Continuum/BF4PhysicalCutoffFiniteIndexBridge.lean:138`-`156`).

At the completed strong-coupling endpoint, the operator is stated directly as the OS even-time transfer: `strictJointCylinderCompletedTwoStepTransfer` is the time translation by two lattice half-steps, described as Euclidean spacing `2a` (`lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer.lean:37`-`44`).

No heat-bath generator-to-OS-transfer bridge is required by these declarations because no heat-bath generator is the bounded operator. A declaration identifying this finite BF4 operator with a continuum Hamiltonian exponential remains part of the open continuum reconstruction/spacing problem, not a finite heat-bath bridge.

## E. Diagram-to-code map

| roadmap node | backing declaration(s) and module(s) | ledger entry/status |
|---|---|---|
| Peel the complete component | Root component: `SlabFaceStrandSeed.component`, `lean/YMGap/Continuum/CompactDualSlabFaceStrandSeedComponent.lean:130`; accepted local peel: `SlabFusionWitnessFaceStrandSeed.lower_auxiliary_mem_atLink`, `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentDrop.lean:443`; global accepted target: `lowerAssignment_mem`, `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentAssignment.lean:144`; exact payment: `expandedFiberWeight_le`, `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentWeight.lean:566`; exact source reconstruction: `reconstructCompleteAssignment_eq`, `lean/YMGap/Continuum/CompactDualSlabFaceStrandComponentReconstruction.lean:362` (`WORKTREE-ONLY`). Exact boundary classification is NOT FOUND. | `[compact-dual-slab-face-strand-component-drop]`, `lean/SORRY_LEDGER.md:19062`; `[...-assignment]`, `:19103`; `[...-weight]`, `:19135`; `[...-reconstruction]`, `:19170` (`WORKTREE-ONLY`). Finite code counting remains open at `:19190`-`:19193`. |
| Exact heat-weight ratio | `anchorCoeffW_succ_le`, `lean/YMGap/Continuum/CompactDualSlabExpandedFacePeelWeight.lean:63`; `anchorPacketCoefficient_succ_le`, `:85`; exact candidate component ratio `anchorExpandedFaceAnimalCandidateRatio_eqv_one_51200`, `:456`. | `[compact-dual-slab-expanded-face-peel-weight]`, `lean/SORRY_LEDGER.md:18799`. The ledger explicitly says `1/51,200` is not yet a component summability theorem at `:18824`-`:18829`. |
| Uniform posterior-variance fraction | **NOT FOUND.** Existing identity only: `centralPhysicalFiniteVacuumSector_deficit_eqv_half_conditionalPairwiseVariance`, `lean/YMGap/Continuum/BF4PhysicalVacuumSectorConditionalVariance.lean:262`. | `[bf4-vacuum-sector-conditional-variance]`, `lean/SORRY_LEDGER.md:18094`; the positive cutoff-independent fraction is the open obligation at `:18110`-`:18114`. |
| Uniform strict form bound | Strong-coupling strict-joint route: `anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap`, `lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCenteredCompletedGap.lean:402`, for `0 <= coupling <= 1/400`. This declaration is not downstream of the component peel. Conditional finite-BF4 compiler: `fixedNome_completed_vacuum_form_gap_sixteenth`, `lean/YMGap/Continuum/BF4PhysicalFixedNomeCompletedOperatorNormGap.lean:109`, requires an uninhabited `FixedNomeCutoffCenteredSixteenth`. | Exact ledger entry for the unconditional strict-joint theorem/module: **NOT FOUND** after searching `lean/SORRY_LEDGER.md` for its module and declaration names. Related conditional compiler entry `[BF4-local-gluing-completed-operator-gap]`, `lean/SORRY_LEDGER.md:3469`, explicitly leaves its certificate and spacing/continuum work open at `:3484`-`:3493`. |
| Completed finite-volume spectral gap | Fixed finite rate: `centralPhysicalFiniteVacuumSector_abs_matrix_le_poincareRate_mul_diagonal`, `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPoincareGap.lean:470`; rate depends on cutoff. Conditional completed finite-cutoff theorem: `fixedNome_completed_vacuum_operator_norm_gap_sixteenth`, `lean/YMGap/Continuum/BF4PhysicalFixedNomeCompletedOperatorNormGap.lean:144`; its certificate is explicitly uninhabited at `:15`-`:18`. Independent completed strong-coupling OS theorem: `anchorDecoratedDoubledTimeRate_completed_vacuum_operator_norm_gap`, `lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap.lean:440`. No declaration connects the component peel to any of these gaps. | `[BF4-finite-vacuum-sector-poincare-gap]`, `lean/SORRY_LEDGER.md:4431`; it states cutoff dependence at `:4453`-`:4455`. The larger completed handoff is tracked under `[M4-same-object-continuum-gap]`, `lean/SORRY_LEDGER.md:359`; same-object cutoff/continuum inputs remain open. |
| Uniform thermodynamic and continuum passage | Thermodynamic strong-coupling bound exists: `orientedDoubledTimeCentralConnectedLimit_abs_le_geometric`, `lean/YMGap/Continuum/Z4CouplingParametricSignedThermodynamicClustering.lean:1392`; its module explicitly disclaims a continuum gap at `:11`-`:14`. Continuum/spacing transport is only the uninhabited interface `CompletedWeakToStrongRGBridge`, `lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointCompletedRGTransport.lean:135`, explicitly described as open/uninhabited at `:124`-`:135`. | `[M4-same-object-continuum-gap]`, `lean/SORRY_LEDGER.md:359`; the ledger retains continuum existence and same-object scaling/reconstruction obligations, including `ContinuumYMExistence` at `:577` and the open status summarized at `:1123`-`:1149`. |
| Continuum QFT axioms + isolated vacuum + `Delta > 0` | Interfaces exist but no inhabitant: `ContinuumYMExistence`, `lean/YMGap/Continuum/FourDExistence.lean:449`; `ContinuumYMWithGap`, `:487`; `ClayTarget`, `lean/YMGap/Rubric/ClayScorecard.lean:366`; `ClayTargetPinned`, `lean/YMGap/Rubric/ClayTargetPinned.lean:129`. `ym_mass_gap_of_existence` merely projects a gap from an assumed `ContinuumYMWithGap`, `lean/YMGap/Continuum/FourDExistence.lean:521`-`527`. | `[M4-same-object-continuum-gap]`, `lean/SORRY_LEDGER.md:359`. The ledger says `ContinuumYMExistence` and the corrected target remain uninhabited at `lean/SORRY_LEDGER.md:1123`-`:1149`. `ClayTarget` itself states that it has no inhabitant at `lean/YMGap/Rubric/ClayScorecard.lean:353`-`365`. |

### E.1 Diagram boxes with zero backing declarations

The following exact nodes/edges exist only as roadmap language; no backing declaration was found in the searched modules:

1. **Closed/classified boundary strand component** -- no declaration classifying rooted strand components by physical/time boundary behavior.
2. **Component-peel conditional-transition lower bound** -- no theorem turns the fixed-anchor energy payment/reconstruction into a lower bound for the actual physical conditional kernel.
3. **Uniform positive posterior-variance fraction** -- only the exact one-half identity exists; the lower fraction is explicitly open.
4. **Component/strand-to-`singleStep` compiler** -- no declaration imports or consumes both the component data and `SingleStepDefectBound`.

The other roadmap nodes are not zero-declaration boxes: they have either proved declarations with narrower scope or deliberately uninhabited structures. They are not thereby proved at the roadmap's full scope.

## REFUTATION CANDIDATES

**NONE FOUND.** No proved statement in the audited strand/component-to-gap material is both:

1. uniform in beta over a stated beta range, and
2. supported only by GROUP-AGNOSTIC declarations.

The potentially dangerous interface is `SingleStepDefectBound`: it is GROUP-AGNOSTIC at the type level and its prose calls the field a real non-abelian SU(N) estimate (`lean/YMGap/Continuum/SingleStepDefectReduction.lean:25`-`38`, `:284`-`:297`), but it is deliberately uninhabited (`:44`) and no beta-uniform theorem constructs it. The proven strand/component payment is NON-ABELIAN and fixed at `w = 1/400`; the completed `1/16` theorem is a strong-coupling statement over `0 <= coupling <= 1/400`, not a beta- or continuum-uniform statement. Therefore the audited source does not presently derive a false all-beta mass gap for compact U(1) in four dimensions.
