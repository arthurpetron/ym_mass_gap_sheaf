# Scope note: the cube-carrier ↔ Wilson-carrier bridge (2026-10-06 PT)

This note is a SCOPE NOTE only. No theorem is claimed. It makes no progress on the gap branch.

## 1. Exact statement (the open node)

Two carriers are involved. Fix a scale `j`, with nome `w_j` from the trajectory schedule and
width `width_j`.
- **Cube carrier.** `CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement w_j 0`.
  - It is the completed canonical root sector of the cutoff-removed adaptive physical BF4
    Markov carrier: SU(2), extent one, half-extent `0`.
  - Its inner product is `centralPhysicalVacuumSectorCylinderCompletedInner`, and its transfer
    is `centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer`.
- **Wilson carrier.** The all-nome literal-width Wilson completion `Completion w_j width_j`.
  - Its inner product is `completedInner`, and its time is `completedTime 1`, the geometric
    Euclidean time step.
  - It contains the vacuum complement `VacuumComplement` (`B U x = 0`) and the Expr anchors
    `Y_j`.

A **bridge at scale j** is a map `ι_j` from the cube vacuum complement to the Wilson vacuum
complement (or the reverse direction) with four properties:
1. **Isometric:** `completedInner (ι u) (ι v) = centralPhysical…CompletedInner u v`. Linearity
   then follows from the forms.
2. **Intertwining:** `completedTime 1 (ι u) = ι (centralPhysical…VacuumTransfer u)`.
3. **Range (for the gap → Wilson-anchor direction):** the anchor `Y_j` lies in `ι_j(…)`, or in
   its closure.
4. **Surjectivity (for B04's direction):** onto the Wilson vacuum complement, or onto the
   anchor's cyclic subspace. This is needed to turn a Wilson all-vector rate into the cube
   datum `CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData` that B04l
   consumes.

The bridge has two uses:
- **Cube → Wilson.** Given (1)–(3), a cube strict contraction at rate `q` gives
  `OrbitContraction (Y_j) q` on the Wilson carrier. This direction feeds the window/gap
  compatibility and `ExprCenteredContractionLower`.
- **Wilson → B04.** Given (1), (2) and (4), the `ExprPhysicalRateBand` of
  `BF4WilsonAllNomeExprTwoSidedBand` becomes a genuine B04l band. Today only the rational
  bookkeeping `b04Band_of_exprBand (hmatch : (gap j).rate = r j)` exists.

## 2. What is already in Lean

**Cube side**

| Declaration | File | Content |
| --- | --- | --- |
| `CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData` | `BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.lean:50` | All-vector squared-norm contraction datum (B04l input) |
| `CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement`, `centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer` | `BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.lean:50,58` | Cube vacuum complement and its transfer |
| `centralPhysicalVacuumSectorCylinderCompletedInner` | `BF4PhysicalCutoffVacuumSectorCylinderTransferLift.lean:39` | Cube completed inner product, pulled back from the global completion |
| `completedSectorContraction` (`w ≤ 1/2`) | `BF4PhysicalCubeCompletedMarginalGap.lean:58` | The only producer. Its header says: "does not identify geometric Euclidean time" |
| BF4PhysicalCubeObservableRealization module | `BF4PhysicalCubeObservableRealization.lean` | Dense reflected-form identification of cube states with literal cylinder observables, INSIDE the cube world. Its header says: "not a marginal-norm isometry, a completion equivalence, a geometric-time pin" |
| `PathCubeContraction`, `trajectoryDynamicFamily`, `nomeSchedule_eventually_not_le_half` | `BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:593-613` | B04l interface along the trajectory. Every schedule leaves `w ≤ 1/2` |
| `PathPhysicalContractionBand`, `pathCubeContraction_of_band`, `rateBand_of_pathPhysicalContractionBand`, `pathPhysicalContractionBand_of_rateBand` | `BF4WilsonAllNomeGenericNormalizedAnchor.lean:895-924` | The OPEN band, and its exact equivalence with B04l's band |
| `DynamicVacuumSectorPhysicalRateBand` | `BF4PhysicalDynamicVacuumSectorCompletedFamily.lean:121` | B04l's consumed shape |

**Wilson side**

| Declaration | File | Content |
| --- | --- | --- |
| `Completion`, `completedInner` | `BF4WilsonAllNomeCompletedInner.lean:59,64` | Wilson carrier |
| `completedTime`, `VacuumComplement` | `BF4WilsonAllNomeCompletedTime.lean:73,171` | Geometric time and the vacuum complement (time-invariant, `:174`) |
| `WilsonVacuumRayleighRate` | `BF4WilsonAllNomeH1FixedScale.lean:476` | OPEN for `r<1`. All-vector Rayleigh form `B(y,Ty) ≤ r B(y,y)` |
| `OrbitContraction`, `window_gap_compat` | `BF4WilsonAllNomeWindowGapCompatibility.lean:360,375` | Orbit contraction and the window/gap compatibility |
| `ExprPathOrbitContraction` | `BF4WilsonAllNomeExprWindowGapCompatibility.lean:65` | Expr-layer gap input |
| `ExprCenteredContractionLower`, `ExprPhysicalRateBand`, `expr_twoSidedBand_package`, `b04Band_of_exprBand` | `BF4WilsonAllNomeExprTwoSidedBand.lean` (this pass) | Packaging plus rational bookkeeping handoff |

**Elsewhere.** `BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff` and
`BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff` connect the B04l dynamic family to a
*selected Wilson OS/GNS datum*. They work through `RawMovingCubeWilsonMatrixCoefficientPin`
and the exact-rate handoff. Those data are UNINHABITED, and the selected GNS carrier is not
identified with the all-nome `Completion` above.

**Missing.** No declaration maps between the two carriers in either direction. Nor does any
declaration identify the two limiting forms on a common dense set. The 2026-10-05 audits record
this too ("no theorem links it to the all-nome Wilson carrier of A03"; "no bridge moves a cube
rate onto the Wilson carrier").

## 3. Verdict: NOT pure finite algebra; it needs new analytic input

The bridge needs four separate inputs, of which only the last is algebraic:
1. **Two different limits.** The cube form is the cutoff-removed limit of an adaptive
   conditional Markov form. The Wilson form is the exact-slab joint cutoff/time limit at
   literal width. Identifying them on a common dense set (cube cylinder states ↔ intrinsic
   Wilson expressions) equates limits of two different approximation schemes. That is
   convergence and uniqueness content, not a finite identity. At any finite cutoff the two
   constructions are different finite objects.
2. **A time pin.** The cube transfer is a marginal conditional dynamics, and its producer
   states that it "does not identify geometric Euclidean time". Intertwining with
   `completedTime 1` needs a geometric-time pin for the cube transfer. That pin is open
   analytic input, the same gap as the cube observable realization's "not … a geometric-time
   pin".
3. **Volume mismatch.** B04l's family is fixed at half-extent `0` (extent one), while the
   Wilson trajectory has growing `width_j`. Even scale by scale, the spatial extents differ.
   A bridge needs either an extent-matched cube family (new construction) or a
   restriction/conditional-expectation argument. Both are analytic, since they involve
   limits in the spatial direction.
4. **The transport itself (algebraic).** Given an isometric intertwiner with the range
   property (1)–(3), moving a cube all-vector contraction onto the Wilson anchor orbit is a
   one-line pullback of the norm inequality. It is pure algebra, but it is conditional on
   inputs 1–3, which are the content.

Decision: **I stopped at this note.** I did not add a conditional transport lemma, because it
would be another packaging of an unbuilt Type-level datum.

**What is needed.**
- (a) A common dense observable algebra together with a proof that the two limiting pairings
  agree on it, for the same `w`.
- (b) A geometric-time pin for the cube transfer.
- (c) An extent-matched cube family along `width_j`, or a proof that the extent-one sector
  embeds isometrically and time-equivariantly.
- (d) For B04, an ALL-VECTOR rate on the Wilson side (`WilsonVacuumRayleighRate`, or its
  squared-norm form) rather than the anchor-orbit contraction. Rayleigh ⇒ orbit contraction
  is paper-level (`AUDIT-WINDOW-GAP-COMPATIBILITY-2026-10-06.md`, remark).

Separately, B04 still needs the per-scale cube contraction for `w_j > 1/2` (the open
`PathCubeContraction`; see the B04l `w → 1` characterization). A bridge alone does not
provide that contraction.
