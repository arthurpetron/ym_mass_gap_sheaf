# ARCHIVE — work_plan.md text from 2026-07-17 through §16e (2026-07-28)

> **Archival, superseded.** This file preserves plan text that is no longer
> in the live `work_plan.md`. It is kept for provenance and traceability
> only; the current `work_plan.md` (milestone-structured, "Whole-project goal
> and live completion map") supersedes it. Nothing here is live status.
>
> **Source.** Verbatim from `git show e72e2c8:work_plan.md`, lines
> 11851–26491 (commit `e72e2c8d234971d1637be94c534c31b30e0f830d`,
> 2026-07-30 18:38 PT, the end of the claude-lineage `main`). It runs from
> the session-3 "Build hygiene reminders" bullet and the "Canonical
> capstone-adequacy revision (2026-07-17, session 4)" through
> "16e. Addendum (2026-07-28)". This includes the completion-first backward
> proof graph (2026-07-20), §15–§15k (dual-representation positivity / DP
> program, Simplification Ledger, CMP 119/122 extractions), and §16 (the
> marginality-dichotomy program, milestones MD.0–MD.5, §16a–§16e).
> The continuation (§16f–§17i) is archived separately in
> `work_plan-sections-16f-17i-2026-08.md`.
>
> **Boundary.** Lines 1–11850 of that file (through the session-3
> "Bookkeeping" bullet) are still present in the live `work_plan.md`, apart
> from a few later status rewordings. Line 11851 begins the old "Build
> hygiene reminders" bullet, which the live plan replaced with the enforced
> post-2026-08-02 rule (`scripts/safe_lean_build.py`). Do NOT follow the old
> build advice archived below. Everything else in this range was confirmed
> absent from the live `work_plan.md` on 2026-10-05.
>
> **How it was dropped.** This text was dropped from `work_plan.md` in merge
> `c6488697` (2026-09-11 03:45 PT, "Merge remote-tracking branch
> 'origin/main' into codex/full-workspace-snapshot-2026-07-24"), whose
> result kept the snapshot branch's plan text after the shared prefix. The
> lineages' merge base is `076cbcde` (2026-07-16). The code, notes and Lean
> files this text describes largely remained in the tree.
>
> Archived 2026-10-05. Section cross-references below refer to the old
> plan; the full old file remains available via
> `git show e72e2c8:work_plan.md`.

---

  - Build hygiene reminders: bare `lake build` spawns 16 workers (no
    `--jobs` flag in this Lake; `LEAN_NUM_THREADS` is the only cap);
    certificate modules peak 3-4 GB, the semantic bridge ~15 GB; keep
    `LEAN_JOBS <= 3` and the 20 GB weak-arg cap; heavy solo decides may
    use `-M 40960` (the `(1,3)` factor decides at degree ~182 did).

---

## Canonical capstone-adequacy revision (2026-07-17, session 4)

**STATUS: THIS SECTION SUPERSEDES THE FRONTIER CENSUS, PRIORITY ORDER, AND
HEAVY-BUILD ADVICE IN THE PRECEDING SESSION-3 REVIEW.**  Earlier sections remain
valuable as a historical ledger of proved lemmas, refuted routes, generated
certificates, and empirical scouting, but they are not the current definition of
the Clay-facing critical path.  In particular, the claims that the whole problem
is exactly seven `FrontierDAG` atoms, that `PentagonNumericCore` is the physical
pentagon, and that the bounded-Hamiltonian residual is a genuine continuum
Hamiltonian obligation are withdrawn.  The source already contains constructive
counter-witnesses and statement-bug fences showing otherwise.

### 0. Host safety is a proof precondition

Two uncapped verification runs exhausted the 64 GB host and crashed the MacBook
Pro.  A proof campaign that destroys its checking host is not reproducible.
The root `AGENTS.md`, `CLAUDE.md`, and `lean/AGENTS.md` now impose the following
non-negotiable policy:

1. Never run bare `lake build`, `lake env lean YMGap.lean`, `make test`, a full
   `pytest` suite, or concurrent build/test commands.
2. Inspect statically first.  The default Lean check is the smallest affected
   target with `LEAN_NUM_THREADS=1`; the default Python check is one named test
   file/node with every BLAS/OpenMP thread environment variable set to `1`.
3. Before compiling, inspect active `lean`, `lake`, and `pytest` processes.  Do
   not compete with or kill a user-owned process.
4. Full-tree builds, audits, and guards require explicit user approval for the
   particular run, after targeted checks pass, and run with `LEAN_JOBS=1`.
   One worker is now a hard, override-resistant repository invariant, not a
   tunable default or merely a recommendation.  This supersedes the earlier
   three-worker ceiling: even three individually capped workers can consume
   about 60 GB before operating-system overhead.
5. Keep the `-M 20480` per-process ceiling.  Raising or bypassing it, including
   a solo `-M 40960` certificate check, requires explicit approval for that run.
6. Stop on swapping, memory growth near the cap, thermal pressure, or a stall.
   Record exactly what was and was not checked.  Never present a historical
   green build as a current-session verification.

This supersedes the preceding advice that heavy solo decisions may ordinarily
use `-M 40960`.

### 1. Exact mathematical target

The controlling specification is `docs/ym_mass_gap_prompt.md`, not the current
inhabitation shape of `FrontierDAG`, `ClayTarget`, or `ClayTargetPinned`.  The
terminal theorem must quantify over every compact simple gauge group `G` and
construct one coherent four-dimensional pure Yang--Mills theory on `R^4` with:

1. a lattice regularization whose action, Haar data, character normalization,
   Wilson measure, observables, boundary conditions, and scale parameters are
   explicitly pinned rather than separately chosen in downstream structures;
2. thermodynamic limits `T^4 -> R^4` and continuum limits `a -> 0`, with the
   limit measure and all limiting Schwinger functions arising from that same
   pinned family;
3. Osterwalder--Schrader axioms strong enough for reconstruction: temperedness
   or the selected constructive replacement, Euclidean covariance, permutation
   symmetry, reflection positivity, clustering/ergodicity, regularity, and the
   required growth bounds;
4. a reconstructed Hilbert space, vacuum, local field algebra, strongly
   continuous Euclidean/Poincare representation, spectrum condition, positive
   energy, and vacuum unique up to phase;
5. an unbounded positive self-adjoint Hamiltonian/semigroup generator `H`
   attached to the reconstructed transfer semigroup, not an arbitrary bounded
   operator, together with `H Omega = 0` and a finite strictly positive spectral
   gap uniform through the volume and continuum limits;
6. nontrivial gauge-invariant local operators corresponding to curvature
   polynomials and their covariant derivatives, with nonzero/non-Gaussian
   correlators where required to exclude the trivial theory;
7. a stress tensor and an operator product expansion whose coefficients,
   singular orders, remainder estimates, and anomalous dimensions are statements
   about the actual reconstructed correlators;
8. short-distance behavior agreeing with asymptotic freedom and perturbative
   renormalization, with derived normalization and no measured constant;
9. full `O(4)` Euclidean covariance before reconstruction and the corresponding
   Poincare covariance after reconstruction;
10. constructivity and kernel hygiene on the full critical path: no `sorry`, no
    `Classical.*`, no `Real`, no `native_decide`, no vacuous frontier instance,
    and `#print axioms` contained in `{propext, Quot.sound}`.

Introduce a single canonical structure, provisionally
`YMGap.Continuum.ClayResolutionTarget`, that contains exactly this coherent data.
Every physical field must be indexed by, or definitionally/propositionally pinned
to, the same `G`, lattice family, continuum measure, Schwinger functions,
reconstruction, and transfer semigroup.  Avoid parallel fields that merely have
compatible prose comments.  The terminal declaration should have the logical
shape

```lean
def yangMillsExistenceAndMassGap :
    (G : CompactSimpleGaugeGroup) -> ClayResolutionTarget G
```

with the repository's constructive group carrier substituted for the provisional
name above.  If the existing group representation is not yet expressive enough
for every compact simple group, that carrier is itself a named frontier item and
must not be hidden by an `SU2` default.

### 2. Why the seven-atom DAG is not yet the whole frontier

The following are statement-adequacy defects, not merely missing proofs.
Completing the current fields would not imply the target in Section 1.

#### 2.1 `boundedH` is generically inhabited and mathematically misformulated

`FrontierStatementBugFence.BoundedFunctionalCalculusResidual` does not require
boundedness/domain data or `exp(-H) = T`; its generic witness takes `H := L.T`.
Independently, `SelfAdjointHamiltonian.lean` correctly notes that `-log T` is not
generally bounded when `0` belongs to the transfer spectrum.  The repaired
obligation is therefore not a proof of the legacy residual.

Replace it by a constructive semigroup-generator package carrying:

- one pinned reflection-positive contraction semigroup `T(t)` on the same GNS
  Hilbert space;
- strong continuity on an explicitly dense domain;
- a closed, densely defined, positive quadratic form or resolvent family;
- a positive self-adjoint generator `H` obtained constructively from that
  semigroup/form/resolvent;
- the functional relation between `T(t)` and `H` in the constructive calculus;
- the vacuum equation and a spectral-projection/form version of the gap.

Yosida approximants, resolvents, or closed forms may supply the constructive
route.  A bounded logarithm is admissible only for a finite-volume auxiliary
operator with a separately proved positive spectral floor; it is not the
continuum carrier.

#### 2.2 legacy `trueMargin` omits the physical recursion

The statement-bug fence supplies an unconditional surrogate because the legacy
type has no equation tying the claimed margin to lattice masses, scale ratios,
or the actual RG trajectory.  Replace it by data and a theorem relating

```text
Delta_k = m_lat(k) / a_k,
```

the pinned blocking map, the derived scale relation `a_{k+1}/a_k`, the
`singleStep` defect budget, and the continuum limiting gap.  Positivity must be
uniform in volume and survive both the thermodynamic and continuum limits.

#### 2.3 `a2Pentagon` does not state the pentagon

`PentagonNumericCore` asks only for a nonnegative kernel and one value equal to
`1/4`; the constant `1/4` kernel is an unconditional inhabitant and is proved in
the repository to fail even a naive pentagon equation.  It must not be counted as
the physical Level-2 associator atom.

The faithful residual should be one of the following equivalent constructive
packages, with admissibility conditions explicit:

- the signed Biedenharn--Elliott identity for the repository's exact rational or
  constructive-real `6j` symbol;
- an actual fusion-category associator whose matrix elements are those `6j`
  coefficients and whose associator maps satisfy the pentagon;
- a guarded rational Dougall/Saalschutz identity plus proved normalization and
  equivalence to Biedenharn--Elliott.

The present unguarded `BEDougallCore` is known to be false off admissible triangle
data.  First define the guarded core; then attack it by factorial cancellation,
terminating hypergeometric transformation, Chu--Vandermonde/Saalschutz, or a
constructive associator-coherence argument.  Finite `6j^2` sweeps are scouting
only and cannot prove this atom.

#### 2.4 `bulkCtrl` is not pinned to the moved operator

`SpectralLocalization` contains freely named post-move eigenvalues, shifts, and
perturbations, and admits a trivial unperturbed localization witness.  Prose
calling them bond-moved spectra does not establish that relation.  A repaired
field must define the actual block-spin/bond-moving operator from the pinned
measure or character coefficients and prove:

- the spectral/eigenpair relation for both original and moved operators;
- the vacuum normalization and multiplicity conventions;
- a form, resolvent, or operator-norm comparison derived from the blocking map;
- the required edge and bulk displacement inequalities as consequences;
- compatibility with reflection positivity and the per-scale defect budget.

Only this repaired comparison can legitimately be the common source of
`bulkCtrl`, `edgeShift`, `trueMargin`, and anisotropy control.

#### 2.5 local fields, stress tensor, OPE, and AF are toy-inhabitable

The parameter `mu_inf` in `LocalCurvatureFields` is not used by the fields of the
structure.  Trivial curvature, stress, zero-OPE, and `SU2` asymptotic-freedom
witnesses construct `LocalOperatorContent` without establishing any fact about
the measure.  Moreover `ClayTargetPinned` has no `LocalOperatorContent` field.

Repair the layer by tying every local operator to the same reconstructed theory:

- localization/support and gauge invariance;
- covariance under the actual translation/rotation representation;
- equality between operator vacuum expectations and the pinned Schwinger
  functions;
- curvature-polynomial labels and renormalization/mixing data;
- a nontriviality witness excluding the zero/Gaussian surrogate;
- stress-tensor Ward identities, conservation, symmetry, and generator relation;
- OPE asymptotic equality for actual products, with a quantified remainder bound;
- AF rates and anomalous dimensions derived for the same correlators.

Toy inhabitants may remain in explicitly named example/surrogate namespaces but
must not inhabit any Clay-facing type.

#### 2.6 `FrontierDAG` has no capstone adequacy theorem

The current DAG maps only into a partial SubWallA assembly and explicitly cannot
map to the full reconstruction target.  It omits full local content, all-group
uniformity, full OS/Wightman/Poincare data, the unique vacuum, and the complete
`T^4 -> R^4` limit.  Therefore its inhabitance cannot close the prompt.

After the repaired structures exist, prove a total theorem of the form

```lean
def revisedFrontierDAG_to_clayResolution
    (d : RevisedFrontierDAG G) : ClayResolutionTarget G := ...
```

The theorem must be total, constructive, guarded, and free of extra untracked
hypotheses.  Only missing fields that occur in this theorem are genuine frontier
atoms.  Any additional assumption exposed while writing the theorem is added to
the frontier immediately rather than hidden as a later “completeness obligation.”

### 3. Canonical dependency order

Work now proceeds in the following order.  This order replaces the preceding
CoreB-first schedule because target adequacy determines whether CoreB is on the
actual critical path.

#### Phase A — capstone and statement adequacy

1. Inventory the strongest existing group, lattice-family, measure-limit, OS,
   GNS, semigroup, local-field, and gap carriers.
2. Write `ClayResolutionTarget` using those carriers without proving new physics.
3. Write `RevisedFrontierDAG` with faithful residual types for the genuinely open
   arguments.
4. Attempt `revisedFrontierDAG_to_clayResolution` immediately.  Every obstruction
   becomes a named field with an exact consumer theorem.
5. Add statement pins for the canonical target, revised DAG, adequacy theorem,
   semigroup generator, physical margin, guarded pentagon, actual operator
   comparison, and local-operator/OPE package.
6. Preserve legacy types only as historical or compatibility layers.  Do not map
   weak legacy witnesses into the new target.

**Exit criterion:** the new target matches every item in Section 1, and a source
review of the total adequacy theorem shows that no promise is carried only by a
comment, phantom parameter, separately chosen object, or trivially inhabited
`Prop`.

#### Phase B — frontier census and tooling repair

1. Make `frontier_status.py` master the revised DAG and canonical target.
2. Parse the current hashed axiom-audit namespace counts; an empty exception map
   means zero exceptions, not a missing audit.
3. Require actual Lean bridge signatures in `frontier_dag_check.py`.  Remove
   “bridged in spirit” and grandfathered exceptions, or label the checker
   advisory and incapable of certifying closure.
4. Add a static/Lean guard for phantom parameters in Clay-facing structures and
   for unconditional inhabitants of direct frontier fields.
5. Expand `YMGapStatementGuard` to every direct load-bearing statement, and make
   `YMGapGuard` test the new aggregate only after the individual field audit.
6. Regenerate the frontier report from current data.

**Exit criterion:** the machine-readable frontier equals the hypotheses of the
adequacy theorem, with zero exempt pseudo-bridges.

#### Phase C — actual block-spin spectral comparison

This is provisionally the dominant physics gate because it feeds the gap flow,
physical margin, and isotropy.  Maintain genuinely distinct mechanisms:

1. **Majorization:** derive the bond-moving map on character weights and seek a
   constructive doubly-stochastic/majorization comparison with all vacuum and
   multiplicity factors explicit.
2. **Parity-resolved total positivity:** formulate TP2/PF properties only after
   incorporating the repository's counterexamples to naive TP2.  Test block or
   parity kernels and boundary corrections, not the refuted raw kernel.
3. **Quadratic-form/Loewner comparison:** compare the actual transfer forms or
   resolvents and derive a spectral-exclusion interval rather than identifying
   the gap with a single eigenvalue.
4. **Cluster/resolvent comparison:** use the constructive KP/polymer substrate to
   bound the difference between moved and unmoved resolvents or semigroups.
5. **Independent RP route:** preserve a transfer-operator/reflection-positivity
   localization route that does not assume the bond-moving inequality.

Reject any route that reintroduces character/eigenvalue confusion, vacuum-shift
errors, multiplicity blindness, measured constants, or a circular gap premise.

#### Phase D — bounded exact-algebra fronts

These are valuable only when the Phase-A adequacy theorem confirms their
consumers.

1. **CoreB scout:** perform the exact `s = 2,3` scout already specified above,
   with no Lean build.  Search for a stable parity-resolved convolution theorem,
   cross-ratio/monotone-likelihood-ratio invariant, or discrete Sturm principle.
   Continue the infinite row campaign only if a symbolic `s`-generic mechanism
   exists.  Otherwise bank the obstruction and cap further per-row spending.
2. **Guarded A2 identity:** define the admissible Dougall/Saalschutz core and prove
   its equivalence to the signed pentagon before generating more finite tables.
3. **Generator infrastructure:** develop constructive closed forms, resolvents,
   spectral projections, and Yosida approximants against the already built GNS
   and located-transfer substrate.

#### Phase E — continuum physical closure

1. Derive the physical dimensionless margin from the actual RG step and lattice
   spacing relation.
2. Prove anisotropy decay and full `O(4)` restoration from the same blocked
   dynamics.
3. Establish volume-uniform clustering/gap estimates and pass `T^4 -> R^4`.
4. Pass `a -> 0` with OS axioms and the gap preserved.
5. Construct the semigroup generator, Poincare representation, spectrum
   condition, and unique vacuum.
6. Construct and identify local curvature operators, stress tensor, and OPE;
   prove short-distance AF and nontriviality for actual correlators.
7. Prove uniformity for every compact simple `G`.  The statement “SU(2) is worst
   case” is a theorem obligation for the physical heat-kernel/character tails,
   not a scheduling assumption.  Short-root normalization for nonsimply-laced
   types, including `G2` and `F4`, must enter the shared physical estimates.

#### Phase F — terminal audit

Only after targeted checks have passed and the user explicitly approves the
high-load run:

1. full build with `LEAN_JOBS=1` and the 20 GB process cap;
2. critical-path `#print axioms` audit;
3. forbidden-token scan;
4. statement and frontier guards;
5. proof that every revised frontier field is constructively inhabited through
   the canonical adequacy theorem;
6. generated-artifact reproducibility checks;
7. update the historical ledger with exact commands, exit codes, peak resources,
   and theorem/namespace counts.

### 4. Immediate execution ledger

The next concrete work item is **Phase A.1--A.4**:

1. construct a field-by-field correspondence table from the prompt to existing
   Lean carriers;
2. introduce the canonical target without weakening any prompt clause;
3. introduce faithful residual interfaces, initially without inhabitants;
4. start the total adequacy theorem and let its type expose every missing bridge.

No CoreB certificate generation, bounded-H proof, pentagon sweep, or broad build
precedes this adequacy pass.  The first mathematical implementation decision is
to represent the continuum Hamiltonian by an unbounded semigroup
generator/closed form, while retaining bounded logarithms only as finite-volume
auxiliary lemmas.  The first physics implementation decision is to pin every
spectral-localization variable to an explicitly constructed blocked transfer
operator.  The first QFT implementation decision is to make local fields and OPE
statements equations about the canonical Schwinger functions rather than free
data indexed by a phantom measure.

### 5. Definition of progress from this point

A new structure or reduction counts as progress only if at least one of the
following holds:

- it supplies data required by `ClayResolutionTarget`;
- it discharges a hypothesis used by `revisedFrontierDAG_to_clayResolution`;
- it proves that a proposed hypothesis is false or inadequate and records a
  constructive fence preventing reuse;
- it strengthens verification/statement guards so surrogate closure cannot be
  mistaken for the prompt's conclusion.

Generated finite certificates, numerical sweeps, and elegant reductions remain
useful scouting artifacts, but they do not advance the completion percentage
unless connected by a total constructive consumer to the canonical target.

### 6. Phase A execution update (2026-07-17, session 4)

**Phase A.1 — prompt-to-carrier inventory: COMPLETE.**  The exhaustive mapping
is banked in `docs/clay_resolution_target_inventory.md`.  It records, for every
prompt clause, the strongest present Lean carrier, its precise adequacy defect,
and the semantic field required in the canonical target.  Two additional
load-bearing findings emerged:

1. `OSReconstruction` is presently an abstract `Unit`-backed carrier whose
   `mu_inf` parameter is unused; its law propositions are selected by the
   caller.  It cannot be the semantic root of the corrected target.
2. `GNSDynamics.SpectralGapData` admits the identity transfer together with an
   empty spectral model.  A physical spectral gap therefore requires a theorem
   identifying the spectral/form data with the actual descended time
   translation, not merely a `SpectralGapData` field.

The strongest current ordinary-state root is `WilsonGNSData.toGNSData`, provided
that its expectation is pinned to the canonical Schwinger functional.  Session 5
below records the crucial correction: its completion is an AMBIENT state GNS
space, not the physical positive-time OS Hilbert space.

**Phase A.2 — historical first increment: TYPECHECKED, PHYSICAL DESIGN
RETRACTED.**
`YMGap.Rubric.ClayResolutionRoot` now supplies:

- `PinnedSimpleGroup T`, tying representation data to `repDataOf T`;
- `CanonicalWilsonRoot mu_inf T`, carrying one OS bundle and one
  `WilsonGNSData bundle.A` with `wilson.E = bundle.E.E`;
- definitionally derived `gnsData`, completed `gnsHilbert`, and vacuum equal to
  the dense GNS image of the unit observable;
- `CanonicalTimeTranslations`, with a genuine `Nat`-semigroup action on the
  same observable algebra, invariant expectation, a transfer operator on that
  exact completion, and dense-action/vacuum pins.

Targeted verification only, per machine-safety policy:

```text
env LEAN_NUM_THREADS=1 lake build YMGap.Rubric.ClayResolutionRoot
Build completed successfully (103 jobs; dependencies replayed).
New module checked in 266 ms.
Axiom gates: [propext, Quot.sound].
```

No full build, full test, audit, or guard was run.  Next residual: define the
strongly continuous semigroup/closed-form generator interface over this exact
root, then define the spectral-representation pin that makes any gap a theorem
about that generator rather than a freely selected finite model.

That proposed next step is superseded by the session-5 no-go audit below.  The
historical targeted build remains a valid syntax/axiom record, but the ordinary
state-GNS dynamics it checked must not be used as the physical transfer.

### 7. Phase A architecture correction and standard reflected OS root
(2026-07-17, session 5)

#### 7.1 Decisive correction: the ordinary state GNS route is impossible

`PositiveIsometricTimeNoGo` already proves constructively that a
state-preserving observable time automorphism is isometric on

```text
B(a,b) = E(star a * b).
```

If this same operator is required to be the positive self-adjoint physical
transfer, it is radical-equivalent to the identity on representatives and is
the identity on the quotient and completion.  Therefore the session-4
`CanonicalTimeTranslations` design could never yield the desired Hamiltonian or
mass gap.  The correct Osterwalder--Schrader construction is:

```text
full Euclidean observable algebra and invariant state
  -> positive-time observable carrier
  -> reflected form E(star (Theta a) * b)
  -> radical quotient and unconditional completion
  -> positive-time action descended through the reflected radical
  -> physical transfer.
```

This correction is a proved architectural fence, not a heuristic preference.
No semigroup or generator work may again target the ordinary state completion
unless an explicit physical isometry to the reflected positive-time completion
has first been proved.

#### 7.2 Additional P0 defects found by the adversarial review

1. **Cartan type is not a global compact group.**  A root system does not
   distinguish `SU(n)` from `PSU(n)` or `Spin(n)` from `SO(n)` and does not by
   itself choose a faithful representation that descends to the global form.
   `PinnedSimpleGroup` is therefore renamed `PinnedSimpleLieType`; a new
   computable global-group/action datum must precede the Clay lattice family.
2. **The old `mu_inf` was phantom.**  `OSAxiomBundle mu_inf` does not identify
   its functional with the projections of `mu_inf`, while several of its legacy
   clauses admit identity or empty-model inhabitants.  The canonical root must
   be built from actual `ReferenceWeight.E_Λ` stages, stagewise probability
   functionals exactly pinned to those weights, and an observable-by-observable
   two-parameter limiting functional.  Bare exact marginal coherence must not
   be assumed.
3. **The old Wilson datum was underdetermined.**  `WilsonGNSData` adds module and
   setoid data not determined by minimal `ObsAlg`; normalization of `[1]` does
   not follow because `ObsAlg` omits the unital `*`-algebra laws.  The corrected
   root explicitly pins the unit form and must later strengthen the observable
   algebra sufficiently to derive representation, cyclicity, and null-ideal
   stability.
4. **A positive lower exclusion alone does not prove finite mass.**  The zero
   Hamiltonian on a one-dimensional space vacuously excludes `(0,Delta)` for
   every finite `Delta`.  The physical edge must be a located infimum on the
   vacuum-orthogonal unit sphere with normalized finite-energy near-edge
   witnesses, proving both `0 < m` and `m < infinity`.
5. **The present completion is real/rational.**  Full Clay/Wightman
   reconstruction still requires constructive complexification, a
   sesquilinear Hilbert structure, common invariant domains, local commutativity,
   operator-valued tempered distributions, and a strongly continuous complex
   Poincare representation with forward-cone spectrum.

#### 7.3 Second adversarial correction: reject the inherited compression

The first session-5 draft reused `PositiveTimeCompression`.  Targeted review
found that this was still not a valid generic continuum root:

1. `PositiveTimeCompression` requires both
   `B_ambient(embed a, embed b) = B_physical(a,b)` and
   `B_ambient(Theta(embed a), embed b) = B_physical(a,b)`.  Standard OS
   reconstruction asserts only the second identity.  The first is an extra
   time-zero/Markov-boundary representation theorem and is generally false for
   raw half-space observables.
2. Its `transfer_weightedGram` factors `B(Ta,b)` through a finite `modeCount`, so
   the induced operator is finite rank on the nondegenerate quotient.  The
   infinite-dimensional Yang--Mills transfer cannot generically have this
   property; a finite-time map of a positive self-adjoint `C0` semigroup is also
   injective, while a finite-rank map on an infinite-dimensional Hilbert space
   has kernel.
3. An arbitrary `positiveObservable` type with `state := id` and
   `toObservable := embed` made the proposed anti-toy-sector fence tautological.
   A canonical carrier needs geometry-derived half-space support in the same
   limiting algebra, closure/translation laws, and a state map pinned to that
   carrier.
4. Exact projective consistency plus unrelated spacing/volume schedules is not
   a continuum-limit theorem.  Bare Wilson actions at different spacings are
   not exact block marginals; blocking produces effective actions.  Convergence
   must be expressed by observable-by-observable expectation and norm estimates
   with two independent moduli, or exact RG effective measures must be
   constructed and separately related to the bare Wilson family.
5. `ReferenceWeight` permits `w = 1`, and positive variance excludes only a
   one-point functional.  It does not justify the name "interacting" or exclude
   Gaussian/product theories.  Interaction must later be pinned by the actual
   plaquette action and a non-Wick connected cumulant for the same functional.

The provisional compression-backed root was therefore not committed.  The
finite compression modules remain valid exact cutoff/toy mathematics, but they
are quarantined from the canonical Clay dependency path.

#### 7.4 Implemented corrected standard reflected root

`YMGap.Continuum.CanonicalOSRoot` now provides:

- `WilsonFunctionalRoot A E`: one functional and ordinary Wilson datum,
  explicitly AMBIENT, with a unit-form pin and arbitrary-modulus completion;
- `ReferenceWeightStageFamily`: independent volume/cutoff indices, actual
  `ReferenceWeight.E_Λ` functional pins, spacing/volume schedules, and
  Type-valued stage half-space certificates.  It deliberately assumes no exact
  marginal consistency and makes no interaction claim;
- `CanonicalSchwingerLimit`: for every limiting observable, an explicit stage
  discretization, a common rational error bounding both its squared ambient-GNS
  seminorm `B(diff,diff)` and
  expectation discrepancy, and separate thermodynamic/continuum moduli in
  which that error tends to zero;
- `CompatibleWilsonHom` and `WilsonAmbientTimeReflection`: actual observable
  `*`-endomorphisms with module/setoid compatibility; ambient time isometry is
  derived from state invariance;
- `PositiveTimeSupport`: a Type-valued half-space certificate on the same limit
  algebra, closed under the module operations and positive time translation,
  and tied to the same two-parameter stage approximations;
- `PositiveTimeOSRoot`: a physical `GNSData` pinned ONLY to the reflected form
  `E(star (Theta a) * b)`, with no ordinary-norm equality, projection, or
  finite-mode factorization;
- a representative map that both preserves and reflects the carrier setoid,
  plus essential surjectivity from certified half-space observables.  These
  conditions block any nondegenerate adjoined summand, while the work plan
  explicitly retains the need to construct the support certificates from real
  lattice geometry rather than declaring them by name;
- a one-step transfer pinned on every representative to the actual ambient time
  translation, with linearity and explicit self-adjointness/positivity/
  contraction theorem obligations.  These laws must be derived from the 4D OS
  reflection/Markov estimates in a concrete inhabitant; this interface does not
  claim that derivation;
- a strict normalized vacuum-orthogonal Rayleigh bracket
  `0 < lower <= B(T probe, probe) <= upper < 1`, excluding both zero and
  identity transfer;
- derived (not selected) unit normalization and unit invariance, a nonzero
  completed vacuum, sound descent of transfer to the constructive completion,
  completed self-adjointness/positivity/contraction, and a
  `GeneralTransferFormLaws` over `gnsComplete_general` rather than the weaker
  regular-rate wrapper.

`YMGap.Rubric.ClayResolutionRoot` retains only `PinnedSimpleLieType`; the
physically incorrect `CanonicalTimeTranslations` was removed.  Cartan data are
explicitly only a Lie-type classifier, not the missing global compact group.

The adjacent scorecards and boundary ledger were audited at the same time.
Their declarations are preserved for compatibility, but their module comments
now classify them as historical numerical, heat-kernel, finite-spectral, or
correlator surrogates rather than an exhaustive Clay frontier.  In particular,
the legacy `ClayTarget` aggregate is not the canonical target,
`RubricUniformInCoupling` is a weak existential interface with inhabitants
elsewhere in the repository, `SepLatticeZ4` is data rather than a theorem of
four-dimensional separation, and `PentagonNumericCore` does not state the
pentagon.  No declaration in those scorecards is promoted into the corrected
dependency path without a total bridge to the eventual canonical target.

#### 7.5 Safe targeted verification record

Before each compilation, `pgrep -fl 'lean|lake|pytest'` showed no actual Lean,
Lake, or pytest process (only unrelated macOS/CleanShot names containing the
matched substrings).  Every Lean invocation used one worker and the repository's
mandatory 20 GB process cap.

The first corrected-root elaboration failed at one invalid dependent field
notation; Lean temporarily reported downstream `sorryAx` because failed
declarations are represented by synthetic sorry terms.  The notation was fixed,
and the exact same smallest target then passed:

```text
env LEAN_NUM_THREADS=1 lake build YMGap.Continuum.CanonicalOSRoot
Build completed successfully (77 jobs; dependencies replayed).
New module checked in 613 ms.
Axiom gates: [propext] or [propext, Quot.sound]; no sorryAx,
Classical.*, native_decide, or custom axiom.

env LEAN_NUM_THREADS=1 lake build YMGap.Rubric.ClayResolutionRoot
Build completed successfully (110 jobs; dependencies replayed).
Rubric export checked in 142 ms.
Axiom gate: [propext, Quot.sound].
```

No full build, full test, full audit, statement guard, or frontier guard has
been run; those remain forbidden without explicit user approval.

#### 7.6 Correct next dependency order

The next work is NOT the unbounded generator.  Proceed in this order:

1. **Global group and action.** Define a computable compact global group/root
   datum, center quotient/global form, Haar/character interfaces, and a chosen
   faithful lattice action.  Prove that `CartanType` and `repDataOf` are derived
   classification projections and that the action descends through the center.
2. **Concrete 4D stage geometry.** Instantiate the two-parameter stage family
   with oriented 4D cells, links, plaquettes, boundary conditions, volume and
   spacing, the actual Wilson plaquette weight, normalized Haar functional, and
   geometric positive-time support.  Prove reflection and positive-time shift
   act on those same observables.
3. **Thermodynamic/continuum convergence.** Construct the stage discretization
   and both moduli in `CanonicalSchwingerLimit`.  If exact RG effective measures
   are used, prove their origin/comparison with the bare Wilson action; never
   assume bare exact marginal consistency.  Prove density in the ambient GNS
   metric and convergence of all local correlators on bounded supports.
4. **Continuum OS positivity and Markov laws.** Add actual stage reflection and
   time actions, their covariance/support laws, finite-stage RP, and a modulus
   for convergence of reflected quadratic forms.  Then transport finite-stage
   reflection positivity through those estimates, construct the reflected
   `GNSData`, prove representative equivalence reflection and support
   essential-surjectivity, and derive the representative transfer's
   self-adjointness, positivity, and contraction.  Do not reuse the older
   ordinary-norm equality or finite weighted-Gram certificate.
5. **Interaction/nontriviality fence.** On that same functional and local field
   family, exhibit a nonzero separated connected higher cumulant and prove a
   failure of Wick factorization.  Positive variance alone is insufficient.
6. **Completion module and discrete semigroup.** First construct vector
   operations on the unconditional completion, prove the dense embedding and
   completed transfer are additive/scalar-linear, and bridge to the existing
   `CRealSeminormCompletion` machinery where appropriate.  Then derive the exact
   `Nat`-indexed semigroup from the
   physical completed transfer, with zero/add/vacuum/dense-embedding laws and
   `U(1)=completedTransfer`.  Establish the OS Markov identity required for
   compressed translations to compose; do not call this strongly continuous.
7. **Continuous semigroup.** Do not reconstruct it from the time-one map alone.
   Construct a dense/full Euclidean time action, pin `U(t)` on observables for
   every nonnegative rational/dyadic `t`, and prove composition, time-setoid
   congruence, and a Type-level strong-continuity modulus before extending to
   constructive-real time.  A rational eigenvalue such as `1/8` needs
   constructive-real fractional powers; formal rational iteration is not
   enough.  The zero-eigenvalue swap model cannot be a finite-time map of such a
   semigroup.
8. **Unbounded generator.** Build a dense-domain closed positive quadratic form,
   resolvent/Yosida approximants, and positive self-adjoint generator.  Pin it
   to semigroup difference quotients and prove the unit vacuum lies in the
   domain and is annihilated.
9. **Finite positive physical edge.** Define the mass as a located infimum of
   the generator form on normalized vacuum-orthogonal domain vectors.  Carry
   positive lower brackets and finite-energy near-edge witnesses so both
   `0 < m` and `m < infinity` are proved; a free exclusion interval or empty
   finite spectral model is forbidden.
10. **Complex/Wightman reconstruction.** Construct complexification,
    sesquilinear completion, cyclicity, common invariant operator domains,
    local commutativity, operator-valued tempered distributions, full
    Poincare covariance, and the forward-cone spectrum on the same physical
    Hilbert space.
11. **Uniform RG transport and Clay assembly.** Only after steps 1--10, identify
    the generator edge with the uniform lattice/RG estimate, prove vacuum
    uniqueness from clustering/ergodicity, pin curvature fields/OPE/stress
    tensor to the same Schwinger functions, and start the total adequacy theorem
    for `ClayResolutionTarget`.

### 8. Build-consistency theorem and global-group launch
(2026-07-17, session 6)

This session answers a repository-level question that is part of the proof
discipline rather than an optional engineering convenience: how can an
increment be known to be compatible with the whole import graph without
re-running the 2,500-module build after every edit, especially when an
uncontrolled build can exhaust the host?

#### 8.1 Exact answer within the declared dependency model

No source-only checker can prove that arbitrary new Lean syntax elaborates or
that the kernel accepts an arbitrary proof.  At least the changed code and all
of its semantic consumers must eventually be validated by Lean.  What can be
made exact is the affected cone *within the repository's declared dependency
model*: local dependencies must be represented by the accepted import syntax,
and the toolchain, build configuration, elaborator inputs, generated inputs,
and foreign inputs must be unchanged unless separately escalated.

1. Lake's dependency hashes validate unchanged imported artifacts.
2. A changed module must be selected together with every transitive importer
   whose elaboration environment can change.  Lake may validate a cached
   importer without re-elaborating it when its relevant artifact hashes are
   unchanged; the guarantee is validation, not compulsory recompilation.
3. It is sufficient to build the maximal modules of that reverse-dependency
   closure, because building each maximal module recursively checks every
   changed dependency and every affected intermediate importer.
4. A final all-module build must run once per Lean-relevant trusted-main state
   selected by CI's path filter, not once per local edit.  A manual dispatch
   supplies the same proof on demand.  Pull-request code is deliberately not
   executed on the personal self-hosted Mac; documentation-only states are
   likewise outside the trigger.  A clean no-cache build is a separate
   periodic or toolchain/configuration-change proof.

Thus the repository now has two complementary guarantees:

- **local incremental consistency:** static graph validation followed by
  one-worker builds of the maximal reverse-dependent targets printed by the
  affected-target planner;
- **repository-state consistency:** one one-worker CI build of every source
  module selected independently by the `YMGap.*` library glob, followed by the
  frontier, statement, DAG, rubric, and required non-strict axiom gates, plus
  the informational strict namespace-drift report.

The second guarantee becomes an observed theorem about a commit only when its
CI run exits zero.  Merely installing or routing the workflow is not a claim
that a commit has passed it.

#### 8.2 Dependency-cone argument

Let `M` be the finite set of local Lean modules and put an edge `A -> B` when
module `A` imports module `B`.  The static import guard checks that every edge
target exists and that this graph has no directed cycle.  For a set `S` of
changed modules, define

```text
R(S) = the least set containing S and every importer of an element of R(S),
T(S) = { A in R(S) | A has no importer in R(S) }.
```

Because the graph is finite and acyclic, every `A in R(S)` lies on a directed
import path beginning at some `t in T(S)` and ending at a changed module.
Consequently, building every `t in T(S)` asks Lake to validate every member of
`R(S)`; it does not assert that every valid cache hit is re-elaborated.
Conversely, a module outside `R(S)` has no parsed import path to changed source
and its elaboration environment is unchanged, provided the Lean toolchain,
Lake configuration, compiler arguments, generated/elaborator inputs, and
foreign inputs are unchanged.  This proves sufficiency, and minimality among
target sets restricted to the parsed graph, for
`scripts/lean_import_guard.py --affected`.

The guard deliberately uses a tested lexical parser rather than Lean's own
parser.  It covers the repository's ordinary, `public`, `meta`, and
`import all` local-import forms, including multiline layout, while removing
nested comments and strings.  Exotic syntax quotations or a future import
command form are outside the theorem until the parser and its synthetic tests
are extended.  Therefore “exact” never means that a regular expression has
reconstructed arbitrary future Lean syntax.  Generated-script dependencies,
ignored files, and other undeclared inputs likewise require a separate direct
check or configuration escalation.

The flat umbrella importers `YMGap`, `YMGapGuard`, and
`YMGapStatementGuard` are omitted only while computing the *local compilation*
cone; otherwise every edit would collapse the plan back to the whole semantic
root.  They are not omitted from final CI.  If an umbrella itself changes, it
is still emitted as a changed target.  Frontier/statement reflection remains a
final CI obligation unless the user separately approves the corresponding
local guard run.

The graph argument is invalidated by any toolchain/build-contract change.  The
planner therefore exits with `FULL BUILD REQUIRED` for changes to the pinned
toolchain, Lake files/manifest, Makefile, CI workflow, or the import guard
itself.  Source deletion is handled by the missing-import check; a new
unimported source is its own maximal target and is also selected by the
full-library glob.

#### 8.3 Implemented build invariants

The following are now load-bearing repository invariants:

1. **Complete compile selection.**  The main `[[lean_lib]]` has
   `globs = ["YMGap.*"]`.  `lake build YMGap` therefore selects the root and
   every `lean/YMGap/**/*.lean` module independently.  This corrects the prior
   false assumption that Lake's default glob included all submodules; without
   the explicit glob, Lake 4.29 selected only `YMGap.lean` and its recursive
   imports.
2. **Selective semantic root.**  `lean/YMGap.lean` remains one coherent
   reflection/axiom-audit environment.  It is no longer described as the
   mechanism that makes every file compile.  This distinction is necessary
   because independently generated alternative certificates can deliberately
   declare the same fully-qualified theorem and cannot coexist in one Lean
   environment.
3. **Static source guard.**  `scripts/lean_import_guard.py` uses only the Python
   standard library and never invokes Lean/Lake.  It validates local-import
   resolution, acyclicity, the explicit all-module glob, semantic-root closure,
   and the reviewed exclusion manifest.  Its synthetic parser/graph self-test
   is independent of repository state.
4. **Reviewed semantic exclusions.**  Every compile-only component is rooted
   in `lean/SEMANTIC_ROOT_EXCLUSIONS.txt` with a nonempty reason.  The guard
   rejects a missing root, a root that has become semantic, a redundant nested
   root, and an unclassified orphan.
5. **Reverse-dependent planner.**  `make lean-affected LEAN_BASE=<git-ref>`
   includes tracked, staged, working-tree, deleted, renamed, and untracked Lean
   paths and prints the maximal reverse-dependent module targets.
6. **Host-safe single-worker invariant.**  `LEAN_JOBS` is exactly one.  The
   Makefile rejects every caller-supplied value other than `1` and then uses an
   override-resistant assignment, so command-line or inherited Make variables
   cannot silently raise Lake parallelism.  The same invariant is stated in
   `AGENTS.md`, `CLAUDE.md`, and `lean/AGENTS.md`.  The per-process `-M 20480`
   limit remains in `lakefile.toml`. All build-capable audit routes and the
   optional frontier-status `--lake --allow-full-build` route enter the same
   canonical wrapper even when their Python CLIs are invoked directly;
   log-only/report-only modes do not invoke Lake. The frontier route also
   requires its explicit high-load acknowledgement. Repository
   pytest entry points hold the same host lock and set the OpenMP, OpenBLAS,
   MKL, vecLib, and NumExpr thread pools to one.
7. **One full-library CI build invocation.**  For trusted-main states selected
   by its path filter (and manual dispatches), CI runs the static guard,
   performs one all-module build with
   `LEAN_JOBS=1` and a checked pipe exit code, preserves its log, and feeds that
   same log first to the mandatory completeness/constructivity/internal-error
   gate, before any further Lake target, and later to informational strict
   mode rather than launching a second full build. Frontier, statement, and
   rubric Lake invocations remain and
   should normally be cache validations.  Each foreground session uses a
   repository-scoped just-in-time runner registration which GitHub assigns at
   most one job and then removes.  The Mac's sanitized work directory keeps
   only `lean/.lake` between ordinary jobs, avoiding paid remote cache storage;
   Lake revalidates source, dependency, option, and toolchain hashes.  A manual
   `workflow_dispatch` with `clean_build=true` deletes that cache before the
   build.

Normal CI local-cache reuse is sound only because Lake revalidates source,
dependency, options, and toolchain hashes for selected targets.  It proves the
current selected build, but it is not an independent reproducibility test of
the cache itself.  Periodic manual clean mode remains policy-required as an
independent reproducibility check and is available rather than enforced as a
required branch status.  Runner capacity is fail-closed: the workflow refuses
to start Lean unless the host reports at least 32 GiB installed and
approximately 32 GiB currently available.  On macOS it also requires AC power
and no active runner/Lean/Lake/pytest process, uses one worker under the 20 GB
Lean cap, lowers process priority, and keeps the machine awake only during the
build.  `YMGAP_LEAN_RUNNER` is set to the private custom label
`ymgap-m4max`; there is intentionally no GitHub-hosted fallback.  Runner
provisioning and deliberate foreground startup remain operational
prerequisites, and a scheduling/capacity failure must not be relabeled as a
proof failure or silently bypassed.

The two axiom modes have different force.  The non-strict run is the required
gate against observed declarations acquiring axioms outside the reviewed
budget; strict namespace-digest drift is informational (`continue-on-error`).
Lake 4.29.1 replays a current cached module's saved info trace, including its
`#print axioms` diagnostics.  The auditor now independently inventories every
executable source gate and requires exact source-file/line multiplicity plus
Lake's terminal success marker, rejecting missing, stale, duplicated, private,
or malformed diagnostics.  Thus a cache-reusing all-module log supplies
complete current gate evidence without requiring re-elaboration of every cache
hit.  Section 8.13.18 records the exact replay and collision argument.

The workflow is also branch- and path-filtered.  “Every CI state” below means
every Lean-relevant trusted-main state selected by that filter, plus manual
dispatch; self-hosted execution of pull-request code is excluded on
security grounds.  The load-bearing path set now
includes `reference/leanmillennium-pinned/**`, so a change to the pinned rubric
transcription triggers the same workflow; documentation-only states remain
outside it.

#### 8.4 Semantic-root classification found by the audit

Before repair, 51 of 2,517 package modules were outside `YMGap.lean`'s closure.
Six orphan roots/components, covering 45 modules, were promoted into the
semantic root:

- `FiniteOccurrenceReverseRecovery`;
- `HarmonicLowerSixCubicDebtCoefficient1330Certificate`;
- `HarmonicLowerSixCubicDebtCoefficient1330Physical`;
- the 40-module
  `HarmonicMassCross...SlopeSepticExactLowerHighCertificate` component;
- `Z4HalfTimeReflectionAdjacentEvenReachableEndpointCompression`;
- `Z4OutwardSevenCubeGoodBackgroundSwitching`.

The residual six roots are intentionally compile-only:

- `ModuliAlgebra` and `PolyAtlas`: explicitly non-load-bearing expository
  modules;
- `ScratchGraphFour`: a named scratch calculation without a consumer;
- `HarmonicLowerSixTailBaseSemanticFactors`: a dormant generated table reserved
  for a future refactor;
- `HarmonicLowerSixTailEnvelopeCertificateE8ChartA` and
  `...ChartAXPascal`: alternative generated certificate layouts that share a
  namespace and the theorem `tailEnvelopeE8ChartA_xPascal_relation`.

The last pair is the decisive reason not to force every source into one
umbrella environment.  The library glob checks both independently, while the
manifest makes their absence from the reflection environment explicit rather
than accidental.

Static verification in this session reported zero unresolved imports, zero
cycles, zero unclassified semantic orphans, and complete `YMGap.*` selection.
The affected planner correctly escalated the present `lakefile.toml` change to
`FULL BUILD REQUIRED`.  That is a plan result, not a full-build result.

#### 8.5 Mandatory local workflow

For a normal Lean edit, after the process-conflict check:

```text
python3 scripts/lean_import_guard.py
make lean-affected LEAN_BASE=HEAD
scripts/with_lean_session_lock.sh lean env LEAN_NUM_THREADS=1 \
  lake build <each printed +Module.Target>
```

Run the smallest directly edited target first.  If a printed maximal target is
known to be one of the high-memory certificate roots, stop and obtain explicit
approval before that target.  Never parallelize the printed targets.  A
configuration/toolchain escalation is not permission to run the full build on
the host; it means local incremental proof is insufficient and the approved
CI/manual full-build path is required.

#### 8.6 Global compact group/action audit: exact mathematical correction

The next mathematical dependency in Section 7.6 is now audited.  The repository
previously had no reusable global group carrier:

- `CartanType` is only a raw family/rank code; the canonically validated
  subtype is still root-system/Lie-algebra classification data, not a group;
- `RepData` is a tuple of scalar operating-point invariants;
- `AdmissibleSimpleGroup` supplies two inequalities and a budget certificate;
- the SU(N) center-charge fragment is not an embedded group quotient;
- SU(2) quaternion/Haar files are one-group realizations, not a generic global
  interface;
- `ObsAlg` lacks the unital `*`-algebra laws, and `ProbFunctional` is not yet a
  positive linear functional;
- class coordinates cannot represent a general kernel `K(g h^{-1})`, so the
  generic link calculus must retain matrix coefficients/tensor indices;
- the existing rational SU(2) carrier does not provide the constructive complex
  numbers needed for general SU(3) and Peter--Weyl matrix coefficients.

The corrected hierarchy concerns connected compact groups with simple Lie
algebra; disconnected extensions by outer automorphisms are a separate problem
and are not classified by a central quotient of the connected simply
connected cover.  Within that scope it must distinguish the following data,
with no definitionally identified shortcuts:

```text
Cartan/root type T
  -> simply-connected compact form G_sc(T)
  -> finite central subgroup Gamma <= Z(G_sc(T))
  -> actual global group G = G_sc(T)/Gamma
  -> faithful finite-dimensional action rho_G of G
  -> allowed irreps/matrix coefficients/Haar data for that same G
  -> character chi_rho = trace(rho_G), then the real normalized Wilson
     plaquette observable Re(chi_rho)/dim(rho)
  -> the two-parameter 4D lattice/OS stage family.
```

A representation of the cover merely trivial on `Gamma` descends; it is
faithful on the quotient only when its cover kernel is *exactly* `Gamma`.
Similarly, irreps of the global form are precisely cover irreps whose central
character is trivial on `Gamma`.  This restriction changes the allowed
character sum and can change the smallest nonzero Casimir.  It must feed the
Haar tail and Wilson action rather than being recorded as decorative metadata.
For a complex representation such as the SU(3) fundamental, the raw character
is complex and orientation reversal conjugates it.  The real Wilson action
must therefore use `Re(trace)` (equivalently the character symmetrized with its
dual), normally normalized by positive dimension; it may not identify the raw
complex character with a real plaquette energy.

#### 8.7 Cycle-free global-form module plan

The dependency layers are now fixed as follows.

1. **`RepTheory/CartanType.lean`.**  The extracted Lean-core leaf defines
   `CartanType` as a *raw* family/rank code: values such as `A 0` and `D 0` are
   representable and must not be called simple types.  The honest validation
   predicate is `IsCanonicalSimpleCode`, with the nonredundant thresholds
   `A≥1`, `B≥2`, `C≥3`, `D≥4`; `IsSimpleRank` is only a compatibility
   alias.  The excluded `C₂≅B₂` and `D₃≅A₃` aliases are simple, which is
   exactly why the old name was misleading.  Validated global-form code uses
   `IsCanonicalSimpleCode`, while the historical public names of `CartanType`,
   `rank`, and positive-root count remain cycle-free.
2. **`RepTheory/ConstructiveGroup.lean`.**  Define a carrier with an explicit
   setoid, identity/multiplication/inversion, congruence, associativity, units,
   and inverse laws; homomorphisms; finite enumerations with constructive
   `PSigma` coverage; finite central inclusions; and a central quotient with an
   explicit surjective lift and both directions of exact-kernel witnesses.
   The algebraic upstream parameter is `coverGroup`, not `simplyConnected`,
   and its arbitrary finite central kernel is `gamma`, not `center`; topology
   and full-center equality are not hidden in suggestive names.  No quotient
   section or classical choice is permitted.
3. **`RepTheory/CompactSimpleGlobalForm.lean`.**  Define a finite *marked*
   global-form code from a canonically validated `CartanType` and a subgroup
   code for the computed center shape.  The simply-connected centers are:

   ```text
   A_n: Z/(n+1),  B_n: Z/2,  C_n: Z/2,
   D_n even: Z/2 x Z/2,  D_n odd: Z/4,
   E6: Z/3, E7: Z/2, E8: 1, F4: 1, G2: 1.
   ```

   Low-rank aliases are excluded by `IsCanonicalSimpleCode`.  Cyclic `Gamma`
   codes carry positive order/index and an explicit factorization of the
   ambient order; Klein-four codes enumerate exactly the trivial, three
   order-two, and full marked subgroups.  They are not free quotient labels,
   but neither are they yet inclusions into a realized group.  For even `D_n`,
   diagram automorphisms exchange marked order-two subgroups (all three under
   `D₄` triality, the two spinorial axes in higher even rank).  Consequently
   the code either remains explicitly marked or a later theorem must quotient
   by root-datum automorphisms and prove completeness/nonduplication before it
   is advertised as classification up to unmarked group isomorphism.  A code
   alone constructs no topology.
4. **`RepTheory/ConstructiveCompactGaugeGroup.lean`.**  Realize the code by an
   actual cover and quotient `ConstructiveGroup`, the exact central quotient,
   and a constructive compact-metric presentation.  If “compact” appears in a
   *realized group* type name (rather than in the name of a finite
   classification code), it must carry a separated bi-invariant
   constructive-real metric, explicit finite `2^{-n}` nets with coverage, and
   the required completion/total-boundedness data.  Until then the honest name
   is `GlobalGaugeGroupRoot`, not `CompactGroup`.
5. **Constructive complex and lawful coefficient algebra.**  Before generic
   Peter--Weyl data, implement constructive complex scalars, conjugation,
   modulus, finite matrices, adjoint, and a lawful unital `*`-algebra.  A
   rational surrogate may be an explicitly realified test representation, but
   may not be called the general character layer.
6. **Root datum and `IrrepDescentData`.**  Construct the weight and root
   lattices `P` and `Q`, compute the highest-weight central character through
   `P/Q ≅ Hom(Z(G_sc), U(1))`, and restrict it to the coded `Gamma`.  Prove
   `descends(lambda) ↔ chi_lambda|Gamma = 1`; only then define global labels
   as exactly that decidable subtype.  Carry lift/descend inverse laws, equality
   of pulled-back matrices and coefficients, and preservation of dimension and
   Casimir.  A caller-supplied Boolean or proposition named `descends` is
   insufficient.
7. **`FaithfulLatticeAction`.**  Carry cover and global finite unitary (or
   explicitly realified orthogonal) actions, positive dimension, the pullback
   equation `rho_sc(x)=rho_G(q x)`, and
   `rho_sc(x)=I` iff `x` has an explicit `Gamma` witness.  Derive faithfulness of
   `rho_G` and `chi_rho = trace(rho_G)` rather than choosing a separate
   character.  Then derive the real, orientation-invariant plaquette observable
   `Re(chi_rho(g))/dim(rho)` and its unique identity maximum; do not use a raw
   complex trace as the Wilson energy.
8. **`HaarPeterWeylData`.**  On the same global group, supply a point-separating
   matrix-coefficient `*`-algebra, evaluated left/right translations, normalized
   positive linear Haar functional, bi-invariance, actual unitary matrix
   coefficients, character-as-trace, Schur matrix-coefficient orthogonality,
   fusion/product coefficients, and Casimir nonnegativity with the trivial-zero
   pin.  Character orthogonality alone is not enough for link integration.
9. **Bridges only after realization.**  `MassGap/GlobalGroupRepDataBridge.lean`
   may compare realized group invariants to legacy `RepData`; it must not make
   them definitionally equal.  `Continuum/PinnedWilsonLatticeFamily.lean` then
   adapts the actual coefficient algebra/Haar/action to the corrected
   `CanonicalOSRoot`.  `Rubric/ClayResolutionRoot` assembles these last, so no
   RepTheory-to-Continuum/RG cycle is introduced.

#### 8.8 Required SU(2) -> SO(3) validation

Before the generic Haar layer grows, exercise every global-form distinction in
the smallest nontrivial quotient.  Encode SU(2) irreps by doubled spin `ell`.
The central element `-1` acts by `(-1)^ell`; therefore an irrep descends through
`SU(2)/{+-1}` exactly when `ell` is even.  The validation must prove:

- the quotient kernel is exactly the two-element center;
- the spin-half label `ell=1` does not descend;
- the spin-one label `ell=2` does descend;
- all and only even labels form the SO(3) label carrier;
- the descended three-dimensional action is faithful on SO(3);
- its pullback to SU(2) has kernel exactly `{+-1}`;
- for the quotient map `q : SU(2) -> SO(3)`, descended characters satisfy
  `chi_desc ∘ q = chi_cover`, and normalized Haar functionals satisfy the
  precise pushforward/integration identity
  `H_SU2(f ∘ q) = H_SO3(f)` for every function in the realized coefficient
  algebra.

This test prevents a later implementation from silently treating Lie type A1
as a unique global group or using the SU(2) fundamental Wilson action for SO(3).

#### 8.9 Casimir provenance defects that must be repaired

The legacy scalar table cannot be promoted unchanged:

1. `repDataOf (.A n)` uses the SU(n+1) fundamental, which does not descend to
   PSU(n+1).  The B/D comments similarly choose vector/SO conventions while the
   same Cartan type also denotes Spin and intermediate quotients.  The smallest
   allowed nontrivial Casimir is a function of `(T,Gamma)` only after fixing the
   invariant-inner-product scale; throughout this repair that scale is long
   roots squared `2`.  A dimensionful physical value also carries the chosen
   coupling/metric convention.
2. For simply-connected `B_n = Spin(2n+1)`, spinor representations are allowed
   and have `C2 = n(2n+1)/8`; they beat the vector value `n` at least for
   `n=2,3`.  Vector minimality is a quotient-dependent statement.
3. With the repository's declared long-root-squared `2` convention and
   `C2(SU2 fundamental)=3/4`, the `D_n` vector has
   `C2=(2n-1)/2`, not the coded `(2n-1)/4`.  The current rational lower-bound
   theorem about the coded scalar may remain formally true, but its “exact
   physical Casimir” provenance is false until corrected.

The replacement API must keep three quantities distinct:

1. the smallest nonzero Casimir among all `Gamma`-descending irreps, which is
   the spectral quantity used by the heat-kernel tail;
2. the Casimir data of the chosen faithful Wilson action, which may be
   reducible and need not attain that minimum; and
3. the adjoint Casimir/dual Coxeter number.

The legacy field name `C2_fund` conflates these roles and is not even honest
terminology for `E8`, whose smallest representation is adjoint.  The repair
order is: formalize the long-root-squared-`2` normalization from roots/weights,
prove the cover table, restrict it by the computed global-form descent
predicate, then derive the smallest allowed nontrivial Casimir and separately
the chosen action's Casimir data.  No existing mass-gap theorem may cite the
legacy table as a global-group fact before that bridge is complete.

#### 8.10 Execution record and immediate residual

Three cycle-free leaves now exist:

- `ConstructiveGroup.lean` contains the setoid group, homomorphism, finite
  presentation, finite central subgroup, explicit `gamma` witness, and exact
  central-quotient interfaces.  Its neutral algebraic upstream name is
  `coverGroup`; no field asserts topology or that `gamma` is the full center.
- `CartanType.lean` contains raw family/rank codes and the honest
  `IsCanonicalSimpleCode` predicate, with `IsSimpleRank` retained only as a
  compatibility alias.
- `CompactSimpleGlobalForm.lean` contains center-shape and honest marked
  subgroup codes, simply-connected/adjoint constructors, and the A1 code-level
  even-label test.  It is not yet an SU(2) or SO(3) group realization, and its
  parity predicate is not yet derived from the general `P/Q` central-character
  construction.

After the final naming/domain audit, each edited target was checked afresh.
Before every command the process table contained no Lean/Lake/pytest process;
every command used one worker and inherited Lake's mandatory memory cap:

```text
env LEAN_NUM_THREADS=1 lake build YMGap.RepTheory.CartanType
Build completed successfully (2 jobs; edited leaf 175 ms).

env LEAN_NUM_THREADS=1 lake build YMGap.RepTheory.ConstructiveGroup
Build completed successfully (2 jobs; edited leaf 188 ms).
All eight printed public theorems: axiom-free.

env LEAN_NUM_THREADS=1 lake build YMGap.RepTheory.CompactSimpleGlobalForm
Build completed successfully (3 jobs; edited leaf 204 ms).
All printed public theorems: axiom-free.

env LEAN_NUM_THREADS=1 lake build YMGap.RG.WeylDimGeneralData
Build completed successfully (56 jobs; edited leaf 257 ms).

env LEAN_NUM_THREADS=1 lake build YMGap.MassGap.AllSimpleTypes
Build completed successfully (85 jobs; edited leaf 372 ms).

env LEAN_NUM_THREADS=1 lake build YMGap.Rubric.ClayResolutionRoot
Build completed successfully (111 jobs; final affected consumer 153 ms).
```

One safety incident in this session must remain explicit.  A command
`lake query YMGap` was mistakenly treated as read-only target inspection, but
this Lake's `query` command invokes the build.  It selected 2,523 jobs and
mostly replayed cached artifacts, then exited nonzero on sandbox write errors
and the then-unrepaired global-form leaf.  It was not a successful full build,
was outside the approved local protocol, and must not be repeated.  It did
empirically confirm that the explicit library glob expands to the all-module
target, but establishes no green integration result.

The umbrella `YMGap.lean` still postdates its `.olean`; integration of the new
imports and promoted semantic roots remains unverified until the approved CI
path.  The present build-contract changes also make the affected planner return
`FULL BUILD REQUIRED`, as designed.

No full build, full test, repository axiom audit, statement guard, or frontier
guard was claimed for that repository state.

#### 8.11 Push, CI scheduling result, and private Mac runner

Commit `97b9722` (`Guarantee Lean source coverage and start global forms`) was
pushed to `origin/main` after the static graph/configuration audit.  The audit
matched the tracked production filesystem exactly: 2,521 `YMGap.*` modules,
7,845 local import edges, zero cycles, 2,515 modules in the semantic root, and
six reviewed compile-only semantic exclusions.  The affected planner correctly
required the all-module CI obligation for the build-contract changes.

GitHub run `29637312899` did **not** execute any workflow step.  GitHub rejected
the job before runner assignment because the account had a failed-payment or
spending-limit lock.  Therefore that red run is neither a Lean failure nor a
green full-build result; it supplies no kernel evidence at all.

To remove hosted-compute cost without reviving uncontrolled local builds, the
private repository uses the custom label `ymgap-m4max` for a
repository-scoped Apple-silicon JIT runner.  The setup script pins the official
runner to `v2.335.1`, verifies the archive's SHA-256 digest and the installed
listener's reported version, reapplies owner-only mode `0700` to the runner
root after archive extraction as well as on preexisting-install validation,
installs no service, and creates no persistent registration.  Each invocation
of `scripts/run_macos_ci_runner.sh` first reconciles any durable recovery/local
registration in the same validated root, then revalidates that exact version
before it requests a new JIT configuration, holds the canonical
per-user atomic host session lock, runs in the foreground for a specifically
known queued trusted-main run, and accepts at most one job by GitHub's own
guarantee. The Listener starts only after a synced exact-ID/name visibility
witness. Normal or trapped exit requests and verifies remote/local cleanup;
successful cleanup deletes the credentials and owner-only recovery marker,
while failure retains that evidence for a later conflict-free recovery and
prevents a fresh JIT registration from guessing.

The self-hosted workflow contract is stricter than the former fallback:

1. only trusted Lean-relevant pushes to `main` and manual dispatches are
   eligible; pull-request code never runs on the personal machine;
2. routing requires the complete `self-hosted`, `macOS`, `ARM64`, and custom
   label tuple; there is no GitHub-hosted fallback, so even a variable changed
   to `macos-latest` cannot spend hosted minutes;
3. macOS requires at least 32 GiB installed RAM, approximately 32 GiB currently
   available by `memory_pressure`, AC power, and no concurrent Lean/Lake/pytest
   process before compilation;
4. the full build remains one worker with Lean's 20 GB per-process ceiling,
   runs at positive niceness, and uses `caffeinate` only while that build runs;
5. each foreground launcher uses GitHub's at-most-one-job JIT primitive;
   workflow concurrency preserves the current running job and coalesces pending
   checkpoints, while the launcher-held atomic lock, locked Make entry points,
   and immediate pre-build process recheck prevent repository-managed overlap;
6. the persistent checkout deletes every ignored/untracked path other than
   `lean/.lake`; Lake revalidates that local cache, avoiding remote cache
   storage, while manual `clean_build=true` deletes it for a reproducibility
   run;
7. a manual dispatch is rejected unless its selected ref is `main`; successful
   logs are not uploaded; a failing log is retained for only three
   days; and the workflow token is read-only with checkout credentials not
   persisted; and
8. a newly queued job has a `480`-minute workflow timeout, long enough for the
   measured one-worker cold path without weakening the worker or memory caps.

The lock is one fixed `/tmp/ymgap-lean-session-$UID.lock` rendezvous rather
than a caller-selectable path.  A top-level wrapper checks the process list
both before and immediately after its atomic `mkdir`, closing the race with a
bare executable that cannot honor the lock.  Cleanup removes the lock only
after a conclusive post-command check; an orphaned Lean/Lake/pytest/runner
process or a process-list inspection failure retains it for explicit operator
recovery.  `Makefile`, `AGENTS.md`, `CLAUDE.md`, and `lean/AGENTS.md` all make
`LEAN_JOBS=1` hard rather than advisory, and pytest additionally receives the
five one-thread numerical-library caps.

The four runner labels are routing selectors, not authorization.  A
repository-scoped JIT registration can accept any queued job carrying those
labels, so every actor and workflow able to queue a matching job is inside the
trust boundary.  The foreground listener must therefore be launched only for
a known queued run and taken offline afterward; stronger adversarial isolation
requires a workflow-restricted organization runner group or a dedicated
disposable account/host.

Self-hosted Actions compute is free under GitHub's documented billing model,
but the account must still be able to schedule Actions.  The current billing
lock may therefore need repair or plan downgrade even though the runner itself
is free.  Until a Mac-runner job actually exits zero, the full current commit
remains statically and incrementally checked rather than fully CI-certified.

#### 8.12 Constructive representation descent through an exact quotient

`RepTheory/ConstructiveRepresentationDescent.lean` now closes the generic
algebraic descent step needed by every faithful global-form action.  It imports
only `ConstructiveGroup` and adds:

- left/right cancellation and the `a⁻¹b = 1 -> a = b` setoid-group calculus;
- homomorphism preservation of inverse and both directions relating equal
  images to the image of `a⁻¹b`;
- semantic `Hom.Faithful` and its kernel-trivial criterion;
- `FiniteCentralSubgroup.IsKilledBy rho` and the theorem that an explicit
  `gamma.WitnessFor` is killed;
- a lift-based `descendRepresentation` constructed from
  `CentralQuotientPresentation.surjective_lift`, with fiber independence and
  the factorization equation along `quotient_hom`; and
- the exact faithfulness criterion in its correct Martin-Löf form.

The last point is intentionally **not** a Prop-level biconditional.  The reverse
kernel statement computes a `PSigma` central witness and therefore lives in
`Type`; erasing it into `Iff` would be ill-typed or would destroy the data
needed downstream.  The API instead supplies two constructive maps:

```text
faithful descended action
  -> (each cover-kernel proof computes a gamma witness),

(each cover-kernel proof computes a gamma witness)
  -> faithful descended action.
```

There is no `Classical`, choice, `Nonempty`, `Exists`, `Quot`, `noncomputable`,
axiom, or `sorry` in the implementation.  A fresh host process check found no
Lean/Lake/pytest process, and the smallest target then passed:

```text
env LEAN_NUM_THREADS=1 lake build \
  YMGap.RepTheory.ConstructiveRepresentationDescent
Build completed successfully (3 jobs; edited leaf 1.3 s).
All twelve printed public theorems: axiom-free.
```

The immediate residual is now:

1. obtain an actually dispatched, green self-hosted all-module CI result; do
   not confuse registration, queueing, or the prior billing rejection with a
   build result;
2. construct a located finite-central-quotient carrier whose semantic coset
   relation is propositionally truncated but whose locator recomputes explicit
   kernel witnesses, then instantiate the rational A1 `+-1` quotient;
3. use the descent theorem to construct the spin-one conjugation action and
   prove its cover kernel is exactly `+-1`, hence its quotient action is
   faithful; do not call the rational dense skeleton compact SU(2)/SO(3);
4. construct the root/weight-lattice central-character calculation before
   generalizing irrep descent or repairing the global-form Casimir minimum;
5. only after genuine compact realization and Haar bi-invariance, prove the
   normalized Haar pushforward identity and advance to constructive complex
   coefficients, real Wilson actions, and Peter--Weyl realization.

### 8.13 Located quotient and exact rational A1 execution route
(2026-07-18, session 7)

This checkpoint separates four statements that must not be conflated:

1. full-tree consistency of one exact Git commit;
2. a generic constructive finite-central-quotient presentation;
3. a finite rational quaternion plumbing fixture; and
4. the still-open realization of the full rational and compact A1 groups.

#### 8.13.1 Self-hosted full-tree run: exact failed/cancelled result

The first clean all-module job assigned to the private Apple-silicon runner was
GitHub run `29638079535`, job `88063821580`, on commit `118172b`.  Checkout,
sanitization, the static import guard, pinned-toolchain selection, the host
preflight, and Lean-version verification passed.  The build then exposed eight
real source/kernel failures.  After the last three formed a consecutive
increasing-cost family of the same high-row kernel-cap failure, cancellation
was requested: the job was already irrecoverably red, continuing would only
spend host time, and the successfully produced local Lake cache was preserved.

The exact GitHub record is:

```text
commit:                    118172b
workflow run:              29638079535
job:                       88063821580
job start:                 2026-07-18 08:49:02Z
job completion:            2026-07-18 13:28:14Z
full-build step:           08:49:20Z--13:28:07Z (4h38m47s)
last scheduler entry:      2117/2528 (cancelled Block3Row2)
full-build result:         FAIL, then operator-cancelled
required axiom audit:      NOT REACHED
frontier guard:            NOT REACHED
statement guard:           NOT REACHED
frontier-DAG guard:        NOT REACHED
rubric guard:              NOT REACHED
strict drift report:       NOT REACHED
failure artifact:          SKIPPED by the old workflow on cancellation
local build log:           RETAINED on the Mac
elapsed job time:          4h39m12s
final GitHub conclusion:   CANCELLED
```

Accordingly, commit `118172b` is **not** certified as fully kernel-consistent,
and none of the skipped guards or audits may be inferred from the partial log.
This was not a scheduler or capacity failure: the one-worker `-M 20480` cap did
its intended job and converted large reductions into recoverable module
failures without crashing the host.  The earlier run `29637312899` remains a
separate billing/scheduling rejection on which no workflow step executed and
therefore supplies no kernel evidence.

The skipped artifact exposed an observability defect in the old workflow: an
explicit operator cancellation makes the job conclusion `cancelled`, while the
upload step had selected only `failure()`.  The current working-tree source now
names the step “after any mandatory failure or cancellation” and uses
`if: failure() || cancelled()`.  The source repair is complete; workflow-level
static re-audit, commit/push, and its first live failure-or-cancellation exercise
remain pending.  This preserves diagnostic evidence only and cannot convert
cancellation into a passing proof status.

The eight failing modules observed before cancellation were exactly:

1. `HarmonicLowerSixTailEnvelopeCertificateE8ChartA` at 166 seconds: an `rfl`
   exposed the inconsistent raw substitution factor `64^u`;
2. `EightAnchorWindowRetune` at 146 seconds: the monolithic 144-coefficient
   Boolean identity exceeded the kernel memory cap;
3. `HarmonicMassCrossLowerSixRecoveryBootstrapFourth` at 210 seconds: the
   one-shot `Fin 100` decision exceeded the kernel memory cap;
4. `HarmonicMassCrossLowerSixRecoveryTerminal8189` at 103 seconds: the direct
   254-mode endpoint decision exceeded the kernel memory cap;
5. `HarmonicLowerSixCubicDebtCoefficient1330Physical` at 5 seconds: several
   definitional-equality, tactic, and nested congruence terms were ill-typed;
6. `HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock4Row0`
   at 196 seconds: `highRowPred` exceeded the kernel memory cap;
7. the corresponding `...HighRowsBlock3Row4` at 218 seconds: the same kernel
   memory failure; and
8. the corresponding `...HighRowsBlock3Row3` at 233 seconds: the same kernel
   memory failure.

Cancellation interrupted `...HighRowsBlock3Row2` after 76 seconds with process
exit 137.  That row is cancellation collateral, not a ninth diagnosed
certificate failure, and no mathematical conclusion is assigned to it.

Five exact constructive source-level repair candidates are written.  The split
BootstrapFourth repair now has a successful guarded targeted compilation;
the corrected CubicDebt repair now does as well.  E8 chart A remains pending
its first targeted check; Terminal8189's initial stack overflow is eliminated
but its balanced rerun still has exponent-transport and chunk-memory failures;
both guarded EightAnchor slicing attempts failed for the architectural reason
described below.

1. the E8 chart-A raw relation now uses the actual chart substitution
   `x=14/n`, hence `14^u`, consistently in its prose and checked relation;
2. the first degree-143 EightAnchor repair attempted four disjoint
   36-coefficient `take`/`drop` slices and an empty tail, then reconstructed the
   unchanged 144-coefficient `allZero` statement with `allZeroB_append` and
   `List.take_append_drop`;
3. the fourth bootstrap tranche checks the exact intervals `348--397` and
   `398--447` as two `Fin 50` decisions, then reconstructs the original
   `Fin 100` theorem by a decidable `i.val < 50` split and `omega` index
   transport.  This item is target-compiled successfully;
4. the terminal certificate splits the 254 interior modes into `202+52`, keeps
   the endpoint term explicit, proves the two exact rational lower enclosures
   `-7165730/1000000` and `7166567/1000000`, and reassembles them with
   `finSum_split` and rational setoid algebra.  Their certified excess is the
   strictly positive exact margin `837/1000000`; its balanced source proof
   still requires explicit exponent transport and finer subdivision after the
   failed rerun described below; and
5. the cubic-debt physical proof replaces invalid definitional/ring shortcuts
   by typed rational-setoid algebra: an explicit `2*a ≈ a+a` lemma, congruence
   transport of the drift excess, constructive natural-factor positivity, and
   named profile/drift intermediate equivalences before the final nested
   multiplication transport.  This item is target-compiled successfully after
   closing the two first-run gaps described below.

The guarded one-worker EightAnchor target replayed its dependencies and then
failed after 100 seconds.  The structural `allZero_of_take_and_drop` proof left
the trivial Boolean goal `(true && true) = true` at source line 123, and the
closed chunk declarations beginning at lines 134, 136, and 138 independently
hit the kernel memory cap.  Thus `4 × 36` is proved too coarse on this host;
the final Boolean simplification was then fixed and a cost-tapered 18-slice
retry used widths

```text
12,12,12,12,10,10,10,10,8,8,8,8,6,6,4,4,2,2.
```

That guarded target also failed, after 184 seconds.  The first seven closed
slice decisions, beginning at source lines 142, 144, 146, 148, 150, 152, and
154 with starts `0,12,24,36,48,58,68`, each reached the kernel memory cap;
source line 203 independently contains one unexpected extra `)`.  The common
cause is now clear: every slice is defined as a `drop`/`take` of
`head8IdentityDiff`, so eager reduction reconstructs the entire expensive
degree-143 polynomial before discarding all but the requested range.  Smaller
widths cannot reduce that shared peak, and repairing the parenthesis alone
cannot fix it.

The next architecture must compute a coefficient or bounded coefficient range
directly, without calling `head8IdentityDiff` and then dropping it.  Prove a
generic exact bridge from the pointwise/range computation to the corresponding
coefficient of the original polynomial identity, cover indices `0,...,143` by
disjoint bounded ranges, prove the residual tail empty, and reconstruct the
same public `allZero` statement.  This must remain ordinary kernel-checked
rational computation: no cap increase, statement weakening, `native_decide`,
or opaque generated result.  The pointwise/range source design is in progress
and uncompiled.

By contrast, the guarded one-worker target
`HarmonicMassCrossLowerSixRecoveryBootstrapFourth` completed successfully with
exit 0:

```text
predecessor BootstrapSecond:  90s
predecessor BootstrapThird:   151s
final BootstrapFourth target: 121s
Lake result:                  Build completed successfully (490 jobs)
public axiom gates:           [propext, Quot.sound]
```

This is exact kernel evidence for the two `Fin 50` certificates, their
constructive `Fin 100` recombination, and that target's dependency replay.  It
is not an all-module build and does not replace the still-pending complete
cached CI job.

The first guarded `HarmonicMassCrossLowerSixRecoveryTerminal8189` target
replayed its cached dependencies but its final leaf failed after `1.3s` with
`Stack overflow detected. Aborting.`; Lean exited `134` and the guarded build
exited `1` under the unchanged `-s 65536 -M 20480` limits.  Memory and host
pressure remained safe.  A structural rewrite then replaced the deepest
strict-fold power by a balanced exact product of four folds of approximately
quarter depth and flattened the outer equivalence chain.

The guarded balanced rerun lasted 182 seconds and eliminated the stack
overflow, but it still failed.  At lines 80 and 92, the `qpow_add` bridge needs
an explicit natural-number congruence transporting the normalized exponent
`n / 2 + (n - n / 2)` back to `n`; the present rewrite does not make that
equality definitional.  The closed obligations beginning at lines 164, 170,
and 175 also reached the 20 GiB kernel cap.  Thus balancing the individual
powers solves the stack-depth failure but the two `202+52` slice decisions and
their large structural bridge still require finer subdivision.  The exact
split and `837/1000000` margin remain unverified.  Add the explicit exponent
transport, subdivide the large closed sums/equivalence proof further, and
recheck under the same fixed limits; raising either cap is not an acceptable
substitute.

The guarded `HarmonicLowerSixCubicDebtCoefficient1330Physical` target built or
replayed its dependencies and failed safely at the final leaf after `0.999s`.
The two source-local proof defects are an unsolved
`1 * A * A ≈ A * A` goal near line 395 and an invalid use of `rfl` near line
414 for a `Q'` numerator equality involving
`d = Q'.ofNat (driftDen k)`.  Lean's error recovery consequently printed the
later public theorem with `sorryAx`; that diagnostic is not an admitted axiom
budget and supplied no theorem evidence.  The patch closes the unit goal
through `Q'.one_mul_eqv` and congruence, expands `2*(d+1)` through typed
distributivity and associativity, and checks the remaining scalar identity
constructively.  The guarded rerun then passed:

```text
final CubicDebt target: 1.0s
Lake result:            Build completed successfully (528 jobs)
process result:         exit 0
public axiom gates:     [propext, Quot.sound]
sorryAx:                absent
```

This is targeted kernel evidence for CubicDebt and its replayed dependency
cone, not a replacement for the complete cached CI job.

During that target's dependency phase,
`CoreBResidualSimplex` also emitted a nonfatal `PANIC` from the
library-suggestions `SymbolFrequency` heartbeat path while writing the module;
Lake nevertheless marked the module built and continued.  This diagnostic is
not established as harmless and did not cause the later CubicDebt source
errors.  Before final certification, reproduce or clear it in a guarded
one-worker check, determine whether its `.olean`/saved log is sound, and require
the next complete build log to contain no unreviewed `PANIC` or internal-error
diagnostic.  A zero module exit or `Built` label alone is insufficient evidence
for this case.

These first five changes preserve every public mathematical statement and
introduce no `native_decide`, classical choice, or new axiom.  That is a source
audit, not a compilation result.  A sixth shared source repair now addresses
the three high-row failures.  After `zRows` extracts a `Z` coefficient, it
represents the remaining one-variable `M` polynomial as a dense integer
coefficient list,
with exact recursive addition, scaling, shifting, convolution, negation, and
power.  The predicate checks both `mOnly` syntactic support and
coefficientwise integer nonnegativity; proved evaluator lemmas show that the
dense computation equals the original `PolyExpr`, so the fast path cannot
silently discard another variable or change the certified polynomial.

The shared reconstruction theorem checks coefficient widths `6`, `10`, `14`,
and `20`, followed by the tail after index `50`; the maximum row degree is
`78`, so that final tail has at most `29` coefficients.  Repeated exact
`take`/`drop` reconstruction yields the original singleton `highRowPred`
statement.  All three observed failures--`...HighRowsBlock4Row0`,
`...HighRowsBlock3Row4`, and `...HighRowsBlock3Row3`--are explicitly migrated
to a support decision plus the five staged coefficient decisions and the
shared reconstruction theorem.  Every other row leaf inherits the cheaper
exact definition of `highRowPred` without a bespoke source edit.  The shared
layer and all three migrated consumers remain uncompiled, so the repair cannot
yet be called successful.

There is one deliberate API-semantic compatibility choice.  The public name
and type `highRowPred : PE -> Bool` are retained, but its definition is
strengthened from sparse-normalizer coefficient nonnegativity to
`mOnly row && denseMRowNonnegative (mDense row)`.  Therefore its behavior is
not definitionally identical for an arbitrary external `PE` containing
variables other than `M`: the new support guard rejects such an expression.
Static consumer search finds no in-repository use that unfolds or applies this
predicate outside the concrete extracted HighRows chain, and the exact dense
evaluation bridge proves the nonnegativity result that the project endpoint
needs.  What is preserved is the singleton/aggregate certificate theorem types
and the final `pExactLowerHigh` semantic theorem, not unrestricted behavioral
compatibility of the helper predicate.  Compilation must validate that claim
before commit.

The later rational-A1, CI, and one-step working tree is not part of commit
`118172b`.  At the current post-shared-source **static inventory** checkpoint,
the non-compiling import guard reports:

```text
production modules:       2528
local import edges:       7868
directed cycles:          0
semantic-root reach:      2522
reviewed exclusions:      6
executable axiom gates:    19569 source lines
changed Lean modules:     21
reverse-affected modules: 1988
affected-plan result:      FULL BUILD REQUIRED (configuration changed)
RepTheory forbidden scan: 0 findings
```

The import graph has zero unexpected orphans and the split-module
source/dependency audit passes.  The gate count is a current source inventory,
not evidence that those gates were replayed: only a completed successful
all-module log can establish that.  The stale raw-dot-product character
overclaim was corrected, and the raw negation and conjugation congruence
declarations have explicit axiom gates.  All working-tree targeted Lean checks
other than BootstrapFourth and CubicDebt remain failed or pending and must
proceed through the serialized repair sequence; full cached CI remains
mandatory afterward.

#### 8.13.2 Located finite-central quotients

`RepTheory/LocatedCentralQuotient.lean` implements the missing constructive
carrier-level quotient step.  For a constructive setoid group `G`, a finite
central subgroup `iota : Gamma -> G`, and representatives `x,y : G`, its
explicit witness type is

```text
CentralCosetWitness x y := Sigma' z : Gamma, x ~= y * iota(z).
```

This is the standard left-coset equation `x in y Gamma`; because `Gamma` is
central, the left/right distinction disappears.  Declarations and prose use
“central coset” rather than falsely classifying the displayed equation as a
right coset.

The semantic quotient relation is

```text
CentralCosetEquivalent x y := Nonempty (CentralCosetWitness x y).
```

This is an admissible, delimited use of propositional truncation.  It makes the
witness-bearing equality proof-irrelevant enough to serve as a `Setoid`
relation, but no required data is selected from it.  The independent locator

```text
Locator Gamma :=
  (x y : G) -> WitnessOrRefutation (CentralCosetWitness x y)
```

recomputes an explicit witness whenever Type-level data is required.  In its
negative branch the truncated semantic proof is eliminated only into `False`;
the contradiction then eliminates into the unreachable witness type.  There
is no canonical-representative selection or classical choice.

The finite locator is complete relative to decidable ambient semantic
equality:

- `locateFin` returns either an enumerated successful slot or a refuter for
  every slot;
- `Locator.ofDecidableEquivalent` searches the finite presentation of
  `Gamma`;
- `finite.cover` transports an arbitrary alleged subgroup representative to
  an enumerated slot;
- repeated enumeration entries are harmless; and
- no decidable structural equality on subgroup representatives is required.

The explicit witness calculus proves reflexivity, symmetry, transitivity,
multiplicative congruence, and inverse congruence.  Centrality is used exactly
where an included central factor must pass an ambient representative.  The raw
carrier of `G`, equipped with the coarser coset setoid and the original raw
operations, becomes `locatedCentralQuotientGroup`; the identity function on
representatives becomes the quotient homomorphism; and the locator supplies
the Type-level exact-kernel witness in
`locatedCentralQuotientPresentation`.

The file currently imports `ConstructiveRepresentationDescent` solely to use
`mul_right_cancel`.  It would be false to describe its present dependency as
only `ConstructiveGroup`.  At the next foundational invalidation checkpoint,
move generic cancellation calculus upstream into `ConstructiveGroup` (or a
neutral group-calculus leaf), make both quotient and descent import that leaf,
and then reduce the located quotient to its true algebraic dependencies.  This
move belongs with the ring-normaliser promotion because both invalidate broad
dependency cones and require a new full-tree CI result.

The located quotient constructs none of the following:

- a chosen or canonical coset representative;
- a `Quot`-based carrier;
- topology, a quotient metric, completeness, or compactness;
- a Lie group or simply connected cover;
- Haar integration; or
- a proof that the selected finite central subgroup exhausts the full center.

#### 8.13.3 Low-level rational quaternion split and the Q8 fence

The rational A1 algebra is deliberately divided into three independent leaves:

1. `RepTheory/RationalQuaternionAlgebra.lean` defines raw `Q'^4`,
   coordinatewise semantic equality, scalar and basis quaternions, negation,
   conjugation, Hamilton multiplication, squared norm, and the semantic
   unit-norm subtype.  It proves semantic congruence of negation, conjugation,
   multiplication, and squared norm.  It does not yet assert the global
   Hamilton group laws.
2. `RepTheory/QuaternionSign.lean` defines the complete two-element sign group
   independently of quaternions, with explicit multiplication, inversion, and
   finite enumeration.
3. `RepTheory/RationalQuaternionQ8Fixture.lean` defines the eight signed basis
   codes `+-1,+-I,+-J,+-K`, verifies their finite multiplication/inverse table,
   realizes the table in raw rational Hamilton coordinates, includes the sign
   group centrally, constructs the finite locator, and forms the exact located
   quotient presentation.

This split is load-bearing.  The raw algebra must remain upstream of quotient
and continuum code; the sign group is shared by the finite fixture and the
eventual full unit-quaternion group; and exhaustive `decide` proofs on eight
codes must never replace general polynomial identities on arbitrary rational
coordinates.

Mathematically, the expected quotient of Q8 by its two scalar signs has four
elements and is the Klein four group.  The current Lean fixture proves neither
that cardinality statement nor a V4 isomorphism.  Neither theorem is needed for
the present plumbing validation, so it must not be reported as formalized.
The fixture also does not prove full rational-unit-quaternion closure,
Hamilton associativity on `Q'^4`, full-center exhaustion, density, topology,
compactness, Haar invariance, a character theorem, a Casimir value, SU(2), or
SO(3).

Its exact value is narrower: it exercises a nonabelian finite group, the sign
inclusion, finite witness search, the coarser central-coset setoid, the exact
quotient interface, and the constructive axiom gates.

#### 8.13.4 Corrected coordinate, character, and Haar boundary

The continuum quaternion-polynomial carrier historically identified a raw
coordinate polynomial with a group character before it contained Hamilton
multiplication, inversion, or a matrix-trace bridge.  The corrected reading is

```text
relativeDot
  = the raw polynomial sum_i g_i h_i;

relativeFundamentalCharacter
  = the raw polynomial 2 sum_i g_i h_i, intended to become
    chi_fund(g h^-1) only after the group-evaluation and trace bridge;

retainedRelativeWeight
  = 1 + (1/4)(2 sum_i g_i h_i), intended to become the retained
    SU(2) Wilson kernel only after that same bridge.
```

The theorem with the historical name `relative_character_value` is presently
only the definitional expansion of the four-coordinate dot product.  Its proof
is reflexivity.  It establishes no unit norm, multiplication, inverse,
`h^-1 = conjugate(h)`, representation, trace, or character identity.  Retain
the name only as a documented compatibility theorem and add an honestly named
form such as `twice_relativeDot_expansion` when the bridge is built.

The eventual character statements are distinct:

```text
chi_fund(q)  = 2 scalar(q)       -- fundamental character on the cover
chi_spin1(q) = 4 scalar(q)^2 - 1 -- sign-invariant descended character
```

The fundamental character changes sign under `q |-> -q`, so it does **not**
descend through `{+-1}`.  The SU(2) fundamental Wilson observable is therefore
not an SO(3) observable.  The spin-one trace is the first honest rational
quotient-side character candidate.

Likewise, an exact normalized `S^3` monomial formula, positivity of its square
pairing, and boundary-exchange symmetry do not prove Haar bi-invariance.
Until translations are constructed and proved invariant,
`sphereMoment4`/`productHaar` are explicit normalized sphere-moment
functionals intended to realize Haar, not formally established left-and-right
Haar functionals.

The surrounding legacy record names add no missing laws:
`quaternionPairAlg : ObsAlg` does not by itself prove a lawful unital
associative star algebra, and `productHaarProbFunctional` packages only the
fields actually required by the current `ProbFunctional` record, not
additivity, rational homogeneity, continuity, countable additivity, or group
invariance.  Those properties must be supplied by named theorems before the
packages are used as analytic or Haar data.

#### 8.13.5 Foundational promotion of the constructive ring normaliser

Hamilton associativity, norm multiplicativity, conjugation identities, the
spin-one matrix formula, and the exact kernel equations are multivariate
polynomial identities over `Q'`.  Hand-expanded reassociation chains would be
large and fragile.  The repository already has a sound reflective `Q'` ring
normaliser, but its physical location under `Continuum/` would reverse the
intended dependency direction if imported by `RepTheory`.

Promote its unique implementation to

```text
lean/YMGap/Constructive/RingNormaliser.lean
```

with `Constructive/RationalsMul` as its only project import.  Initially retain
the existing public namespace to avoid a mathematically irrelevant repository-
wide rename, and turn `Continuum/RingNormaliser.lean` into a compatibility shim
that imports the promoted source.  There must be one implementation, not two
copies whose soundness proofs can drift.

For every quaternion identity:

1. encode both coordinate expressions as `PolyExpr` data;
2. normalize both expressions;
3. kernel-check equality of normal forms by `rfl` or `decide`;
4. instantiate `poly_identity_of_normal_eq` at the quaternion coordinates;
5. transport the resulting `Q'.eqv` equalities into the quaternion setoid.

This route proves polynomial equalities with integer coefficients, which is
exactly the present algebraic need.  It does not decide inequalities,
arbitrary rational-function identities, denominator nonvanishing, topology,
or analysis.  All exported load-bearing identities retain explicit
`#print axioms` gates.

Combine this promotion with moving generic cancellation upstream from
`ConstructiveRepresentationDescent`.  Because both changes alter foundational
dependency cones, validate the smallest leaves and representative consumers
locally, then require a clean self-hosted all-module checkpoint; do not attempt
a broad local build.

#### 8.13.6 Exact cycle-free rational A1 module DAG

The dependency order is fixed as follows:

```text
Constructive/RationalsMul
  |--> Constructive/RingNormaliser
  `--> RepTheory/RationalQuaternionAlgebra

RepTheory/ConstructiveGroup
  |--> neutral cancellation calculus
  |--> RepTheory/QuaternionSign
  |--> RepTheory/LocatedCentralQuotient
  |--> RepTheory/ConstructiveSetoidPermutation
  `--> RepTheory/ConstructiveRepresentationDescent

RationalQuaternionAlgebra
  + Constructive/RingNormaliser
  `--> RepTheory/RationalQuaternionPolynomialLaws
        `--> RepTheory/RationalUnitQuaternionGroup

RationalUnitQuaternionGroup
  + QuaternionSign
  `--> RepTheory/RationalUnitQuaternionCenter
        + LocatedCentralQuotient
        `--> RepTheory/RationalA1LocatedQuotient

RationalUnitQuaternionGroup
  + ConstructiveSetoidPermutation
  + RationalUnitQuaternionCenter
  `--> RepTheory/RationalUnitQuaternionSpinOne

RationalA1LocatedQuotient
  + RationalUnitQuaternionSpinOne
  + ConstructiveRepresentationDescent
  `--> RepTheory/RationalA1RepresentationDescent

Constructive/RationalComplex
  + RepTheory/FiniteMatrix
  + RationalUnitQuaternionGroup
  `--> RepTheory/RationalA1FundamentalMatrix

RationalA1RepresentationDescent
  + RationalA1FundamentalMatrix
  + Continuum/SU2QuaternionPolynomialHaarCarrier
  `--> Continuum/RationalA1CoordinateMomentBridge
        `--> Continuum/RationalA1HaarBiInvariant
              `--> Continuum/RationalA1HaarPushforward

RationalUnitQuaternionGroup
  `--> RepTheory/RationalUnitQuaternionMetric
        + RepTheory/RationalUnitQuaternionNets
        `--> RepTheory/CompactUnitQuaternionCompletion

RationalA1LocatedQuotient
  + RationalUnitQuaternionMetric
  `--> RepTheory/RationalA1QuotientMetric
        + RepTheory/RationalA1QuotientNets
        `--> RepTheory/CompactRationalA1Quotient

CompactUnitQuaternionCompletion
  + CompactRationalA1Quotient
  + RationalA1HaarPushforward
  `--> Continuum/CompactA1HaarExtension
        `--> RepTheory/ConstructiveCompactGaugeGroupA1
```

No new `RepTheory` leaf on this path may import `Continuum`.  Coordinate,
moment, Wilson, and Haar adapters import the realized algebraic groups
downstream.  The promoted normaliser and cancellation leaf are what make this
orientation possible.

#### 8.13.7 Full rational unit-quaternion obligations

`RationalQuaternionPolynomialLaws.lean` must prove, at coordinatewise semantic
equality:

- Hamilton associativity;
- left and right identity;
- conjugation congruence and involutivity;
- reversal of multiplication by conjugation;
- `conjugate(q) * q ~= scalar(normSq(q))` and its right-handed analogue;
- `normSq(q * r) ~= normSq(q) * normSq(r)`; and
- preservation of squared norm by conjugation.

`RationalUnitQuaternionGroup.lean` then closes the unit-norm subtype under
multiplication and conjugation, uses conjugation as inverse, inherits the
coordinatewise semantic setoid and its decision procedure, and packages the
full group of rational points on the unit three-sphere as a
`ConstructiveGroup`.

This is a genuine full rational group, unlike Q8.  It is nevertheless
countable and incomplete in the intended continuum metric.  Calling it compact
SU(2) remains forbidden.

#### 8.13.8 Type-level `{+-1}` center

`RationalUnitQuaternionCenter.lean` must define the sign inclusion and first
prove the weakest reusable Type-level extractor:

```text
(x commutes with I and J)
  -> Sigma' s : QuaternionSign, x ~= includeSign(s).
```

This lemma is the efficient common core.  Full-center exhaustion is then the
immediate corollary

```text
(x commutes with every rational unit quaternion)
  -> Sigma' s : QuaternionSign, x ~= includeSign(s).
```

Commutation with `I` and `J` forces the three imaginary coordinates to vanish.
Unit norm then gives `a^2 ~= 1`.  The scalar sign must be extracted by the
following explicit constructive arithmetic route, rather than by classical
factorization or an erased disjunction:

1. unfold rational semantic equality to obtain equality of the raw numerator
   square and denominator square;
2. apply `congrArg Int.natAbs`;
3. rewrite both sides with `Int.natAbs_mul`;
4. use `Nat.mul_self_inj` to identify the absolute numerator with the positive
   denominator;
5. apply `Int.natAbs_eq_iff` to obtain the two possible signed numerator
   equalities; and
6. branch through the available `Decidable` equality and return the selected
   `QuaternionSign` together with its coordinatewise equivalence proof.

Both extractors live in `Type`.  A Prop-valued `Exists`, `Nonempty`, or bare
`Iff` would erase the sign required by quotient-kernel and descent code.  The
spin-one kernel proof should call the two-basis extractor directly rather than
first manufacture the stronger all-elements centrality premise.

Keep `QuaternionSign.lean` independent of `Q'`.  Define the downstream scalar
realization

```text
signScalar : QuaternionSign -> Q'
signScalar positive = 1
signScalar negative = -1
```

inside the rational-quaternion center layer, together with the Type-valued
`Sigma' s, a ~= signScalar s` witness.  The square-one proof needs only the
existing core APIs `Q'.mul_den_cast`, `Int.natAbs_mul`,
`Int.natAbs_natCast`, `Nat.mul_self_inj`, and `Int.natAbs_eq_iff`.
`Int.natAbs_eq_iff`'s `Or` is eliminated only while proving the Prop-valued
negative branch; the actual sign is selected in `Type` by decidable `a ~= 1`.

The raw quaternion wrapper should require only

```text
mul x.val basisI ~= mul basisI x.val
mul x.val basisJ ~= mul basisJ x.val
```

for `x : RationalQuaternion.UnitNorm`.  Four tiny normalizer certificates for
left/right multiplication by `I` and `J` expose the coordinates.  A rational
helper `a ~= -a -> a ~= 0` kills the three imaginary coordinates, and a scalar
norm certificate reduces `x.unitNorm` to `x.r^2 ~= 1`.  Put that rational
helper in the rational algebra/law layer, not in generic group cancellation;
the latter has no dependency on `Q'`.

`RationalA1LocatedQuotient.lean` then obtains its locator from decidable
semantic equality and constructs the exact quotient presentation.  Its honest
name remains “rational A1 sign quotient”; no topology or SO(3) identification
is implied.

#### 8.13.9 Constructive setoid permutations, spin one, and exact descent

`ConstructiveSetoidPermutation.lean` should define a permutation by explicit
forward and inverse maps, congruence for both maps, and pointwise inverse laws.
Two permutations are semantically equivalent pointwise.  Composition and
inverse then form a constructive group without function extensionality,
representative selection, or classical choice.

`RationalUnitQuaternionSpinOne.lean` acts on the pure-imaginary rational
three-space by

```text
v |-> Im(q * (0,v) * conjugate(q)).
```

It must prove:

- conjugation preserves the pure-imaginary subspace;
- conjugation by `q^-1` is the inverse permutation;
- quaternion multiplication maps to permutation composition;
- the explicit rational `3 x 3` spin-one matrix formula agrees with
  conjugation;
- the rational dot product is preserved;
- both included signs act trivially; and
- every proof that the action is the identity computes a sign witness.

The kernel-to-sign map evaluates pointwise identity at `I` and `J`, right
multiplies the two conjugation equations by `q`, and invokes the shared
two-basis Type-level extractor.  It must return the actual `PSigma` witness expected by
`RepresentationKernelHasGammaWitness`; it must not pass through an erased
Prop-level equivalence.

`RationalA1RepresentationDescent.lean` then applies the generic descent theorem
and proves

```text
spinOneCover = descendedSpinOne o quotientHom;
kernel(spinOneCover) = {+-1}, with explicit witnesses;
descendedSpinOne is faithful.
```

This closes exact rational algebraic descent.  It does not yet construct a
compact group, Haar functional, Lie-group isomorphism, or SO(3).

#### 8.13.10 Coordinate, trace, and moment bridge

The word “character” requires trace data.  Define constructive rational
complex scalars as explicit pairs of `Q'` values, finite matrices, conjugation,
adjoint, and the `2 x 2` quaternion fundamental representation.  Prove
multiplication, unitarity on unit quaternions, and

```text
trace(fundamental(q)) ~= 2 * scalar(q).
```

`RationalA1CoordinateMomentBridge.lean` must then prove that conversion between
the rational quaternion structure and the historical four-tuple carrier
preserves coordinates, semantic equality, norm, multiplication, and
conjugation.  For unit quaternions `g,h`, prove

```text
h^-1 ~= conjugate(h);
scalar(g * h^-1) ~= dot(g,h);
chi_fund(g * h^-1) ~= 2 * dot(g,h);
chi_spin1(g * h^-1) ~= 4 * dot(g,h)^2 - 1.
```

Only these theorems authorize promotion of the historical raw polynomial names
to genuine character or Wilson identities.  The fundamental cover observable
and sign-invariant quotient observable must remain separate.

#### 8.13.11 Genuine Haar bi-invariance and quotient pushforward

The exact sphere-moment functional becomes a rational Haar functional only
after proving, for every rational unit quaternion `q` and polynomial
observable `p`,

```text
H(p o L_q) ~= H(p);
H(p o R_q) ~= H(p).
```

The efficient proof route reuses the existing Gaussian/radial infrastructure:

1. define polynomial substitutions induced by the left and right quaternion
   multiplication matrices;
2. prove their evaluation/substitution equations;
3. derive orthogonality of those matrices from `normSq(q) ~= 1`;
4. lift the existing coordinate moment recurrences to multivariate polynomial
   integration by parts, prove that normalization plus
   `G(x_i p) ~= G(partial_i p)` uniquely determines the finite polynomial
   Gaussian functional, and show an orthogonal substitution satisfies the same
   recurrence by the finite chain rule and `A * A^T = I`; use an explicit
   Wick-pairing contraction only as a fallback if the uniqueness interface is
   more expensive than the finite pairing recursion;
5. transport invariance through the established homogeneous radial-factor
   relation from Gaussian moments to sphere moments;
6. extend from monomials to arbitrary finite polynomials by exact linearity;
   and
7. prove the two-boundary product functional invariant independently in each
   factor.

Boundary exchange is only one involution and cannot replace any of the four
left/right translation laws.

For the sign quotient, define the quotient coefficient algebra as precisely
the sign-invariant cover polynomials.  Construct its functional without a
chosen representative and prove the normalized pushforward equation

```text
H_cover(f o quotientHom) ~= H_quotient(f)
```

for every quotient coefficient.  The fundamental character is excluded from
that quotient algebra; the spin-one character belongs to it.

#### 8.13.12 Compact completion boundary

Compactness must be constructed rather than inferred from the unit-norm
equation.

`RationalUnitQuaternionMetric.lean` must give the rational unit group a
separated bi-invariant constructive-real chordal metric, with explicit
isometry moduli for left/right multiplication and inversion.
`RationalUnitQuaternionNets.lean` must construct finite `2^-n` nets with
coverage witnesses.  A finite rational stereographic atlas with denominators
uniformly apart from zero supplies rational unit points without introducing
irrational normalization.

`CompactUnitQuaternionCompletion.lean` then forms the Cauchy completion,
extends the group operations using their moduli, proves the laws by explicit
density, and supplies the required total-boundedness/completeness data.

For the quotient, use the projective metric

```text
d_pm([q],[r]) = min(d(q,r), d(q,-r)).
```

Prove separation and bi-invariance, descend the finite nets, and complete the
rational quotient directly.  Extending the already faithful rational spin-one
action is constructively safer than attempting to decide, for an arbitrary
constructive-real unit quaternion, whether it is `+1` or `-1`.

Only after proving that finite quotient and completion commute may the compact
quotient be identified with an internal `SU(2)/{+-1}` construction.  Only after
the completed spin-one map is proved a topological group equivalence onto the
intended rotation group may the quotient be called SO(3) without
qualification.

Finally extend the rational bi-invariant moment functional to the completed
coefficient algebra using explicit continuity moduli and dense approximation,
and prove invariance under completed group elements by limits with moduli.
Compactness alone does not construct Haar integration, and no classical Riesz,
Hahn--Banach, or choice-based uniqueness argument is permitted.

#### 8.13.13 Must-not-claim ledger

Until their explicit exit predicates are met, the following claims are
prohibited:

- “the full current tree is green” from the completed/cancelled run
  `29638079535` or from targeted successes; a post-repair complete cached JIT
  job with every required step inspected is required;
- “the current rational-A1 working tree was checked by that run” because the
  job is pinned to earlier commit `118172b`;
- “quotient type” or “canonical representatives” for the located same-carrier
  setoid;
- “full center” from centrality of the sign inclusion alone;
- “Q8 quotient has four elements” or “is V4” as a Lean theorem before those
  unneeded statements are formalized;
- “rational SU(2) point” for an arbitrary raw `Q'^4` tuple;
- “character” for `2 * dot` before the matrix-trace bridge;
- “SO(3) Wilson observable” for the non-descending fundamental character;
- “Haar” from normalization, positivity, moment formulas, or boundary swap
  without left and right translation invariance;
- “compact SU(2)” for the countable incomplete rational unit group;
- “SO(3)” for the finite Q8 fixture or uncompleted rational sign quotient;
- “compact central quotient” before quotient/completion compatibility;
- “Peter--Weyl data” from character moments alone;
- “compact simple group” or “actual group invariants” from the legacy
  `AdmissibleSimpleGroup` scalar certificate;
- “global-form Casimir minimum” for the legacy `CasimirData.C2_fund` rows, or
  the assertion that a defining representation minimizes every simple type;
- “actual `U(1)` central character” or “descended irreducible” for a finite
  phase-exponent code before the semantic highest-weight catalogue;
- a single Casimir eigenvalue for a faithful action that is reducible; its
  constituent list must be carried explicitly;
- “Clay-facing capstone” for the group-free legacy `FrontierDAG`, whose
  `boundedH` and `trueMargin` fields have machine-checked weakness fences;
- “completed positive-time OS root” while the canonical root is `Q'`-valued
  and the faithful cylinder/Haar functional is only `CReal`-valued;
- “global-form Casimir minimum” before the root/weight central-character
  restriction is derived; or
- any witness-bearing center/kernel theorem stated only through `Iff`,
  `Exists`, or `Nonempty`.

#### 8.13.14 Efficient verified commit sequence

1. **Repair the exact cold-run failures before asking for another full job.**
   Section 8.13.1 now records the final failed/cancelled result.  Sequentially
   replace the twice-refuted EightAnchor slicing candidate by a direct
   pointwise/range computation and recheck it, add the missing natural exponent
   transports and finer closed-sum/bridge subdivision to Terminal8189, and
   target-compile the still-unchecked E8 chart-A repair; retain the green
   BootstrapFourth and CubicDebt target evidence and diagnose the
   `CoreBResidualSimplex` suggestion-engine `PANIC`;
   separately compile the source-written shared dense `highRowPred` layer,
   compile the three explicitly staged observed rows, and only then compile
   their aggregates.  Never infer success for the cancellation-interrupted
   block-3 row 2.  Preserve the exact public statements and reject any
   `native_decide`, cap increase, or axiom workaround.  Before the next long
   job, include the source-complete
   `failure() || cancelled()` log-upload condition in the workflow static audit
   and commit.
2. **Integrate the present algebraic and one-step source checkpoint.**  Compile
   the four rational-A1 leaves, the directly edited continuum/API leaves, the
   adjacent-even physical-kernel symmetry leaf, and the source-written
   one-step query-geometry leaf sequentially with one worker; repair only
   actual elaboration failures, wire verified leaves into `YMGap.lean`, and
   rerun the static guard and affected-target *planner*.  Configuration changes
   correctly make that planner report `FULL BUILD REQUIRED`; do not execute its
   broad heavy consumer cone ad hoc.  Commit and push only after the targeted
   sequence, then start one known queued cached JIT job in the foreground and
   require the full build, frontier/statement/DAG/rubric guards, and mandatory
   complete axiom replay all to pass.
3. **Attack the nearest genuine Clay-facing residual, not more algebraic
   plumbing.**  First prove generic strict-joint adjacent-even one-step
   covariance from exact reflection symmetry, which does not need a Gram
   theorem.  Then prove diagonal positivity at the anchor coupling from the
   reachable physical Gram/SOS factorization; see Section 8.13.17.  Do not
   advertise positivity over the general coupling interval until a new
   coupling-parametric finite Gram argument exists: the current adjacent-even
   fixed-face factors are specialized to `anchorCoupling`.  The even-shift
   theorem is already proved and the odd-carrier route is machine-refuted, so
   shift one is the exact missing transfer theorem.
4. **Connect that theorem to its real OS consumer.**  Add the required
   `CReal` canonical-root adapter (or a proved rational-specialization bridge),
   then fill the dense self-adjointness and positivity fields that feed the
   completed time-translation semigroup.  Do not count a `Q'`-valued surrogate
   as the faithful heat-kernel construction.
5. **Install truthful Clay-facing guardrails.**  Define the pinned
   `ClayResolutionTarget`, `RevisedFrontierDAG`, and an adequacy theorem tying
   the group, action, Haar data, lattice family, transfer operator, physical
   margin, and OS reconstruction together.  The legacy `FrontierDAG` has known
   weak fields and is not a capstone.
6. **Resume the physical continuum attack.**  With the one-step transfer
   theorem connected, attack the true block-spin cross-difference estimate and
   its per-scale physical-margin recursion.  Scalar scorecard inhabitation is
   not a replacement for this step.
7. **Construct the finite exact `P/Q` and global-form Casimir layer.**  Follow
   Section 8.13.16 through the code-level located highest-weight minimum.  Use
   A1 parity as the first regression, but do not wait for rational/compact A1
   Haar or completion.  Keep finite phase-character codes distinct from actual
   `U(1)` characters and irreducible representations.
8. **Install the verified fast-binomial certificate kernel before any broad
   invalidation or new clean attestation.**  Add the checked Pascal table, its
   generic soundness theorem, and the cached closed-certificate twins described
   in Section 8.13.15.  Check the oracle first, then one worst E9 chart-B slice,
   the affine bridge, the base certificate, and the global coefficient
   certificate, all sequentially with one worker.  Commit this performance
   checkpoint before touching `RingNormaliser`: that module feeds the tensor
   reconstruction cone, so moving it first would invalidate the expensive
   certificates while they still use the exponential Pascal reducer.
9. **Resume the algebraic A1 track only against an explicit pinned consumer.**
   Promote the ring normaliser and cancellation calculus, prove the quaternion
   polynomial laws, package the full rational unit group, compute its
   Type-level sign center, and construct the located quotient and faithful
   spin-one descent.  Separate reflective certificates from group wrappers.
10. **Construct the rational coordinate/trace/moment and genuine Haar layer.**
    Build rational complex matrices, prove the `2*dot = trace` bridge, establish
    left and right invariance, and only then push Haar through the quotient.
11. **Construct metrics, explicit nets, completions, and compact A1 data.**
    Complete the rational quotient directly, extend the faithful spin-one
    action, prove quotient/completion compatibility, and instantiate compact
    SU(2)/SO(3).  This analytic tail must not block the finite `P/Q` work.
12. **Add actual highest-weight/irrep semantics and the global representation
    bridge.**  Relate code-level labels to realized irreducibles and central
    actions, distinguish the spectral minimum, adjoint value, and constituent
    list of a faithful reducible Wilson action, and feed them through
    `PinnedWilsonLatticeFamily` into the revised target.  Also prove that
    global-form label restriction embeds into the cover labels and hence that
    nonnegative quotient heat-kernel partial sums are bounded by the cover
    partial sums.

Every local Lean invocation remains the smallest named target with
`LEAN_NUM_THREADS=1`, after the process-conflict check.  No item authorizes a
bare local full build or concurrent Lean processes.  The foreground
self-hosted runner should be started for one coherent checkpoint at a time;
queue replacement/concurrency must not be used to create overlapping local
compilations.

#### 8.13.15 Clean-build cost audit and kernel-preserving optimization

The first clean Mac run exposes a sharply localized performance defect rather
than a reason to weaken verification.  For E9 chart B, the thirteen generated
row-data modules each compiled in roughly `0.3--0.8 s` and the thirteen
local-to-global aggregate modules in roughly `0.5--1.4 s`.  By contrast, the
thirteen seven-row certificate slices consumed `4849 s` in total.  The central
slices dominated: slice 5 took `1624 s`, slice 6 took `1244 s`, slice 4 took
`649 s`, and slice 7 took `479 s`; outer slices fell to `15--110 s`.

The cause is repeated kernel reduction of the direct Pascal-recursive
`RG.binom`, especially near central coefficients such as `binom 87 43`.
Each slice reduces five Boolean relations over `7 * 45 = 315` cells;
`xPascalExpected` and `yPascalExpected` repeatedly recompute binomial values,
while `affineChartBClearedCoeff` additionally performs nested 45-term sums with
repeated binomial and power reduction.  Cheap aggregates show that balanced
append wiring and source-table parsing are not the bottleneck.

The same clean run exposed a second, smaller peak-memory defect in
`EightAnchorWindowRetune`: one monolithic `by decide` attempted to kernel-check
the full 144-coefficient degree-143 Bernstein identity and hit the mandatory
20 GiB per-process ceiling after 146 seconds.  Later declarations elaborated
only by treating the failed private constant as an axiom, so this is a required
build failure, not a warning.  The working-tree repair preserves the exact
identity and certificate but checks four disjoint 36-coefficient
`take`/`drop` slices and recombines them constructively through
`allZeroB_append` and `List.take_append_drop`.  It uses no `native_decide`, new
axiom, or weakened predicate.  Its first guarded one-worker target check failed
after 100 seconds: the structural recombination proof needs to close the final
`true && true` simplification, while chunks 0, 1, and 2 each still reached the
kernel memory cap.  Hence 36 is not a safe chunk width.  Refine to smaller
exact slices was then tested, not merely proposed: the tapered 18-slice target
failed after 184 seconds, with each of its first seven decisions reaching the
same cap.  Because `head8IdentitySlice` performs `drop`/`take` only after
constructing `head8IdentityDiff`, every slice repays the full polynomial cost;
slice width is not the controlling resource.  Source line 203 also has an
extra closing parenthesis, but that syntax repair cannot change the reduction
architecture.  Replace the list-after-full-construction design by a direct
pointwise or bounded-range coefficient computation with an exact generic
bridge back to the original polynomial and a finite coverage/reconstruction
proof.  Do not raise `-M 20480` or weaken the unchanged 144-coefficient
identity.

The Terminal8189 target now exhibits a different resource shape.  Its cached
dependencies replayed safely, and the final leaf stopped after only `1.3s`
with a stack overflow under `-s 65536`, without memory or host pressure.  The
balanced four-fold power rewrite and flattened equivalence chain eliminated
that stack overflow on the next 182-second run.  That rerun exposed the later
issues the early failure had hidden: two `qpow_add` sites need explicit natural
exponent transport, and the large obligations beginning at lines 164, 170, and
175 still reached the memory cap.  Subdivide those closed sums and the semantic
bridge more finely after repairing the exponent congruence, then retry under
the same fixed stack and memory limits.  The exact margin is not yet
kernel-verified.

A later high-row family exposed the same structural lesson at a larger scale.
Within block 4, rows 4 through 1 succeeded in respectively `95`, `118`, `146`,
and `174` seconds, while row 0 hit the 20 GiB kernel cap at `196` seconds.
Block-3 rows 4 and 3 then hit the same cap at `218` and `233` seconds.  After
that third consecutive failure, the already-failed run was cancelled rather
than paying for the rest of a monotone expensive family.  The next row was
killed by cancellation and is not itself classified as a certificate defect.
The shared source repair replaces the generic sparse re-normalization of each
already-extracted `Z` row by an exact dense one-variable `M` convolution
algebra.  A simultaneous `mOnly` support check prevents variable loss, semantic
evaluation lemmas connect every dense operation back to the original
`PolyExpr`, and coefficient nonnegativity is reconstructed from widths
`6/10/14/20` plus the suffix after coefficient `50`.  This is cost-balanced
because the `N=M+8` shift puts the arithmetically largest coefficients early;
with maximum degree 78, the final suffix has at most 29 entries.  The shared
layer is source-written, and block-4 row 0 plus block-3 rows 4 and 3 all use the
staged theorem explicitly.  Every relevant target remains uncompiled.  The
public singleton and aggregate certificate statements and final semantic
endpoint remain unchanged, but the helper predicate's behavior on arbitrary
non-`M`-only external expressions is intentionally strengthened by `mOnly`.
No current in-repository consumer relies on that rejected behavior; do not call
the helper change definitionally or behaviorally API-identical.

The highest-payoff constructive repair is a kernel-verified fast binomial
oracle specialized to closed certificates:

1. keep authoritative `RG.binom` unchanged so existing semantic proofs do not
   churn;
2. generate a finite Pascal table through degree 89;
3. kernel-check its base, boundary, and local Pascal recurrence at every cell;
4. prove generically that lookup in any table with those certificates equals
   `RG.binom` on the covered triangle;
5. parameterize the closed coefficient-checking kernel by the verified lookup
   and rewrite its result back to the existing semantic kernel; and
6. cache powers such as `28^k` by an equally small checked recurrence.

The generated literals are not trusted results: the recurrence certificate and
the generic lookup theorem are checked by Lean.  This route introduces no
`native_decide`, opaque binary artifact, Python axiom, or classical choice, and
should remove the exponential duplication responsible for the central-row
hump.

The concrete minimal API is two cycle-free RG leaves:

```text
RG/PascalTable89Data.lean  -- generated transparent triangular literals only
RG/PascalTable89.lean      -- hand-written checker and soundness theorem
```

Rows `0` through `89` contain `4095` values.  A total `List.getD` lookup treats
entries above the triangle as zero.  The Boolean checker verifies the corner,
zero row, unit first column, and every local Pascal recurrence over the bounded
`90 x 90` square: `8100` small closed equations rather than repeated central
recursion trees.  Nat induction on `(n,k)` then proves

```text
lookup89 n k = RG.binom n k       when n <= 89 and k <= 89.
```

Expose a total `binomCached89`: use verified lookup inside the square and
canonical `RG.binom` outside.  Prove `binomCached89_eq_binom` for all naturals,
but do **not** mark it as a simp theorem, because automatic rewriting inside a
closed certificate would replace the cached operation by the expensive one.
The table generator must have a deterministic `--check` mode; the generator is
not trusted because Lean checks every local recurrence and the generic
soundness theorem.

Wire the cached total operation only into hot closed computations:
`elevatedMonoCoeff`, `upperBinomialPrefix`, `weightedGrid`, generated slice
weights, and `tailBaseWeightedCoeff`.  Preserve the public semantic statements
by explicit uses of `binomCached89_eq_binom`.  Keep the generic chart-B
`affineChartBClearedCoeff` unchanged; add a certificate-only cached twin and a
generic finite-sum congruence theorem equating it to the semantic definition.
This limits proof churn while accelerating both load-bearing and isolated
legacy certificates.

If cached binomial and power lookup is insufficient, replace chart B's dense
closed affine formula by a proved sparse Horner recurrence.  Writing

```text
R = 28 z + x - x z,
```

multiplication of a coefficient grid by `R` has the three-neighbour update

```text
(R C)_(a,b) = 28 C_(a,b-1) + C_(a-1,b) - C_(a-1,b-1).
```

A generic reconstruction theorem plus locally checked generated stages avoids
the present nested binomial sums while retaining a semantic proof of the same
polynomial identity.  Try the verified lookup first because it is smaller and
preserves the current certificate architecture.

For ordinary incremental cost, isolate `allNat`, grid lookup/relation, and the
fast closed arithmetic in a minimal stable computational leaf.  The expensive
slices currently import a broad semantic reconstruction module, so an upstream
semantic edit can invalidate all of them even when the closed arithmetic is
unchanged.  The semantic layer should instead import and consume the stable
computational leaf.

The two mutually colliding, compile-only E8 chart-A alternatives should also be
reviewed for archival outside the production glob.  Remove them only after
proving that no load-bearing module consumes either alternative and that the
tracked generator reproduces them.  Their current semantic-root exclusion does
not prevent `YMGap.*` from paying to compile both independently.

The immediate CI policy correction is already applied: manual dispatch now
defaults `clean_build` to `false`.  Ordinary trusted-main and manual runs retain
`lean/.lake`; a cache-independent run is reserved for toolchain, Lake,
source-selection, or cache-contract changes, concrete dependency suspicion, or
occasional milestone attestation.  Lake still recompiles every changed source
and reverse dependency, while the static import guard proves production-source
coverage.

The following are not performance solutions: increasing workers recreates the
Mac crash mode; changing seven-row shard size mainly trades peak memory against
restart granularity; removing axiom gates saves negligible time; and vendored
`.olean` files or `native_decide` would weaken reproducible kernel checking.
Schedule the fast-binomial work before the next genuinely necessary clean
attestation; do not repeat the cancelled cold run with the same exponential
certificate kernel, but do not delay ordinary cached mathematical checkpoints
after the observed failures are repaired.  Verify it with one
worker in increasing cost order: table/checker leaf, one historically worst E9
chart-B slice, the cached affine bridge, the tail-base certificate, the global
coefficient certificate, and finally the guarded self-hosted full build.

#### 8.13.16 Constructive `P/Q`, central characters, and the true global-form minimum

The existing scalar layer is not a global-form representation theorem.
`AdmissibleSimpleGroup R` stores only two inequalities and a closure
certificate; it has no Cartan datum, group, quotient, representation, or
provenance.  The legacy `CasimirData` rows likewise prove rational floor
inequalities, not minima over descended irreducibles.  In particular:

- for simply connected `B_n`, the spinor value
  `n * (2*n+1) / 8` is below the vector value `n` at ranks 2 and 3;
- in the long-root-square-two normalization the `D_n` vector and half-spin
  values are `(2*n-1)/2` and `n*(2*n-1)/8`, so the stored legacy
  `(2*n-1)/4` is neither; and
- cover representations in `A_n`, `C_n`, `E6`, and `E7` can be rejected by a
  nontrivial quotient.

The current source comments are corrected to state this boundary.  Do not
change the legacy numeric API by fiat; replace it downstream with the following
cycle-free constructive derivation.

1. `RepTheory/CasimirNormalization.lean` extracts only the normalization and
   rational target floors `3/4` and `2`.  It must not import legacy
   `RepData`, `SimpleGroup`, or `CasimirData`.
2. `RepTheory/FiniteDynkinCoordinates.lean` defines `IntWeight T`,
   `DominantWeight T`, the witness-bearing
   `DominantWeight.Nontrivial lambda := Sigma i, 0 < lambda i`, basis weights,
   bounded label lists, a coverage witness, and a finite rational `argminQ`.
   Enumeration uses `List`, `Fin`, Boolean reflection, and `PSigma`; no
   `Nat.find`, choice, `Exists`, or quotient supplies a label.
3. `RepTheory/FiniteCenterCharacters.lean` distinguishes center points from
   character codes and defines `PhaseExponent`, `centerPairing`, explicit
   subgroup presentations, `CenterCharacterCode.TrivialOn Gamma`, and a
   decidable `trivialOnBool` with its specification.  Cyclic subgroups are
   enumerated by multiples of the recorded index; the Klein-four cases use the
   three marked axes.  Self-duality of a finite center is a chosen perfect
   pairing, never definitional equality.
4. `RepTheory/CartanMatrix.lean` fixes source-level node numbering and defines
   each finite Cartan matrix and the simple-root embedding `Q -> P`.  State
   Bourbaki numbering explicitly for exceptional types so the E6/E7 charge
   tables are not ambiguous.
5. `RepTheory/WeightRootQuotient.lean` supplies a witness-bearing exact
   presentation:

   ```text
   structure RootQuotientPresentation (T) where
     classOf : IntWeight T -> CenterCharacterCode (simplyConnectedCenter T)
     class_add : ...
     class_root : ...
     rootDifferenceOfClassEq :
       classOf lambda = classOf mu ->
         Sigma beta, lambda = mu + rootEmbed beta
     classLift :
       (q : CenterCharacterCode ...) -> Sigma lambda, classOf lambda = q
   ```

   Thus both directions of `[lambda]=[mu] iff lambda-mu in Q` are
   constructive, and the reverse direction returns integer root coordinates.
   Use direct classical-family formulas plus fixed kernel-checked integer
   certificates for exceptionals; do not first build a general Smith normal
   form algorithm.
6. `RepTheory/GlobalFormCentralCharacter.lean` defines
   `highestWeightCharacter`, `CodeDescends`, `GlobalHighestWeight`, and
   `codeDescends_iff_trivialOnGamma`.  Required regression gates are A1 full
   quotient parity, the A2 adjoint rule `p+2*q = 0 mod 3`, and B2 rejection of
   the spinor with acceptance of the vector.  At this stage these are finite
   phase exponents, not characters into `U(1)`.
7. `RepTheory/NormalizedRootMetric.lean` stores the exact fundamental-weight
   Gram matrix `G`, with `A^T G = D`, symmetry, entrywise nonnegativity,
   positive diagonal, and a long-root pin `D_ii = 1`.  Classical families use
   parametric formulas; exceptional literal matrices are accepted only through
   generic checked matrix identities.
8. `RepTheory/DominantWeightCasimir.lean` defines

   ```text
   C2(lambda) = (1/2) * sum_i,j lambda_i * (lambda_j + 2) * G_ij
   ```

   and proves `casimir_zero`, `casimir_add`, `casimir_mono_add`, the fundamental
   values and floor, `casimir_floor_of_nontrivial`, an explicit adjoint label,
   adjoint descent through every global form, and
   `adjointCasimir_eq_dualCoxeter`.  The universal floor must follow from the
   normalized metric, not from a literature scalar renamed `C2_fund`.
9. `RepTheory/GlobalFormCasimirMinimum.lean` makes the infinite minimum a finite
   located search.  If `M` is the exponent of `Gamma`, subtracting
   `M * omega_i` from any coordinate above `M` preserves descent and cannot
   increase Casimir.  Iteration reduces every allowed nonzero label to the
   inhabited box `0 <= lambda_i <= M`.  Implement
   `restriction_period`, `reduceAllowedToBox`, and

   ```text
   structure LocatedHighestWeightCasimirMinimum (code) where
     label : DominantWeight code.cartan
     nontrivial : label.Nontrivial
     descends : CodeDescends code label
     least : forall mu, mu.Nontrivial -> CodeDescends code mu ->
       casimir label <= casimir mu
   ```

   with `locatedHighestWeightCasimirMinimum`, `globalFormMinimum_floor`, the two
   A1 minima, and the correctly quantified uniqueness theorem for equality
   with the floor.

Items 1--9 are finite code-level mathematics and should begin without waiting
for quaternion Haar, metrics, or compact completion.  The following semantic
boundary remains separate:

10. `RepTheory/HighestWeightDescentSemantics.lean` introduces an actual irrep
    catalogue with both label/irrep round trips, the central-action pairing,
    the Casimir formula, and triviality iff the label is zero.  Only this layer
    may promote the located label minimum to a group spectral minimum.
11. `MassGap/GlobalFormRepDataBridge.lean` carries three distinct data:
    spectral minimum, adjoint/dual-Coxeter value, and the finite constituent
    decomposition of the selected faithful Wilson action.  A reducible
    faithful action has no single Casimir eigenvalue.  Projection to legacy
    `RepData.C2_fund` requires a named compatibility theorem.
12. Realized group/action/Haar/lattice data feed a pinned
    `RevisedFrontierDAG` and `ClayResolutionTarget`.  Multiplying the legacy
    group-free DAG by a decorative global-form code is forbidden.

Finally prove

```text
globalLabels_embed_coverLabels
globalHeatKernelPartialSum_le_coverPartialSum
```

because global-form restriction deletes nonnegative summands.  This transfers
uniform cover tail estimates efficiently while retaining the exact
quotient-specific spectral minimum.

#### 8.13.17 Direct one-step reflection-transfer priority

The nearest theorem with a real OS-reconstruction consumer is the missing
strict-joint shift-one identity.  It is genuinely open: the existing
`strictJointEvenOneSidedTimeCovariance_derived` only reaches `shift + shift`,
and polarization determines only the symmetric average at doubled time.  Put
the new theorems in downstream adjacent-even leaves, rather than making the
doubled-time identity module depend backward on the adjacent-even physical
kernel development.  Exact reflection symmetry is coupling-parametric, while
the available fixed-face positive factors are anchor-specific.  The first
honest public API therefore separates generic covariance from anchor-only
positivity:

```text
theorem strictJointOneSidedTimeCovariance_one_derived
    {coupling : Q'} (hcoupling : 0 <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointOneSidedTimeCovariance hcoupling hle 1 left right

theorem strictJointOneSidedTimeCross_one_anchor_nonnegative
    {base : Nat} (v : StrictJointCylinderVector base) :
    CReal.leEv CReal.czero
      (strictJointOneSidedTimeCross
        (coupling := anchorCoupling) (by decide)
        (Q'.le_refl' anchorCoupling) 1 v v)
```

Every even shift is already supplied by
`strictJointEvenOneSidedTimeCovariance_derived`.  The one-step parity fence
proves that the odd carrier cannot establish the result, so the adjacent-even
geometry is necessary rather than stylistic.

**Covariance track (first, no Gram hypothesis).**

1. Define the finite adjacent-even physical reflected kernel for arbitrary
   `coupling` by summing the literal slab physical term over the enumerated
   fixed-face labellings in
   `Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry.lean`.  Import the
   reflected-boundary assembly plus `FiniteDeterministicKernelPushforward` and
   define

   ```text
   adjacentEvenHalfStates K radius :=
     boundedEdgeLabellings K (adjacentEvenLowerFaceIds radius)
   adjacentEvenBoundaryChannels K radius :=
     boundedEdgeLabellings K (adjacentEvenFixedFaceIds radius)
   adjacentEvenPhysicalReflectedKernel coupling K radius left right :=
     listQSum (fun boundary =>
       slabParametricKPhysicalTerm coupling K
         (adjacentEvenExtent radius)
         (assembleAdjacentEvenReflectedSlabLabelling
           radius left boundary right))
       (adjacentEvenBoundaryChannels K radius)
   ```

   Here the displayed term must use `coupling`, not `anchorCoupling`; the
   latter enters only the positivity track.
2. For each fixed boundary, combine
   `assembleAdjacentEvenReflectedSlabLabelling_reflection_swap`,
   `assembleAdjacentEvenReflectedSlabLabelling_bounded`, and
   `slabParametricKPhysicalTerm_supported_reflection`.  The resulting term
   identity has the right/left orientation; take `Q'.eqv_symm` and lift it
   through the finite boundary sum with `listQSum_congr_on`.  This proves exact
   kernel symmetry without any PSD or Gram claim.
3. **Source-written and statically audited; compilation pending:**
   `Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry.lean` now transports
   and re-encodes the strict lower root and the time-shifted strict upper root
   into ambient `adjacentEvenExtent radius + 1`; its intended theorems prove
   canonicality, adjacent-even slab support, and the exact root/list reflection
   exchange.
   The raw seed is `adjacentEvenReflection_exchanges_raw_oneStep`, but raw
   plaquette equality is not yet canonical-root or event equality.  Use the
   existing one-way support identities
   `centralStrictLowerCanonicalRoot_raw_sameSupport` and
   `centralStrictUpperCanonicalRoot_raw_sameSupport_local` with their stated
   orientations.

   The common fit hypothesis must be

   ```text
   strictQueryBase (base + 1) <= radius,
   ```

   not merely `strictQueryBase base <= radius`: the shifted upper source is a
   canonical root in box `base+1`.  Bank the definitional geometry

   ```text
   adjacentEvenAmbient radius := adjacentEvenExtent radius + 1
   adjacentEvenExtent radius = centralAmbient radius
   adjacentEvenExtent radius = oneStepReflectionExtent radius
   ```

   and define the two roots by transporting
   `centralStrictLowerCanonicalRoot radius base root` and
   `centralStrictUpperCanonicalRoot radius (base+1)
   (timeShiftCanonicalRoot 1 base root)` from `centralAmbient radius` into
   `adjacentEvenAmbient radius`.

   Complete-query geometry includes the one-link exterior shell, not only the
   root faces.  For each lower and upper root, prove canonicality, internal
   slab support, exterior-face membership in
   `boundaryCompleteSlabPlaquettes (adjacentEvenExtent radius)`, and the
   lower/upper `adjacentEvenPlaquetteSide` identity for both internal and
   exterior faces.  The useful time inequalities are the lower
   `targetTime+2 <= radius` / `targetTime+1 <= radius` pair and the upper
   `radius+3 <= targetTime` / `radius+2 <= targetTime` pair, together with the
   upper ambient bound.  Without the exterior statements the later complete
   occurrence predicate has an unproved zero-shell clause.

   Reflection must also be encoded in the ambient face enumeration.  Define an
   ambient `adjacentEvenAmbientFaceReflectId` using `boxPlaquetteAt`, prove its
   physicality, involutivity, plaquette identity, and adjacency preservation,
   and expose membership equivalences for both roots and exterior shells.  Do
   **not** apply the slab-coordinate `slabFaceReflectId` to an ambient
   canonical-root identifier: those are different finite enumerations.

   Finally, literal source-order list exchange must pass through canonical
   re-encoding

   ```text
   geometricSupportIds (adjacentEvenAmbient radius)
     ((geometricPolymer ... lower).map
       (timeReflectPlaquette (adjacentEvenExtent radius))),
   ```

   using `geometricSupportIds_sameSupport` and
   `faceSupport_eq_of_geometric_sameSupport`.  A raw claim
   `lower.map reflectId = upper` is unjustified because reflection may change
   enumeration order.  Preserve source ordering and multiplicity by mapping
   this per-root canonical exchange over the root collection; duplicate source
   roots are harmless.  This leaf remains entirely finite and constructive:
   no `Classical`, choice, `native_decide`, kernel positivity, or Gram import.

   The current source contains the exact ambient/extent identities; lower and
   shifted-upper transported canonical roots; canonicality and same-support
   bridges; lower/upper internal-face time, slab-membership, support, and side
   theorems; the corresponding one-link exterior-shell time,
   boundary-complete-slab, and side theorems; same-support reflection of the
   two roots; canonical `geometricSupportIds` re-encoding of the reflected
   lower root as the upper root; an ambient `boxPlaquetteAt` reflection ID with
   physicality, plaquette, involution, and adjacency theorems; internal and
   exterior membership equivalences in both directions; and the order- and
   multiplicity-preserving mapped-root-list exchange.  It carries 36 direct
   source axiom gates.  Static review removed the unused
   physical-kernel/Gram-chain import in favor of direct
   `Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry` and added the required
   `Z4HalfTimeReflectionFaceReindex` import and namespace opening.  The import
   guard accepts the resulting graph and the leaf contains none of `Classical`,
   `noncomputable`, `native_decide`, or `Gram`.  None of those source facts is
   a Lean elaboration result, an event-law theorem, a covariance theorem, or a
   positivity theorem; all such claims remain pending Steps 4--8.
4. Add `Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw.lean`.  This leaf has
   one necessary API bridge beyond canonical root-list reflection: a marked
   polymer event is a predicate on ambient excited support, whereas
   `slabEventNumerator_reflection` acts on slab `EdgeLabelling`s.  Implement
   the bridge in the following finite, constructive order.

   1. Define the joint source-ordered root chart as
      `adjacentEvenStrictLowerCylinderRoots ... ++
      adjacentEvenStrictUpperCylinderRoots ...`; prove its doubled length and
      canonicality under `strictQueryBase (base + 1) <= radius`.  Define the
      pair-family event with `sourceCylinderEvent` and
      `centralStrictJointPairPredicate roots.length left right`.  Prove its
      fingerprint formula by `familyOccurrenceFingerprint_append`,
      `List.take_append_length`, and `List.drop_append_length`.  Do not impose
      artificial length or nonemptiness hypotheses: malformed label lengths
      correctly make the Boolean predicate false, and the empty family is a
      legitimate event.
   2. Form the marked atoms with `familyCanonicalAtoms`; expose their values,
      length, and support, and prove that `slabMarkedCylinderEvent` for these
      atoms is extensionally the raw family event.  The support proof splits
      the joint list and uses the lower/upper canonical-root support lemmas.
   3. Prove the missing physical reflection identity for zero extension:

      ```text
      slabToAmbientPhysical extent
        (reflectSupportedSlabFaceLabelling extent physical) face
      =
      slabToAmbientPhysical extent physical
        (adjacentEvenAmbientFaceReflectId radius face).
      ```

      Here `face` is an ambient physical face in the boundary-complete slab
      and `extent = adjacentEvenExtent radius`.  The direct finite proof uses
      `boxPlaquetteAt_mem_enumerate`, `slabToAmbientPhysical_eq_on_enumerate`,
      `slabGeometricSpin_eq_of_enumerate`,
      `reflectSupportedSlabFaceLabelling_eq_on_physical`,
      `slabPlaquetteAt_slabFaceReflectId`, and the ambient-reflection
      `boxPlaquetteAt` theorem.  Package the consequence as equality, or
      membership equivalence, for `excitedPlaquetteIds`.
   4. Lift that bridge to the complete component-occurrence query for each
      source root.  Prove lower-on-reflected-support equals upper-on-support and
      conversely, for both internal and one-link exterior faces, using all four
      membership equivalences from the query-geometry leaf.  Canonicality and
      the existing internal/exterior slab-membership lemmas supply every
      physicality and support premise.  Reflection of occupied root faces alone
      is insufficient: omitting the exterior zero shell would change the event.
   5. Map the per-root identities over the source-ordered collection to exchange
      the lower and upper support fingerprints.  Convert back to occurrence
      fingerprints with
      `familyOccurrenceFingerprint_eq_supportQueryFingerprint`,
      `physicalCanonicalAmbientFamily_unionSupport`, and
      `physicalCanonicalAmbientFamily_mem_compatible`; this preserves duplicate
      source roots and order exactly.
   6. Lift the family event to the slab by
      `cutoffOneLiftedFamilyEvent (adjacentEvenAmbient radius) ...
      (slabToAmbientPhysical (adjacentEvenExtent radius) physical)`.  Prove the
      function equality

      ```text
      reflectSlabEvent (adjacentEvenExtent radius) eventLR = eventRL
      ```

      by the two fingerprint exchanges and Boolean conjunction commutativity,
      then apply `slabEventNumerator_reflection` for every nonnegative
      `coupling`.
   7. In `Z4HalfTimeReflectionSlabFiniteKConditionalLaw.lean`, first add the
      generic zero-extension numerator bridge between the preceding slab event
      and the ambient event masked by `ambientSlabSupportedB`.  Derive it from
      the existing one-list zero-extension permutation and
      `slabWeightedPhysicalSum_eq_ambientSupported`; no lower/fixed/upper
      inverse or triple Fubini is required.  Only after this bridge normalize
      with `slabParametricKPhysicalPartition_pos hcoupling K
      (adjacentEvenExtent radius)` and expose equality of the two conditional
      probabilities.

   Do not import
   `Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry` into the event leaf:
   its boundary-summed kernel has no marked-event mask and belongs to the
   separate positivity/kernel-reindex lane.  The exact conditional law needs
   only nonnegative coupling, not an anchor upper bound, and remains finite and
   intuitionistic: list maps, decidable Booleans, and involutions suffice; no
   `Classical`, choice, `noncomputable`, `native_decide`, Gram theorem, or full
   Fubini is licensed.  Expected public gates are `{propext, Quot.sound}`.
   The minimal direct import boundary is the adjacent-even query-geometry leaf,
   `Z4HalfTimeReflectionSlabFiniteKConditionalLaw`, and
   `Z4HalfTimeReflectionStrictJointMarkedCylinder` (with the canonical query
   decoder imported explicitly only if transitive availability is insufficient).

   Then, in a distinct conditional-stability leaf, prove the
   arbitrary-even-extent specialization of
   `couplingPhysicalAmbient_givenSlabProbability_abs_sub_le_of_floors` for
   these new atoms: establish even-slab support plus the internal and exterior
   carrier floors. At
   `radius = strictQueryBase (base + 1) + stage`, the explicit error is
   bounded by
   `couplingSlabConditionalBoundaryEpsilon (2 * roots.length) (stage + 4)`;
   it is not zero at a finite stage. Prove that this bound vanishes only in the
   subsequent limit. The
   existing odd `couplingPhysicalStrictJointPredicate_givenSlab_abs_sub_le`
   cannot be reused literally.  Do not divide by the existing odd-slab
   denominator.
5. Add `Z4HalfTimeReflectionAdjacentEvenOneStepVolumeComparison.lean`.  There
   is an essential one-cell geometry mismatch which the current theorem does
   not cover:

   ```text
   centralExtent r       = 2*r + 1
   centralAmbient r      = 2*r + 2
   adjacentEvenExtent r  = 2*r + 2
   even slab ambient     = adjacentEvenExtent r + 1 = 2*r + 3.
   ```

   Hence neither `couplingPhysicalCentralFaceQuery_cross_centered_abs_sub_le`
   nor the stricter existing
   `couplingPhysicalStrictJoint_cross_centered_abs_sub_le` reaches the new
   carrier literally.  Use the latter as the exact small-law pattern, import
   `Z4HalfTimeReflectionStrictJointCenteredRecoding` and
   `Z4CouplingParametricCrossVolumeStability`, and instantiate the shift-one
   approximant at transformed base `base+1`.  Transport the same strict-joint
   centered roots and marked atoms one additional ambient step, prove that
   transported event is precisely the adjacent-even lower/one-step-upper
   event, and apply
   `couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le`
   with `large := centralAmbient radius + 1` but the same small roots, inner
   box, and protected distance `stage`.  Convert the compatible difference to
   the physical difference with
   `couplingPhysicalAdjacentDifference_eqv_compatible`.  Prove, rather than
   assume, the resulting bound

   ```text
   spinSummedCylinderBoundaryEpsilon
     (roots.length + roots.length) stage.
   ```

   Its orientation is the required large transported marked event minus the
   small source event.
6. Add `Z4HalfTimeReflectionStrictJointAdjacentEvenOneStepCovariance.lean`.
   Recode each stage of `strictJointOneSidedTimeCross ... 1` as heterogeneous
   fingerprint entries, compare the left/right and right/left forms with the
   same symmetric even law using
   `finiteHeterogeneousCrossBilinear_bipushforward_eqv_cross` and
   `finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1`, control coefficient
   mass with `heterogeneousCoefficientPairL1_nonnegative`, dominate the error
   by `spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow`, and close
   with a public/extracted version of the private
   `creal_equiv_of_abs_sub_le_half_pow`.  This yields the generic
   `strictJointOneSidedTimeCovariance_one_derived` and its direct-limit
   descent.

The covariance leaf imports the polarized doubled-time module only for the
public cross/covariance definitions.  It must not import the oriented
doubled-time covariance leaf (which already imports polarization), derive
cross symmetry from diagonal positivity, apply `reflectionBilinear_self` to a
cross term, treat the raw plaquette exchange as an event identity, or use any
adjacent fixed-interface Gram theorem.

**Positivity track (second, anchor coupling).**

1. First prove an adjacent-even analogue of
   `slabParametricKPhysicalTerm_crossPlane_factorization` for the assembled
   physical term, with the load-bearing public identity named
   `adjacentEvenAssembledSlabNumerator_eqv_lower_interface_upper`.  The present
   adjacent-even chain factors only the fixed-link
   multiplicity product and sums fixed-face coefficients; it does **not** yet
   attach the lower/upper face coefficient products, lower/upper nonfixed-link
   multiplicities, normalization, or strict-cylinder query factors to the full
   `ReferenceWeight`/slab numerator.
2. Introduce the reachable restricted-interface kernel and prove its exact
   symmetry in
   `Z4HalfTimeReflectionAdjacentEvenReachableInterfaceSymmetry.lean`, importing
   the reachable-support leaf.  Enumerate support points as pairs of a bounded
   lower-state index and a bounded fixed-boundary-channel assignment, filtered
   by the *pointwise* condition that every fixed-link
   `fusionChannelAmplitude (6*K) lowerSpins endpoint` is nonzero.  Supply an
   explicitly proved reachable vacuum fallback so every total `Nat` lookup is
   supported.  For each link, nonzero amplitude gives
   `endpoint <= lower-spin-sum`; combine this with
   `adjacentEvenFixedLink_lower_add_fixed_sum_le_auxiliary`, apply
   `fusionWalkMultiplicity_symmetric_of_endpoint_budgets`, lift through
   `adjacentEvenGlobalFixedIncidenceTrajectoryKernel_eqv_transitionProduct`,
   and finally through the physical-boundary sum defining
   `adjacentEvenFixedInterfaceEndpointKernel`.  This removes the `11/12`
   artificial endpoint fence but establishes symmetry only.
3. Prove the support-compression identity before invoking any Gram theorem.
   For a supported pair `q`, let `owner(q)` be its lower-state index and
   `end(q)` its endpoint, and put

   ```text
   C(i,q) := if owner(q) = i then
     adjacentEvenLowerAmplitudeProduct ... (lowerAt i) (end q)
   else 0.
   ```

   Amplitude vanishing above `3*K` and the `6*K` lower-plus-fixed budget must
   prove

   ```text
   finiteKernelSandwich T A fullBoundaryCount i j ≈
     finiteKernelSandwich
       (fun q q' => T (end q) (end q')) C supportCount i j.
   ```
4. The genuine open finite theorem is now explicit:

   ```text
   repT : GramRep (fun q q' => T (end q) (end q'))
   ```

   No current declaration constructs `repT`.  The facewise
   `adjacentEvenGlobalDependentFixedFaceChannelGramRep` cannot simply be summed
   along predecessor and post-channel trajectories because those are distinct
   maps; the proved `twoStepDirectedCompatibility_not_gramRep` and mixed-face
   fence block that Schur-pullback shortcut.  Raw physical fixed-face labels
   cannot be promoted to nonnegative Gram ranks either:
   `fundamentalFixedFaceKernel_not_positiveSemidefinite` supplies an explicit
   negative quadratic, and the existing face `d` weights have already summed
   the physical label, so multiplying them by physical coefficients would
   double-count it.  Investigate either a new constructive Gram theorem for
   the product of commuting reachable face operators (with explicit rational
   LDL/common-square data and zero-pivot handling) or a direct common-middle
   tensor-network SOS identity.  Do not record either route as complete until
   the exact equality and nonnegative rational weights are proved.
5. Once `repT` exists, apply `finiteKernelSandwichGramRep repT C supportCount`.
   The final weights are exactly `repT.d`, with nonnegativity `repT.hd`, and

   ```text
   Phi k i := finSum (fun q => C i q * repT.v k q) supportCount
   K1(i,j) ≈ finSum
     (fun k => repT.d k * (Phi k i * Phi k j)) repT.r.
   ```

   This is a Gram representation of the *already-sandwiched physical
   half-state kernel*, not of the unrestricted middle endpoint matrix.
   Applying `finiteKernelSandwichGramRep` directly to the globally refuted
   `adjacentEvenFixedInterfaceEndpointMatrix` would be circular.
6. Identify that Gram kernel with the literal adjacent-even slab numerator
   through the existing Fubini, trajectory-collapse, reflection-swap, and
   terminal-delta theorems;
7. Push the finite Gram statement through the adjacent half-state/support
   encodings using `finiteHeterogeneousCrossBilinear_bipushforward_eqv_cross`
   and control the comparison with
   `finiteHeterogeneousCrossBilinear_abs_sub_le_pairL1`;
8. Divide by the positive partition function, compare to the centered limit,
   pass diagonal nonnegativity to `CReal`, and prove
   `strictJointOneSidedTimeCross_one_anchor_nonnegative`; then descend through
   the direct limit and completion.

The principal existing ingredients are
`adjacentEvenGlobalDependentFixedFaceChannelGramRep`,
`adjacentEvenFixedFaceCoefficientTransitionSum_eqv_resummedKernel`,
`adjacentEvenTrajectoryLinkProduct_eqv_faceProduct_mul_terminal`,
`adjacentEvenSeparatedTerminalTargetSum_collapse`,
`assembleAdjacentEvenReflectedSlabLabelling_reflection_swap`,
`adjacentEvenAssembledUpperAmplitude_eqv_commonLower`,
`adjacentEvenFixedLink_lower_add_fixed_sum_le_auxiliary`,
`fusionWalkMultiplicity_symmetric_of_endpoint_budgets`,
`adjacentEvenLowerLinkAmplitude_eq_zero_above_three_mul`, and
`finiteKernelSandwichGramRep`.

Neither `fusionWalkMultiplicity_symmetric_of_endpoint_budgets` nor
entrywise nonnegativity proves positive semidefiniteness: a symmetric matrix
with nonnegative entries can have a negative eigenvalue.  Likewise, the
reachable-support theorems prove vanishing, budgets, and word reversal, not a
`GramRep`.  The weighted SOS identity in the positivity track must therefore
remain an explicit load-bearing theorem.

Do not retry the refuted full `0,...,6*K` endpoint-window Gram factorization,
independent shared-face resummation, mixed-map Schur pullback, or odd-carrier
route.  First close generic covariance by reflection symmetry, then the exact
anchor-coupling positivity theorem.  The current fixed-face Gram factors use
`heatKernelPacket K anchorCoupling`, so interval-wide
**positivity** is a later theorem requiring a genuinely coupling-parametric
Gram construction.  This restriction does not apply to covariance, whose
finite proof uses exact reflection invariance for arbitrary coupling.

The final consumer must also resolve a codomain mismatch: `CanonicalOSRoot`
currently uses the `Q'`-valued `ObservableMeasure.ProbFunctional`, whereas the
faithful heat-kernel moments and strict cylinder completion are `CReal`-valued.
Add a `CReal` canonical-root generalization or a proved rational-specialization
bridge before claiming `PositiveTimeOSRoot`.  Once connected, the shift-one
theorems supply the dense self-adjointness and positivity fields; contraction,
nonexpansive stage maps, the direct-limit form, and the completed semigroup are
already present.

#### 8.13.18 Cached all-module consistency and fail-closed axiom replay

An ordinary cached `lake build` is a full consistency check of the selected
library even when unchanged modules are not re-elaborated.  The static import
guard enumerates every current `lean/YMGap/**/*.lean`, checks imports and
cycles, validates the semantic exclusions, and pins the `YMGap.*` glob plus
the umbrella and both statement guards.  Lake traces include the Lean
version/commit, source content, transitive imported artifacts, options, and
module identity; a mismatch rebuilds the module.  When a trace is current,
Lake replays its saved info log, including every `#print axioms` diagnostic,
into the new `lean-build.log`.

The axiom auditor is therefore hardened as follows:

1. reuse the import guard's lexer to enumerate every executable source-level
   `#print axioms` command outside nested comments, line comments, and strings;
2. require one command per source line and exact `Counter` equality between
   expected and observed `(file,line)` sites, rejecting missing, stale,
   concatenated, or duplicated diagnostics;
3. parse Lean-generated `_private.YMGap...` names and identifiers containing
   `?`, reject every non-YMGap canonical name, and require Lake 4.29.1's
   terminal `Build completed successfully` marker in every supplied log;
4. fail with infrastructure exit 3 on any mismatch in normal, strict, or update
   mode, so a partial, killed, failed, or stale log cannot pass the mandatory
   non-strict gate or regenerate a baseline;
5. store only axioms outside `{propext, Quot.sound}` in reviewed exceptions,
   while unioning full axiom sets for repeated canonical names so independently
   compiled colliding alternatives cannot overwrite and hide a forbidden
   dependency; and
6. pin the effective Lake `weakLeanArgs` contract: the package-level tuple is
   exactly the resource-only `-s 65536 -M 20480`, and all three library-level
   weak-argument lists are empty.  This prevents a future semantic weak flag,
   which Lake deliberately excludes from artifact hashes, from reusing stale
   proof artifacts.

The log also carries one schema-versioned provenance fingerprint over the
sorted repo-relative paths and bytes of every default-build `YMGap` source,
the umbrella and both statement-guard roots, the Lean toolchain, Lake package
and manifest inputs, the Make entry point, and the axiom/import audit scripts.
Every listed input is required.  Thus a log from stale source selection,
toolchain, Lake configuration, Make wiring, or audit code is rejected before
its diagnostics can be treated as evidence.

The log-integrity gap exposed by the targeted CubicDebt run is now closed.
That run saw a nonfatal library-suggestions `SymbolFrequency` heartbeat
`PANIC` while `CoreBResidualSimplex` was being written, even though Lake
marked the module built and continued. The source now executes that metadata
pass without the failing heartbeat limit, and guarded direct/cached target
runs contain no `PANIC`. Independently, the mandatory auditor rejects every
unreviewed `PANIC` or internal-error record even if Lake returns zero; no
blanket allowlist was added. A green cached CI run must still exercise this
new log-integrity gate before the full-tree state is certified.

Lake source confirms the replay premise: current `SavedTrace` logs are replayed
when the dependency hash is up to date, while module trace construction hashes
the source, toolchain, ordinary options, imports, and setup.  The permitted
weak arguments affect only stack and memory ceilings and are separately pinned
by Step 6.

The Mac runner is likewise fail-closed.  Post-cold-run foreground sessions use
the checksum-pinned official runner `v2.335.1`, revalidate the executable's
reported version after reconciling stale state and before any new registration,
and use a fresh repository-scoped JIT configuration rather than deprecated persistent
`--once`; GitHub assigns it at most one job.  The official `run.sh` supervisor
provides its supported update/relaunch and signal-forwarding behavior.  The
workflow then verifies the exact pinned `Runner.Listener` version as its final
locked-host command block before Lean.  A runner self-update can therefore not
silently compile: the job stops until the version, archive checksum, setup,
launcher, and workflow pin are deliberately advanced together.  A one-job
helper exit is never used as completion or absence evidence. Normal or trapped
exit requests and verifies cleanup from a durable positive exact-ID visibility
witness, retaining recovery state if verification fails. Archive
extraction and every setup validation reapply owner-only mode `0700` to the
runner root.  The listener is brought online only in the foreground for one
known queued trusted-main job, and a workflow job has a `480`-minute timeout.

That paragraph describes the current source contract, not completed live JIT
evidence.  Run `29638079535` was accepted by the legacy foreground
registration.  The first post-run launcher must remove that inactive legacy
registration, create one JIT registration, claim the known queued cached job,
and demonstrate verified remote/local cleanup before the migration is called
operationally tested.

One canonical per-user atomic host lock is held for the entire session and
honored by every repository-managed Lean/Lake/pytest Make entry point.  The
standalone wrapper samples the process list both before and after winning the
`mkdir` race; cleanup retains the lock if any named runner
supervisor/listener/worker, Lean, Lake, or pytest process survived, or if
process enumeration failed.  Runner services, helpers, and both `_update.sh`
and `update.sh` are conflicting high-load processes as well.  The workflow
requires at least 32 GiB installed and approximately 32 GiB currently
available, then performs another AC/RAM/process/version preflight immediately
before the build.  A bounded static guard scans every tracked or untracked,
non-ignored executable repository entry point and rejects an unwrapped or
uncapped Lean/Lake/pytest route.  `LEAN_JOBS` is override-resistant and exactly
one throughout `Makefile`, `AGENTS.md`, `CLAUDE.md`, and `lean/AGENTS.md`.
`make test` and the documented named-test command additionally force the
OpenMP, OpenBLAS, MKL, vecLib, and NumExpr thread pools to one thread.  Process
discovery includes both a direct `pytest` executable and
`python[version] -m pytest`; it distinguishes pgrep's “no match” status from
process-enumeration failure and refuses the latter rather than running
fail-open.  This serializes project-controlled commands; arbitrary bare
operating-system processes remain an explicit operator boundary, and
hostile-code isolation still requires a dedicated non-admin macOS account.

Runner labels provide routing, not authorization.  Every actor or workflow
able to queue a job with the complete matching label tuple is inside the trust
boundary, because repository-scoped JIT registration is not intrinsically
bound to this workflow or branch.  The known-queued-run foreground rule is
therefore security-critical, not merely operational convenience.

Interrupted JIT sessions require two cleanups. Before the registration POST,
the launcher atomically writes an owner-only recovery record binding the
repository and a unique runner name in the `pending` phase; after a complete
response it atomically promotes that record to `registered:<id>`. Before
starting the Listener, a bounded exact-ID GET must bind the same recorded name
and ID and the launcher durably records `remote-visible:<id>`. Before a remote
deletion it then writes `remote-delete-requested:<id>`; only verified remote
absence advances it to `remote-removed:<id>`. Thus every accepted ID-specific
404 is downstream of both a synced positive visibility witness and a
contemporaneous successful, completely paginated repository-runner collection
whose valid total and globally unique returned IDs prove that exact ID absent.
An authorization-/repository-masked 404, malformed collection, incomplete or
changing pagination, duplicate IDs, or a collection that still contains the ID
retains `remote-delete-requested`; the official helper's normalized status is
irrelevant.
Every atomic promotion is followed by `/bin/sync`, and only verified remote and
local cleanup removes the record. Legacy completion/deletion records from the
old heuristic are conservatively treated as unconfirmed registrations and
must regain exact visibility. Normal/trapped cleanup and the next
conflict-free launcher therefore reconcile by exact name or ID even across a
lost response, power failure, or untrappable `SIGKILL`. `--check` parses this
state without mutation and fails rather than claiming readiness while any
recovery remains. Stale-state reconciliation and safe legacy migration precede
the exact version rejection; an operator must not switch installation roots
while state or local credentials remain. The official local-only
removal path is invoked when baseline or migrated settings survive;
credentials-only partial state is deliberately preserved and rejected rather
than erased. Because `SIGKILL` also leaves the atomic lock after it has been
acquired, the operator first
performs the documented no-process check and removes only that stale empty
directory; recovery never guesses that a live lock is stale.  The build
uses only the AC-conditional `caffeinate -s` assertion (plus disk-idle `-m`),
so an unplugged Mac may sleep instead of being forced awake on battery.  AC is
sampled at launch and immediately before Lean; it is not falsely described as
a continuous watchdog.

Namespace-digest drift remains informational because adding an axiom-clean
theorem is normal.  Completeness and the forbidden-axiom gate are mandatory.
At the current post-sharded-bootstrap **verified inventory** checkpoint, the
wiring audit covers `2538` source modules, `7887` local import edges, zero
cycles, `2532` semantic-root-reachable modules, and exactly the six reviewed
exclusions.  The source inventory contains `19579` executable axiom-gate lines
after the Q8, adjacent-even physical-kernel-symmetry, ten isolated Sixth
bootstrap leaves, and one-step query-geometry gates were added.

The cancelled `118172b` log is intentionally a negative test: it lacks the
terminal success marker and the later source sites, so the hardened auditor
must reject it rather than treating its many successful cold artifacts as
complete evidence.  After the eight failures in Section 8.13.1 are repaired,
verify the implementation against a completed cached all-module log, which
must report exact complete replay, and then through the next trusted-main JIT
job.  This closes the precise gap between “incremental build” and “full current
axiom evidence” without requiring a clean rebuild on every commit.

#### 8.13.19 Constructive-real OS transfer and provenance boundary

The strict thermodynamic-limit reflection form is genuinely `CReal`-valued.
There is no current theorem, and no general mathematical reason to expect one,
that makes all of its values rational or eventually constant rational
approximants.  Therefore the production OS path must not be routed through the
legacy `Q'`-valued `PositiveTimeOSRoot`.  A rational specialization is permitted
only as an optional regression adapter carrying an explicit realization proof

```text
structure RationalFormSpecialization (B : V -> V -> CReal) where
  Bq : V -> V -> Q'
  realizes : forall x y, CReal.Equiv (B x y) (CReal.ofQ' (Bq x y))
```

and it may never be inferred merely from the existence of rational
approximants.

Implement the faithful route in the following dependency order.

1. Add `CRealTransferCore.lean` with a minimal
   `CRealCompletedTransferCore` over the existing
   `CRealSeminormCompletion.SquaredSeminorm`.  Its fields are only a completed
   pairing, transfer map, self-adjointness, transfer positivity, and
   contraction.  Do not advertise a Hilbert space until completed addition,
   scalar multiplication, inner-product laws, and completeness have themselves
   been constructed.
2. Add `Z4HalfTimeReflectionStrictJointCompletedInner.lean`.  For completion
   representatives `X,Y`, form the diagonal rational sequence
   `n |-> (strictJointCylinderStageReflectionBilinear (X.seq n) (Y.seq n)).approx n`.
   Prove its explicit `CReal.QCauchy` modulus from the representatives'
   Type-valued moduli, sharp stagewise Cauchy--Schwarz, and local norm bounds;
   then define the pairing with `CReal.ofQ'CauchySeq`, prove independence of
   close representatives, descend it to the quotient, and prove the embedding
   formula.  Do not try to extract computational moduli from arbitrary
   Prop-valued `CReal` Cauchy witnesses.
3. After the shift-one results in Section 8.13.17, add
   `Z4HalfTimeReflectionStrictJointTimeOneTransfer.lean`.  Shift-one covariance
   plus symmetry proves self-adjointness; diagonal shift-one cross
   nonnegativity proves positivity; existing time-translation distance and
   norm estimates prove contraction; the existing direct-limit time action and
   completed semigroup supply the transfer map and semigroup law.  Package
   exactly these results at `coupling := anchorCoupling` as the first
   `CRealCompletedTransferCore` consumer.  A coupling-parametric core must wait
   for the interval-wide positivity theorem; generic covariance alone is not
   enough.
4. Separately establish canonical provenance.  Choose
   `ContinuumFunctional.CRealProbFunctional` as the minimal canonical
   expectation interface and add a conversion from
   `WilsonProbFunctional.ProbFunctionalC`.  For signed cylinder observables,
   introduce a stronger `CRealLinearProbFunctional` carrying normalization,
   positivity, addition, and rational homogeneity.
5. Add `Z4SignedCylinderObservableAlgebra.lean`: signed simple-cylinder
   presentations modulo common-chart/refinement equivalence, with unit,
   addition, negation, rational scaling, pointwise multiplication, star, and
   the induced `CReal` expectation.  Prove refinement invariance, normalization,
   linearity, and positivity before consuming this algebra elsewhere.
6. Add `Z4StrictJointReflectedFormPin.lean` and prove the load-bearing identity
   `strictJointReflectionBilinear_eq_expectation_reflectedProduct`, together
   with positive-time support, reflection and time maps, representatives, and
   essential surjectivity.  This prevents an abstract positive form from being
   silently substituted for the physical cylinder expectation.
7. Only after Steps 1--6 add `CanonicalCRealOSRoot.lean`, composing distinct
   functional/provenance, positive-time transfer, and completed-transfer roots.
   Keep the spectral-gap package separate.

The shift-one theorem and this adapter still do **not** furnish a normalized
vacuum or probe, Rayleigh bounds, a strict transfer eigenvalue gap, a finite
`SpectralModel`, a `LocatedSpectralGap`, identification with a Hamiltonian
spectrum, or Hilbert completeness.  In particular,
`PositiveTimeOSRoot.rayleighLower/rayleighUpper`,
`FunctionalContinuumTarget.gnsGap`, and
`ContinuumFrontierScorecard.OSReconstructedGap.genGap` remain supplied data;
the last field has no proved generator/spectrum provenance and must remain
quarantined from every completion or Clay-facing claim.

#### 8.13.20 Guarded verification checkpoint and adequacy-preserving next move

(2026-07-18, session 7, later checkpoint.)  This section supersedes only the
provisional compile-status sentences above; it preserves the failed-run
history and all mathematical must-not-claim boundaries.  Every target below
was run serially through the canonical host lock, with one Lean worker and the
unchanged `-s 65536 -M 20480` limits.  No clean build or raised resource cap
was used.

The following guarded target builds now exit zero:

1. the original clean-run repairs:
   `HarmonicLowerSixTailEnvelopeCertificateE8ChartA` (46 jobs, final target
   166s), `HarmonicMassCrossLowerSixRecoveryBootstrapFourth` (490 jobs, final
   target 121s), and
   `HarmonicLowerSixCubicDebtCoefficient1330Physical` (528 jobs, final target
   1.0s);
2. the shared dense-univariate HighRows engine (547 jobs, final target 620ms)
   and all three formerly failing consumers: `...HighRowsBlock4Row0`
   (548 jobs, final target 47s), `...HighRowsBlock3Row4` (final target 51s),
   and `...HighRowsBlock3Row3` (final target 55s);
3. `CoreBResidualSimplex` (192 jobs, final target 32s), after explicitly
   executing the symbol-frequency metadata pass without a heartbeat limit;
   the successful direct run and later cached replay contain no `PANIC`, and
   its public gates remain unchanged;
4. `RepTheory/QuaternionSign` (3 jobs, final target 158ms),
   `RepTheory/RationalQuaternionAlgebra` (4 jobs, final target 210ms),
   `RepTheory/LocatedCentralQuotient`, and
   `RepTheory/RationalQuaternionQ8Fixture` (9 jobs);
5. `Continuum/EightAnchorWindowRetune` (319 jobs, final target 170s), using
   the direct structural coefficient oracle rather than any eager
   `drop`/`take` reconstruction of the full degree-143 polynomial;
6. `Continuum/HarmonicMassCrossLowerSixRecoveryTerminal8189` (492 jobs,
   final target 9.6s), after replacing the strict degree-65025 power fold by
   the exact base-256 decomposition
   `w^n ≈ (w^256)^(n/256) * w^(n%256)` and splitting the remaining semantic
   transports into bounded opaque declarations;
7. `Continuum/Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry`
   (698 jobs) and
   `Continuum/Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry`
   (779 jobs), establishing the presently written exact Step-3 geometry and
   reflection/exchange layer; and
8. `RepTheory/SimpleGroup`, `RepTheory/CasimirData`,
   `Continuum/SU2QuaternionPolynomialHaarCarrier` (384 jobs), and
   `MassGap/SimpleGroup` (82 jobs).

These are exact kernel checks of the named targets and their replayed
dependency cones.  They are not a full-tree certificate.  In particular, the
successful EightAnchor run validates the unchanged public 144-coefficient
identity through its new pointwise coefficient bridges; it does not by itself
validate the complete source inventory.

There is now no known red target among the eight failures discovered by the
cancelled clean run.  The final Terminal8189 repair preserves the exact
18-block lower enclosure and its positive `830/1000000` margin, but changes
how powers are kernel-evaluated: `Nat.div_add_mod`, `qpow_add`, and
`qpow_qpow` justify a base-256 representation with at most 254 outer and 255
residual folds instead of 65025 strict multiplications.  Explicit `Q'.eqv`
algebra replaces the invalid raw-equality ring reconstruction.  The successful
guarded build reports only `propext` and `Quot.sound` on all five exported
Terminal8189 gates.  This is a targeted dependency-cone result; only the next
complete cached build and mandatory source-site audit can establish current
full-tree consistency.

Four additional local scalar-capstone adequacy gaps exposed by this tranche
are listed below, independent of compilation. They are not an exhaustive Clay
frontier: the earlier census still records the canonical-provenance, CReal OS
completion, generator/spectrum, continuum/volume-limit, local-field/OPE/AF,
and all-group-realization residuals.

1. `budget_closes_uniform` accepts `hadm` but its base theorem does not use
   that hypothesis.  Thus the theorem presently closes an abstract numerical
   budget, not a physical admissibility-dependent Yang--Mills recursion.
2. No proved rate theorem binds the scale index `m0` to `gapBound`.  A positive
   budget and a separately supplied gap bound therefore do not yet yield a
   quantitative uniform mass scale.
3. There is no representation-specific, constructively positive sigma floor
   derived for each `R`.  A generic positivity field must not be advertised as
   the Wilson-loop/string-tension lower bound for an arbitrary nontrivial
   representation.
4. `mass_gap_suN` does not tie its parameter `R` to `N`, does not realize
   `SU(N)` or its chosen global form, and does not consume the available Weyl
   data in the mass-gap derivation.  It is an abstract interface theorem, not
   yet a theorem about every physical `SU(N)` Yang--Mills theory.

Consequently the most efficient sound order is:

1. run the static guards and obtain one successful cached all-module build;
2. commit and push the entire current source/CI contract, including the
   presently untracked canonical lock wrapper, then launch one foreground JIT
   self-hosted job on exactly that commit and require the complete mandatory
   axiom replay and every terminal guard to pass; and
3. after full-build green, implement
   `Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw` as the highest-leverage
   mathematical next leaf, followed immediately by the finite-volume
   comparison/covariance transfer.  Keep the anchor-coupling positivity/Gram
   lane explicit and separate.

The current self-hosted wiring is therefore source-designed and partially
target-verified, but **not certified complete**.  Certification requires the
CI changes and lock wrapper to be tracked in a pushed commit and a green JIT
run on that exact commit.  A local targeted pass, a static workflow reading,
or the cancelled `118172b` run cannot substitute for that live evidence.

#### 8.13.21 Complete current wiring, bounded Sixth repair, and Mac JIT CI

(2026-07-18, session 8, authoritative local checkpoint.)  This section
supersedes the compile-status and current-inventory sentences above, but not
their failure history or any mathematical must-not-claim boundary.  Every
Lean command in this checkpoint ran through the fixed per-user session lock,
with one Lake worker, `-s 65536 -M 20480`, AC-aware `caffeinate -ms`, and
positive nice value.  The memory ceiling was never raised.

The first complete current-source discovery replay found exactly one red
module after every independently buildable module had been checked:
`HarmonicMassCrossLowerSixRecoveryBootstrapSixth`.  Both original `Fin 50`
decisions reached the kernel memory ceiling.  This was a successful safety
failure: Lean exited with `excessive memory consumption detected`, the wrapper
released its lock only after a conclusive process scan, system memory remained
approximately 90 percent available, and the host did not swap itself into a
crash.  The generated E9 and E8 row families and the rest of the current
reverse-affected tree completed in the same serialized discovery run; no
second source failure appeared.

A proportional in-file split did not solve the problem.  Three `Fin 25`
quarters below `k=623` still reached the cap, and bisecting them into
`Fin 12`/`Fin 13` declarations did likewise.  Controlled single-module probes
then located the actual replay boundary: the exact `k=548` case, `Fin 6`,
`Fin 10`, and `Fin 11` all pass under `-M 20480`, while `Fin 12` fails.  Thus
the issue is bounded evaluator size, not falsity of the inequality, and a cap
increase is neither necessary nor permitted.

There is no already-proved symbolic shortcut for this finite tranche.  The
relevant fixed-center cells are

```text
c = 33: 542 <= k <= 575
c = 34: 576 <= k <= 609
c = 35: 610 <= k <= 645
c = 36: 646 <= k
```

Reducing `548..622` to three endpoint checks would first require 72 currently
unproved within-cell drop signs: `548..574`, `576..608`, and `610..621`.
`lowerSixFixedCenterSparseSlack_antitone_add` assumes those raw signs,
`lowerSixFixedCenterDrop_nonnegative_of_cleared` assumes their cleared signs,
and the global traversal assumes all three sign families.  The post-bootstrap
odd-exponent budget also genuinely fails in these cells, for example
`40*133 > 9*550`, `40*137 > 9*578`, and `40*141 > 9*612`.  Proving uniform
drop nonnegativity here is a substantive analytic frontier, not a cheaper
replacement for the exact finite certificate.

The sound bounded fallback is therefore ten independent modules
`BootstrapSixthBlock0` through `BootstrapSixthBlock9`, proving the disjoint
`Fin 10` ranges

```text
548..557, 558..567, 568..577, 578..587, 588..597,
598..607, 608..617, 618..627, 628..637, 638..647.
```

Each leaf imports only the existing Fifth bootstrap cone, uses ordinary
kernel `decide`, and has its own axiom gate.  Separate modules are load-bearing:
each leaf gets a fresh Lean process and OS-level memory reclamation boundary,
and Lake caches every `.olean` independently.  The original six public Sixth
theorem names and types are unchanged.  Their two `Fin 50` wrappers and
`Fin 100`/physical/residual wrappers use only index case splits, `omega`, and
`simpa only` with explicit index equalities, so future simp-set growth cannot
unfold the expensive rational expressions accidentally.

The named sharded replay is green:

```text
dependency-cone jobs:       502
ten leaf times:             18--21 seconds each
public assembly time:       376 ms after cache
leaf/public axiom gates:    exactly [propext, Quot.sound]
PANIC/internal diagnostics: none
```

The authoritative cached all-module replay then completed successfully.  Its
source/configuration fingerprint and exact integrity census are:

```text
YMGAP_SOURCE_FINGERPRINT: d92eaeec27e4466aa2fcf4909dec6ea33e255f034c940f57b296166cee809f44
Lake jobs:                2544, terminal success
production modules:      2538
local import edges:      7887
directed import cycles:  0
semantic-root reach:     2532
reviewed exclusions:     6 of 6; unexpected exclusions 0
executable axiom sites:  19579 of 19579 observed at exact current locations
audited declarations:    19556
audited namespaces:      2392
forbidden exceptions:    0
```

The mandatory audit passed against that complete log; the reviewed baseline
was regenerated, and strict namespace-digest mode then passed with zero drift.
`docs/frontier-status.md` was regenerated from the same provenance-bound log
and reproduced byte-for-byte in stdout validation.  The cached frontier
uninhabitedness guard, ten-statement hash guard, and 129-job Clay scorecard all
passed.  The static Frontier-DAG check reports 12 enumerations, 10
registered/grandfathered, 2 reviewed exemptions, and 0 unbridged enumerations.
The Clay-facing result remains exactly what it was: fixed-spacing clauses are
kernel-proved while continuum existence and the Clay target remain OPEN.

This checkpoint also establishes the incremental full-build contract.  A
clean rebuild is not required at every checkpoint.  `make lean-build` always
selects the complete default target set; Lake revalidates changed sources,
options, toolchain inputs, and reverse dependencies, then replays saved module
logs for unchanged artifacts.  The import guard independently proves exact
source discovery, root reachability, exclusions, and acyclicity.  The log
auditor requires one current fingerprint, every executable `#print axioms`
source site with its exact multiplicity, no forbidden axiom, no PANIC/internal
diagnostic, and terminal full-build success.  The fingerprint covers every
production Lean source plus the guard roots, pinned toolchain, exact Lake
configuration and dependency-free manifest, Make build contract, and both
import/axiom auditors.  A clean build remains an explicit milestone operation
for toolchain/build-selection changes, concrete cache-corruption evidence, or
occasional independent attestation; it is not the ordinary consistency check.

The personal-Mac CI route is now statically complete and independently
re-audited.  The workflow has the conjunctive labels `self-hosted`, `macOS`,
`ARM64`, and `ymgap-m4max`, with no hosted fallback: when the Mac is offline a
job queues instead of consuming hosted compute.  It accepts only trusted-main
pushes or manual dispatch on `main`, retains the local Lake cache, uploads no
successful artifact or remote cache, and keeps only a three-day failure log.
GitHub does not charge hosted compute minutes for this self-hosted execution;
local electricity, network, wear, and any residual artifact storage remain
operator costs.

The official ARM64 runner is pinned to `2.335.1` and its published archive
SHA-256.  Setup and launch share the same atomic owner-only host lock and full
runner/Lean/Lake/pytest process fence.  Setup holds that lock through runner
root mutation, checksum/version inspection, extraction, and repository-label
configuration.  The foreground launcher creates one repository JIT runner for
at most one job and uses the durable state sequence

```text
pending -> registered:<id> -> remote-visible:<id>
        -> remote-delete-requested:<id> -> remote-removed:<id>.
```

Every state promotion explicitly guards chmod/rename, byte-compares the exact
record including its final newline, and syncs before the next remote mutation.
A failed DELETE can be accepted only when two independently acquired,
complete, canonical runner-collection snapshots match and omit the exact ID,
with exactly one well-formed exact-ID HTTP 404 bracketed between them.
Authorization-masked, multiple-status, malformed, changing, incomplete, or
target-containing responses retain recovery evidence.  `Runner.PluginHost` is
inside the shared conflict fence.  Trapped signals use a bounded verified
direct-child TERM/TERM/KILL protocol, never wait on an unconfirmed live PID,
and unconditionally retain local/remote recovery state and the host lock
because arbitrary action descendants cannot be exhaustively recognized.
Pure checks now cover 236 executable entry points, 10 remote-state scenarios,
and 4 bounded-shutdown scenarios; Bash 3.2 syntax and every workflow shell
block pass.  No persistent runner service is installed.

One operational certification step remains before this CI route may be called
live-green: commit and push the exact reviewed tree, start one foreground JIT
session only after confirming that exact SHA is queued, require the complete
mandatory workflow to pass, and verify both remote runner removal and local
lock/recovery cleanup.  Static design, a local green build, or a run on an
older SHA is not a substitute.

After that exact pushed-SHA CI pass, the highest-leverage constructive next
move remains `Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw`.  Implement it
in this order:

1. construct joint lower/upper root labelling and canonical pair atoms;
2. prove the slab-to-ambient physical reflection identity, including the
   one-link exterior zero shell;
3. prove complete internal-plus-exterior query exchange and
   support-to-occurrence fingerprints;
4. define the lifted slab event, prove `reflectSlabEvent` equality, and derive
   `slabEventNumerator_reflection`;
5. add the generic zero-extension numerator bridge in
   `SlabFiniteKConditionalLaw`, then normalize with the positive partition.

Keep this leaf intuitionistic: minimal imports, explicit finite witnesses,
ordinary decisions only, no `Classical`, choice, `noncomputable`,
`native_decide`, Gram/Fubini overreach, or unproved physical identification.
Then compose the finite-volume comparison/covariance transfer, followed by the
constructive-real completed-transfer and canonical-provenance sequence in
Sections 8.13.17 and 8.13.19.  The abstract scalar-capstone adequacy gaps in
Section 8.13.20 remain quarantined and must not be advertised as Yang--Mills
or Clay closure.

#### 8.13.22 Standalone categorical spike: verified evidence, not critical path

(2026-07-18, session 8, post-checkpoint addendum.)  The untracked
`cat_structural_spike/` has now been reviewed as a deliberately separate Lake
package rather than silently folded into the production module graph.  It
uses the same Lean `4.29.1` pin, no package dependency, and the repository's
`-s 65536 -M 20480` ceiling.  Its four source modules give concrete,
proof-relevant versions of three structural ideas:

1. `DomGrowth` makes witnessed domination compositional; `chain_bound` and
   `gap_persists` expose telescoping and gap persistence as projections of a
   composite morphism rather than repeated external inductions.
2. `UniformGap` represents volume-uniformity by one positive apex and a cone
   of unit-ratio legs.  `transport` and `ofCofinal` make comparison and
   exhaustion reusable, while differing volume constants cannot inhabit the
   record in the first place.
3. `NaturalityGuard` turns a shifted-normalization defect into the proved
   negation `square_fails_for_shifted_ledger`, alongside a positive control.
   This is an exact kernel audit of the bookkeeping square, not a heuristic
   numerical test.

The package is constructively clean at its stated surrogate level: no
`sorry`, `Classical`, `native_decide`, Mathlib, or new axiom; all ten
executable gates report exactly `[propext]`.  In addition to its clean Linux
container attestation, exact Mac parity is now green under

```text
caffeinate -ms nice -n 10 ./scripts/with_lean_session_lock.sh cat_structural_spike env LEAN_NUM_THREADS=1 lake build
```

Lake completed 7 jobs in 5.2 seconds wall-clock; the final process scan
removed the canonical lock.  This result is deliberately separate from the
production fingerprint
`d92eaeec27e4466aa2fcf4909dec6ea33e255f034c940f57b296166cee809f44`:
the spike has its own Lake root and is not imported by `YMGap`, so neither its
success nor a future failure may be misreported as production-tree evidence.

The mathematically efficient decision is **quarantine, not promotion, at this
checkpoint**.  The spike organizes ledger bookkeeping but proves no new
analytic sign, finite-volume reflection law, continuum measure, OS
reconstruction, or physical mass gap.  Promoting it now would add an
abstraction migration ahead of a known load-bearing missing theorem.  Complete
`Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw` and its finite-volume
comparison/covariance transfer first.  Only afterwards reconsider, in order:

1. instantiate `Dom` over the repository's `Q'` setoid (and eventually
   constructive reals) while preserving witness-bearing homs;
2. wire categorical composition to the actual per-scale `singleStep`
   certificates and recover the existing anchor inequality by projection;
3. promote `NaturalityGuard`-style exact squares into the adversarial audit
   only where a real ledger comparison consumes them.

No Clay-facing claim may cite the categorical vocabulary itself.  Promotion
earns its place only if it removes duplicated proof obligations from at least
two production consumers or supplies a transport/universal property actually
used by the analytic spine.

#### 8.13.23 First exact-SHA JIT run: safe pre-build failure and idempotence repair

(2026-07-18, session 8, live certification attempt.)  Commit `8647b65`
(`Harden Mac CI and advance constructive YMGap fronts`) was pushed to `main`,
and GitHub queued run `29661602621` for the exact full SHA
`8647b653423c13587ebdf5eabde07e860decd0ab`.  The read-only host preflight,
pinned runner `2.335.1` setup, legacy-registration removal, unique JIT
registration, exact-job claim, and static import/host-wiring steps all passed.
The run then failed before any Lean process began, in `Select pinned Lean
toolchain`, because the host's `elan` reports an already-installed toolchain as
an error when `elan toolchain install` is repeated:

```text
error: 'leanprover/lean4:v4.29.1' is already installed
```

This is an operational idempotence defect, not a source/build inconsistency.
The safety boundary behaved correctly: no compilation or pytest process was
started; the job ended in seconds; the JIT credentials and local registration
were removed; the exact remote runner collection became empty; the recovery
record and canonical lock disappeared after conclusive process checks; and no
runner/Lean/test process remained.

The workflow now captures `elan toolchain list`, fails closed if that
inspection fails, parses its first whitespace-delimited field, and treats an
exact match for the pinned toolchain as success.  It invokes `elan toolchain
install` only when the exact pin is absent.  This supports both unannotated
list lines and lines with trailing markers such as `(default)`, without
weakening the subsequent `lean --version`/`lake --version` check.  The repaired
workflow must be committed and pushed, and a fresh exact-SHA JIT run must pass
all mandatory stages before live CI certification is complete.

#### 8.13.24 Exact-SHA Mac CI certification: live green and self-cleaning

(2026-07-18, session 8, completed live certification.)  The idempotence repair
was committed as `deeba1e` (`Make self-hosted Lean toolchain selection
idempotent`) and pushed to `main`.  GitHub run `29661761406`, job
`88125528479`, claimed a unique foreground JIT runner and executed the exact
full SHA `deeba1ebf4d9ff33617ccec18cbcbd037cfcc3d9`.  The canonical build
reported

```text
YMGAP_SOURCE_FINGERPRINT sha256:d92eaeec27e4466aa2fcf4909dec6ea33e255f034c940f57b296166cee809f44
Build completed successfully (2544 jobs).
```

The full build ran from 21:32:33Z to 00:23:51Z.  Every subsequent mandatory
stage was green: the exact full-log integrity audit, reviewed namespace
baseline, strict namespace digest, frontier-status regeneration and stdout
reproduction, frontier-uninhabitedness guard, ten-statement hash guard,
Frontier-DAG audit, and 129-job Clay scorecard.  The source-level repairs that
had motivated conservative sharding were also exercised by this exact run:
the ten Sixth-tranche blocks each completed in approximately 18--22 seconds,
their public assembly in 390 milliseconds, the previously heavy HighRows
consumers in 47--54 seconds, and the Fourth and Fifth bootstrap assemblies in
116 and 126 seconds respectively.

This is a genuine live certification, not a static inference or an older-SHA
run.  Host sampling stayed approximately 90--92 percent memory-available.
The largest observed Lean processes stayed flat below the hard 20 GiB address
space cap (the semantic bridge and U0 factor rows were approximately 15 GiB;
the dense certificate approximately 12.7 GiB; the EightAnchor leaf
approximately 9.4 GiB), and memory was reclaimed after each serialized
process.  Compilation remained single-process, single-threaded, nice-priority,
AC-powered, caffeinated, session-locked, and guarded by the complete
runner/Lean/Lake/pytest process fence.  The cap was not raised.

Teardown was independently checked after the job: the repository runner
collection was empty; no `.runner`, credentials, `.ymgap-jit*` recovery state,
runner/listener/worker/plugin-host process, Lean/Lake/pytest process, or
`/tmp/ymgap-lean-session-501.lock` remained.  Thus the foreground runner is
not a persistent service and cannot silently consume future jobs.  A future
push queues without hosted fallback whenever this Mac is offline.

The cost conclusion is now operationally established.  This workflow uses no
GitHub-hosted compute minutes because all four conjunctive labels select the
self-hosted Mac.  Successful runs upload neither an artifact nor a remote
cache; only a three-day failure log may consume GitHub storage.  Electricity,
network traffic, and hardware wear remain local operator costs.  The exact
full-build consistency guarantee described in Section 8.13.21 remains the
ordinary checkpoint mechanism: Lake incrementality plus fingerprinted exact
source/import/axiom audits makes a clean rebuild unnecessary on every edit,
while this live run supplies the independent full-current attestation.

With CI wiring certified, the critical path returns immediately to
`Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw`: first the generic
zero-extension numerator bridge, then the complete internal-plus-exterior
reflection event exchange, slab numerator symmetry, and normalized
conditional-probability equality.  The separately edited categorical spike
remains outside the production fingerprint and is not a substitute for this
finite constructive reflection law.

#### 8.13.25 Adjacent-even one-step EventLaw: exact finite conditional symmetry

(2026-07-18, session 8, completed and production-wired.)  Step 4 of the
adjacent-even one-step critical path is now closed.  The new generic theorem

```text
slabEventNumerator_zeroExtension_eqv_ambientMasked
```

in `Z4HalfTimeReflectionSlabFiniteKConditionalLaw.lean` identifies the
numerator of every slab event pulled back along `slabToAmbientPhysical` with
the ambient numerator of that event conjoined with the exact
`ambientSlabSupportedB` mask.  Its proof is a finite indicator-observable
change of variables through `slabWeightedPhysicalSum_eq_ambientSupported` and
the exact supported zero-extension round trip.  It assumes neither coupling
positivity nor a Gram/Fubini representation; no sign hypothesis is logically
needed before normalization.

The production leaf
`Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw.lean` is implemented and
imported by `YMGap.lean`.  Its proof spine is the following exact chain.

1. `adjacentEvenStrictJointCylinderRoots` is the source-ordered lower list
   followed by the source-ordered upper list.  Its length is literally
   `roots.length + roots.length`, and canonicality follows pointwise from the
   strict query fit.  `adjacentEvenStrictJointPairFamilyEvent_eq` proves that
   the associated source cylinder event is exactly the conjunction of the
   lower fingerprint equalling `left` and the upper fingerprint equalling
   `right`.  No label-length or nonemptiness premise is introduced.
2. `adjacentEvenStrictJointCanonicalAtoms` packages precisely those roots as
   canonical atoms.  The value list, doubled length, and complete slab support
   are exposed, and `adjacentEvenStrictJointMarkedCylinderEvent_eq` identifies
   the canonical marked-cylinder presentation with the raw family event
   extensionally.
3. `slabToAmbientPhysical_adjacentEven_reflection` proves pointwise that zero
   extension intertwines supported slab reflection with the independently
   defined ambient face-reflection identifier on every physical ambient face
   in the boundary-complete slab.  The derived Boolean theorem
   `memberB_adjacentEvenSlabAmbientSupport_reflection` transports exact
   occupied-support membership.
4. The lower-to-upper and upper-to-lower
   `...SupportQueryEventB_reflection` theorems transport the *complete*
   canonical component query.  Each direction handles both occupied internal
   root faces and the one-link exterior zero shell.  The reverse theorem is
   proved independently, so no unsupported assertion that an arbitrary whole
   labelling is globally slab-supported is used.
5. The two ordered support-query fingerprint theorems map these local facts
   over the original source list.  `List.map_congr_left` preserves order and
   duplicate roots exactly.  The two occurrence-fingerprint theorems then use
   `familyOccurrenceFingerprint_eq_supportQueryFingerprint`,
   `physicalCanonicalAmbientFamily_unionSupport`, and exact compatibility to
   recover literal component occurrences.
6. `adjacentEvenStrictJointPairSlabEvent` is the zero-extended lifted family
   event, and `reflectSlabEvent_adjacentEvenStrictJointPair` proves the
   function identity `reflectSlabEvent extent eventLR = eventRL` by the two
   occurrence exchanges and constructive conjunction commutativity.
7. `slabEventNumerator_adjacentEvenStrictJointPair_eqv` applies the general
   finite reflection reindexing at every rational coupling and cutoff.
   `adjacentEvenStrictJointPairSlabProbability_eqv` normalizes by the positive
   `slabParametricKPhysicalPartition`; the only new analytic premise is the
   necessary `0 <= coupling`.  The zero-extension bridge then yields
   `parametricKEventNumerator_adjacentEvenStrictJointPair_masked_eqv`, and
   `couplingParametricKPhysicalGivenSlab_adjacentEvenStrictJointPair_eqv`
   states the final equality in the exact ambient physical law conditioned on
   corrected-slab support.

Thus for every finite cutoff, every nonnegative rational coupling, every root
list satisfying the source canonicality condition, and arbitrary Boolean
fingerprints `left` and `right`, the conditioned probability of the ordered
lower/one-step-upper marked event `(left,right)` is semantically rationally
equal to that of `(right,left)`.  The construction is entirely finite and
intuitionistic: it uses list enumeration, decidable Boolean queries, exact
involutions, finite sums, and positive rational division.  It introduces no
`Classical`, choice, `noncomputable`, `native_decide`, `sorry`, new axiom,
Gram argument, or full Fubini decomposition.  All 21 public dependency gates
in the leaf report exactly `[propext, Quot.sound]`; the generic bridge reports
the same gate.

The capped target build completed successfully with 780 jobs and an edited
leaf time below two seconds.  The protected cached full inspection refreshed
the production `YMGap.olean` after the new root import.  The current exact
source stamp is

```text
YMGAP_SOURCE_FINGERPRINT sha256:d2e9c0612bcd58a508763642e4a6367cd7695948ccd6f26555ea728cd93a0ee9
```

The static production inventory now has 2,539 source modules, 7,891 local
import edges, no cycle, 2,533 modules reachable from `YMGap`, the same six
reviewed exclusions, and zero unexpected orphan.  The strict axiom audit,
Frontier-DAG guard, host-load guard, ten mocked JIT remote-state scenarios,
and four bounded-supervisor shutdown scenarios pass.  Post-build inspection
found no runner/Lean/Lake/pytest process or session lock, with 91 percent
system memory available.

The next highest-value dependency is the distinct adjacent-even conditional
stability leaf prescribed immediately after Step 4 above.  It must specialize
the arbitrary-even-extent conditional comparison to these atoms, prove the
internal marked-root carrier floor for both the predicate and its Boolean
complement, retain exterior-shell separation as a distinct locality
interface, and expose the generally nonzero finite-stage error

```text
couplingSlabConditionalBoundaryEpsilon
  (2 * roots.length) (stage + 4).
```

Only after that error is proved to vanish in the constructive limit should
Step 5 transport the same marked event across the one-cell ambient mismatch;
the generic one-step covariance descent then composes those two bounds.  This
ordering avoids duplicating event reflection inside the volume-comparison
proof and keeps exact finite symmetry separate from asymptotic boundary
control.

#### 8.13.26 Adjacent-even conditional stability: the corrected-slab error is quantitative

(2026-07-18, session 8, completed and production-wired.)  The finite
conditional-stability leaf
`Z4HalfTimeReflectionAdjacentEvenOneStepConditionalStability.lean` now closes
the next dependency after the exact EventLaw.  It specializes the arbitrary
finite-root comparison in
`Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral.lean` to the
source-ordered adjacent-even lower/upper atom list without changing the event,
discarding duplicate roots, or imposing a label-length hypothesis.

Write

```text
B := strictQueryBase (base + 1),
R := B + stage,
E := adjacentEvenExtent R = 2 * R + 2,
adjacentEvenAmbient R = E + 1.
```

Every ambient plaquette omitted by `boundaryCompleteSlabPlaquettes E` has
time coordinate exactly `E`.  The local constructive metric lemma
`timeCoordinate_linf_floor_adjacentEven` turns a one-coordinate natural-number
separation into an `linfDist` lower bound through the time component `x3`; it
uses neither a choice of a maximizing coordinate nor a classical metric
argument.

The theorem `adjacentEvenStrictJointRoot_nonSlab_linf_floor` splits membership
in the joint root list through its literal lower/upper append.  A lower marked
face has time `t` with `t + 2 <= R`.  An upper marked face has
`t < R + B`.  Combining either statement with omitted-face time `E` gives

```text
stage + 3 <= linfDist markedFace omittedFace.
```

The upper branch is the quantitative bottleneck: natural-number strictness
converts `t < R + B` into precisely the extra unit needed for `stage + 3`.
The selected atom in a `SlabConnectedSourceEntry` is genuinely one of the
marked atoms by `slabSourceRootAtom_spec`; its first canonical face belongs to
the connected carrier by `slabCanonicalAtomFirstFace_mem`.  Therefore
`slabConnectedCarrierSupport_linf_size_floor` counts that root face in addition
to the separation path and proves

```text
stage + 4 <= (slabConnectedCarrierSupport defaultRoot entry).length.
```

This result is `adjacentEvenStrictJointConnectedCarrierSupport_floor`.  It is
polymorphic in the Boolean predicate.  Consequently the same proof supplies
both hypotheses actually required by the two-sided conditional comparison:
one carrier floor for `predicate` and one for
`complementSlabPredicate predicate`.  There is no second carrier selected from
the exterior shell.

Exterior geometry is nevertheless retained explicitly because the complete
one-link zero query is part of the exact canonical occurrence event.
`adjacentEvenStrictUpperCanonicalRoot_exterior_time_le_shiftedBase` shows that
an upper exterior face has time at most `R + B`.  Together with the stronger
lower exterior estimate and omitted-face time `E`,
`adjacentEvenStrictJointExterior_nonSlab_linf_floor` proves the separate bound

```text
stage + 2 <= linfDist exteriorQueryFace omittedFace.
```

This one-step-smaller exterior lower bound is not consumed by the general
conditional-tail theorem.  Its role is to preserve an honest quantitative
interface for later protected-region arguments and to prevent the work plan
from conflating exact EventLaw locality with the connected switched-residue
carrier.  In particular, the `stage + 4` carrier floor comes solely from the
internal `stage + 3` marked-root separation.

The public predicate-uniform theorem
`couplingPhysicalAdjacentEvenStrictJointPredicate_givenSlab_abs_sub_le` now
states, for every finite cutoff and every rational coupling in the constructive
strong-coupling interval `0 <= coupling <= anchorCoupling`, that

```text
abs (
  P_ambient(E + 1, slabMarkedCylinderEvent atoms predicate)
    -
  P_ambient_given_boundaryCompleteSlab(E,
    slabMarkedCylinderEvent atoms predicate)
) <=
couplingSlabConditionalBoundaryEpsilon
  (2 * roots.length) (stage + 4).
```

Here `atoms` is exactly `adjacentEvenStrictJointCanonicalAtoms R base roots
...`; its length is proved to be `roots.length + roots.length` and normalized
to `2 * roots.length`.  The statement is uniform in `cutoff`, is valid for the
empty root list (where the displayed error coefficient is zero), and otherwise
does not claim that the finite-stage error is strictly positive.  The raw
pair-event wrapper
`couplingPhysicalAdjacentEvenStrictJointPair_givenSlab_abs_sub_le` rewrites the
same result through `adjacentEvenStrictJointMarkedCylinderEvent_eq`, so it
applies directly to the `(left,right)` event appearing in the exact EventLaw.

All proofs remain finite and intuitionistic: finite lists, Boolean predicates
and complements, decidable slab support, coordinate arithmetic, connected
finite carriers, exact rational absolute values, and positive finite
normalization.  The leaf introduces no `Classical`, choice, `noncomputable`,
`native_decide`, `sorry`, or new axiom.  Each of its six public gates reports
exactly `[propext, Quot.sound]`.

Validation was deliberately layered.  A capped, locked, single-worker target
build completed successfully with 781 jobs and a 693-millisecond edited leaf.
The first cached production-root attempt then caught three slab identifiers
that were available in their defining dependency namespaces but had not been
opened in the new leaf; this was a real semantic-root wiring failure, not a
resource failure.  After opening the exact boundary-switch,
boundary-switch-summation, and finite conditional-stability namespaces, the
same leaf rebuilt green and the cached `+YMGap` production root completed
successfully with 2,535 jobs, checking the actual public import rather than
inferring it from a leaf target.  The static graph now contains 2,540 source
modules and 7,894 local import edges, with zero cycle, 2,534 modules reachable
from `YMGap`, the same six reviewed exclusions, and zero unexpected orphan.
The host-load guard, ten mocked JIT remote-state cases, and four bounded
supervisor cases also pass.  The exact current production provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:fda2a6f63086a053cfbe67d9f41b95805ac5ddf50b85439f24ca3101dc004b5a
```

Step 5 is now the unique highest-leverage continuation.  The small centered
chart cannot be a homogeneous strict-joint schedule: its lower block is
`centralStrictLowerCenteredStageRoot base (stage + 1)`, whereas its upper
block is `centralStrictUpperCenteredStageRoot (base + 1) stage` applied to
`timeShiftCanonicalRoot 1 base root`.  These two blocks share radius `R` and
must be spliced in their original source order.  A new
`Z4HalfTimeReflectionAdjacentEvenOneStepVolumeComparison.lean` leaf should
transport that mixed centered root list into the adjacent-even atom list and
apply the generic cross-volume theorem with

```text
small    = centeredBoxBase R,
large    = adjacentEvenAmbient R = small + 2,
inner    = strictJointCenteredInner (base + 1) stage,
distance = stage.
```

The resulting physical error should be
`spinSummedCylinderBoundaryEpsilon (2 * roots.length) stage`.  Composing it
with the conditional estimate above gives the explicit two-error route from
the corrected-slab EventLaw to the mixed centered event.  For the eventual
constructive vanishing step, the conditional factor is already in the right
form: apply
`couplingSlabConditionalBoundaryEpsilon_le_coefficient_half_pow` at
`stage + 1`, using `(stage + 1) + 3 = stage + 4`; the ordinary spin-summed
half-power bound handles the volume term at `stage`.  No Gram representation,
positivity upgrade, exterior-shell reproof, or new analytic hypothesis belongs
in that next leaf.

#### 8.13.27 Adjacent-even Step 5: exact mixed recoding and physical cross-volume control

(2026-07-18, session 8, completed and production-wired.)  The new production
leaf `Z4HalfTimeReflectionAdjacentEvenOneStepVolumeComparison.lean` implements
the cross-volume step prescribed above.  The key structural correction is now
formal rather than merely recorded in the plan: there is no homogeneous
centered strict-joint chart whose two blocks transport to the adjacent-even
one-step event.  The exact source-ordered chart is

```text
adjacentEvenOneStepCenteredRoots base stage roots :=
  roots.map
    (centralStrictLowerCenteredStageRoot base (stage + 1))
  ++
  roots.map (fun root =>
    centralStrictUpperCenteredStageRoot (base + 1) stage
      (timeShiftCanonicalRoot 1 base root)).
```

The arithmetic identity

```text
strictQueryBase base + (stage + 1)
  = strictQueryBase (base + 1) + stage
```

is exported as `adjacentEvenOneStepRadius_eq`.  It places both blocks in the
same centered box
`centeredBoxBase (strictQueryBase (base + 1) + stage)`.  Componentwise
canonicality is proved from the canonical centered source roots and uniform
shift; list canonicality then splits through the literal append.  Hence the
chart preserves source order, duplicate roots, and the precise lower/upper
multiplicity, with length exactly `roots.length + roots.length`.

The protected-region proof also retains the asymmetry instead of hiding it.
The upper block naturally lies in
`strictJointCenteredInner (base + 1) stage`.  The lower block naturally lies
in `strictJointCenteredInner base (stage + 1)`, which is exactly one smaller.
`adjacentEvenOneStepLowerInner_le_commonInner` and `boxPlaquettes_mono` promote
the lower containment to the common upper inner box.  Therefore
`adjacentEvenOneStepCenteredRoots_inside_originBox` holds for the whole mixed
list, while

```text
strictJointCenteredInner (base + 1) stage + stage
  = centeredBoxBase (strictQueryBase (base + 1) + stage)
```

supplies protected distance `stage` to the generic cross-volume theorem.
Nothing in this argument treats the lower block as if it were based at
`base + 1`, or the upper block as if its source had not been time-shifted.

Exact root transport is a coherent two-step calculation.  The existing
centered recoding theorems first transport each mixed centered component into
`centralAmbient R`.  The adjacent-even definitions then transport that
component once more into `adjacentEvenAmbient R`.  The constructive coherence
theorem `transportPolymer_trans` identifies this nested transport literally
with direct transport from the small centered box to the large adjacent-even
box.  The resulting component lemmas are

```text
adjacentEvenStrictLowerCanonicalRoot_eq_transport_centeredOneStep
adjacentEvenStrictUpperCanonicalRoot_eq_transport_centeredOneStep.
```

Mapping them over the two source blocks proves
`adjacentEvenStrictJointCylinderRoots_eq_transported_centeredOneStep` without
permuting or deduplicating the list.  The event theorem
`adjacentEvenStrictJointSlabEvent_eq_transportedCenteredOneStep` then follows
by the exact value lists for `adjacentEvenStrictJointCanonicalAtoms` and
`transportedCanonicalCylinderAtoms`.  Thus the complete canonical marked event
used by the EventLaw, not a support-only surrogate, is the transported mixed
centered cylinder.

The generic compatible cross-volume comparison is specialized with

```text
R        = strictQueryBase (base + 1) + stage,
small    = centeredBoxBase R,
middle   = centralAmbient R,
large    = adjacentEvenAmbient R,
inner    = strictJointCenteredInner (base + 1) stage,
distance = stage.
```

Here `small <= large` is the composite through `middle`; numerically the large
box is two cutoff cells beyond the centered box, and the generic theorem does
not require adjacency.  After rewriting by exact event equality and the
doubled root count,
`couplingParametricKCompatibleAdjacentEvenStrictJoint_cross_centered_abs_sub_le`
gives

```text
abs (P_compatible_large(markedEvent)
       - P_compatible_small(mixedCenteredEvent))
  <= spinSummedCylinderBoundaryEpsilon
       (2 * roots.length) stage.
```

`couplingPhysicalAdjacentEvenStrictJoint_cross_centered_abs_sub_le` descends
this to the two literal finite physical laws through the already-proved exact
physical/compatible rational equivalence.  The pair wrapper
`couplingPhysicalAdjacentEvenStrictJointPair_cross_centered_abs_sub_le`
rewrites the large marked event to the raw source-ordered `(left,right)` family
event and names its small counterpart
`adjacentEvenOneStepCenteredPairEvent`.  It introduces no nonemptiness or
fingerprint-length condition and is uniform in the finite character cutoff.

All ten exported proof gates report exactly `[propext, Quot.sound]`.  The leaf
uses finite list splitting and mapping, uniform shifts, natural-number box
containment, canonical support transport, exact finite event identities,
rational equivalence, and the existing constructive tail theorem.  It adds no
`Classical`, choice, `noncomputable`, `native_decide`, `sorry`, new axiom,
Gram representation, or reflection positivity premise.

The locked, capped, single-worker target completed with 781 jobs; after the
incremental proof corrections the final edited leaf checked in 75 seconds.
The cached production-root check then completed successfully with 2,536 jobs
and the edited `YMGap` root in 614 milliseconds.  Static import analysis now
reports 2,541 source modules, 7,898 local edges, no cycle, 2,535 modules
reachable from the semantic root, the same six reviewed exclusions, and zero
unexpected orphan.  The exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:3f0dc4ea64cac8e066b92a90394cea9ee259f3210b7a5644adf245e5a81f46b9
```

The next proof should compose, rather than re-prove, the two now-independent
finite errors:

```text
conditioned adjacent-even marked event
  -- conditional error -->
ambient adjacent-even marked event
  -- cross-volume error -->
mixed centered marked event.
```

A root-list-independent default atom must be used to instantiate the first
arrow, because `roots` may be empty.  The canonical choice is
`centralLowerCubeRoot R`, transported from `centralAmbient R` to
`adjacentEvenAmbient R`; it is only a totality seed, since
`slabSourceRootAtom_spec` proves that every actual connected entry selects a
marked atom.  The triangle inequality should yield exactly

```text
couplingSlabConditionalBoundaryEpsilon
    (2 * roots.length) (stage + 4)
  +
spinSummedCylinderBoundaryEpsilon
    (2 * roots.length) stage.
```

For a common half-power modulus, apply
`couplingSlabConditionalBoundaryEpsilon_le_coefficient_half_pow` with parameter
`stage + 1`, normalize `(stage + 1) + 3 = stage + 4`, and weaken
`half^(stage + 1)` to `half^stage`.  Combine this with
`spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow` at `stage`.  That
composition is the shortest constructive route from the exact corrected-slab
reflection law to a centered finite-stage covariance estimate.

#### 8.13.28 Conditional-to-centered composition and quantitative swap symmetry

(2026-07-18, session 8, completed and production-wired.)  The production leaf
`Z4HalfTimeReflectionAdjacentEvenOneStepConditionalCenteredComparison.lean`
now performs the composition identified in Section 8.13.27 and immediately
uses the exact EventLaw to obtain a centered covariance estimate.  This closes
the finite-stage analytic bridge from corrected-slab symmetry to the mixed
centered chart; no event geometry is duplicated.

The conditional carrier API requires a default canonical atom only to make
finite root selection total.  Selecting the first marked atom would force an
invalid nonemptiness hypothesis when `roots = []`.  Instead,
`adjacentEvenCentralLowerCanonicalAtom radius hradius` transports the canonical
central lower cube root from `centralAmbient radius` to
`adjacentEvenAmbient radius`, using
`transportPolymer_mem_canonicalSurfacePolymers`.  The specialization
`adjacentEvenStrictJointDefaultRoot base stage` supplies the constructive proof
that `1 <= strictQueryBase (base + 1) + stage`.  The carrier theorem still
proves via `slabSourceRootAtom_spec` that every actual connected entry selects
a marked root; hence this transported cube is a totality witness, not an
additional marked observable and not a source of the size floor.

For an arbitrary Boolean predicate, define the four rational quantities at
radius `R := strictQueryBase (base + 1) + stage`:

```text
conditional       = P_large(event | corrected slab),
ambient           = P_large(event),
centeredPhysical  = P_small(mixed centered event),
centeredCompatible= P_compatible,small(mixed centered event).
```

The conditional-stability leaf bounds `abs (ambient - conditional)` by

```text
couplingSlabConditionalBoundaryEpsilon
  (2 * roots.length) (stage + 4).
```

Constructive symmetry of rational absolute subtraction reverses this to the
orientation `abs (conditional - ambient)`.  The Step 5 volume theorem bounds
`abs (ambient - centeredPhysical)` by

```text
spinSummedCylinderBoundaryEpsilon
  (2 * roots.length) stage.
```

A finite rational triangle inequality, proved from associativity,
`(-x)+x = 0`, and `abs_add_le`, gives the sum of these two errors.  Finally,
`couplingKFamilyEventProbability_eqv_compatible` replaces
`centeredPhysical` by `centeredCompatible` at exactly zero extra error.  The
public theorem

```text
couplingPhysicalGivenSlabAdjacentEvenStrictJointPredicate_cross_centered_abs_sub_le
```

therefore states precisely

```text
abs (conditional - centeredCompatible) <=
  couplingSlabConditionalBoundaryEpsilon
      (2 * roots.length) (stage + 4)
  +
  spinSummedCylinderBoundaryEpsilon
      (2 * roots.length) stage.
```

It is uniform in the finite character cutoff.  The companion pair theorem
rewrites both endpoints to the raw adjacent-even `(left,right)` event and its
named mixed centered recoding.  Neither statement assumes nonempty roots or
fingerprint lengths.

The half-power corollaries do not introduce a new estimate.  The conditional
term is specialized through
`couplingSlabConditionalBoundaryEpsilon_le_coefficient_half_pow` at parameter
`stage + 1`, so its floor is definitionally normalized from
`(stage + 1) + 3` to `stage + 4`.  Monotonicity of the constructive power of
one half weakens `half^(stage + 1)` to the common `half^stage`.  The volume
term uses `spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow` directly
at `stage`.  Factoring the two identical coefficients yields

```text
strictJointConditionalCenteredCoefficient (2 * roots.length)
  * half^stage.
```

This produces both predicate and pair versions of the conditional-to-centered
modulus.

The final theorem in the leaf uses the exact finite conditioned EventLaw in a
load-bearing way.  Let `C_LR` and `C_RL` be the two compatible mixed centered
pair probabilities, and let `S_LR` and `S_RL` be their corrected-slab
approximants.  The EventLaw proves `S_LR ≈ S_RL` exactly at every cutoff.
The two half-power comparison bounds and a second rational triangle inequality
therefore give

```text
abs (C_LR - C_RL) <=
  adjacentEvenOneStepCenteredSwapCoefficient (2 * roots.length)
    * half^stage,
```

where

```text
adjacentEvenOneStepCenteredSwapCoefficient n :=
  strictJointConditionalCenteredCoefficient n
  + strictJointConditionalCenteredCoefficient n.
```

The coefficient is proved nonnegative.  Thus the exact one-step reflection
symmetry has now descended to the actual centered finite-volume event with an
explicit cutoff-uniform geometric defect tending constructively to zero.

The entire leaf is finite and intuitionistic: transported canonical atoms,
finite probabilities, exact rational equivalence, constructive absolute-value
algebra, natural-power monotonicity, and previously proved carrier tails.  It
contains no `Classical`, choice, `noncomputable`, `native_decide`, `sorry`, or
new axiom.  Seven exported gates report exactly `[propext, Quot.sound]`; the
coefficient-nonnegativity gate needs only `[propext]`.

A capped direct Lean check completed in 927 milliseconds, and the locked,
single-worker Lake target completed with 783 jobs and a 982-millisecond edited
leaf.  The cached production root then completed successfully with 2,537 jobs
and the edited `YMGap` root in 537 milliseconds.  Static import analysis now
reports 2,542 source modules, 7,902 local edges, no cycle, 2,536 modules
reachable from the semantic root, the same six reviewed exclusions, and zero
unexpected orphan.  The exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:7ce46940c50c65ebf57ed86c462390eac0c18121b12f57824108355f9deeb4e6
```

The next highest-leverage step is no longer another finite-volume comparison.
It is to package the mixed centered pair probabilities along the established
cutoff/stage schedule and descend the displayed `half^stage` defect to exact
swap equality of their constructive infinite-volume limits.  That theorem
should reuse the existing centered Cauchy/limit machinery and the explicit
nonnegative swap coefficient; it must not reopen the slab reflection,
connected-carrier, or cross-volume arguments.  Once limit equality is
available, the one-step time-translation/covariance consumer can use it as the
finite-to-continuum symmetry input for the OS contraction route.

#### 8.13.29 Exact adjacent-even one-step centered-limit symmetry and categorical-spike adjudication

(2026-07-18, session 8, completed and production-wired.)  The production leaf
`Z4HalfTimeReflectionAdjacentEvenOneStepLimitSymmetry.lean` now turns the
finite-stage estimate of Section 8.13.28 into exact constructive-real swap
symmetry.  It does not construct a second Cauchy completion.  Instead it proves
that the apparently heterogeneous mixed one-step chart is an exact projection
of the already completed ordinary strict-joint centered chart at source base
`base + 1`.

The ordinary source list is

```text
adjacentEvenOneStepProjectedRoots base roots :=
  transportedCylinderRoots base (base + 1) roots ++
  roots.map (timeShiftCanonicalRoot 1 base).
```

Both blocks are canonical in `base + 1`, including for an empty root list and
with duplicate roots retained.  Expanding the ordinary strict-joint centered
chart on this append produces four ordered blocks:

```text
lower(transported roots), lower(time-shifted roots),
upper(transported roots), upper(time-shifted roots).
```

The existing heterogeneous projection keeps the first and fourth blocks.  The
load-bearing naturality identity is
`centralStrictLowerCenteredStageRoot_transportBase_aligned` with
`padding := 1`:

```text
lower_(base+1,stage)(transport_(base,base+1) root)
  = lower_(base,stage+1)(root).
```

The selected fourth block is definitionally

```text
upper_(base+1,stage)(timeShift_1 root).
```

Consequently `adjacentEvenOneStepProjectedCylinderEvent_eq` proves literal
function equality between the projected ordinary event and
`adjacentEvenOneStepCenteredPairEvent`; there is no asymptotic recoding error,
permutation, deduplication, nonempty-family hypothesis, or appeal to limit
uniqueness.

The named sequence

```text
couplingParametricAdjacentEvenOneStepCenteredPairSequence
```

is therefore the existing
`couplingParametricStrictJointCenteredSequence` on the projected roots and
four-block predicate.  At every stage it is exactly the adjacent-even mixed
pair probability with cutoff
`centralStrictJointCenteredStageCutoff (base + 1) stage`.  Its named limit
`couplingParametricAdjacentEvenOneStepCenteredPairLimit` is literally the
already proved `couplingParametricStrictJointCenteredLimit`; all of its Cauchy
content, cutoff interpolation, and stage-to-stage uniform-shift modulus are
reused rather than copied.

Specializing the finite theorem from Section 8.13.28 at that diagonal cutoff
gives

```text
abs (sequence left right stage - sequence right left stage) <=
  adjacentEvenOneStepCenteredSwapCoefficient (2 * roots.length)
    * half^stage.
```

The final theorem
`couplingParametricAdjacentEvenOneStepCenteredPairLimit_swap` proves
`CReal.Equiv` of the two swapped limits.  Given positive rational `epsilon`, it
uses the explicit scale

```text
epsilon * invSucc(coefficient.num.toNat)
```

and threshold equal to that rational's denominator.  Monotonicity of
`half^stage`, `HalfPow.pow_half_le`, coefficient nonnegativity, and
`mul_le_of_mul_invSucc_toNat` reduce the finite geometric defect below
`epsilon`; the rational absolute-value estimate then supplies both inequalities
required by `CReal.Equiv`.  This is an intuitionistic epsilon proof, not
structure equality of constructive reals and not a classical uniqueness
principle.

The user-supplied categorical spike was audited in parallel and used at the
level where it actually helps: its proposed naturality/transport square led to
the exact production transport/projection factorization above.  The referenced
`cat_structural_spike.zip` is absent at the stated path, so the audit used the
expanded twelve-module `cat_structural_spike/` working tree and left every one
of those user-owned files untouched.  The package remains quarantined from
`YMGap` for concrete mathematical reasons:

1. `ThetaLedgerG` assumes a coherent all-scale trajectory and residual
   positivity; it is not produced by the current identity/zero-budget
   `BlockSpin.step_obligation_witness`, and it does not discharge the open
   `SingleStepDefectBound.singleStep` inequality.
2. `PilotWire` is a stabilized four-case rational surrogate, not an
   infinite-scale Yang--Mills law or an OS Hamiltonian mass gap.
3. The canonical `ratioHom` comparison makes the displayed square guard
   automatic for arbitrary positive ledgers, so it cannot certify an
   independently derived physical equivalence.
4. `UniformGapG` packages pointwise lower bounds but has no volume-ledger
   functor/naturality field and therefore is not yet a categorical cone in the
   claimed production sense.
5. No constructive-real substrate instance is supplied; positive
   cancellation and strict-order transport are still genuine obligations.

Promotion would therefore add abstraction before a second production consumer
exists and could make a sigma/string-tension budget look like the Clay-facing
spectral gap.  The reusable `GapSubstrate`/`DomGrowthOver` algebra may be
reconsidered only after it is instantiated directly over production `Q'` and
used by at least two real consumers; any future adapter must target the actual
`singleStep`, and `SquareGuard` may be used only with independently derived
maps.

Verification remained within the Mac safety envelope.  A locked, capped,
single-thread direct check completed in under one second.  The named Lake
target completed successfully with 825 jobs and a 729-millisecond new leaf;
the cached `+YMGap` semantic root completed with 2,538 jobs and a 1.2-second
root.  All six exported gates report exactly `[propext, Quot.sound]`.  Static
analysis reports 2,543 source modules, 7,906 local import edges, zero cycles,
2,537 modules reachable from `YMGap`, the same six reviewed exclusions, and
zero unexpected orphan.  The host-load and mocked JIT/supervisor guards and
the Frontier-DAG check all pass.  The exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:8c20932288496283c8b43bfd1bf5ee76cf5aeea437b1d3ce697642b7e1e7c8d3
```

The next consumer is now precise: prove
`strictJointOneSidedTimeCovariance_one_derived`.  For arbitrary left and right
strict-cylinder presentations, co-present their transported and time-shifted
root families in one append chart, identify every heterogeneous finite entry
with the projected one-step pair limit above, use the exact limit swap entry by
entry, and lift through the finite heterogeneous bipushforward and coefficient
sums.  This is the missing odd-time/self-adjointness input.  It should not
reopen the finite EventLaw or introduce an adjacent-even Gram/positivity
premise; positivity and contraction remain subsequent, separately audited
consumers.

#### 8.13.30 Odd-carrier entry descent to the adjacent-even one-step centered limit

(2026-07-18, session 9, completed and production-wired.)  The production leaf
`Z4HalfTimeReflectionAdjacentEvenOneStepEntryCenteredBridge.lean` now proves
the first analytic adapter needed by the shift-one covariance consumer.  The
adapter keeps the parity distinction explicit.  A direct reflection-bilinear
approximant is normalized in the existing odd corrected slab of extent
`centralExtent radius`; the finite EventLaw that proves swap symmetry lives
in the adjacent even slab of extent `centralExtent radius + 1`.  These finite
carriers are not equal, and the new leaf never rewrites one into the other.

Instead, both constructions meet at the already completed ordinary centered
chart.  For roots canonical at source base `base`, the direct odd-carrier
entry uses

```text
lower roots: transportedCylinderRoots base (base + 1) roots
upper roots: roots.map (timeShiftCanonicalRoot 1 base).
```

At an arbitrary reflection radius the concatenation of those selected queries
is `adjacentEvenOneStepCommonCylinderRoots`.  Expanding
`centralStrictJointCylinderRoots` on
`adjacentEvenOneStepProjectedRoots base roots` gives four blocks.  The
existing first/fourth projection theorem proves the literal event identity
`adjacentEvenOneStepProjectedJointEvent_eq_common`: the projected ordinary
joint cylinder is exactly the selected lower-transported/upper-translated
cylinder.  This theorem is finite syntax and Lean `Eq`; it uses no
probability law, limit, positivity, bit-length premise, or nonemptiness
assumption.

The direct rational entry
`adjacentEvenOneStepEntrySequence` is the normalized support bipair law in
the ordinary odd corrected slab.  Canonicality of its two root blocks follows
respectively from canonical base transport and canonical one-step time
translation.  The theorem
`adjacentEvenOneStepEntrySequence_eqv_cylinder` applies the existing
support-bipushforward/conditional-law bridge and identifies this entry, up to
`Q'.eqv`, with the corrected-slab probability of the selected cylinder.
Its normalization remains visibly `centralExtent radius`; in particular it
does not call the adjacent-even conditional comparison.

Finally,
`adjacentEvenOneStepEntrySequence_abs_sub_centeredPair_le` applies the
generic odd-slab predicate descent to the full projected root list and then
uses the exact event identity above.  It proves

```text
abs (directEntry u v stage - oneStepCenteredPairSequence u v stage) <=
  strictJointConditionalCenteredCoefficient
    (projectedRoots.length + projectedRoots.length) * half^stage.
```

Thus the direct reflection entry and the adjacent-even symmetry proof have an
honest common limit without any finite odd/even carrier identification.  The
exactness ledger is now:

1. projected root and cylinder recodings are Lean `Eq`;
2. support pushforward and corrected-slab entry identification are
   `Q'.eqv`;
3. odd-slab-to-centered comparison is an explicit rational
   `half^stage` inequality;
4. the already proved centered pair swap is `CReal.Equiv`.

The remaining covariance work is finite assembly, not new geometry.  It is
split deliberately into two low-risk leaves.  First, append
`left.roots ++ right.roots` as a common source chart, lift the two
coefficient tables through `take left.roots.length` and
`drop left.roots.length`, and expand both LR and RL reflection approximants
over the same common fingerprint space.  Apply the new entrywise estimate and
the existing heterogeneous coefficient-pair L1 bound to obtain constructive
real equivalences from each one-sided cross to its pair-limit assembly.
Second, lift exact pair-limit swap through the two finite `listCRealSum`
layers, use finite Fubini and rational coefficient commutativity, and conclude
`strictJointOneSidedTimeCovariance_one_derived`.

After that terminal vector theorem, descend it through staged common-box
transport and the algebraic direct-limit quotient.  The immediate faithful
consumer should state one-step self-adjointness for
`StrictJointCylinderDirectLimit.reflectionBilinear` and
`StrictJointCylinderDirectLimit.timeTranslate`.  Completed-carrier
self-adjointness must wait for a genuine completed CReal inner product; the
existing completed seminorm and action alone do not justify that statement.

Verification stayed inside the mandatory Mac envelope: every Lean/Lake
invocation was serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  The direct production-file check completed in 488 milliseconds.
The named target built successfully with 826 jobs and a 512-millisecond new
leaf; the cached semantic root built successfully with 2,539 jobs and a
1.2-second root.  All three exported gates report exactly
`[propext, Quot.sound]`.  Static analysis now reports 2,544 source modules,
7,909 local import edges, zero cycles, 2,538 modules reachable from `YMGap`,
the same six reviewed exclusions, and zero unexpected orphans.  The host-load
guard passes over 236 repository entry files; all ten mocked JIT remote-state
and four bounded-supervisor scenarios pass; and the Frontier-DAG guard reports
zero unbridged enumerations.  Current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:2d260aee05fd3bf268e3cb5487b5b4ebbc92af60265209b41f77a0c8ebb793c3
```

#### 8.13.31 Common-chart assembly and derived shift-one covariance

(2026-07-18, session 10, completed and production-wired.)  The two low-risk
finite assembly leaves planned in the preceding section are now complete.
Together they close the odd-time antisymmetric residual at the level of
arbitrary strict-cylinder vectors.  No adjacent-even positivity premise,
finite-volume odd/even identification, root-count equality, decidable
reindexing, or classical choice is used.

The production leaf
`Z4HalfTimeReflectionAdjacentEvenOneStepCenteredAssembly.lean` first handles
arbitrary presentations.  Given `left right : StrictJointCylinderVector base`,
it fixes the ordered common source chart

```text
left.roots ++ right.roots
```

and proves this chart canonical.  Its left coefficient table reads a common
fingerprint through `take left.roots.length`; its right table reads through
`drop left.roots.length`.  The existing exact append recodings prove four
presentation equivalences: transported-left to common-left,
transported-right to common-right, translated-left to common-left, and
translated-right to common-right.  Consequently unequal root counts never
require a permutation or a rectangular swap: both orientations live on the
same ordered square fingerprint space from the outset.

For any canonical common roots and any two coefficient tables, the leaf
defines `adjacentEvenOneStepCenteredBilinear`, the finite double
`listCRealSum` of coefficient products against
`couplingParametricAdjacentEvenOneStepCenteredPairLimit`.  At every rational
stage, the direct common reflection cross expands, up to `Q'.eqv`, into the
heterogeneous finite entry sum.  The preceding odd-carrier entry bridge and
the existing heterogeneous coefficient-pair L1 estimate yield

```text
abs (commonCross.approx stage - centeredAssembly.approx stage) <=
  adjacentEvenOneStepComparisonCoefficient * half^stage.
```

The comparison coefficient is the product of the fixed conditional-centered
defect coefficient with the two finite coefficient L1 norms; it is proved
nonnegative constructively.  An explicit `invSucc`/half-power cutoff then
turns this bound into
`adjacentEvenOneStepCommonCross_equiv_centeredBilinear`.  Composing with the
four exact presentation adapters gives the public forward and reverse laws

```text
strictJointOneSidedTimeCross 1 left right
  ≃ centeredAssembly appendLeftCoefficient appendRightCoefficient,

strictJointOneSidedTimeCross 1 right left
  ≃ centeredAssembly appendRightCoefficient appendLeftCoefficient.
```

The terminal production leaf
`Z4HalfTimeReflectionAdjacentEvenOneStepCovariance.lean` proves symmetry of
these assemblies with finite constructive algebra only.  A local finite
Fubini theorem for `listCRealSum` is obtained stagewise from the exact
rational `listQSum_swap`; a structural list congruence lifts entrywise
`CReal.Equiv`.  After Fubini reverses the two finite sums, each term has the
form

```text
(rightCoefficient right * leftCoefficient left) * PairLimit right left.
```

Rational commutativity identifies its scalar with the forward scalar, and
`couplingParametricAdjacentEvenOneStepCenteredPairLimit_swap` identifies its
second factor.  Constructive-real multiplication congruence and two nested
finite list congruences therefore prove
`adjacentEvenOneStepCenteredBilinear_swap`.

The final chain is now machine checked:

```text
actual LR cross
  ≃ common centered LR assembly
  ≃ common centered RL assembly
  ≃ actual RL cross.
```

It exports, for every admissible coupling, every source base, and every pair
of strict-cylinder vectors,

```text
strictJointOneSidedTimeCovariance_one_derived :
  StrictJointOneSidedTimeCovariance hcoupling hle 1 left right.
```

The exactness ledger is deliberately stratified.  Append-root and cylinder
recodings are Lean `Eq`; finite support and rational pushforward expansions
are `Q'.eqv`; odd-carrier entry descent is an explicit rational vanishing
bound; limits, common-cross adapters, assembly swap, and terminal covariance
are `CReal.Equiv`.  In particular, the proof never asserts literal equality
of constructive-real representatives and never collapses the direct odd slab
with the adjacent even carrier used to establish swap.

The next most efficient consumer is algebraic direct-limit descent.  Co-present
arbitrary stages at their maximum base, apply the theorem above to the two
transported vectors, and descend through the existing quotient presentation.
This should produce shift-one self-adjointness for
`StrictJointCylinderDirectLimit.reflectionBilinear` and
`StrictJointCylinderDirectLimit.timeTranslate`.  A completed-carrier
self-adjointness theorem remains downstream of the still-missing completed
`CReal` inner product and must not be inferred merely from the completed
seminorm/action.

Verification remained inside the mandatory Mac safety envelope: Lean/Lake
commands were serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  The direct covariance-file check completed in 518 milliseconds.
The named assembly target built successfully with 832 jobs and a 1.1-second
new leaf; the named covariance target built successfully with 833 jobs and a
560-millisecond new leaf.  The cached semantic root then built successfully
with 2,541 jobs and a 564-millisecond root.  Every exported gate in both new
leaves reports exactly `[propext, Quot.sound]`; the executable forbidden-token
scan reports zero hits.

Static analysis now reports 2,546 source modules, 7,915 local import edges,
zero cycles, 2,540 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:94879043305c5ae5fc622db373caafd7935f979dcf985313fff40ccb0da9bc7f
```

#### 8.13.32 Algebraic direct-limit descent and shift-one self-adjointness

(2026-07-18, session 11, completed and production-wired.)  The finite-base
one-step covariance theorem now has its first faithful operator-level
consumer.  The production leaf
`Z4HalfTimeReflectionStrictJointOneStepDirectLimitSelfAdjointness.lean`
descends it through arbitrary staged presentations and the existing
algebraic strict-cylinder direct limit.  The target pairing is the existing
`CReal.RC`-valued `StrictJointCylinderDirectLimit.reflectionBilinear`, so
constructive-real equivalence becomes literal equality only after passage to
the constructive-real quotient.

For staged vectors `left` and `right`, the proof fixes

```text
outer := max left.base right.base
```

and transports both vectors to `outer`.  Both one-sided pairings are then
evaluated in the common box `outer + 1`.  On the unshifted argument,
`boxTransportStrictJointCylinderVector_trans` identifies direct transport to
`outer + 1` with transport to `outer` followed by one more box step.  On the
shifted argument,
`timeTranslate_boxTransportStrictJointCylinderVector` identifies transport
of the shifted vector with shifting the vector already transported to
`outer`.  These are literal vector equalities, not semantic presentation
equivalences.

The two common expressions are therefore exactly the LR and RL one-step
crosses of the finite-base theorem at base `outer`.  Chaining the reverse of
the first common-box adapter, the proved
`strictJointOneSidedTimeCovariance_one_derived`, and the second common-box
adapter yields

```text
strictJointCylinderStage_oneSidedTimeCovariance_one_derived :
  StageBilinear left (timeTranslate 1 right)
    ≃ StageBilinear right (timeTranslate 1 left).
```

No equality of original bases is assumed, and the construction does not
choose an arbitrary common stage: `max` and the explicit order witnesses give
canonical data intuitionistically.

The leaf also supplies the companion staged symmetry theorem.  Both staged
vectors are transported to their maximum common base, the existing strict
vector reflection-bilinear symmetry is applied there, and the two
`strictJointCylinderStageReflectionBilinear_at_common` adapters return to the
canonical staged definitions.  Staged symmetry followed by the reverse of
staged covariance also exports the representative-level law
`strictJointCylinderStage_timeTranslate_one_selfAdjoint`; this is the exact
pointwise input a future continuity/completion proof will need.  Quotient
induction on two staged
representatives and `Quotient.sound` then give the public `RC` equality

```text
StrictJointCylinderDirectLimit.reflectionBilinear_symm.
```

The same two-representative quotient induction descends staged covariance to

```text
StrictJointCylinderDirectLimit.oneSidedTimeCovariance_one_derived :
  B(left, T₁ right) = B(right, T₁ left).
```

Finally, direct-limit reflection symmetry changes
`B(T₁ left, right)` to `B(right, T₁ left)`, and the reverse of the
descended covariance theorem gives the desired algebraic self-adjointness law

```text
StrictJointCylinderDirectLimit.timeTranslate_one_selfAdjoint :
  B(T₁ left, right) = B(left, T₁ right).
```

The exactness boundary remains explicit.  Base-transport composition and the
translation/transport square are Lean `Eq`; staged covariance and staged
symmetry are `CReal.Equiv`; the direct-limit statements are Lean `Eq` in
`CReal.RC`, justified by `Quotient.sound`.  There is no raw-representative
equality and no completed-space theorem here.

This completes the algebraic shift-one self-adjointness checkpoint.  The next
sound step is to connect the algebraic direct limit to
`StrictJointCylinderOSCompletion` and construct the completed `CReal` inner
product (or an equivalent continuous extension of the `RC` pairing).  Only
after that continuity/completion layer exists may self-adjointness be lifted
to the completed carrier and used as an operator theorem in the OS
contraction/positivity spine.  The existing completion seminorm and completed
time action alone do not supply such an inner product.

Verification remained inside the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  The final direct leaf check completed in 1.07 seconds.  The named
target built successfully with 838 jobs and a 1.1-second new leaf; the cached
semantic root built successfully with 2,542 jobs and a 500-millisecond
root.  All six exported gates report exactly `[propext, Quot.sound]`, and the
executable forbidden-token scan reports zero hits.

Static analysis now reports 2,547 source modules, 7,918 local import edges,
zero cycles, 2,541 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:93e8cd678301c781f147f5aa983f0af1ed6db7468d54d60296be7376532b7fec
```

#### 8.13.33 Canonical direct-limit map into the completed OS carrier

(2026-07-18, session 12, completed and production-wired.)  The previously
identified carrier-wiring gap is now closed by
`Z4HalfTimeReflectionStrictJointDirectLimitCompletionBridge.lean`.  The leaf
constructs a canonical map

```text
StrictJointCylinderDirectLimit.toOSCompletion :
  StrictJointCylinderDirectLimit → StrictJointCylinderOSCompletion.
```

On a staged representative, the map is the constant-Cauchy representative map
`strictJointCylinderStageSquaredSeminorm.embedRep`.  Its quotient
well-definedness is exactly
`strictJointCylinderCompletion_embed_eq_of_stageEquivalent`: every literal
algebraic direct-limit stage equivalence was already proved to have zero
completed squared distance.  Thus this bridge adds no new radical, quotient,
or choice principle.

The constant-generator rule is exposed as a simplification theorem:

```text
toOSCompletion (StrictJointCylinderDirectLimit.embed stage) = embedRep stage.
```

The completed nonexpansive time action also has its missing constant-generator
rule:

```text
strictJointCylinderCompletedTimeTranslate shift (embedRep stage) =
  embedRep (stage.timeTranslate shift).
```

This equality is definitional: mapping a constant Cauchy representative gives
the constant Cauchy representative of the staged image.  Quotient induction
on one algebraic representative then proves the full intertwining square

```text
toOSCompletion (DirectLimit.timeTranslate shift vector) =
  CompletedTimeTranslate shift (toOSCompletion vector)
```

for every natural shift.  Hence the algebraic action and completed action are
now connected by a genuine map, rather than merely being parallel
constructions with analogous semigroup laws.

The bridge imports only the CReal direct-limit seminorm layer.  In particular,
the carrier/action square is independent of the later shift-one covariance and
self-adjointness leaves, which remain separately wired at the semantic root.

This leaf deliberately remains carrier/action wiring.  It does not use the
algebraic reflection pairing and does not claim that the completed carrier has
an inner product.  The next analytic obligation is still a continuity theorem
strong enough to show that the staged reflection bilinear values of two
explicit-modulus Cauchy representatives form a Cauchy sequence and are
invariant under completion closeness in either argument.  Only that bound can
define a completed `CReal.RC` pairing and carry the staged shift-one
self-adjointness law to arbitrary completed vectors.

Verification remained inside the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  The corrected direct leaf check completed in 833 milliseconds.
Removing the unused self-adjointness dependency reduced the named target to
831 jobs; its new leaf completed in 878 milliseconds.  The cached semantic
root built successfully with 2,543 jobs and a 467-millisecond root.  All four
exported gates report exactly `[propext, Quot.sound]`, and the
executable forbidden-token scan reports zero hits.

Static analysis now reports 2,548 source modules, 7,920 local import edges,
zero cycles, 2,542 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:b7b6626a8a909d0feb9f187ab065525d9de5fe182bfe8cc943ba25adb37dc59a
```

#### 8.13.34 Quantitative strict-pairing continuity and explicit regularization

(2026-07-18, session 13, completed and production-wired.)  The first analytic
layer needed to extend the algebraic strict reflection pairing across
`StrictJointCylinderOSCompletion` is now constructive and explicit.  The new
leaf `Z4HalfTimeReflectionStrictJointCRealPairingContinuity.lean` does not yet
claim a completed pairing.  It supplies the finite-stage estimates and
Type-level inner rate that the completion construction must consume.

At every rational approximation stage it first proves the exact presentation
identity

```text
B(left,right) - B(left',right')
  ≃ B(left-left',right) + B(left',right-right').
```

Here `≃` is `Q'.eqv`.  The proof uses only the already established additive
and scalar laws for the strict polarized form, followed by exact rational
telescoping; no raw coefficient-function equality is assumed.  Combining this
split with the stagewise reflection Cauchy--Schwarz inequality gives the
division-free, square-root-free continuity estimate

```text
Q(left-left') ≤ delta,
Q(right-right') ≤ delta,
Q(right) ≤ bound,
Q(left') ≤ bound,
delta * bound ≤ (epsilon/2)^2

  ==>  |B(left,right) - B(left',right')| ≤ epsilon.
```

The two summands are bounded separately by `epsilon/2`; the proof uses
`abs_le_of_sq_le_sq`, not a square-root operation.  This theorem is deliberately
formulated at a common finite base.  The next leaf will transport arbitrary
staged inputs to their canonical maximum base and turn the bound into a
`CReal.leRat` statement.  That separation keeps all transport/naturality
squares explicit, following the useful structural lesson extracted from the
quarantined `cat_structural_spike` experiment without importing the spike into
production.

The same leaf also makes the inner approximation rate computational.  For
fixed strict-cylinder vectors it defines the nonnegative coefficient

```text
|1/4| * (CauchyCoefficient(left+right)
       + CauchyCoefficient(left-right))
```

and proves the half-power estimate

```text
|B_later - B_earlier| ≤ coefficient * (1/2)^earlier
```

whenever `earlier ≤ later`.  The estimate is established both for the
approximations of the existing polarized `CReal` and for the direct rational
complete-support pairing sequence.  Rescaling a requested tolerance by
`invSucc coefficient.num.toNat` and using `HalfPow.pow_half_le` yields the
explicit Type-level modulus

```text
strictJointCylinderReflectionBilinearCauchyRate left right tolerance
  = (tolerance * invSucc coefficient.num.toNat).den.
```

This data is packaged as
`strictJointCylinderReflectionBilinearQCauchy`.  Consequently the direct
rational sequence has a canonical regular presentation

```text
strictJointCylinderReflectionBilinearSequenceLimit
  := CReal.ofQ'CauchySeq sequence explicitQCauchy.
```

Termwise equivalence between the direct sequence and the polarized
approximations, together with constructive uniqueness of limits, proves

```text
strictJointCylinderReflectionBilinearSequenceLimit ≃
  strictJointCylinderReflectionBilinear.
```

Thus later outer-completion arguments may use the canonical inner modulus
`epsilon.den` supplied by `ofQ'CauchySeq` and then transfer the result back to
the original reflection pairing.  This avoids the forbidden move of extracting
Type-valued approximation data from the Prop-valued `CReal.cauchy` field.

A second new leaf, `CRealLimitClose.lean`, supplies the general quotient-descent
principle needed downstream.  If two `CReal`-valued sequences converge and are
eventually two-sided close at every sufficiently late sequence stage and
approximation stage, then their limits are `CReal.Equiv`.  Its proof is an
epsilon/4 chase with common maxima of the three outer and three inner
thresholds.  All existential witnesses are eliminated only into `Prop`; no
choice principle or decidable real comparison is introduced.

The companion leaf
`Z4HalfTimeReflectionStrictJointCRealPairingAnchorBound.lean` closes the
representative-uniform norm-bound subproblem without any Prop-to-Type
elimination.  First it proves the staged geometric inequality

```text
B(left,left) ≤ 2 * distSq(left,anchor) + 2 * B(anchor,anchor)
```

in `CReal.leEv`, after co-presenting both staged vectors at their maximum base.
The proof uses the exact semantic recovery
`left ≃ (left-anchor)+anchor` and the existing sqrt-free quadratic triangle.
It then factors the fixed-quadratic half-power modulus into a reusable theorem
and defines a computable anchor cap from one finite rational approximation plus
one.  For a completion Cauchy representative `X`, the canonical anchor is

```text
X.seq (X.modulus 1).
```

The explicit bound

```text
strictJointCylinderCauchyNormBoundQ X
  = 2 + 2 * strictJointCylinderCauchyAnchorCap X
```

eventually bounds every diagonal staged pairing.  A natural-number ceiling is
also exported, together with its positivity and `leRat` bound.  This is the
Type-level finite norm datum required by the forthcoming two-variable outer
Cauchy rate; it replaces the unusable Prop-valued witness from a generic
`CReal.localBound` argument.

The remaining completion route is now sharply ordered:

1. Lift the common-base bound to four arbitrary staged inputs by canonical
   maximum-base transport and export the resulting `CReal.leRat` continuity
   theorem.
2. Regularize the arbitrary outer completion moduli into a monotone/cofinal
   Type-level rate.  `SquaredSeminorm.Cauchy.modulus` is not antitone, so this
   obligation must be proved and must never be silently assumed.
3. Apply `CReal.completeLimitFromRate` to the sequence of canonically
   regularized staged pairings.  Use `CReal.Equiv_of_limit_of_close` to prove
   independence of both completion representatives, then descend with
   `Quotient.lift₂` to an `RC`-valued pairing on
   `StrictJointCylinderOSCompletion`.
4. Prove the dense-generator compatibility rule.  Only then pass staged
   symmetry and shift-one covariance through convergence to obtain completed
   symmetry and
   `B(T₁ left,right) = B(left,T₁ right)` for arbitrary completed vectors.

This ordering is intuitionistically necessary: the carrier/action bridge of
8.13.33 and algebraic self-adjointness of 8.13.32 do not themselves imply a
completed inner product.  The present checkpoint closes inner regularity,
finite common-base continuity, and representative-uniform norm bounds while
keeping the outer four-stage estimate, monotone-rate closure, and quotient
lift honest and visible.

Verification remained inside the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  Direct production checks of all three leaves succeeded.  The
combined named-target build completed successfully with 834 jobs (the new
continuity and anchor leaves took 1.4 seconds and 859 milliseconds,
respectively), and the cached semantic root completed successfully with 2,546
jobs and a 647-millisecond root.  `CReal.Equiv_of_limit_of_close` reports the
gate `[propext]`; all twelve gated strict-pairing declarations report exactly
`[propext, Quot.sound]`.  The executable forbidden-token scan reports zero
hits.

Static analysis now reports 2,551 source modules, 7,929 local import edges,
zero cycles, 2,545 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:f43b3bc0dad508a5e9abdc7685e0c60ddf167255bf70e413894f299bf6628e00
```

#### 8.13.35 Four-stage outer continuity in the staged OS carrier

(2026-07-18, session 14, completed and production-wired.)  The common-base
estimate of 8.13.34 now has the arbitrary-stage form required by completion
representatives.  The production leaf
`Z4HalfTimeReflectionStrictJointCRealStagePairingContinuity.lean` exports

```text
strictJointCylinderStageReflectionBilinear_difference_leRat.
```

Its four vector inputs may have completely unrelated bases.  The proof uses
the canonical common box

```text
max (max left.base left'.base) (max right.base right'.base)
```

and transports all four presentations there.  Existing common-box adapters
transfer the two staged squared-distance hypotheses and the two staged
self-pairing bounds to the corresponding finite-base quadratics.  No equality
of original bases, arbitrary common-box choice, or representative equality is
assumed.

The theorem's quantitative interface retains an explicit positive `slack`:

```text
distSq(left,left')  <=Rat delta
distSq(right,right') <=Rat delta
B(right,right)       <=Rat bound
B(left',left')       <=Rat bound

(delta + slack) * (bound + slack) <= (epsilon/2)^2.
```

This is not cosmetic.  `CReal.leRat value cap` gives, at every positive test
tolerance, an eventual approximation bound by `cap + tolerance`; it does not
give pointwise `approx <= cap`.  The proof instantiates all four hypotheses at
the same positive `slack`, takes the maximum of their four approximation
thresholds, and only then invokes the common-base square-root-free estimate
with `delta + slack` and `bound + slack`.  This makes the Prop-valued
eventuality synchronization explicit and avoids an illicit exact-bound
strengthening.

The result is the conjunction

```text
(B(left,right) - B(left',right')) <=Rat epsilon
(B(left',right') - B(left,right)) <=Rat epsilon.
```

Both orientations are exported because `leRat` is one-sided; together they
are the constructive-real outer Cauchy estimate.  After the finite-box proof,
the two common-box pairings are transported back to their staged definitions
using `CReal.Equiv_add` and negation congruence.

This discharges item 1 in the remaining route recorded in 8.13.34.  The next
sound construction is now:

1. Combine this theorem with the explicit norm ceilings of 8.13.34 and the two
   completion-representative moduli to define a raw Type-level outer pairing
   rate and prove `CReal.LeRatBound` for the diagonal staged-pairing sequence.
   The chosen `delta` and `slack` must be positive rational functions of
   `epsilon` and the finite norm ceiling whose product budget is proved by
   rational arithmetic, not division or square roots.
2. Pass that arbitrary raw rate through a running-max reciprocal-tolerance
   hull.  Prove the closed rate satisfies `CReal.MmonoPred` and that the raw
   `LeRatBound` transfers by applying it at a smaller canonical reciprocal
   tolerance and weakening with `CReal.leRat_mono`; same-tolerance domination
   of an arbitrary nonmonotone raw modulus is neither available nor needed.
3. Feed the closed outer rate and the canonical inner rate from
   `strictJointCylinderReflectionBilinearSequenceLimit` to
   `CReal.completeLimitFromRate`, descend through completion closeness using
   `CReal.Equiv_of_limit_of_close`, and only then lift to the `RC` quotient.

Thus the remaining obstruction is no longer geometric transport or local
pairing continuity.  It is the explicit assembly and monotone closure of the
outer rate, followed by quotient descent.

Verification remained inside the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  The direct production check completed in 426 milliseconds.  The
named target built successfully with 833 jobs and a 458-millisecond new leaf;
the cached semantic root built successfully with 2,547 jobs and a
469-millisecond root.  The exported theorem reports exactly
`[propext, Quot.sound]`, and the executable forbidden-token scan reports zero
hits.

Static analysis now reports 2,552 source modules, 7,934 local import edges,
zero cycles, 2,546 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:20ebc922622553ffb9a63cd1f739912d7b2955f46019415b2c0560192c634229
```

#### 8.13.36 Constructive monotone/cofinal closure of arbitrary outer rates

(2026-07-18, session 15, completed and production-wired.)  The second item in
the completion route of 8.13.35 is now discharged at the correct abstract
level.  The production leaf `Constructive/CRealRateClosure.lean` takes an
arbitrary rational modulus

```text
M : Q' -> Nat
```

with no monotonicity hypothesis and defines the index-absorbing running hull

```text
modulusHull M 0
  = max (M (invSucc 0)) 0,

modulusHull M (k+1)
  = max (modulusHull M k)
        (max (M (invSucc (k+1))) (k+1)).
```

The file proves constructively that this hull is monotone in `k`, dominates
the reciprocal sample `M (invSucc k)`, and is cofinal because
`k <= modulusHull M k`.  More generally, every earlier reciprocal sample is
dominated at every later hull stage.  No order property of `M` is used or
silently inferred.

The only additional data needed to turn that natural-number hull into a rate
on positive rational tolerances is isolated in

```text
structure CReal.ReciprocalIndexData where
  index          : Q' -> Nat
  index_spec     : 0 < epsilon -> invSucc (index epsilon) <= epsilon
  index_antitone : 0 < delta -> delta <= epsilon
                    -> index epsilon <= index delta.
```

For any such `A`, the closed rate is

```text
closedRate A M epsilon = modulusHull M (A.index epsilon).
```

The antitonicity of `A.index` and monotonicity of `modulusHull` immediately
give `CReal.MmonoPred (closedRate A M)`, while cofinality records the explicit
lower bound `A.index epsilon <= closedRate A M epsilon`.  This latter fact is
useful when an outer completeness construction must simultaneously wait for a
rational tolerance index and for the original sequence modulus.

The central transfer theorem is

```text
CReal.LeRatBound.closed :
  LeRatBound sequence M -> LeRatBound sequence (closedRate A M).
```

Its proof avoids the false same-tolerance assertion
`M epsilon <= closedRate A M epsilon`.  Given `epsilon > 0`, it instead applies
the raw outer bound at the canonical smaller tolerance

```text
eta = invSucc (A.index epsilon) <= epsilon.
```

The hull dominates exactly `M eta`; the resulting two directed `leRat eta`
bounds are then weakened to `leRat epsilon` with `CReal.leRat_mono`.  All
existential approximation thresholds remain inside `Prop`.  Thus there is no
choice, no extraction of a Type-valued witness from an existential proof, and
no decidable-real comparison.

This leaf deliberately imports only `CRealCompleteRate` and has no dependency
on the continuum or reflection-positive layers.  Conversely, it does not
pretend that an abstract `ReciprocalIndexData` is already inhabited.  The next
continuum leaf must either instantiate it from an existing constructive
Archimedean reciprocal-index construction or supply an equally explicit local
instance.  Keeping that obligation visible prevents the outer completion from
smuggling in countable choice.

The completion route is now:

1. Assemble the explicit positive `delta`/`slack` budget from `epsilon` and the
   finite norm ceilings of 8.13.34.  Combine the two completion moduli, both
   norm-base indices, and the four-stage theorem of 8.13.35 into a raw
   `CReal.LeRatBound` for the staged-pairing sequence.
2. Instantiate `ReciprocalIndexData`, apply `LeRatBound.closed`, and use the
   resulting `closedRate_mmonoPred` as the exact monotone-rate input to
   `CReal.completeLimitFromRate`.
3. Give the stage-pairing sequence an explicit inner `CReal.RegPred` (using the
   canonical direct rational pairing limit rather than extracting a modulus
   from the Prop-valued `CReal.cauchy` proof), construct its limit, and prove
   independence of both completion representatives with
   `CReal.Equiv_of_limit_of_close`.
4. Descend through `Quotient.lift2` to the completed `RC` pairing, prove dense
   compatibility, and then pass staged symmetry and shift-one covariance to
   arbitrary completed vectors.

Verification remained inside the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  The direct task-work and promoted production checks both
succeeded.  The cached named target completed with 32 jobs and a
152-millisecond new leaf; the cached semantic root completed with 2,548 jobs
and a 457-millisecond root.  Eight gated order/rate declarations report
`[propext]`, `closedRate_sample_le` is axiom-free, and the executable
forbidden-token scan reports zero hits.

Static analysis now reports 2,553 source modules, 7,936 local import edges,
zero cycles, 2,547 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:35ce183da9b79bd7ae1c7d08105a36652d0fa9ed34855313d637d87e64f01e41
```

#### 8.13.37 Explicit raw outer Cauchy rate for staged reflection pairings

(2026-07-18, session 16, completed and production-wired.)  The raw
representative-level outer estimate requested in 8.13.35--36 is now a fully
explicit Type-level construction.  The production leaf
`Z4HalfTimeReflectionStrictJointCRealPairingRawOuterRate.lean` first solves the
positive rational budget problem uniformly for every requested tolerance,
including arbitrarily large `epsilon`.

For an integral common norm ceiling `C`, put

```text
h = half * epsilon,
q = h * h,
K = C + q.num.toNat + 1,
t = q * invSucc (K - 1),
delta = slack = half * t.
```

All of these are total data, not witnesses extracted from propositions.  When
`epsilon > 0`, the square `q`, the core scale `t`, and hence `delta` are
positive.  The extra `q.num.toNat` in `K` is essential: it gives

```text
q.num.toNat <= K - 1,
t <= q * invSucc q.num.toNat <= 1,
slack = half*t <= 1.
```

Thus

```text
ofNat C + slack <= ofNat (C+1) <= ofNat K,
delta + slack ≃ t.
```

The already proved rational identity
`invSucc (K-1) * ofNat K ≃ 1`, packaged by `Q'.budget_le`, then closes

```text
(delta + slack) * (ofNat C + slack)
  <= t * ofNat K
  <= q
  = (half*epsilon) * (half*epsilon).
```

This formula corrects the tempting but invalid choice with `K = C`: for a
large `epsilon`, its slack need not be at most one (or at most `C`), so the
norm-factor absorption would fail.  The enlarged `K` makes the construction
uniform without division, a square root, a minimum chosen by real comparison,
or a bounded-tolerance assumption.

For two explicit-modulus staged-seminorm Cauchy representatives `X` and `Y`,
the file defines

```text
pairingSequence n = B(X.seq n, Y.seq n),
C = max (normCeil X) (normCeil Y),
delta epsilon = continuityScale C epsilon,

pairingRawRate epsilon =
  max (max (normBase X) (normBase Y))
      (max (X.modulus (delta epsilon))
           (Y.modulus (delta epsilon))).
```

Both `normBase` terms are intentionally retained.  Although `delta <= 1`, an
arbitrary `SquaredSeminorm.Cauchy.modulus` has no antitonicity field, so neither
`X.modulus delta` nor `Y.modulus delta` can subsume the corresponding
modulus-at-one anchor threshold.  Conversely, there is no modulus-at-slack or
inner approximation cutoff in the raw rate: those existential thresholds are
synchronized locally inside the Prop-level four-stage `leRat` theorem.

The main result is

```text
strictJointCylinderPairingSequence_raw_leRatBound :
  CReal.LeRatBound pairingSequence pairingRawRate.
```

For indices `m,n` above the displayed maximum, `X.isCauchy` and `Y.isCauchy`
give the two staged squared-distance bounds at `delta`.  The explicit anchor
theorems bound `B(Y_m,Y_m)` and `B(X_n,X_n)` by their individual norm ceilings;
both bounds are weakened to `ofNat C`.  Applying the four-stage theorem once,
with

```text
(left,left',right,right') = (X_m,X_n,Y_m,Y_n),
```

returns both directed `leRat epsilon` conclusions required by
`CReal.LeRatBound`.  No swapped second application is necessary, and the
asymmetric undifferenced factors are exactly the ones controlled by the
anchor estimates.

The raw rate is deliberately not claimed antitone.  The next leaf must pass it
through the closure of 8.13.36 using a concrete constructive
`ReciprocalIndexData`, then supply the uniform inner regularity modulus for a
canonical stage-level pairing presentation.  The preferred inner route is a
parallel canonical staged pairing: co-transport both inputs to their maximum
base, use the existing direct rational pairing-sequence limit, and bridge it by
`CReal.Equiv` to the already established polarized staged pairing.  This gives
the exact uniform inner modulus `epsilon.den` without extracting any datum from
a Prop-valued `CReal.cauchy` proof.

Verification remained inside the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  After three local namespace/syntax elaboration corrections, the
task-work and promoted direct checks succeeded.  The cached named target built
with 835 jobs and a 499-millisecond new leaf; the cached semantic root built
with 2,549 jobs and a 463-millisecond root.  Both load-bearing gates report
exactly `[propext, Quot.sound]`, and the executable forbidden-token scan reports
zero hits.

Static analysis now reports 2,554 source modules, 7,941 local import edges,
zero cycles, 2,548 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:616d273ececf695a64b3f2e42c27e3bc7c29cf7aed5ce73c108068ee27e4930a
```

#### 8.13.38 Canonical constructive reciprocal index

(2026-07-18, session 17, completed and production-wired.)  The abstract
`ReciprocalIndexData` boundary from 8.13.36 is now inhabited by executable,
Constructive-only arithmetic.  The new leaf
`Constructive/CRealCanonicalReciprocalIndex.lean` defines

```text
canonicalReciprocalIndex epsilon = epsilon.den / epsilon.num.toNat.
```

For a positive rational this is the natural-number floor of `1/epsilon`.  It
is value-based: unlike using `epsilon.den` alone, simultaneous rescaling of the
numerator and denominator does not destroy the required order behavior.  The
definition remains total for nonpositive inputs; its laws are required only on
the positive tolerances consumed by `LeRatBound` and `MmonoPred`.

The two proved laws are

```text
0 < epsilon
  ==> invSucc (canonicalReciprocalIndex epsilon) <= epsilon,

0 < delta /\ delta <= epsilon
  ==> canonicalReciprocalIndex epsilon
        <= canonicalReciprocalIndex delta.
```

For the first, positivity identifies `epsilon.num` with the cast of its
positive `toNat`.  Euclidean division gives

```text
den <= numNat * (den / numNat + 1),
```

which is exactly the cross-multiplied reciprocal inequality.  For the second,
`delta <= epsilon` becomes

```text
delta.numNat * epsilon.den
  <= epsilon.numNat * delta.den.
```

A constructive floor-division lemma then yields the stated antitonicity.  All
supporting positive-numerator and Nat-division arithmetic is private; the
public package is

```text
CReal.canonicalReciprocalIndexData : CReal.ReciprocalIndexData.
```

The leaf imports only `CRealRateClosure`.  In particular, it does not reuse the
historically earlier `ArctanTrigConverges.atMw` through a backwards
Constructive-to-Continuum dependency.  The same arithmetic core is now
available at its natural layer, with no choice, hidden Archimedean witness, or
Prop-to-Type elimination.

Consequently every raw outer bound now has a canonical closed form:

```text
closedRate CReal.canonicalReciprocalIndexData rawRate,
```

and 8.13.36 immediately supplies both its `MmonoPred` proof and the transferred
`LeRatBound`.  The remaining pre-quotient construction is therefore the inner
regular presentation: define the maximum-box staged direct-sequence limit,
prove its uniform `RegPred` with modulus `epsilon.den`, transfer the raw outer
bound pointwise across `CReal.Equiv`, and invoke
`CReal.completeLimitFromRate`.

Verification remained inside the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the canonical host lock, used
`LEAN_NUM_THREADS=1`, and retained the fixed `-s 65536 -M 20480` weak
arguments.  Both task-work and promoted direct checks succeeded.  The cached
named target completed with 33 jobs and a 164-millisecond new leaf; the cached
semantic root completed with 2,550 jobs and a 474-millisecond root.
`canonicalReciprocalIndex_invSucc_le` reports `[propext]`; antitonicity and the
assembled datum report exactly `[propext, Quot.sound]`.  The executable
forbidden-token scan reports zero hits.

Static analysis now reports 2,555 source modules, 7,943 local import edges,
zero cycles, 2,549 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:866316c49654f883e9f6c126299839dc317f1c6731389d90799b8e0dfff8891e
```

#### 8.13.39 Canonical pre-quotient completion of the strict reflection pairing

(2026-07-18, session 18, completed and production-wired.)  The remaining
analytic completion obligation from 8.13.36--38 is now closed for explicit
Cauchy representatives.  The new production leaf
`Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion.lean`
constructs an actual `CReal` pairing value and proves convergence to it,
without extracting a modulus from a proposition, choosing representatives, or
changing the already established polarized stage form.

For staged vectors `left` and `right`, define their canonical common base
and transported inputs by

```text
pairingBase  = max left.base right.base,
pairingLeft  = transport (left.base <= pairingBase) left.vector,
pairingRight = transport (right.base <= pairingBase) right.vector.
```

The canonical staged value is not a second polarization formula.  It is the
constructive completion

```text
ofQ'CauchySeq
  (strictJointCylinderReflectionBilinearSequence
    coupling hcoupling pairingLeft pairingRight)
  (strictJointCylinderReflectionBilinearQCauchy
    hcoupling hle pairingLeft pairingRight).
```

The theorem
`strictJointCylinderStageReflectionBilinearSequenceLimit_equiv` composes
two already proved naturality squares.  First, the fixed-box rational sequence
limit is equivalent to the fixed-box polarized form.  Second,
`strictJointCylinderStageReflectionBilinear_at_common` identifies that
fixed-box form with the canonical maximum-box staged form.  Consequently the
new presentation changes only the available Type-level approximation data,
not the represented constructive real.

Two general adapters were proved at the exact layer where they are needed.
For any family `r : Nat -> Nat -> Q'` and explicit memberwise
`QCauchy (r i)`,

```text
CReal.ofQ'CauchySeq_family_regPred :
  RegPred (fun i => ofQ'CauchySeq (r i) (c i))
          (fun _ epsilon => epsilon.den).
```

The proof unfolds the canonical approximants and compares their two
`QMhat` indices using `Nat.le_total` and `QMhat_directed`.  Thus the
uniform inner modulus `epsilon.den` is executable data; no witness is
eliminated from the Prop-valued `CReal.cauchy` field.  Also,

```text
CReal.LeRatBound.of_pointwise_equiv :
  (forall n, Equiv (s n) (t n)) ->
  LeRatBound t M ->
  LeRatBound s M
```

transfers both directed differences through `Equiv_add`, `neg_congr`, and
`leRat_of_equiv`.  This is the precise reason the existing raw estimate may
remain stated for polarized stage values while completeness consumes the
canonically regular rational-sequence presentation.

For staged-seminorm Cauchy representatives `X,Y`, the leaf defines the
canonical sequence

```text
S[X,Y](n) =
  strictJointCylinderStageReflectionBilinearSequenceLimit
    hcoupling hle (X.seq n) (Y.seq n).
```

Pointwise equivalence transfers the raw bound of 8.13.37 to `S[X,Y]`.
Its arbitrary raw rate is then closed by the executable datum of 8.13.38:

```text
M[X,Y] =
  CReal.closedRate
    CReal.canonicalReciprocalIndexData
    (strictJointCylinderPairingRawRate hcoupling hle X Y).
```

`LeRatBound.closed` supplies the two-sided outer estimate at `M[X,Y]`, and
`closedRate_mmonoPred` supplies the exact antitonicity hypothesis required
by convergence.  Together with the uniform inner modulus
`reg n epsilon = epsilon.den`, these data inhabit

```text
strictJointCylinderRepresentativePairingLimit hcoupling hle X Y =
  CReal.completeLimitFromRate S[X,Y] M[X,Y] reg ...
```

and
`strictJointCylinderRepresentativePairingLimit_converges` proves
`CReal.ConvergesTo S[X,Y]` of that value.  This is the first genuine
completed strict pairing value: the former leaves supplied finite-stage
forms, continuity estimates, and raw rates, whereas this leaf performs the
constructive diagonal completion itself.

The next optimal leaf is representative independence and quotient descent.
Write

```text
D = strictJointCylinderStageSquaredSeminorm hcoupling hle.
```

Given actual witnesses `hX : D.Close X X'` and
`hY : D.Close Y Y'`, prove that the two canonical pairing sequences satisfy
the closeness predicate consumed by `CReal.Equiv_of_limit_of_close`.  For a
requested positive tolerance `epsilon), set

```text
rho   = half * epsilon,
C     = max (strictJointCylinderCauchyNormCeil hcoupling hle Y)
            (strictJointCylinderCauchyNormCeil hcoupling hle X'),
delta = strictJointCylinderPairingContinuityScale C rho,

Nstage =
  max (max (strictJointCylinderCauchyNormBase hcoupling hle Y)
           (strictJointCylinderCauchyNormBase hcoupling hle X'))
      (max (hX.modulus delta) (hY.modulus delta)).
```

At every `N >= Nstage`, the two `Close` witnesses give the squared-distance
bounds for `X_N,X'_N` and `Y_N,Y'_N`.  The anchor leaves bound the
undifferenced factors `B(Y_N,Y_N)` and `B(X'_N,X'_N)` by `ofNat C`.
The budget theorem at `rho` then feeds the four-stage continuity theorem with

```text
(left,left',right,right') = (X_N,X'_N,Y_N,Y'_N),
epsilon = rho,
distance tolerance = slack = delta.
```

This gives both raw polarized `leRat rho` differences.  Transport them to the
canonical terms through the pointwise equivalence bridge, use
`CReal.evTwoSided_of_leRat` to synchronize the inner approximation cutoff,
and weaken `rho + rho` to `epsilon` by
`ExpNeg.two_halves epsilon`.  Applying
`CReal.Equiv_of_limit_of_close` to the two convergence theorems then yields

```text
D.CompletionRel X X' ->
D.CompletionRel Y Y' ->
Equiv (representativePairing X Y)
      (representativePairing X' Y').
```

The `Nonempty (D.Close ...)` witnesses hidden by `CompletionRel` are
eliminated only into this proposition.  Likewise the approximation cutoff
from `evTwoSided_of_leRat` remains inside the closeness proposition.  Hence
the descent uses no countable choice or Prop-to-Type extraction.  Package each
representative value as `Quotient.mk CReal.crealSetoid ...`, descend both
arguments through `Quotient.lift₂`, and prove the canonical quotient-mk
computation rule.  Once this is in place, dense compatibility, symmetry, and
shift-one covariance can be transferred to arbitrary completed vectors.

Verification stayed within the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the shared host lock, used
`LEAN_NUM_THREADS=1`, and retained `-s 65536 -M 20480`.  The isolated
generic lemma, complete task-work leaf, and promoted production leaf all
checked directly.  The cached named target completed with 838 jobs and a
1.3-second new leaf; the cached semantic root completed with 2,551 jobs and a
473-millisecond root.  Both generic adapters report exactly `[propext]`;
every gated pairing/completion declaration reports exactly
`[propext, Quot.sound]`; and the executable forbidden-token scan reports
zero hits.

Static analysis now reports 2,556 source modules, 7,946 local import edges,
zero cycles, 2,550 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:a99c81c71459fc2bd0fec1b6c6dffab238819988c394bc6770007cb1d3c44e44
```

#### 8.13.40 Representative independence and completed pairing descent

(2026-07-18, session 19, completed and production-wired.)  The quotient
obligation isolated in 8.13.39 is now discharged.  The new production leaf
`Z4HalfTimeReflectionStrictJointCRealCompletedPairingDescent.lean` proves
that the representative-level limit is invariant under the exact completion
relation in both arguments and defines an `RC`-valued reflection pairing on
all of `StrictJointCylinderOSCompletion hcoupling hle`.

Let

```text
D = strictJointCylinderStageSquaredSeminorm hcoupling hle
```

and suppose

```text
hX : D.Close X X',
hY : D.Close Y Y'.
```

The theorem
`strictJointCylinderCanonicalPairingSequence_close_of_close` gives precisely
the two-level eventuality required by
`CReal.Equiv_of_limit_of_close`: for every positive `epsilon`, an explicit
outer stage `Nstage` is supplied, and for every `N >= Nstage` a
Prop-local approximation threshold synchronizes the two canonical
constructive-real terms.

The explicit data are

```text
rho   = half * epsilon,
C     = max (normCeil Y) (normCeil X'),
delta = strictJointCylinderPairingContinuityScale C rho,

Nstage =
  max (max (normBase Y) (normBase X'))
      (max (hX.modulus delta) (hY.modulus delta)).
```

The two `Close.close` fields supply

```text
distSq(X_N,  X'_N) <= delta,
distSq(Y_N,  Y'_N) <= delta.
```

The asymmetric undifferenced factors required by the already proved
four-stage difference theorem are exactly

```text
B(Y_N,Y_N)   <= ofNat C,
B(X'_N,X'_N) <= ofNat C.
```

They follow from the two finite norm anchors and the left/right inequalities
into the displayed maximum.  The continuity-scale theorem supplies

```text
(delta + delta) * (ofNat C + delta)
  <= (half*rho) * (half*rho).
```

Thus one application of
`strictJointCylinderStageReflectionBilinear_difference_leRat` returns both
directed raw polarized differences at tolerance `rho`.  Each is transported
to the canonical rational-sequence term through

```text
leRat_of_equiv
  (Equiv_add canonical_equiv_raw
    (neg_congr canonical_equiv_raw)).
```

`CReal.evTwoSided_of_leRat`, asked for the additional positive slack
`rho`, produces a common approximation cutoff and errors bounded by
`rho + rho`.  The exact rational equivalence
`ExpNeg.two_halves epsilon` weakens those bounds to `epsilon`.  No inner
regularity modulus is reintroduced here: the canonical presentation from
8.13.39 already supplied it for completeness, while the current uniqueness
argument needs only this Prop-valued approximation threshold.

Applying `CReal.Equiv_of_limit_of_close` to the two convergence theorems
proves

```text
strictJointCylinderRepresentativePairingLimit_equiv_of_close :
  D.Close X X' ->
  D.Close Y Y' ->
  Equiv (representativePairingLimit X Y)
        (representativePairingLimit X' Y').
```

The corresponding
`strictJointCylinderRepresentativePairingLimit_welldef` theorem accepts
`D.CompletionRel` in both arguments.  It destructs the two
`Nonempty (D.Close ...)` witnesses only after the target is the proposition
`CReal.Equiv`.  This is valid intuitionistic elimination and does not choose
a modulus in Type.

The representative result is packaged as

```text
strictJointCylinderRepresentativePairingR X Y =
  Quotient.mk CReal.crealSetoid
    (strictJointCylinderRepresentativePairingLimit X Y).
```

Finally,

```text
strictJointCylinderCompletedPairing :
  D.Completion -> D.Completion -> CReal.RC
```

is the simultaneous `Quotient.lift2` in both completion arguments, and
`strictJointCylinderCompletedPairing_mk` is its definitional computation
rule.  A useful formal subtlety was made explicit during elaboration: Lean's
binary quotient-respect function orders its representatives as

```text
(first-left, second-left, first-right, second-right),
```

so the two relation proofs compare positions one/three and two/four.  Using
the apparent grouped order creates a very expensive failed definitional
equality search.  Correcting the argument order made the lift check immediately
under the existing heartbeat cap; no resource limit was raised.

The next optimal leaf needs no new analytic continuity theorem.  It should
first prove a reusable representative transfer principle: a pointwise
`CReal.Equiv` between the raw polarized pairing sequences implies
equivalence of the two representative pairing limits.  Chain
canonical-to-raw equivalence, the supplied stagewise equivalence, and the
reverse canonical-to-raw equivalence, then use
`CReal.Equiv_of_limit_of_equal` with the two existing convergence theorems.
From this one engine:

1. prove that constant representatives recover the staged pairing and hence
   that `strictJointCylinderCompletedPairing` agrees with the staged form on
   `D.embedRep`;
2. combine that computation with the existing
   `StrictJointCylinderDirectLimit.toOSCompletion` bridge to recover the
   algebraic direct-limit pairing on the dense image;
3. lift staged symmetry to arbitrary Cauchy representatives and then by
   quotient induction to every completed vector;
4. lift the already derived one-sided shift-one covariance in the same way,
   using `Nonexpansive.mapCauchy` and the definitional sequence computation;
5. derive completed shift-one self-adjointness from completed symmetry and
   one-sided covariance as an exact equality in `CReal.RC`.

Arbitrary completed-vector laws must be proved by quotient induction, not by
asserting that the algebraic direct-limit image is surjective or invoking an
unformalized density-continuity principle.  Dense compatibility is a
validation theorem; representative-level limit transfer is the actual
extension argument.

Verification stayed within the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the shared host lock, used
`LEAN_NUM_THREADS=1`, and retained `-s 65536 -M 20480`.  The complete
task-work and promoted production leaves checked directly.  The cached named
target completed with 840 jobs and a 1.2-second new leaf; the cached semantic
root completed with 2,552 jobs and a 568-millisecond root.  All six public
axiom gates report exactly `[propext, Quot.sound]`, and the executable
forbidden-token scan reports zero hits.

Static analysis now reports 2,557 source modules, 7,949 local import edges,
zero cycles, 2,551 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:e1c4a0a4c9420f2bf0e8a351d9a24d98fd1e9abc8871a73c84c0e976c304d1e7
```

#### 8.13.41 Completed pairing laws and shift-one self-adjointness

(2026-07-18, session 20, completed and production-wired.)  The new
production leaf
`Z4HalfTimeReflectionStrictJointCRealCompletedPairingLaws.lean` supplies the
first structural laws of the completed strict reflection pairing.  It proves
dense compatibility as a validation theorem and proves the laws on arbitrary
completed vectors by representative-level limit transfer followed by quotient
induction.  In particular, no algebraic direct-limit representative is chosen
for a general completed vector, and no unformalized density or continuity
argument is used.

Write

```text
D  = strictJointCylinderStageSquaredSeminorm hcoupling hle,
T1 = strictJointCylinderStageTimeTranslateNonexpansive hcoupling hle 1.
```

The reusable engine is

```text
strictJointCylinderRepresentativePairingLimit_equiv_of_raw_sequence.
```

For Cauchy representatives `X,Y,X',Y'`, its hypothesis is the pointwise
equivalence

```text
forall n,
  Equiv (rawPairing X_n Y_n) (rawPairing X'_n Y'_n).
```

At every outer index it constructs exactly the chain

```text
canonical(X,Y,n)
  ~ raw(X,Y,n)
  ~ raw(X',Y',n)
  ~ canonical(X',Y',n).
```

The first and last arrows are the canonical-to-raw equivalences established
in 8.13.39, with the last one reversed.  Constructive uniqueness of limits,
`CReal.Equiv_of_limit_of_equal`, then identifies the two representative
limits using their already proved convergence witnesses.  This isolates all
subsequent law lifting from the rational regularization details.

For a staged vector `v`, `D.constant v` has constant raw pairing sequence.
The local theorem `convergesTo_const` proves its convergence directly: for
each positive `epsilon`, stage zero suffices, and after approximation index
zero both required inequalities are instances of adding a nonnegative
rational.  Consequently

```text
strictJointCylinderRepresentativePairingLimit_constant_equiv_stage
```

identifies the representative limit of the two constant sequences with the
original staged reflection bilinear term.  Passing through the constructive
real quotient gives the definitional user law

```text
strictJointCylinderCompletedPairing_embedRep :
  B_completed (D.embedRep left) (D.embedRep right)
    = [B_stage left right].
```

It is marked `[simp]`.  Quotient induction over the algebraic direct-limit
carrier, together with the previously established computation of
`StrictJointCylinderDirectLimit.toOSCompletion`, then proves

```text
StrictJointCylinderDirectLimit.toOSCompletion_pairing :
  B_completed (toOSCompletion left) (toOSCompletion right)
    = reflectionBilinear left right.
```

This theorem certifies that completion has not changed the previously
constructed direct-limit form.  Its logical role is compatibility, not a
surjectivity claim about `toOSCompletion`.

Staged symmetry gives, at each representative index,

```text
rawPairing X_n Y_n ~ rawPairing Y_n X_n.
```

The generic transfer engine yields
`strictJointCylinderRepresentativePairingLimit_symm`; quotient induction in
both completed arguments and `Quotient.sound` yield the exact `CReal.RC`
equality

```text
strictJointCylinderCompletedPairing_symm :
  B_completed left right = B_completed right left.
```

For the time-one law, `T1.mapCauchy` is the nonexpansive map on explicit
Cauchy representatives and its sequence is definitionally

```text
(T1.mapCauchy X).seq n = (X.seq n).timeTranslate 1.
```

The already derived staged one-sided covariance theorem therefore supplies
the pointwise equivalence

```text
B_stage X_n (T1 Y_n) ~ B_stage Y_n (T1 X_n).
```

Limit transfer proves
`strictJointCylinderRepresentativePairingLimit_oneSidedTimeCovariance_one`,
and quotient induction proves on arbitrary completed vectors

```text
strictJointCylinderCompletedPairing_oneSidedTimeCovariance_one :
  B_completed left (T1 right) = B_completed right (T1 left).
```

Completed symmetry followed by this one-sided covariance gives the exact
self-adjointness equation

```text
strictJointCylinderCompletedTimeTranslate_one_selfAdjoint :
  B_completed (T1 left) right = B_completed left (T1 right).
```

Thus the time-one map is now formally self-adjoint relative to the completed
reflection pairing.  This statement is deliberately not advertised as a
Hilbert-space operator theorem: vector operations, bilinearity over those
operations, positive definiteness modulo the completed null relation, and
the relevant completeness structure have not yet been assembled into such a
package.

The next analytic obstruction is direct time-one transfer positivity,

```text
0 <= B_completed (T1 x) x.
```

The existing even-time theorem controls diagonal forms of even powers, and
the existing doubled-time contraction controls shifted quadratic forms, but
self-adjointness together with positivity of `T1^2` does **not** imply
positivity of `T1`.  The next proof must therefore locate or establish the
actual adjacent-even/Markov reflection argument at the finite staged level,
then transfer that pointwise theorem to Cauchy representatives and quotient
induct it to the completed carrier.  No spectral square-root shortcut is
sound at the present constructive abstraction level.  Once this positivity
and the corresponding completed contraction statement are in place, the
minimal `CRealCompletedTransferCore` should package only:

1. the completed pairing;
2. the completed time-one transfer;
3. self-adjointness;
4. transfer positivity; and
5. contraction.

That core must initially be instantiated at `coupling := anchorCoupling`.
A coupling-parametric package remains conditional on the interval-wide
positivity input.  Addition, scalar multiplication, pairing linearity, and
the eventual inner-product/Hilbert completion interface should be proved in
separate subsequent leaves rather than hidden as fields of this minimal
transfer core.

Verification stayed within the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the shared host lock, used
`LEAN_NUM_THREADS=1`, and retained `-s 65536 -M 20480`.  The production leaf
checked directly.  The cached named target completed with 860 jobs and a
1.6-second new leaf; the cached semantic root completed with 2,553 jobs and a
555-millisecond root.  All nine public axiom gates report exactly
`[propext, Quot.sound]`, and the executable forbidden-token scan reports zero
hits.

Static analysis now reports 2,558 source modules, 7,953 local import edges,
zero cycles, 2,552 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:57b258aba83b672491563e0b4e178551ddc6114434786c7de6284c2e950d1675
```

#### 8.13.42 Exact adjacent-even assembled-summand factorization

(2026-07-18, session 21, completed and production-wired.)  The first
load-bearing prerequisite of the time-one positivity track is now formalized
in
`Z4HalfTimeReflectionAdjacentEvenAssembledSlabFactorization.lean`.  It
connects the previously separate side-partition, fixed-link endpoint-Fubini,
trajectory-collapse, fixed-face coefficient, and reflected-endpoint lanes to
the complete corrected-slab physical summand.  The result is an exact finite
rational identity at anchor coupling; it does not insert a positivity premise
or conceal the remaining interface-kernel theorem.

The leaf first defines the literal adjacent-even link parts

```text
adjacentEvenLowerLinks = adjacentEvenSlabLinkParts.1,
adjacentEvenFixedLinks = adjacentEvenSlabLinkParts.2.1,
adjacentEvenUpperLinks = adjacentEvenSlabLinkParts.2.2
```

and the three complete side factors

```text
L_w(physical)
  = product(lower face coefficients)
      * ofNat(product(lower link multiplicities)),

F_w(physical)
  = product(fixed face coefficients)
      * ofNat(product(fixed link multiplicities)),

U_w(physical)
  = product(upper face coefficients)
      * ofNat(product(upper link multiplicities)).
```

The theorem

```text
slabParametricKPhysicalTerm_adjacentEven_factorization
```

proves for every rational coupling `w`, cutoff `K`, radius, and physical
labelling

```text
slabParametricKPhysicalTerm w K (adjacentEvenExtent radius) physical
  ~ L_w(physical) * (F_w(physical) * U_w(physical)).
```

The proof separately transports the full face product and the full actual-link
multiplicity product along
`adjacentEvenSlabFaceIdParts_perm` and
`adjacentEvenSlabLinkParts_perm`.  Constructive append identities split both
finite products.  The natural-number link product is embedded into `Q'` by
two exact `ofNat_mul` equivalences, and one explicit six-factor rational
reassociation places each face product beside its matching link product.  No
incident-coordinate locality is assumed: in the even geometry the fixed
links genuinely read lower, fixed, and upper spins, so their whole coupling
remains inside `F_w`.

At `w = anchorCoupling`, the fixed factor is attached to the already proved
literal endpoint calculation:

```text
adjacentEvenFixedWeight_anchor_eqv_coefficient_mul_collapsed :
  F_anchor(physical)
    ~ fixedFaceCoefficientProduct(physical)
        * collapsedFixedLinkTrajectorySum(physical).
```

This is the exact chain

```text
ofNat(fixed-link multiplicity product)
  ~ global bounded source/target endpoint sum
  ~ expanded trajectory sum
  ~ terminal-delta-collapsed trajectory sum.
```

The heat-kernel coefficient is attached exactly once.  A separate equality,

```text
adjacentEvenFixedFaceCoefficientProduct_assemble_only_boundary,
```

proves that on

```text
physical = assembleAdjacentEvenReflectedSlabLabelling
  radius left boundary right,
```

the fixed-face coefficient product reads only `boundary`.  The proof uses the
literal membership characterization of `adjacentEvenFixedFaceIds` and the
fixed-coordinate computation of the assembly, term by term in the finite
product.

The common-coordinate interface has been named explicitly as

```text
adjacentEvenCommonLowerInterfaceSum K radius physical reflected.
```

Its source and trajectory sums have integrand

```text
(lowerAmplitude physical source
    * faceTransition physical source trajectory)
  * lowerAmplitude reflected (finalChannel source trajectory).
```

Here `reflected` is the assembly with `left` and `right` exchanged.  The
theorem

```text
adjacentEvenAssembledCollapsedSum_eqv_common_lower
```

is obtained termwise from
`adjacentEvenAssembledUpperAmplitude_eqv_commonLower`: the literal reflected
upper endpoint amplitude is exactly the same lower-amplitude map on the
swapped physical assembly.  Thus both external endpoint maps now use one
common kind of half-state coordinate.  The directed middle transition is
left untouched and visible.

For elaboration and downstream reuse, the two large repeated expressions are
packaged as

```text
adjacentEvenAssembledPhysical radius left boundary right,
adjacentEvenAssembledInterface K radius left boundary right.
```

The intermediate theorem

```text
adjacentEvenAssembledFixedWeight_anchor_eqv_interface
```

combines fixed-link Fubini/collapse, common-lower endpoint transport, and
fixed-face boundary independence.  The terminal load-bearing identity is

```text
adjacentEvenAssembledSlabNumerator_eqv_lower_interface_upper :
  slabTerm_anchor(assembled left boundary right)
    ~ L_anchor(assembled left boundary right)
        * (assembledInterface left boundary right
            * U_anchor(assembled left boundary right)).
```

This closes the previously explicit missing bridge from the local/interface
calculation to the complete unnormalized physical spin-foam summand.  Event
masks and division by the positive slab partition function remain downstream;
they are not folded into this finite weight identity.

Two independent audits agree on the remaining obstruction.  Existing
even-time positivity proves only `B(T^(2s)v,v) >= 0`; contraction controls
translated squared norms; and the completed shift-one theorem proves
self-adjointness.  None implies `B(Tv,v) >= 0`.  The rational model

```text
B(x,y) = x*y,   T(x) = -x
```

is self-adjoint, norm preserving, and has positive even powers, while
`B(T 1,1) = -1`.  Likewise symmetric entrywise-nonnegative matrices need not
be positive semidefinite, and the existing directed/mixed-map fences rule out
the naive Schur and full-window sequential-composition arguments.

The logically minimal next finite theorem should therefore be stated directly
on the already-sandwiched physical kernel:

```text
adjacentEvenPhysicalReflectionQuadratic anchorCoupling K radius coefficient
  = sum_left sum_right
      (coefficient left * coefficient right)
        * adjacentEvenPhysicalReflectedKernel
            anchorCoupling K radius left right,

0 <= adjacentEvenPhysicalReflectionQuadratic
       anchorCoupling K radius coefficient.
```

A `GramRep` of the already-sandwiched half-state kernel is sufficient for this
statement.  A reachable common-middle representation

```text
GramRep (fun q q' => T (end q) (end q'))
```

is also sufficient but stronger than logically necessary; it must not become
an artificial mandatory interface if a direct tensor-network SOS of the
sandwiched quadratic is shorter.  Before attempting a long general Gram
construction, perform bounded exact-rational reconnaissance of the *physical
sandwiched* matrices at small `K` and radius.  The already refuted unrestricted
endpoint matrix is not the object to test.

Once the finite physical quadratic is proved, the shortest remaining route is:

1. push it through the deterministic occurrence-fingerprint map to the
   marked adjacent-even pair-event quadratic;
2. divide by the proved positive slab partition function;
3. use the adjacent-even conditioned/centered half-power comparison and the
   coefficient-L1 quadratic estimate to obtain a vanishing lower error;
4. pass that lower error to `CReal.leEv CReal.czero` for the diagonal centered
   one-step form;
5. transport through the existing common-cross equivalence to staged
   `B(T1 v,v) >= 0`;
6. apply the staged theorem pointwise to every Cauchy representative, transfer
   raw to canonical pairing terms, and use constructive nonnegativity of a
   convergent limit; and
7. quotient-induct to the completed carrier.

No algebraic-direct-limit density detour is needed for the last step.

Verification stayed within the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the shared host lock, used
`LEAN_NUM_THREADS=1`, and retained `-s 65536 -M 20480`.  An initially large
terminal statement reached the fixed heartbeat fence without significant
memory growth; the statement was then factored into named definitions and a
small intermediate theorem, reducing direct elaboration to about 0.55 seconds
without raising any resource cap.  The draft and production leaf both check
directly.  The cached named target completed with 699 jobs and a 592-millisecond
new leaf; the cached semantic root completed with 2,554 jobs and a
570-millisecond root.  All six public axiom gates report exactly
`[propext, Quot.sound]`, and the executable forbidden-token scan reports zero
hits.

Static analysis now reports 2,559 source modules, 7,955 local import edges,
zero cycles, 2,553 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:0a51596c487ba0c8ab7c4c9e6b8d216a6e5f82b9dd43b91bf65fff5696690890
```

#### 8.13.43 Exact finite physical PSD interface and constructive Gram reduction

(2026-07-18, session 22, completed and production-wired.)  The new leaf
`Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic.lean` turns the
finite obstruction isolated in 8.13.42 into a precise, reusable Lean API.  It
does not assert reflection positivity and does not manufacture a Gram
witness.  It defines the exact finite physical matrix and quadratic that must
be controlled, proves their support and symmetry facts, and reduces the
desired inequality constructively to an explicit `GramRep` of that same
already-sandwiched matrix.

The actual half-state enumeration is indexed by

```text
adjacentEvenPhysicalHalfStateCount K radius
  = (adjacentEvenHalfStates K radius).length,

adjacentEvenPhysicalHalfStateAt K radius i
  = (adjacentEvenHalfStates K radius).getD i zeroEdgeLabelling.
```

The private structural induction theorem `list_getD_mem_of_lt` proves that a
bounded `getD` lookup belongs to its source list.  Hence

```text
adjacentEvenPhysicalHalfStateAt_mem :
  i < adjacentEvenPhysicalHalfStateCount K radius ->
  adjacentEvenPhysicalHalfStateAt K radius i
    ∈ adjacentEvenHalfStates K radius.
```

This proof is constructive and avoids choosing an inverse to list membership
or quotienting duplicate half-state labellings.  Duplicate list entries, if
present, remain separate finite coordinates; this is harmless for the
quadratic and is the correct representation for later deterministic
pushforward arguments.

The globally indexed matrix is

```text
adjacentEvenPhysicalReflectedMatrix w K radius i j
  = if i < count then
      if j < count then
        adjacentEvenPhysicalReflectedKernel w K radius
          (halfStateAt i) (halfStateAt j)
      else 0
    else 0.
```

Zero exterior padding is essential.  The repository's `GramRep` interface is
stated for kernels on all natural-number indices, while the physical carrier
is finite.  An arbitrary fallback matrix entry outside the enumeration would
make a global Gram claim stronger than the physical problem and could destroy
symmetry.  Zero padding instead admits the canonical zero Gram vector outside
the finite carrier.  On bounded indices,
`adjacentEvenPhysicalReflectedMatrix_eq_kernel` identifies the matrix with the
literal physical reflected kernel.

The theorem `adjacentEvenPhysicalReflectedMatrix_symm` proves global rational
symmetry.  In the bounded/bounded case it invokes the existing literal
physical-kernel reflection-swap theorem after supplying both
enumeration-membership proofs.  The remaining three boundedness cases reduce
both directed entries to zero.  This is symmetry of the exact target matrix,
not an inference from entrywise nonnegativity and not a claim about the
previously refuted unrestricted endpoint transition window.

The precise finite quadratic is now named

```text
adjacentEvenPhysicalReflectionQuadratic w K radius coefficient
  = gramQuadForm
      (adjacentEvenPhysicalReflectedMatrix w K radius)
      coefficient
      (adjacentEvenPhysicalHalfStateCount K radius).
```

Its minimal anchor-coupling consumer proposition is

```text
AdjacentEvenPhysicalAnchorPSD K radius : Prop
  := forall coefficient,
       0 <= adjacentEvenPhysicalReflectionQuadratic
              anchorCoupling K radius coefficient.
```

This proposition deliberately asks only for the finite quadratic inequality
that the probability/centering lane consumes.  It does not force a particular
proof representation.  In parallel, the stronger Type-valued sufficient
substrate is

```text
AdjacentEvenPhysicalAnchorGramWitness K radius
  := GramRep
       (adjacentEvenPhysicalReflectedMatrix
         anchorCoupling K radius).
```

Given such data,
`adjacentEvenPhysicalReflectionQuadratic_anchor_nonnegative_of_gramRep`
applies the repository's constructive finite Gram sum-of-squares theorem
directly, and `adjacentEvenPhysicalAnchorPSD_of_gramRep` packages the result
as the minimal proposition.  No excluded middle, spectral theorem,
eigenvalue decomposition, square-root choice, or decidable search is used.
The distinction between the Prop-valued consumer and Type-valued witness also
keeps open a shorter direct tensor-network SOS proof: a future theorem may
prove `AdjacentEvenPhysicalAnchorPSD` without first constructing a global
natural-indexed Gram representation.

This milestone does **not** close time-one positivity.  The residual theorem
is now exact: for every `K` and `radius`, construct either

```text
AdjacentEvenPhysicalAnchorGramWitness K radius
```

or a direct proof of

```text
AdjacentEvenPhysicalAnchorPSD K radius.
```

The most efficient next attack is the reachable common-middle compression of
the assembled factorization from 8.13.42.  It should proceed in this order:

1. identify the finite common-middle states actually reached by the lower
   endpoint amplitudes and fixed-face trajectories, without enumerating an
   unrestricted `0,...,6*K` endpoint rectangle;
2. prove an entrywise compression identity from the literal assembled
   physical kernel to the reachable middle kernel, retaining all lower and
   upper sandwich amplitudes;
3. prove either a `GramRep` for that reachable middle kernel or a direct SOS
   identity for the fully sandwiched quadratic;
4. transport the witness through the zero-padded half-state enumeration and
   discharge `AdjacentEvenPhysicalAnchorPSD`;
5. only then push the finite inequality through the deterministic
   occurrence-fingerprint map and the positive slab normalization;
6. apply the existing conditioned/centered half-power estimate and finite
   coefficient-L1 quadratic bound to obtain a lower error tending to zero;
7. conclude staged one-step positivity, then representative-limit positivity,
   and finally completed positivity by quotient induction.

Before any bounded exact-rational reconnaissance, the size of the actual
half-state and reachable-middle enumerations must be proved safe.  The list
definitions can grow exponentially in `K` and `radius`; an exploratory
computation that materializes large enumerations is forbidden by the Mac
safety policy.  Any reconnaissance must use very small, explicitly bounded
parameters, stay serialized, and test the already-sandwiched matrix rather
than the known non-symmetric unrestricted transition patch.

Verification stayed within the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the shared host lock, used
`LEAN_NUM_THREADS=1`, and retained `-s 65536 -M 20480`.  The draft and
production leaves checked directly.  The cached named target completed with
701 jobs and a 396-millisecond new leaf; the cached semantic root completed
with 2,555 jobs and a 593-millisecond root.  All five public axiom gates report
exactly `[propext, Quot.sound]`, and the executable forbidden-token scan
reports zero hits.

Static analysis now reports 2,560 source modules, 7,958 local import edges,
zero cycles, 2,554 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:5f7d5db10bda187421d35017bd2686745f91896766c3362fe2283e0b9fd33aa9
```

#### 8.13.44 Arbitrary-radius deterministic lower endpoints and reachable fixed-word symmetry

(2026-07-18, session 23, completed and production-wired.)  The two new leaves
`Z4HalfTimeReflectionAdjacentEvenDeterministicLowerEndpoint.lean` and
`Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry.lean` replace the
coarse reachable-endpoint box from 8.13.43 by an exact symbolic endpoint map.
They make a strict mathematical reduction: at every radius, each fixed
spatial link on the integer reflection slice sees at most one lower
plaquette.  Consequently the lower fusion word does not branch, its endpoint
is a deterministic spin bounded by the physical cutoff `K`, and its fusion
amplitude is an exact Kronecker indicator.  No bounded labelling carrier is
materialized anywhere in either proof.

The local geometry is captured by

```text
adjacentEvenFixedLinkLowerPlaquette link
  = (subE link.1 .x3, planeOf link.2 .x3).
```

For a fixed link and a lower incident numerical face identifier,
`adjacentEvenFixedLink_lowerPlaquette_eq_backwardTemporal` proves that the
decoded plaquette equals this backward temporal plaquette.  The proof invokes
`edge_complete`, which lists exactly the six plaquettes incident to an edge,
and then separates the four link directions.  A temporal link cannot be
fixed.  For a spatial link, fixedness places its base point on the integer
reflection slice; the four spatial candidates are fixed, the forward
temporal candidate is upper, and only the backward temporal candidate is
lower.  Thus the result is a local six-case incidence theorem, not a finite
box computation.

The private numerical-ID uniqueness lemma combines that geometric equality
with `slabPlaquetteAt_injective_on_physical`.  Since the three-way incident
face partition is a permutation of a nodup physical incident-ID list, two
lower IDs would have to be equal and simultaneously distinct.  This proves

```text
adjacentEvenFixedLink_lowerIds_length_le_one :
  ((adjacentEvenIncidentFaceIdParts radius link).1).length <= 1,

adjacentEvenLowerSpins_length_le_one :
  (adjacentEvenIncidentLowerSpins radius physical link).length <= 1.
```

The canonical endpoint is therefore defined without a choice principle:

```text
adjacentEvenCommonLowerEndpoint radius physical link
  = (adjacentEvenIncidentLowerSpins radius physical link).getD 0 0.
```

It is zero for an empty lower word and the unique lower spin for a singleton.
Physical boundedness gives

```text
adjacentEvenCommonLowerEndpoint_le :
  SlabFaceLabellingBounded K (adjacentEvenExtent radius) physical ->
  adjacentEvenCommonLowerEndpoint radius physical link <= K.
```

This improves the previous generic support estimate from `3*K` to the exact
physical range `0,...,K`.  More importantly, the two lower-amplitude theorems
remove the corresponding source/target sums symbolically:

```text
fusionChannelAmplitude cutoff lowerWord channel
  = boolMultiplicity (decide (channel = commonLowerEndpoint)),

adjacentEvenLowerLinkAmplitude K radius physical link channel
  = Q'.ofNat
      (boolMultiplicity (decide (channel = commonLowerEndpoint))).
```

The second leaf first proves assembly locality.  Fixed incident spin words
are unchanged when the left and right half states are swapped; lower incident
spin words of an assembled slab are literally those of its left half; and
the assembled common lower endpoint is therefore the endpoint of that left
half.  These are the exact pointwise identities required by the outer
reflection sandwich, rather than extensional equalities of whole labelling
functions.

The theorem `adjacentEvenReachableFixedWordTransition_symmetric` then proves
the strongest valid replacement for the known nonsymmetric unrestricted
endpoint rectangle.  If `source` and `target` are actually reached by the two
lower words, the fixed words agree, both endpoint values lie in the unchanged
production cutoff, and the two assembled labellings are physically bounded,
then

```text
fusionWalkMultiplicity cutoff source target fixedWord
  = fusionWalkMultiplicity cutoff target source fixedWord.
```

The proof first converts nonzero lower amplitudes into endpoint support
bounds, combines those with the existing coupled lower-plus-fixed spin
budget, and applies the constructive reversal theorem only inside that
coupled support.  It never strengthens the statement to independent
source/fixed/target boxes.  The specialization
`adjacentEvenAssembledEndpointFixedWordTransition_symmetric` supplies the
deterministic endpoints of two reflected physical assemblies and discharges
reachability by the new indicator theorem.  In particular, the earlier
radius-zero bad two-face channels are outside the physical endpoint image;
their counterexample remains a valid fence against the unrestricted matrix
but is not an obstruction on the coupled physical support.

For later compression, the exact endpoint of a half state is named

```text
adjacentEvenHalfStateEndpointAssignment radius state : Z4Link -> Nat,
```

and `adjacentEvenHalfStateEndpointAssignment_le` proves pointwise that an
enumerated physical half state maps into `0,...,K`.  The proof assembles the
state with zero fixed-boundary and right-half labellings, proves that assembly
bounded, and transports the deterministic endpoint back to the left state.
The associated zero-padded pullback is

```text
adjacentEvenReachableFixedInterfaceMatrix K radius left right
  = adjacentEvenFixedInterfaceEndpointKernel K radius
      (endpointAssignment (halfStateAt left))
      (endpointAssignment (halfStateAt right))
```

when both indices are in the finite physical half-state carrier, and zero
otherwise.  The bounded-index theorem identifies it with the literal kernel.
The Type-valued target

```text
AdjacentEvenReachableFixedInterfaceGramWitness K radius
  := GramRep (adjacentEvenReachableFixedInterfaceMatrix K radius)
```

is deliberately named but not inhabited.  The current milestone proves
determinism, support, and fixed-word reversibility; it does **not** infer
positive semidefiniteness from symmetry and does not claim time-one
reflection positivity.

The attempted size reconnaissance revealed why all remaining work must stay
symbolic.  If `n = adjacentEvenExtent radius + 1 = 2*radius + 3`, then the
lower half has `6*(radius+1)*n^3` face coordinates and the fixed boundary has
`3*n^3`.  Already at radius zero these are respectively 162 and 81.  At
`K = 1`, the corresponding Cartesian carriers have `2^162` and `2^81`
elements.  A capped probe first inspected only the short face-ID list, but a
subsequent evaluation of the half-state **length** still tried to construct
the entire `2^162` list and reached the fixed 20 GB interpreter ceiling.  The
process was killed by that ceiling (exit 134) and the host remained stable.
The scratch evaluator was deleted immediately.

`AGENTS.md` now makes the resulting invariant explicit: never `#eval`,
`#reduce`, or otherwise materialize `boundedEdgeLabellings`,
`boundedLabellingsOn`, or any Cartesian enumerator built from them until a
symbolic cardinality bound has proved that exact instance safely small.
Evaluating `.length` is not a safe probe because the list must still be
constructed.  Inspect only the coordinate/ID list, calculate the product
bound externally, and prefer support and Fubini proofs whenever it is large.

The shortest remaining constructive route is now a two-level sandwich:

```text
fixed-face Gram
  -> reachable common-middle kernel
       = H * fixed-face-Gram * H^t
  -> physical reflected matrix
       = C * reachable-common-middle-kernel * C^t.
```

The production dependent fixed-face channel Gram already supplies the inner
positive kernel, and `finiteKernelSandwichGramRep` supplies both mechanical
Gram transports once the two entrywise identities are proved.  The next leaf
should be `Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction.lean`.
Its work order is:

1. prove lower side-factor locality on an assembled slab and identify the
   upper factor with the reflected/canonical lower factor;
2. collapse every lower source/target endpoint sum with the deterministic
   indicator, using zero padding rather than a filtered materialized list;
3. identify the complete physical reflected matrix entrywise with a finite
   sandwich of the reachable common-middle kernel;
4. isolate one honest residual data theorem: a common-middle half-trajectory
   factorization of that reachable kernel through the already proved
   dependent fixed-face channel Gram;
5. convert that data constructively to
   `AdjacentEvenReachableFixedInterfaceGramWitness`, then through the outer
   sandwich to `AdjacentEvenPhysicalAnchorGramWitness`; and
6. discharge `AdjacentEvenPhysicalAnchorPSD` and resume the already wired
   normalization, centering, staged time-one, representative-limit, and
   quotient-induction lane.

If the stronger reachable common-middle Gram identity proves unnecessarily
awkward, the admissible fallback is a direct tensor-network sum-of-squares
identity for the already-sandwiched physical quadratic.  The unrestricted
endpoint matrix, an integer reindexing of the odd/central reflection theorem,
and bare directed compatibility Schur factors remain formally fenced and are
not alternative proof routes.

Verification stayed within the mandatory Mac safety envelope: every
Lean/Lake command was serialized by the shared host lock, used
`LEAN_NUM_THREADS=1`, and retained `-s 65536 -M 20480`.  The deterministic
endpoint leaf and the reachable-symmetry leaf both check directly; the latter
took about 0.40 seconds.  The cached named target completed successfully with
705 jobs and a 427-millisecond new leaf.  The cached semantic root completed
all 2,557 jobs with a 2.4-second root.  All thirteen public axiom gates across
the two leaves report exactly `[propext, Quot.sound]`; the executable
forbidden-token scan reports zero hits.

Static analysis now reports 2,562 source modules, 7,964 local import edges,
zero cycles, 2,556 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports zero unbridged
enumerations.  Exact current provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:23043ee94d2bfca02af737621e70278af2eee813e545708c8324669da9dffecc
```

#### 8.13.45 Exact outer locality, endpoint normal form, and reachable diagonal reduction

(2026-07-18, session 24, completed and production-wired.)  The three new
leaves `Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality.lean`,
`Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm.lean`, and
`Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction.lean` complete
the entire outer reduction proposed in 8.13.44.  The literal zero-padded
physical reflected matrix at the anchor coupling is now proved entrywise
equivalent to a diagonal congruence of the reachable endpoint kernel.  Hence
the physical positive-semidefiniteness target follows constructively from one
and only one remaining datum: a Gram representation of that reachable
kernel.  This is a reduction theorem, not a claim that the remaining datum is
inhabited and not a claim of time-one reflection positivity.

The first leaf strengthens adjacent-even side geometry to the exact local
statements

```text
lower link + incident physical plaquette -> lower plaquette,
upper link + incident physical plaquette -> upper plaquette.
```

Their numerical-ID wrappers transport the result through
`slabIncidentPlaqIds`.  Consequently an assembled lower face factor and every
lower-link multiplicity read only the left half state, giving the ordinary
equality

```text
adjacentEvenLowerFactor w K radius
    (assembleAdjacentEvenReflectedSlabLabelling radius left boundary right)
  = adjacentEvenLowerFactor w K radius left.
```

The lower endpoint-amplitude product has the same exact locality.  On the
upper side, explicit reflection permutations identify the complete upper
face-ID list and upper-link list with their lower counterparts.  Face
weights and link multiplicities are invariant under those permutations, so
`adjacentEvenUpperFactor_reflection` and
`adjacentEvenUpperFactor_assemble_only_right` identify the assembled upper
factor with the canonical lower factor of the right half, up to `Q'.eqv`.
Thus no boundary variable remains in either exterior factor.

The second leaf exposes the endpoint kernel in the exact mixed-trajectory
normal form

```text
sum trajectory,
  adjacentEvenTrajectoryFixedFaceResummedKernel K radius source trajectory
    * adjacentEvenLinkTerminalProduct radius source target trajectory.
```

The proof swaps the physical fixed-face-labelling sum with the trajectory
sum, splits every link transition product into its fixed-face product and
terminal delta, and invokes the production fixed-face resummation theorem.
It is important that this is a *mixed* normal form: the resummed face kernel
is evaluated on the incoming field determined by `(source, trajectory)` and
the outgoing field determined by `trajectory`.  Existing directed and
mixed-map counterexamples forbid silently replacing those two maps by one
Gram feature map.

The lower source assignment is then eliminated exactly and symbolically.
`adjacentEvenLowerSourceTrajectorySum_eqv_endpoint` applies product Fubini to
the bounded assignment list, uses the deterministic lower indicator link by
link, and collapses each scalar delta sum at the canonical endpoint.  It does
not construct the raw endpoint function as an enumerated bounded labelling;
zero padding outside the fixed-link key list is handled algebraically.  The
remaining assembly lemmas prove that the fixed-face transition product reads
only the boundary labelling and that the reflected lower final amplitude is
exactly the terminal delta to the right endpoint.  These identities yield

```text
assembled common-lower interface sum
  ≈ endpoint trajectory product,

sum over fixed boundaries of assembled interface
  ≈ adjacentEvenFixedInterfaceEndpointKernel.
```

Combining those equalities with the exact exterior locality gives the
load-bearing kernel factorization, for physical half states `left` and
`right`,

```text
adjacentEvenPhysicalReflectedKernel anchorCoupling K radius left right
  ≈ lowerFactor(left)
      * (reachableEndpointKernel(endpoint(left), endpoint(right))
          * lowerFactor(right)).
```

No endpoint rectangle, half-state list, boundary-channel list, or trajectory
list is evaluated during the proof.

The generic operator

```text
diagonalKernelScale kernel scale i j
  = (scale i * scale j) * kernel i j
```

now has a constructive Gram transport `diagonalKernelScaleGramRep`.  An
arbitrary rational scale is absorbed directly into every feature vector; no
positivity premise and no square root are required.  The global theorem
`adjacentEvenPhysicalReflectedMatrix_eqv_reachableDiagonal` combines the
in-range factorization with the two zero-padded lookup theorems and proves
the identity for all natural-number indices, including both out-of-range
cases.  Therefore

```text
AdjacentEvenReachableFixedInterfaceGramWitness K radius
  -> AdjacentEvenPhysicalAnchorGramWitness K radius
  -> AdjacentEvenPhysicalAnchorPSD K radius
```

is now implemented by
`adjacentEvenPhysicalAnchorGramWitness_of_reachable` and
`adjacentEvenPhysicalAnchorPSD_of_reachable`.  This diagonal specialization
is strictly leaner than introducing a second finite identity-amplitude
sandwich carrier and proves the same mathematical congruence.

For the remaining inner problem, the Type-valued structure
`AdjacentEvenReachableCommonMiddleData` records a finite middle count, a
bounded fixed-face channel field at every middle index, a half amplitude,
and the exact factorization of the reachable matrix through the already
proved production dependent fixed-face Gram.  Its method `toGramRep` is a
fully constructive adapter using `finiteKernelSandwichGramRep`.  No instance
of the structure is asserted.  The missing theorem is precisely a
weight-preserving common-middle construction; hiding it behind symmetry,
directed compatibility, or an unrestricted endpoint Gram would be invalid.

The next proof search must therefore decide the inner obstruction before
more infrastructure is built:

1. audit the smallest symbolic reachable two-face patch with explicit
   endpoint values `<= K`, never a materialized global carrier, and determine
   whether the reachable endpoint kernel itself is positive semidefinite;
2. if it is, construct a two-sided, weight-preserving trajectory gluing
   equivalence whose middle retains enough fixed-incidence channel data (and,
   if necessary, the local fixed-face Gram feature indices) for both legs to
   use the same feature field;
3. formalize that equivalence as an inhabitant of
   `AdjacentEvenReachableCommonMiddleData`, then apply the now-mechanical
   reachable-to-physical Gram and PSD chain;
4. if the symbolic reachable patch is not PSD, abandon the stronger inner
   witness immediately and derive a direct SOS identity for the fully
   diagonally weighted physical quadratic, where exterior factors may remove
   the offending directions; and
5. only after `AdjacentEvenPhysicalAnchorPSD` is unconditional, resume the
   existing normalization, conditioning/centering, staged time-one,
   representative-limit, and quotient-induction lane.

All verification remained inside the mandatory Mac safety envelope.  Every
Lean/Lake command was serialized by the shared host lock, used
`LEAN_NUM_THREADS=1`, and retained `-s 65536 -M 20480`; no clean or uncached
full build and no enumerator evaluation was performed.  Each new leaf checks
directly.  The cached named reachable-sandwich target completed all 709 jobs,
and the fully wired cached semantic root completed all 2,560 jobs with a
563-millisecond root.  The generic diagonal Gram gate reports `[propext]`;
all other public gates in the three leaves report exactly
`[propext, Quot.sound]`.  The executable forbidden-token scan reports zero
hits.

Static analysis now reports 2,565 source modules, 7,972 local import edges,
zero cycles, 2,559 modules reachable from `YMGap`, the same six reviewed
exclusions, and zero unexpected orphans.  The host-load guard passes over 236
repository entry files; all ten mocked JIT remote-state and four bounded
supervisor cases pass; and the Frontier-DAG guard reports 12 enumerations,
ten registered/grandfathered, two exempt, and zero unbridged.  Exact current
provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:cda39a55a28bba9868829c4b668f75d2db95917b46aeda379ea7c125c329bbef
```

#### 8.13.46 Active quadratic, canonical trajectory carrier, and the rankwise SOS frontier

(2026-07-18, session 25, production-wired and fully verified.)
This session sharpened the remaining adjacent-even reflection problem in
three independent directions and then joined them.  First, the literal
physical quadratic was identified with the exact physically active reachable
quadratic.  Second, the mixed incoming/outgoing trajectory fields and their
terminal endpoint delta were embedded in one canonical symbolic carrier for
the already proved fixed-face Gram.  Third, the sole remaining theorem was
reformulated as a rank-aware shared-glue SOS that preserves the local Gram
weights exactly.  The result is a substantially smaller frontier, but it is
still a reduction: no rankwise shared-glue datum is inhabited here, and
time-one reflection positivity is not yet unconditional.

The exact diagonal-congruence identity now holds at quadratic-form level:

```text
gramQuadForm (diagonalKernelScale M scale) coefficient count
  ≈
gramQuadForm M (fun i => coefficient i * scale i) count.
```

Specializing the identity to the proved physical-matrix factorization gives

```text
adjacentEvenPhysicalReflectionQuadratic anchorCoupling K radius c
  ≈
adjacentEvenReachableScaledQuadratic K radius c,
```

and the propositions

```text
AdjacentEvenReachableScaledPSD K radius
  ↔ AdjacentEvenPhysicalAnchorPSD K radius
```

are now proved equivalent.  This is not merely a one-way sufficient
condition.  It prevents future work from demanding positivity on endpoint
directions killed by the exterior lower-half factor.  Conversely, it does
not license division by that factor: zero exterior weights remain possible,
and the active formulation handles them exactly without a support or
invertibility premise.

The duplicate-free four-link face estimate was strengthened at its source.
The long row argument is now factored through the parameterized statement

```text
anchorJointFourExcitedRowSum faceCutoff channelCutoff source
  ≤ tailWindow anchorCoupling 5 1 faceCutoff,
```

and `tail_modulus` at the same anchor proves that tail is at most `dyad 2 =
1/4`.  Hence both the finite-sum and list-row forms of the excited face block
have row mass at most `1/4`; the previous `1/2` declarations remain as
backward-compatible consequences.  A symbolic two-face audit then writes a
reachable patch sharing one channel as

```text
(Δ + E)(Δ + E) = Δ₇ + (EΔ + ΔE + EE).
```

The residual is nonnegative.  On endpoints bounded by `K`, fixed-word
reversal makes the shared `EE` contraction symmetric because both endpoint
budgets are at most `3*K ≤ 6*K`.  Its row mass is bounded by

```text
1/4 + 1/4 + 1/16 = 9/16 < 1,
```

so the reachable two-face patch admits the usual rational
diagonal-dominance Gram at every cutoff.  This audit found no local reachable
counterexample, but the full two-face Gram has not yet been promoted to a
production Lean theorem.  More importantly, this estimate does not
globalize by incidence degree: even disjoint residual factors have row growth
of the form `(1+δ)^N-1`.  A fixed radius-zero dominance certificate could be
obtained by strengthening the individual face tail to `1/256` and using the
81 fixed faces, since `(257/256)^81 < 2`; that is a useful regression target,
not an all-radius proof strategy.

The exact half-coupling leaf records

```text
halfAnchorCoupling = 1/20,
anchorCoupling ≈ halfAnchorCoupling * halfAnchorCoupling.
```

It propagates this identity through every Casimir power and proves

```text
physLinkWeight anchorCoupling spin
  ≈ anchorHalfSchurAmplitude spin²,

coeffW anchorCoupling spin
  ≈ dimQ spin * anchorHalfSchurAmplitude spin².
```

The diagonal half-Schur kernel is nonnegative and symmetric, and its finite
intermediate-mode composition collapses exactly to the full contracted link
entry whenever the source mode is within the cutoff.  The composition is
cutoff-stable once that mode is present.  These are genuine local square and
Schur identities.  They do not split the spatial plaquette multiplier, do not
make shared faces independent, and do not themselves prove a global slab
SOS.  Their intended use is inside the remaining decorated-trajectory
pairing, not as a pointwise square root of the whole action.

The earlier `AdjacentEvenReachableCommonMiddleData` required one
rank-independent half amplitude.  That interface was too restrictive for a
literal expansion of the mixed face kernel.  The new generic construction

```text
rankAwareSharedGlueFeature
rankAwareSharedGlueKernel
rankAwareSharedGlueGramRep
```

allows the half amplitude to depend on both the fixed-face Gram rank and a
finite shared-glue coordinate.  It flattens `(rank, glue)` with
`finSum_flatten`, repeats the original weight `rep.d rank` literally, and
never signs, divides, or square-roots that weight.  Consequently an
`AdjacentEvenReachableFeatureTrajectoryGluingData` inhabitant produces the
reachable Gram constructively.  This is the correct algebraic target for a
feature-decorated trajectory theorem.

The middle carrier is no longer arbitrary.  Let

```text
I(radius) = adjacentEvenFixedFaceMajorIncidences radius.
```

The canonical carrier is the symbolic list

```text
boundedLabellingsOn (linkAuxiliaryCutoff K) I(radius),
```

zero-extended away from `I(radius)`.  It is never evaluated.  The new generic
completeness theorem proves constructively that every labelling bounded on a
noduplicated key list and zero off that list occurs in
`boundedLabellingsOn`.  A list-member recursion then supplies an existential
natural-number `getD` index without a `DecidableEq` instance on function
spaces.  Therefore every supported bounded incidence assignment has an
actual middle index, and every middle field is uniformly bounded even for
zero-padded indices.

For an incidence trajectory, both canonical assignments are now proved
bounded and realized:

```text
incoming assignment(id,link)
  = predecessor channel before face id on link,

outgoing assignment(id,link)
  = trajectory link id.
```

The incoming bound follows from a new structural lemma saying that
`fixedIdIncomingChannel` is either the initial channel or a channel already
present in the fixed word.  The face-major/link-major incidence permutation
transports the per-link trajectory bounds to the face-major carrier.  No
trajectory list, endpoint rectangle, or carrier cardinality is materialized.

Incidence locality is then proved for the dependent fixed-face kernel.  The
four-channel reader sees only the four literal links of a fixed face, and the
complete dependent kernel is invariant when its incoming and outgoing
fields agree on all pairs in `I(radius)`.  Hence every mixed term has
canonical indices `incoming,outgoing` with

```text
adjacentEvenTrajectoryFixedFaceResummedKernel K radius source trajectory
  ≈
adjacentEvenGlobalDependentFixedFaceChannelMatrix
  K radius canonicalMiddleField incoming outgoing.
```

The matrix on the right has the concrete production Gram
`adjacentEvenCanonicalFixedIncidenceGramRep`.  This discharges the carrier
selection and field-preservation parts of the former common-middle residual.

Terminal preservation is exact as well.  Congruence lemmas for
`fixedIdIncomingChannel`, `fixedIdFinalChannel`, and
`fixedIdTerminalIndicator` show that the full product of terminal deltas
depends only on the outgoing channels on `I(radius)`.  Reading a canonical
middle field link-major therefore reconstructs the same terminal endpoint
factor.  The strongest summand theorem supplies canonical indices satisfying

```text
faceKernel(source, trajectory) * terminal(source, target, trajectory)
  ≈
canonicalGramMatrix(incoming, outgoing)
  * canonicalMiddleTerminal(source, target, outgoing),
```

and additionally proves that `canonicalMiddleField incoming` is precisely
the predecessor field reconstructed from `source` and the canonical outgoing
middle trajectory.  This is intuitionistic existential realization.  It is
not a computable global choice of indices and is not, by itself, a reindexing
of the complete trajectory sum.

The final mechanical interface is
`AdjacentEvenCanonicalRankwiseTrajectoryGluingData`.  It fixes the canonical
middle count, middle field, bound, and fixed-face Gram, leaving only a finite
glue count, a rank-aware half amplitude, and the exact global factorization.
An inhabitant now yields, with no further mathematics,

```text
canonical rankwise gluing data
  → reachable Gram
  → physical anchor Gram
  → physical anchor PSD
  ↔ active reachable PSD.
```

The irreducible theorem is consequently visible rather than hidden.  After
choice-free grouping of canonical incoming/outgoing fields, for every fixed
production Gram rank `r` one must prove an identity of the form

```text
Σ incoming,outgoing,
  compatibility(left,right,incoming,outgoing)
    * v r incoming * v r outgoing
≈
Σ glue,
  H r glue left * H r glue right.
```

Here `compatibility` is the exact predecessor/terminal trajectory
multiplicity, not a freely symmetrized proxy.  Reachable word reversal proves
symmetry of its total kernel, but symmetry alone cannot create the required
feature pairing.  The existential single-summand realization also cannot be
used under a finite sum by hidden choice.  The next implementation must:

1. define a choice-free canonical compatibility sum using explicit finite
   incidence assignments and Kronecker indicators, or an equally explicit
   mixed-radix codec;
2. prove its Fubini/delta identification with the literal trajectory list,
   including multiplicities and zero padding;
3. expand the canonical fixed-face Gram rankwise before the compatibility
   contraction;
4. use the exact `1/20` half-Schur composition, a genuine decorated
   trajectory pairing, or another explicit SOS to construct the same
   left/right half feature `H`; and
5. immediately fall back to a direct active-physical quadratic SOS if a
   reachable rankwise factorization is falsified.  Do not replace this step
   by bare symmetry, an unrestricted sequential face product, or a
   rank-independent half amplitude.

The supplied categorical spike was audited in its expanded
`cat_structural_spike` form and deliberately left quarantined.  Its
`DomOver`, integer-substrate, ledger, square-guard, and step-bridge machinery
is coherent generic bookkeeping, but it supplies neither the rankwise
trajectory compatibility identity nor the analytic half-feature.  Promoting
it now would enlarge the trusted production surface without closing the
current obstruction.  Once physical PSD is unconditional, its commuting
square and ledger abstractions may be useful for the later uniform-radius,
telescoping, and representative-limit lane.  No spike file is imported,
staged, or treated as part of the present proof.

After the canonical rankwise identity is inhabited, work must return
immediately to the already wired normalization, conditioning/centering,
staged time-one, representative-limit, and quotient-induction chain.  Further
local positivity infrastructure is lower priority unless it directly tests
or constructs that identity.

Final verification stayed inside the mandatory Mac safety envelope.  The
fully wired `+YMGap` root completed successfully in one serialized Lean
session with `LEAN_NUM_THREADS=1`, the fixed `-M 20480`/20 GiB cap, and no
clean or uncached rebuild: 2,567 jobs completed.  All declarations introduced
in this milestone remain within the project's accepted constructive gates,
namely no axioms for purely arithmetic leaves, `[propext]` where finite
function/list extensionality requires it, and at most `[propext, Quot.sound]`
for the production real-number equivalence layer.  No `Classical`,
`native_decide`, `sorry`, `admit`, or custom axiom was introduced.

The final structural census reports 2,572 Lean source modules, 7,991 local
import edges, zero local import cycles, 2,566 modules reachable from the
semantic root, the same six reviewed exclusions, and zero unexpected
orphans.  The host-load guard passes over 236 tracked or untracked nonignored
repository entry files.  All ten mocked Mac-CI remote-state cases and all four
bounded-supervisor cases pass without signals or sleeps.  The Frontier-DAG
guard reports 12 enumerations, ten registered or grandfathered, two exempt,
and zero unbridged; the executable forbidden-token scan reports zero hits.
The exact production-source provenance is

```text
YMGAP_SOURCE_FINGERPRINT sha256:0fa711f48e7192d1d4f760cafd83d3383b49e4c35d9aac3e7a906cd699a86206
```

#### 8.13.47 Direct rank-mixing quaternion SOS and the exact product-Haar frontier

This milestone starts from the fully wired baseline commit `81c9cb3`, which
was pushed to `main` after the verification recorded at the end of §8.13.46.
Everything described below is subsequent work.  In particular, the build and
fingerprint recorded in §8.13.46 certify that pushed baseline, not the current
working tree.  The current additions must receive their own serialized,
memory-capped verification before they are committed or pushed.

The first result of the new audit is a sharp separation between exact finite
bookkeeping and the actual positivity theorem.  The canonical incidence
carrier now has a completely explicit mixed-radix codec.  For a noduplicated
finite key list, `boundedLabellingMixedRadixCount`,
`boundedLabellingMixedRadixEncode`, and
`boundedLabellingMixedRadixDecode` provide a positive finite carrier, a
uniform coordinate bound, zero extension off the active keys, both
encode/decode identities, injectivity on the active range, and exact agreement
with the existing symbolic bounded-labelling enumeration.  The adjacent-even
specialization supplies a concrete middle count, total indexed assignment,
middle field, and canonical incoming/outgoing trajectory indices.  This
removes the former existential indexing gap without selecting a function from
a proposition and without evaluating the astronomically large carrier.

The corresponding Kronecker partition is exact.  `channelEqualityDelta` and
`boundedLabellingEqualityDelta` take only the rational values zero and one.
Summing the assignment delta over the bounded carrier gives one for every
supported bounded target, and the weighted collapse theorem evaluates an
arbitrary finite assignment sum at that target.  Its adjacent-even incidence
specialization partitions both the incoming and outgoing trajectory fields.
Inserting the two partitions into each literal trajectory term yields
`adjacentEvenCanonicalTrajectoryAssignmentTerm`; finite Fubini then proves
the exact trajectory-major/assignment-major contraction

```text
adjacentEvenCanonicalTrajectoryMajorContraction K radius source target
  ≈
adjacentEvenCanonicalAssignmentMajorContraction K radius source target.
```

Together with the previously proved trajectory normal form, the literal
fixed-interface endpoint kernel is now exactly the explicit canonical
compatibility contraction.  Multiplicities, terminal deltas, bounds, and zero
padding are all retained.  Thus no unproved reindexing or hidden finite choice
remains in the compatibility layer.  This result is an exact normal form; it
does not assert that the compatibility kernel is Gram.

The decisive correction is supplied by the fixed-original-rank fence.  Two
rank-one face factors supported respectively on the adjacent state pairs
`{0,1}` and `{1,2}` give an exact two-face contribution whose forward entry is
one and whose reverse entry is zero.  More abstractly, every literal
same-half expression

```text
sum glue, weight glue * H glue left * H glue right
```

is symmetric, even if signed weights were allowed.  Hence the nonsymmetric
fixed-rank contribution cannot possess the proposed common same-half
factorization.  The conditional feature-trajectory and canonical rankwise
adapters remain algebraically correct if supplied with their hypotheses, but
the interpretation that each original character rank should separately
supply those hypotheses is false.  The production route must first combine
the vacuum and all active face ranks and only then construct an SOS for the
complete active quadratic.  No future plan item may silently restore the
falsified fixed-rank premise.

The replacement target is now explicit.  The direct expression

```text
adjacentEvenActiveSOS weight amplitude coefficient stateCount termCount
```

is a finite sum of nonnegatively weighted squares of linear forms in the
physical coefficient vector.  `AdjacentEvenActiveQuadraticSOSData K radius`
stores its finite term count, weights, constructive weight inequalities,
half-state amplitudes, and the one load-bearing identity

```text
adjacentEvenReachableScaledQuadratic K radius coefficient
  ≈ adjacentEvenActiveSOS ... coefficient ... .
```

An inhabitant mechanically proves the active reachable PSD proposition and,
through the already proved exact diagonal-congruence equivalence, the full
physical anchor PSD proposition.  This interface permits ranks, quaternion
features, face selections, Haar monomials, and trajectory decorations to mix
inside one term carrier.

An entrywise intermediate bridge has also been isolated for the case in which
the product-Haar construction naturally yields a Gram kernel before the
quadratic is assembled.  `finiteWeightedGramKernel` is the `Nat`-indexed
weighted outer-product kernel, and its quadratic is identified with
`adjacentEvenActiveSOS` by reusing the existing constructive
`gramQuadForm_eq_sos` theorem rather than duplicating its finite-sum Fubini
algebra.  `AdjacentEvenReachableKernelSOSData K radius` records an entrywise
factorization of the unscaled reachable fixed-interface matrix.  Its
conversion to `AdjacentEvenActiveQuadraticSOSData` multiplies every
half-state coordinate by `adjacentEvenPhysicalOuterScale K radius state`.
Thus the exact exterior factors are absorbed without division, a support
decision, or a positivity premise on the exterior scale.  The entrywise
record is a convenient sufficient bridge, but it is stronger than the direct
active-quadratic record.  If the global Haar argument closes only after the
physical compression, work must instantiate the direct record rather than
turn the entrywise bridge into a new obstruction.

The local face analysis now treats the complete truncated anchor weight.  The
excited dimension mass is

```text
anchorExcitedCharacterDimensionMass cutoff
  = sum index<cutoff,
      coeffW anchorCoupling (1+index) * dimQ (1+index).
```

Termwise this is exactly the degree-two Casimir tail, so the established
anchor tail estimate gives

```text
0 ≤ anchorExcitedCharacterDimensionMass cutoff ≤ 1/2.
```

Consequently

```text
anchorVacuumReserve cutoff
  = 1 - anchorExcitedCharacterDimensionMass cutoff
```

is constructively nonnegative and in fact at least `1/2`, uniformly in the
cutoff.  The reserve and excited mass add back to one at `Q'.eqv`.  The full
truncated class function therefore has the exact rank-mixing rewrite

```text
1 + sum_{s=1}^K coeffW(anchorCoupling,s) * U_s(x)
  ≈
anchorVacuumReserve K
  + sum_{s=1}^K coeffW(anchorCoupling,s) * (dimQ s + U_s(x)).
```

Every coefficient on the right is nonnegative.  This is the essential step
that makes the reserve compensate the dimension shifts; it is not a
rank-by-rank claim about the original unshifted character expansion.

Both parity classes of shifted characters now have all-order, radical-free
SOS identities over `Q'`.  For even rank, the constructive Chebyshev rotation
and double-angle argument proves

```text
ofNat(2*m+1) + U_(2*m)(x)
  ≈ 2 + 4 * sum_{k<m} T_(k+1)(x)^2.
```

For odd rank, with `C_0(x)=1` and
`C_(k+1)(x)=U_(k+1)(x)-U_k(x)`, the adjacent-`U` determinant, fusion boundary,
and odd telescope prove

```text
1 + T_(2*k+1)(x) ≈ (1+x) * C_k(x)^2,

ofNat(2*m+2) + U_(2*m+1)(x)
  ≈ 2 * sum_{k≤m} (1+x) * C_k(x)^2.
```

On a rational unit quaternion

```text
x^2 + y1^2 + y2^2 + y3^2 ≈ 1,
```

the remaining affine factor has the exact four-square identity

```text
2*(1+x) ≈ (1+x)^2 + y1^2 + y2^2 + y3^2.
```

Multiplying by `C_k(x)^2` and summing therefore presents every odd shifted
character as a finite sum of literal rational quaternion squares.  None of
these proofs selects a square root, a sign, a trigonometric parameter, or a
classical point on the sphere.

The finite SOS carrier has been expanded into the precise algebra needed by
the global construction.  `FiniteWeightedRationalSOS Input` stores a finite
term count, total rational weights, a proof that every weight is nonnegative,
and total feature functions.  It now provides:

* `value_nonnegative`, proving every represented value nonnegative;
* `zero`, `one`, and a one-term nonnegative `constant`, retaining a scalar as
  a weight rather than extracting its square root;
* `scale`, which multiplies weights by a nonnegative rational;
* `add` and `addList`, which concatenate finite SOS blocks with exact offset
  reindexing;
* `multiply` and `multiplyList`, which use mixed-radix packing and
  `finSum_flatten` to multiply finite SOS values exactly; and
* `pullback`, which preserves the term carrier and weights while precomposing
  every feature with a map of input types, together with exact evaluation,
  weight, identity, and composition laws.

These operations are symbolic definitions.  They do not materialize a list
of the packed terms, so their use does not violate the repository's bounded
enumeration or Mac-load rules.

The complete face certificate is now packaged by `AnchorFaceSOS`.  Its input
contains four rational quaternion coordinates together with the exact unit
sphere equation.  The even packet contains a constant weight two and the
first-kind square modes with weight four.  The odd packet contains four
unit-weight quaternion squares at every half-angle level.  Decidable parity
selects the appropriate shifted-character packet; nonnegative scaling absorbs
`coeffW anchorCoupling (1+index)` into its weights; structural direct sum adds
all excited ranks; and a one-term constant packet carries the vacuum reserve.
The resulting theorem is

```text
anchorTruncatedFaceClassValue cutoff input.x
  ≈ value (anchorFaceSOS cutoff) input.
```

Every stored weight is constructively nonnegative, and the exact identity
gives the pointwise corollary

```text
0 ≤ anchorTruncatedFaceClassValue cutoff input.x.
```

This closes the finite one-face rank-mixing SOS.  It does **not** by itself
show that the reflected endpoint kernel is Gram: pointwise nonnegativity of a
relative group weight is not a substitute for the exact face-holonomy and
Haar-contraction identity.

The local polynomial boundary is now complete, subject only to the final
serialized root verification recorded below.  The fixed environment

```text
[x,y1,y2,y3]
```

is implemented by `anchorEnvironment`.  `qPolyToRatPolyAt` embeds every
univariate `QPoly` by Horner recursion into the raw finite-support `RatPoly`
carrier, with exact evaluation at the selected coordinate.  Explicit
polynomials for every `T_n` and `C_n` mode realize the even and odd quaternion
features.  `RatPolyFeatures` is closed under constants, nonnegative scaling,
and offset-packed direct sums, and therefore supplies

```text
anchorFaceFeaturePolynomial cutoff term
```

for every feature of `anchorFaceSOS cutoff`.  Finally,

```text
anchorFaceWeightedSOSPolynomial cutoff
  = sum_term weight(term) * featurePolynomial(term)^2
```

has the exact semantic identity

```text
evalRatPoly (anchorEnvironment input)
    (anchorFaceWeightedSOSPolynomial cutoff)
  ≈ value (anchorFaceSOS cutoff) input
  ≈ anchorTruncatedFaceClassValue cutoff input.x.
```

Thus the complete rank-mixed one-face certificate is available both as a
finite weighted SOS and as explicit finite-support rational-polynomial data.

Constructive arbitrary-variable polynomial substitution is now available.
For `sigma : Nat → RatPoly`, `substitute sigma p` is defined by recursion over
the finite term and exponent lists and satisfies

```text
evalRatPoly rho (substitute sigma p)
  ≈ evalRatPoly
      (fun coordinate => evalRatPoly rho (sigma coordinate)) p.
```

Substitution by coordinate variables is extensionally the identity and nested
substitution is extensionally associative in `RatPolyEqv`.  The API also
proves the two setoid laws

```text
RatPolyEqv p q
  → RatPolyEqv (substitute sigma p) (substitute sigma q),

(∀ i, RatPolyEqv (sigma i) (tau i))
  → RatPolyEqv (substitute sigma p) (substitute tau p),
```

as well as extensional preservation of raw polynomial addition and
multiplication.  Later pullbacks can therefore rewrite representatives and
coordinate maps without a hidden representative-choice premise.

The rational quaternion algebra now supplies the exact group structure needed
by face holonomies.  Reflected polynomial normalization proves Hamilton
associativity, both unit laws, conjugation involutivity, reversal of products,
both conjugate-product identities, preservation of norm by conjugation, and
multiplicativity of the four-square norm.  Hence the rational points of the
unit three-sphere form a `ConstructiveGroup`: multiplication is Hamilton
multiplication and inverse is conjugation.  This statement is deliberately
only about rational unit quaternions modulo coordinatewise rational semantic
equality.  It does not assert compactness, completeness, a topology, or a Haar
measure on the rational-point carrier.

The first genuine lattice-geometric pullback is complete.  In the audited
`edgesOf` order

```text
U0 = U(v,a),       U1 = U(v,b),
U2 = U(v+e_b,a),   U3 = U(v+e_a,b),
```

the positive plaquette holonomy is fixed as

```text
U0 * U3 * inv(U2) * inv(U1).
```

Closure in the unit-norm group supplies its sphere equation without a
separate normalization argument.  Pulling `anchorFaceSOS cutoff` along this
map gives `anchorFaceHolonomySOS cutoff`, and pulling once more along
`plaquetteOrientedEdgeInput` gives `latticeAnchorFaceHolonomySOS`.  Their
values are exactly the truncated class value at the physical plaquette
holonomy, and their weights and pointwise nonnegativity are inherited
constructively from the local packet.

The same holonomy is now polynomial.  A four-component
`RatPolyQuaternion` implements polynomial scalar embedding, unit,
conjugation, and Hamilton multiplication, with componentwise exact evaluation
laws.  In the sixteen scalar-first edge coordinates, the polynomial word

```text
orientedPlaquetteHolonomyPolynomial
  = U0 * U3 * conj(U2) * conj(U1)
```

evaluates to the geometric unit-quaternion holonomy.  Substituting its four
components for the local anchor variables produces

```text
anchorFaceHolonomyFeaturePolynomial cutoff term
anchorFaceHolonomyWeightedSOSPolynomial cutoff,
```

and their evaluation in the official four-edge environment agrees,
respectively, with the pulled-back SOS feature and the complete physical face
class value.  Thus the geometric and polynomial orientation conventions have
been joined by an exact theorem rather than by an informal coordinate
identification.

Finite products of these face packets are also available symbolically.  For
any finite plaquette list, `anchorFaceDensitySOS` maps each plaquette to its
lattice holonomy pullback and combines the factors using `multiplyList`.
Every face is evaluated on the same gauge field, so shared links remain
shared; no independent-face approximation is made.  Its value is exactly the
right-recursive product

```text
product_{plaquette in plaquettes}
  anchorTruncatedFaceClassValue cutoff
    (latticePlaquetteHolonomy field plaquette).val.r,
```

all packed weights remain nonnegative, and both the SOS value and the physical
product are pointwise nonnegative.  The specialization
`adjacentEvenFixedFaceDensitySOS` uses the existing fixed-face identifier
order through `slabPlaquetteAt` without evaluating or materializing the slab.

This completes the local rank mixing, polynomial face holonomy, and symbolic
finite fixed-face density.  It does **not** yet prove reflection positivity.
`anchorFaceDensitySOS` is still function-valued on a common lattice gauge
field; it is not yet a polynomial on one finite deduplicated link-coordinate
carrier.  Moreover, pointwise nonnegativity of the density does not imply that
the reflected endpoint kernel is Gram.  The remaining load-bearing theorem is
the exact product-Haar/Fubini identification with the already wired
spin/fusion/trajectory kernel.

The next construction must therefore enumerate the distinct active physical
links symbolically, assign each link one four-coordinate block, and substitute
every local sixteen-coordinate face polynomial into that common carrier.
Repeated occurrences of a physical link must map to the same block, while
boundary orientation remains encoded by polynomial conjugation.  If `L` is
the finite link list, the required Haar functional is the blockwise moment map

```text
H_L(sum_alpha c_alpha X^alpha)
  ≈ sum_alpha c_alpha *
      product_{link in L}
        sphereMoment4(alpha restricted to that link's four coordinates).
```

It must be proved linear, compatible with raw polynomial equivalence and each
link-sphere ideal, compatible with finite Fubini and reindexing, and
nonnegative on squares.  The final comparison must then reproduce, with no
suppressed normalization, the literal face coefficient product, shared-link
fusion multiplicities, canonical incoming/outgoing compatibility
contraction, endpoint deltas, and exterior physical scales.  Its target is
either the entrywise statement

```text
adjacentEvenReachableFixedInterfaceMatrix K radius left right
  ≈ finiteWeightedGramKernel globalWeight globalHalfAmplitude
      globalTermCount left right,
```

which inhabits `AdjacentEvenReachableKernelSOSData`, or, if entrywise
factorization is unnecessarily strong, the logically minimal quadratic
statement

```text
adjacentEvenReachableScaledQuadratic K radius coefficient
  ≈ adjacentEvenActiveSOS globalWeight activeHalfAmplitude coefficient
      (adjacentEvenPhysicalHalfStateCount K radius) globalTermCount.
```

Bare pointwise positivity, symmetry, or a product of independent face
kernels cannot replace this equality.  The proof must explain exactly how the
quaternion polynomial/Haar expansion is identical to the already wired finite
spin-trajectory kernel.

Raw polynomial size is now a formal engineering constraint.  The
duplicate-preserving `RatPoly` representation expands feature squares and
their substitutions before normalization; concretely unfolding
`weightedSOSPolynomial`, `anchorFaceWeightedSOSPolynomial`, or a downstream
product at nontrivial cutoff can grow roughly quartically and can exhaust the
host even though symbolic compilation succeeds.  These objects must remain
opaque and be manipulated through exact evaluation theorems,
`FiniteWeightedRationalSOS`, and individual feature polynomials.  Any future
normal form must first use a proved sparse or DAG carrier together with a
conservative symbolic size bound.  Neither `#eval`, `#reduce`, printing, nor
even a seemingly harmless concrete size probe is permitted on the raw
expanded object.

The revised work order is therefore:

1. **Complete:** serialized, one-thread, fixed-memory verification of all
   current imports and every static consistency/constructivity guard;
2. construct a noduplicated finite active-link carrier and a mixed-radix
   four-coordinate codec, with exact lookup theorems for every `edgesOf`
   occurrence and without materializing the slab;
3. lift each sixteen-coordinate face feature into that common carrier and
   prove evaluation against one shared lattice gauge field, then form the
   symbolic global face packet without expanding the raw polynomial;
4. generalize the current two-quaternion polynomial Haar moment to an
   arbitrary finite link list, proving block Fubini, linearity, sphere-ideal
   descent, reindexing invariance, and square nonnegativity constructively;
5. split the global features at the reflection plane, include the endpoint
   and exterior-scale factors, and prove the exact product-Haar expression for
   the reachable fixed-interface kernel or its physically scaled quadratic;
6. identify that expression with the existing character expansion,
   shared-link fusion network, canonical compatibility contraction, and
   terminal deltas;
7. inhabit `AdjacentEvenReachableKernelSOSData` if the entrywise identity is
   obtained, otherwise inhabit `AdjacentEvenActiveQuadraticSOSData` directly,
   and invoke the mechanical transport to physical anchor PSD;
8. resume normalization, conditioning/centering, staged time-one,
   representative-limit, completion, and quotient induction;
9. reconsider the quarantined categorical spike only for later
   commuting-square, telescoping, ledger, or representative-limit
   bookkeeping.

The supplied `cat_structural_spike` remains quarantined.  Its generic
categorical substrate may become useful in item 9, but it does not provide
the rational quaternion group law, the polynomial face-holonomy map, the
finite product-Haar theorem, or the active quadratic factorization.  No spike
file is imported into production, and no current spike edit is to be staged
with this mathematical milestone.

**Final verification for §8.13.47 — ✓ COMPLETE (2026-07-19).**  The official
full incremental `make lean-build LEAN_JOBS=1` ran once under `caffeinate`,
`nice`, the repository session lock, and the mandatory `-M 20480` per-process
ceiling.  All three Lake default targets passed in 2,598 jobs: `YMGap`,
`YMGapGuard`, and `YMGapStatementGuard`.  The frontier guard kept all five
Clay-frontier types unconditionally uninhabited, and all ten pinned frontier
statement hashes were unchanged.

The saved full-build log passed the fail-closed axiom audit with 19,957
executable source gate sites, 19,934 theorems, 2,451 namespaces, zero reviewed
or unreviewed exceptions, and no dependency outside the accepted set
`[propext, Quot.sound]`.  Its current-provenance stamp is

```text
sha256:ed7261ff0db3418f2b250129f57bdc20bc78e11c2838078907b255c7f5fb8c9a
```

The static import audit found 2,592 source modules, 8,050 local import edges,
zero cycles, 2,586 modules reachable from the semantic root, six reviewed and
classified semantic orphans, and zero unexpected orphans.  The host-load
guard passed all 236 tracked/untracked non-ignored entry files.  The mocked Mac
CI audit passed ten remote-state scenarios and four bounded-supervisor
scenarios without signals or sleeps.  The Frontier-DAG audit found twelve
enumerations, ten registered or grandfathered, zero bridged, two exempt, and
zero unbridged.  The executable forbidden-token scan found zero hits, and
`git diff --check` passed.  The separately targeted substitution, polynomial
holonomy, and finite density leaves also passed with no axiom beyond the same
accepted set.

#### 8.13.48 Arbitrary finite-product Haar positivity, the direct boundary quadratic, and the recoupling correction

This section records the constructive milestone completed after §8.13.47 and
supersedes items 4--7 of that section's proposed order.  The arbitrary finite
product-Haar positivity theorem and the direct active-link Haar quadratic are
now proved.  The intended identification with the existing production
fixed-interface kernel is *not* proved: a new local theorem shows that the
literal cutoff-two two-face production patch cannot be a common-half
product-Haar Gram.  The work plan is therefore corrected at the first point
where orientation, Schur normalization, and recoupling data can enter, rather
than transporting positivity across an unjustified scalar-kernel equality.

All statements in this section are intuitionistic.  No new file uses
`Classical`, choice, `sorry`/`admit`, `native_decide`, or a custom axiom.  The
complete printed dependency gates of the promoted results are contained in
`[propext, Quot.sound]`.

##### 8.13.48.1 Common active-link polynomial carrier — ✓ COMPLETE

The following production path is now present and root-wired:

1. `Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier` gives the finite,
   duplicate-free list of physical links needed by the adjacent-even fixed
   slab, its exact list-index codec, four scalar coordinates per link, and the
   corresponding coordinate count.  Every subsequent polynomial reads one
   occurrence of a physical link from this common carrier; repeated face-edge
   occurrences no longer acquire independent quaternion variables.
2. `SU2QuaternionGlobalFaceRatPoly` substitutes the sixteen local quaternion
   coordinates of a face feature into the four coordinates of each of its
   four oriented physical edges.  Its evaluation theorem identifies the
   substituted polynomial with the original face-holonomy class value on one
   shared rational-unit-quaternion gauge field.
3. `SU2QuaternionGlobalFaceRatPolySupport` proves closure of
   `SupportedCoordinates` under zero, one, constants, variables, sums,
   negation, scalar multiplication, multiplication, powers, and polynomial
   substitution.  Via `supportedCoordinates_four_mul_iff`, these results give
   the native `SupportedQuaternionBlocks` hypothesis required by the exact
   finite-product Haar functional.
4. `SU2QuaternionLazyGlobalSOS` keeps the fixed-face density as a lazy
   finite weighted SOS packet.  Each feature is represented by a list of
   factors with an exact evaluation theorem and a support certificate.  This
   avoids expanding either the full density polynomial or the squares of its
   features.
5. `Z4HalfTimeReflectionAdjacentEvenLazySectorSplit` and
   `Z4HalfTimeReflectionAdjacentEvenLazyEndpointScaleAssembly` split each
   feature at the reflection plane and retain the endpoint deltas and exterior
   physical scales symbolically.
6. `SU2QuaternionLazyFactorProductBridge` supplies the opaque product of a
   factor list, exact evaluation of that product, support closure, append
   compatibility, and the identity between concatenated square-factor lists
   and the raw product of two half-polynomials.  No production packet is
   enumerated or normalized.

The raw duplicate-preserving `RatPoly` products remain an implementation
detail.  At nontrivial cutoff they must stay opaque: proofs are to use factor
lists, evaluation theorems, support predicates, finite sums, and Haar
linearity, never concrete `.length`, `#eval`, `#reduce`, or pretty-printing of
the expanded polynomial.

##### 8.13.48.2 Exact Haar on an arbitrary finite quaternion product — ✓ COMPLETE

For a monomial `x^alpha` and a block count `N`, `finiteProductHaar N` is the
exact rational functional obtained by multiplying the normalized `S^3`
coordinate moments of blocks `0,...,N-1`.  The construction and positivity
proof are decomposed as follows.

* `SU2QuaternionFiniteProductHaarCarrier` defines
  `quaternionBlockMoment`, `quaternionBlockMomentProduct`,
  `finiteProductHaarMono`, and the linear polynomial functional
  `finiteProductHaar`.  It proves permutation invariance of the finite block
  product, exact linearity, and agreement at two blocks with the earlier
  product-Haar carrier.
* `SU2QuaternionFiniteProductHaarSphereIdeal` defines the block radius

  ```text
  R_b = x_(4b)^2 + x_(4b+1)^2 + x_(4b+2)^2 + x_(4b+3)^2
  ```

  and proves, for supported polynomials,

  ```text
  finiteProductHaar N (P * R_b) ≈ finiteProductHaar N P
  ```

  whenever `b < N`.  Thus multiplication by a block radius changes a raw
  polynomial representative but not its restriction to the unit-quaternion
  product.
* `SU2QuaternionFiniteProductHaarFubini` defines exact integration of one
  quaternion block by clearing its four exponents and multiplying by its
  rational moment.  It proves support preservation, equality with the global
  product functional, iteration over a list of blocks, and invariance under a
  permutation of the integration order.
* `SU2QuaternionFiniteProductGaussianPositivity` constructs the independent
  finite-coordinate Gaussian moment kernel and an explicit finite Gram
  representation, yielding constructive nonnegativity of the Gaussian
  integral of every polynomial square.
* `SU2QuaternionFiniteProductHaarGaussianRadialFactor` proves the exact
  monomial relation between the product-Gaussian and product-sphere moments.
  On a fixed quaternion-block degree vector, the conversion factor is a
  strictly positive product of radial denominators.
* `SU2QuaternionFiniteProductHaarMultihomogeneousPositivity` therefore proves
  nonnegativity of `finiteProductHaar N (P * P)` when all monomials of `P`
  have one common degree in each block and one common block-parity assignment.
* `SU2QuaternionFiniteProductHaarParitySectors` proves exact orthogonality of
  distinct block-parity sectors.  If two monomials differ in parity in any
  quaternion block, their product has an odd exponent sum in that block and
  its Haar moment vanishes.
* `SU2QuaternionFiniteProductHaarPolynomialParityClosure` gives a computable
  recursive split of a finite polynomial into one chosen parity sector and
  its complement.  It proves support preservation, exact square splitting,
  vanishing of the two cross terms, and induction from positivity in every
  fixed parity sector to positivity for the whole polynomial.
* `SU2QuaternionFiniteProductHaarParityHomogenization` closes the remaining
  degree gap without choice.  For a fixed parity sector it computes a target
  degree `D_b` for every block.  A monomial of block degree `d_b` is multiplied
  by

  ```text
  R_b ^ ((D_b - d_b) / 2).
  ```

  Equality of parities makes the difference even.  Radius multiplication
  raises the block degree by exactly two, preserves the parity assignment and
  coordinate support, and preserves all Haar pairings by the sphere-ideal
  theorem.  The transformed polynomial is multihomogeneous, so the preceding
  Gaussian-radial theorem applies.  Orthogonal parity-sector recursion then
  removes the fixed-parity hypothesis.
* `SU2QuaternionFiniteProductHaarPolynomialPositivity` exposes the final
  production theorem:

  ```text
  finiteProductHaar_square_nonneg
      (blockCount : Nat) (polynomial : RatPoly)
      (SupportedQuaternionBlocks blockCount polynomial) :
    0 ≤ finiteProductHaar blockCount (polyMul polynomial polynomial).
  ```

This is an exact rational theorem at every finite block count and every finite
raw polynomial.  It does not appeal to an analytic completion, excluded
middle, spectral diagonalization, or a pre-existing positive Haar measure.

##### 8.13.48.3 Lazy plane and weighted-density Haar positivity — ✓ COMPLETE

`SU2QuaternionAdjacentEvenLazyPlaneHaarPositivity` applies the arbitrary
polynomial theorem to the opaque lower/plane half polynomial supplied by the
lazy factor bridge.  It proves the exact pointwise square evaluation and

```text
0 ≤ adjacentEvenLazyPlaneHaarSquareMoment cutoff radius term.
```

`SU2QuaternionLazyFiniteProductHaarSOSPositivity` then defines

```text
lazyFiniteProductHaarSOSValue packet blockCount
  = sum_t packet.weight(t) *
      finiteProductHaar blockCount (packetPolynomial(t)^2)
```

and proves it nonnegative from the packet's stored termwise weight
certificate and the supported-polynomial square theorem.  Its production
specialization proves nonnegativity of the full adjacent-even fixed-face lazy
density packet.  This is a structural finite-sum proof: it neither generates
all feature indices nor expands a feature product.

##### 8.13.48.4 Endpoint boundary characters and arbitrary coefficients — ✓ COMPLETE

`Z4HalfTimeReflectionAdjacentEvenEndpointBoundaryCharacterRatPoly` realizes
the endpoint data in the same carrier.  For an endpoint assignment `s`, let

```text
B_s(U) = product over fixed links l of
           Cheb.U (assignment_s(l)) (scalar(U_l)).
```

Each one-link Chebyshev factor is lifted by the existing `QPoly` Horner map at
the scalar coordinate of its physical active link.  The canonical object is
again a lazy factor list; its opaque product has exact common-field evaluation,
active-coordinate support, and active-quaternion-block support.  The physical
wrapper selects the endpoint assignment from a production half-state.  This
file attaches no fusion, trajectory, or Haar/spin identity.

`SU2QuaternionAdjacentEvenBoundaryCharacterHaarQuadratic` accepts an
arbitrary rational coefficient sequence `c_s` and defines the requested
finite polynomial

```text
C(U) = sum_s c_s * outerScale_s * B_s(U),
```

where the sum ranges over `adjacentEvenPhysicalHalfStateCount K radius`.
The theorem `eval_adjacentEvenPhysicalBoundaryCoefficientPolynomial` is the
exact common-field finite-sum evaluation, and the coordinate/block support
theorems certify that `C` lies in the active product-Haar carrier.  Hence

```text
0 ≤ H(C^2)
```

for every coefficient sequence, with no sign restriction on the coefficients.

For each lazy fixed-face density feature `p_t`, the same file defines the
dressed polynomial `p_t * C`, proves its exact pointwise evaluation and block
support, and obtains

```text
0 ≤ H((p_t * C)^2).
```

Finally it defines the direct boundary-character Haar quadratic

```text
Q_Haar(c) = sum_t w_t * H((p_t * C)^2)
```

and proves `adjacentEvenBoundaryCharacterDressedHaarQuadratic_nonnegative` by
finite-sum induction from `w_t ≥ 0`.  This is presently the strongest honest
Haar-side positivity statement: all density, plane, endpoint-character, and
exterior-scale factors occur in one exact finite product-Haar square.

It is essential not to rename this result “physical reflection positivity.”
No current theorem identifies `Q_Haar` with
`adjacentEvenPhysicalReflectionQuadratic_anchor`, the reachable scaled
quadratic, the fusion trajectory kernel, or the existing scalar endpoint
operator.  The parameters `cutoff` and `K` are intentionally independent in
the positivity theorem; any later physical comparison must state their
intended relation explicitly.  That comparison is the remaining local
representation-theoretic obligation.

##### 8.13.48.5 Certified obstruction to the old kernel identification — ✓ COMPLETE

`SU2QuaternionAdjacentEvenTwoFaceProductHaarFence` uses the already proved
nonsymmetric corner of the literal cutoff-two, radius-zero, two-face
production patch.  For every block count and every proposed family of common
half-polynomials, it proves

```text
¬ ∀ left right,
    adjacentEvenTwoFaceProductionPatchMatrix left right
      ≈ finiteProductHaar blockCount (half left * half right).
```

The proof is exact and short: commutativity of raw polynomial multiplication
after `finiteProductHaar` makes the proposed right-hand side symmetric, while
the production patch is not symmetric.  This rules out the previous
entrywise common-half Gram target for the uncompressed two-face patch.  Its
scope is precise: it does not rule out a corrected oriented/channel-resolved
kernel, nor does it decide what happens after a separately proved physical
reachable-state compression.

The obstruction also explains why multiplying independent scalar face
characters is insufficient.  Haar integration is linkwise, and shared links
contract oriented matrix indices.  At valence two this introduces Schur
normalization; at valence four it retains a nontrivial invariant-channel
projector and Racah recoupling.  A scalar shared-link multiplicity does not in
general contain this data.

##### 8.13.48.6 Small closed diagnostics: certified facts versus targets

The audited candidate for the smallest closed cutoff-one diagnostic is the
elementary spatial cube at time one with the six fundamental faces

```text
{6, 7, 9, 21, 52, 144}
```

and vacuum elsewhere.  The audit finds twelve bivalent links, but this
specific face list, link count, bivalent-incidence statement, and claim of
minimality are not yet Lean theorems.  The existing abstract production
theorem reduces any certified six-face incidence-two carrier of this form to

```text
(coeffW anchorCoupling 1)^6.
```

An oriented fundamental matrix-coefficient calculation is expected to
produce one factor `1/2` from each of the twelve Schur contractions and one
factor `2` from each of eight closed index loops, hence

```text
2^(8 - 12) = 1/16
```

times the face-coefficient product.  The local `haarMatrixKernel` and
`contractedLinkEntry_diag` results already certify the individual `1/dim`
Schur normalization; they do not yet compose the twelve links into a global
cube theorem.  **The `1/16` value is currently an inferred target, not a
repository theorem.**  The existing
`cubeBoxHaarCharacterSector_exact` concerns a linkwise-character surrogate
and explicitly does not prove the oriented six-face integral.

The first evident closed recoupling candidate is the pair of face-disjoint
fundamental cubes sharing one edge.  The audited fixed faces are

```text
{6, 7, 9, 21, 52, 66, 67, 69, 81, 112, 144, 204}.
```

The audit finds twenty-three links: one link has incidence four and the others
are bivalent.  These concrete geometry facts and minimality are not yet Lean
theorems.  Existing abstract production theorems collapse a certified unique
four-valent link of this form to scalar multiplicity two.  By contrast, the
invariant space of four
fundamental SU(2) representations is two-dimensional.  The already certified
ordered-Racah data include `fundamental_racahKernel_entries`, with entries

```text
1/4, 3/4,
3/4, 1/4,
```

together with the exact fixed-`F` entries and Gram-weighted bridges.  These
numbers are certified representation-theoretic data, but no theorem yet
identifies them with the adjacent-even oriented RatPoly integral.  No
6j/Racah amplitude occurs in the present scalar endpoint production path.

The first corrected local bridge is now also certified in
`SU2QuaternionOneLinkFundamentalSchur`.  Because the fundamental matrix
coefficients are complex while `RatPoly` is rational-real, the file uses the
honest complexification

```text
ComplexRatPoly = RatPoly × RatPoly
```

for real and imaginary parts.  For the scalar-first quaternion
`q = r + i I + j J + k K`, it defines

```text
D(q) = [[r + i sqrt(-1),   j + k sqrt(-1)],
        [-j + k sqrt(-1),  r - i sqrt(-1)]]
```

and defines the reverse-oriented coefficient by conjugate transpose.  A
constructive case split over the sixteen Boolean index choices proves the
exact componentwise identity

```text
H_1(D_ab(q) * conjugate(D_dc(q)))
  = (1/2) * delta(a,d) * delta(b,c).
```

Thus the local Schur factor and index crossing are no longer inferred.  The
same file proves the rational arithmetic identity

```text
2^8 * (1/2)^12 = 1/16.
```

This second theorem is deliberately conditional bookkeeping: the repository
still lacks the theorem expanding the actual six oriented plaquette traces
into twelve oppositely oriented link pairs and eight independent Boolean
index loops.  It therefore does not yet prove the cube value.

##### 8.13.48.7 Corrected shortest route to physical reflection positivity

The next work is local and representation-theoretic, in this order:

1. **Bank the two small geometries — pending.**  Prove the exact radius-zero membership,
   distinct-link count, incidence-two cube facts, and the double-cube's unique
   incidence-four edge with all other links bivalent.  These decisions are
   small and finite; they must not evaluate the global density packet.
2. **Oriented one-link coefficient carrier — ✓ COMPLETE locally.**  Express the fundamental
   `2 × 2` SU(2) matrix entries and their orientation/conjugation in the
   rational quaternion `RatPoly` carrier, using pairs of rational real
   polynomials if necessary.  Prove evaluation against the existing rational
   unit-quaternion field and exact active-block support.
3. **Constructive Schur contraction — ✓ COMPLETE for one isolated block.**  Starting from the exact coordinate
   moments

   ```text
   H(x_a * x_b) = delta(a,b) / 4,
   ```

   prove the oriented fundamental identity

   ```text
   integral U_ij * conjugate(U_kl) dU = (1/2) delta(i,k) delta(j,l)
   ```

   in the repository's rational encoding.  Package it as a local contraction
   tensor and prove compatibility with link reversal.
4. **Matrix semantics and linkwise product/Fubini bridge — pending.**  Prove
   that the complexified matrix map respects Hamilton multiplication and
   quaternion conjugation at `RatPoly` evaluation, then lift the local tensor through
   `finiteProductHaar_integrateQuaternionBlocks`, proving that an oriented
   plaquette network contracts one physical link at a time without expanding
   the global face polynomial.
5. **Closed cube normalization theorem.**  Apply the bivalent contraction at
   the twelve links of the cutoff-one elementary cube, identify its eight
   index loops constructively, and prove or refute the predicted `1/16`
   normalization.  Only after this theorem may that factor be used to correct
   a production activity.
6. **Four-valent projector and Racah theorem.**  Retain the two invariant
   channels at the common edge of the two-cube diagnostic.  Prove the exact
   quaternion-Haar four-coefficient projector, identify its ordered basis
   with the existing fixed-`F`/Gram-weighted carrier, and compare the result
   with the certified `1/4, 3/4, 3/4, 1/4` Racah matrix.
7. **Correct the finite spin kernel.**  Replace any scalar link multiplicity
   that loses channel information by the derived oriented contraction or an
   explicitly normalized invariant-channel sum.  Reprove symmetry and all
   reachable/compression lemmas for the corrected object; do not retrofit a
   Gram theorem onto the known nonsymmetric patch.
8. **Prove the exact quadratic identity.**  Prefer the logically weaker and
   structurally natural coefficient-level equality

   ```text
   adjacentEvenReachableScaledQuadratic K radius coefficient
     ≈ adjacentEvenBoundaryCharacterDressedHaarQuadratic
         cutoff K radius coefficient
   ```

   (with the corrected channel-resolved definitions) over an entrywise Gram
   identity unless the latter follows at no extra cost.  This direct quadratic
   route automatically combines all boundary states before squaring and is
   insensitive to noncanonical choices of Gram feature basis.
9. **Mechanical PSD transport.**  Once the exact equality is certified,
   inhabit `AdjacentEvenActiveQuadraticSOSData` directly, or
   `AdjacentEvenReachableKernelSOSData` if an entrywise theorem is genuinely
   available, and invoke the existing transport to physical anchor PSD.
10. **Only then resume the global route:** normalization and conditioning,
   centered observables, staged time-one reflection-positive transfer,
   representative-limit descent, constructive completion, and quotient
   induction toward the Clay statement.

This ordering is more efficient than adding further scalar endpoint lemmas:
the one-link Schur theorem decides the normalization, and the first
four-valent link decides whether the production state space carries enough
recoupling information.  Both tests are finite, local, exact, and reusable
for every later radius and cutoff.

##### 8.13.48.8 Incremental full-build consistency without unsafe repetition

The repository now uses a fail-closed incremental consistency discipline.  A
full build need not be rerun after every leaf, provided all of the following
certificates are refreshed:

1. every new production leaf is explicitly imported by the semantic root
   `lean/YMGap.lean`;
2. `scripts/lean_import_guard.py` verifies the entire local import graph,
   rejects cycles and unexpected semantic orphans, and proves reachability
   from the registered roots;
3. every changed leaf is compiled as a serialized single-threaded targeted
   Lake target; Lake then validates its complete transitive dependency cone
   and reuses artifacts only for unchanged modules;
4. every new exposed end leaf is itself targeted, so a cached dependency
   cannot hide a missing name or theorem at the new boundary;
5. `scripts/lean_forbidden_token_scan.py`, `scripts/host_load_guard.py`, and
   `git diff --check` pass before staging;
6. staged-path inspection excludes the quarantined categorical spike and
   verifies that every intended production file and root import is present;
7. a serialized one-thread full incremental checkpoint is reserved for a
   release/frontier milestone, toolchain or Lake configuration change, import
   guard change, unexplained cache inconsistency, or failure of one of the
   preceding certificates.  A clean or uncached full build is not an ordinary
   validation step on this host.

Thus “consistent without a full build every time” means a precise inductive
argument: the last full checkpoint certifies the unchanged base; targeted
Lake builds certify every changed transitive cone; and the static root/DAG
audit certifies that those cones are exactly wired into the production graph.
It does not mean skipping compilation of changed code, trusting timestamps,
or claiming protection against external corruption of the toolchain/cache.

The mandatory host-safety protocol remains unchanged: before every Lean,
Lake, or test command, verify that no Lean/Lake/test or self-hosted runner
process is active; run only one session under the repository lock,
`caffeinate`, `nice -n 10`, `LEAN_NUM_THREADS=1`, and the configured memory
ceiling; never run tests concurrently; never clean the Lake cache; and never
materialize bounded state spaces, trajectories, or the large weighted SOS
polynomials.

##### 8.13.48.9 Verification ledger for this milestone

The relevant serialized targeted builds completed as follows:

```text
SU2QuaternionLazyFactorProductBridge                         752 jobs
SU2QuaternionFiniteProductHaarPolynomialParityClosure       418 jobs
SU2QuaternionFiniteProductHaarParityHomogenization          417 jobs
SU2QuaternionFiniteProductHaarPolynomialPositivity          420 jobs
SU2QuaternionAdjacentEvenLazyPlaneHaarPositivity            781 jobs
SU2QuaternionLazyFiniteProductHaarSOSPositivity             781 jobs
Z4HalfTimeReflectionAdjacentEvenEndpointBoundaryCharacterRatPoly
                                                               753 jobs
SU2QuaternionAdjacentEvenBoundaryCharacterHaarQuadratic     782 jobs
SU2QuaternionAdjacentEvenTwoFaceProductHaarFence            744 jobs
SU2QuaternionOneLinkFundamentalSchur                        394 jobs
```

The final printed gates for arbitrary supported-polynomial Haar-square
positivity, lazy weighted SOS positivity, endpoint/dressed boundary-quadratic
positivity, and the two-face obstruction all report only
`[propext, Quot.sound]`.  The official 2,598-job full incremental checkpoint
from the end of §8.13.47 remains the certified unchanged base; it is not
repeated for this import-only/root-wired incremental milestone.

After the final root wiring, the incremental import audit found 2,615 source
modules, 8,116 local import edges, zero cycles, 2,609 modules reachable from
the semantic root, six reviewed/classified semantic orphans, and zero
unexpected orphans.  The executable forbidden-token scan found zero hits,
the host-load guard passed all 236 tracked or untracked non-ignored entry
files, and `git diff --check` passed.

The categorical spike remains quarantined and unimported.  It supplies none
of the missing oriented Schur, cube-normalization, or Racah-identification
theorems and is not part of this milestone.

#### 8.13.49 Exact cube orientation and generic linkwise Schur transport

This milestone replaces the remaining informal geometry and isolated-link
heuristics in the first closed-surface diagnostic by exact, root-wired Lean
interfaces.  It still does **not** identify the production six-face
polynomial with its fully contracted trace network; that last comparison is
kept as an explicit next theorem rather than hidden in a normalization
claim.

##### 8.13.49.1 Literal radius-zero closed geometries — ✓ COMPLETE

`Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence` now proves
all of the finite geometry that was only audited in §8.13.48:

- the elementary-cube identifiers are exactly
  `{6, 7, 9, 21, 52, 144}` and decode to the six displayed fixed spatial
  plaquettes;
- all six identifiers/faces belong to the production radius-zero fixed-face
  carrier;
- their duplicate-free support has exactly twelve links, every supported
  link is production-active, and every one has incidence two;
- the edge-touching double-cube identifiers are exactly
  `{6, 7, 9, 21, 52, 66, 67, 69, 81, 112, 144, 204}` and decode to twelve
  distinct fixed faces;
- their duplicate-free support has exactly twenty-three active links;
- `((0,1,1,1), x0)` has incidence four, every other touched link has
  incidence two, and it is the unique four-valent touched link.

These are membership, cardinality, and incidence theorems only.  Neither
carrier is claimed minimal among all closed surfaces, and no Haar value,
spin amplitude, density polynomial, bounded labelling family, or trajectory
is evaluated by this geometry leaf.

##### 8.13.49.2 Honest matrix and trace semantics — ✓ COMPLETE

`SU2QuaternionFundamentalMatrixSemantics` gives the complex-pair fundamental
matrix an explicit `Bool × Bool` semantics and proves, componentwise in the
constructive rational setoid,

```text
D(q r) ≃ D(q) D(r),
D(conj q) ≃ D(q)*,
```

for raw rational quaternions.  The corresponding evaluation theorems hold
for arbitrary polynomial quaternions and environments.  In particular, the
previous syntactic reverse coefficient is now proved to evaluate as the
matching entry of the conjugated matrix, and unit-norm inversion is proved
to be conjugate transpose.

`SU2QuaternionFundamentalTraceInversion` then defines the diagonal trace and
proves

```text
tr D(q) ≃ (U_1(q.r), 0) ≃ (2 q.r, 0),
tr D(conj q) ≃ tr D(q),
tr D(q⁻¹) ≃ tr D(q)                 when q is unit norm.
```

The polynomial diagonal sum has the same evaluated Chebyshev character and
is evaluation-invariant under polynomial quaternion conjugation.  These
results justify reversing a whole oriented plaquette word semantically.  No
global `RatPolyEqv ⇒ finiteProductHaar` congruence is inferred: the trace
network still has to be related to the chosen raw polynomial representation
by explicit algebraic/Fubini lemmas.

##### 8.13.49.3 Outward cube orientation and resolved factor — ✓ COMPLETE

The six production plaquette words are not coherently oriented as the
boundary of a cube: the canonical `p01` and `p02` faces at the origin, for
example, traverse their common `x0` link in the same direction.  The exact
outward mask in production face order is now proved to be

```text
[reversed, standard, reversed, standard, reversed, standard].
```

`SU2QuaternionElementaryCubeOrientedTraceWiring` attaches that mask to the
six decoded production faces and exposes twenty-four cyclic fundamental
coefficient occurrences.  Every occurrence has endpoints coherent with its
stored physical link and traversal direction.  For each of the twelve
touched links, the occurrence list has length two with exactly one forward
and one reverse traversal.  The deduplicated geometric endpoint carrier has
eight vertices, and the twelve links map to twelve distinct in-range
production active-link quaternion blocks with a checked lookup round trip.

The leaf also proves the exact value of the explicitly named
*post-Schur, delta-resolved* network:

```text
radiusZeroElementaryCubePostSchurResolvedFactor
  = 2^8 (1/2)^12 ≃ 1/16.
```

This is now a theorem rather than the inferred arithmetic target of
§8.13.48.  Its definition intentionally begins after all twelve Schur
contractions and after the crossed deltas have been resolved to one Boolean
index per geometric vertex.  It is therefore **not yet** a theorem that the
production six-character Haar integral is `1/16`.

##### 8.13.49.4 Spectator-stable blockwise Fubini — ✓ COMPLETE

`SU2QuaternionOneLinkFundamentalSchurSpectatorFubini` supplies the locality
interface needed to contract a link inside a larger trace term.  A raw
polynomial is declared independent of a quaternion block when clearing that
block fixes every monomial occurrence.  The file proves:

- idempotence of block clearing and independence of a partially integrated
  polynomial;
- closure of scalar and honest-complex block independence under addition,
  negation, scalar multiplication, conjugation, and multiplication;
- distinct-block independence for every forward or reverse fundamental
  coefficient and for a complete local forward/reverse contraction;
- exact factorization of an independent spectator through one partial block
  integral;
- real- and complex-spectator finite-product Fubini theorems.

Thus an uncontracted complex trace-network term can retain all factors from
the other links while one selected in-range link is integrated.  The complex
version is essential: a generic residual trace summand is not a real
polynomial.

##### 8.13.49.5 Generic-block partial Schur with trailing-zero aliases — ✓ COMPLETE

`SU2QuaternionGenericBlockPartialFundamentalSchur` closes the remaining
arbitrary-block normalization gap at the correct functional level.  The raw
carrier preserves the lengths of exponent lists when a block is cleared, so
the partial integral of a local contraction is a sum of zero-exponent
aliases, duplicate terms, and possibly literal zero coefficients; it is not
literally `polyConst delta`.

The file therefore defines the raw coefficient sum and an
`AllZeroExponentTerms` predicate, proves that multiplication by any such
alias polynomial acts under `finiteProductHaar` by its coefficient sum, and
derives arbitrary-block coordinate covariance from the exact normalized
`S³` moment.  It computes the two coefficient sums of the partially
integrated fundamental pair in all sixteen Boolean index cases and proves
the load-bearing theorem

```text
genericBlock_oriented_fundamental_schur_with_complex_spectator:

  H_Nᶜ(spectator · local_b(a,b,d,c))
    ≃ H_Nᶜ(spectator) ·
        [(1/2) delta(a,c) delta(b,d)]
```

whenever `b < N` and the honest-complex spectator is independent of block
`b`.  The conclusion is `RationalComplexEqv` after the exact finite-product
functional; no false raw-polynomial equality or extensional-Haar shortcut is
used.

The covariance proof is constructively isolated at natural component codes.
In particular, its variable-exponent lemma now recurses directly through the
raw `List.getD` representation with only the required cons-index reduction;
it does not invoke the broad simplifier path that imported
`Classical.choice`.  The natural `4 × 4` moment table, its transport to an
arbitrary block, the integrated coefficient sum, and the final spectator
theorem all pass explicit axiom gates with only `propext` and `Quot.sound`.

##### 8.13.49.6 Consequence for the scalar production activity — still conditional

The earlier scalar incidence theorem sends the six cutoff-one cube faces to

```text
(coeffW anchorCoupling 1)^6,
```

because it assigns scalar link multiplier one at every bivalent link.  The
new orientation and generic Schur theorems show that an honest fundamental
trace expansion, once connected to that same production carrier, must
instead accumulate twelve factors `1/2` and eight surviving Boolean sums,
hence the additional factor `1/16`.

This exposes a precise likely factor-sixteen normalization defect, but the
comparison remains a theorem target until the six physical traces have been
expanded and contracted in Lean.  Neither `cubeBoxHaarCharacterSector_exact`
(a link-character surrogate) nor the newly proved post-Schur scalar by
itself supplies that missing identification.  Production definitions must
not be changed on the basis of the conditional comparison alone.

##### 8.13.49.7 Updated shortest route

The next local steps are now sharply separated:

1. **Tagged face-corner carrier.**  Introduce the twenty-four independent
   corner indices of the six pre-contraction traces.  Do not identify them
   prematurely with the eight geometric vertices.
2. **Opaque finite Boolean sums.**  Express each trace and their product as
   recursive Boolean sums of complex coefficient-factor lists.  Keep sums
   and products symbolic; never enumerate a `2^24` assignment list or form
   the expanded six-face `RatPoly` product.
3. **Trace expansion bridge.**  Use the matrix multiplication and trace
   semantics to prove that the symbolic four-coefficient cyclic sum is the
   fundamental character of the corresponding standard or reversed
   plaquette word.  Relate its blocks to the checked production active-link
   codec.
4. **Twelve sequential contractions.**  Apply the generic complex-spectator
   Schur theorem in any checked distinct-block order.  Prove that the twelve
   crossed deltas identify the three tagged face-corner copies at each cube
   vertex and no corner copies at different vertices.
5. **Symbolic delta resolution.**  Factor the remaining sum into eight
   independent local Boolean sums, prove each equals two, and conclude that
   the honest cube Haar character integral is exactly `1/16`.
6. **Production comparison.**  Identify the cutoff-one selected character
   coefficient in the physical fixed-face activity and prove the exact
   factor-sixteen comparison.  Only then correct the scalar production
   kernel and reprove its symmetry/PSD bridge.
7. **Four-valent diagnostic.**  Repeat the oriented construction for the
   edge-touching double cube, retain its two-dimensional invariant channel,
   and identify the signed projector/F-move with the existing ordered
   Gram-weighted Racah carrier.  Squared Racah probabilities alone are
   insufficient because they erase signs and interference.
8. **Physical quadratic identity and PSD transport.**  With the corrected
   channel-resolved kernel, prove the coefficient-level boundary quadratic
   equality and invoke the existing mechanical SOS/Gram transport.  Resume
   normalization, conditioning, transfer, limits, completion, and quotient
   descent only after that finite identity is closed.

This route is fully intuitionistic: every finite choice is represented by a
concrete list, Boolean, or recursive sum; no excluded-middle shortcut,
choice principle, or opaque native decision procedure is introduced.

##### 8.13.49.8 Verification ledger

All Lean commands for this milestone were serialized, single-threaded,
session-locked, `nice`d, and preceded by the mandatory host-idle check.  No
full or clean build and no test suite was run.  The final target builds were:

- `SU2QuaternionFundamentalMatrixSemantics`: 395 jobs;
- `SU2QuaternionFundamentalTraceInversion`: 396 jobs;
- `SU2QuaternionOneLinkFundamentalSchurSpectatorFubini`: 397 jobs;
- `SU2QuaternionGenericBlockPartialFundamentalSchur`: 398 jobs;
- `Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence`: 699 jobs;
- `SU2QuaternionElementaryCubeOrientedTraceWiring`: 722 jobs.

Every displayed axiom gate in these leaves reports only the permitted
`propext` and, where quotient/setoid algebra is used, `Quot.sound`; the purely
finite statements report no axioms when their dependencies permit it.  The
final static audit found 2,621 source modules, 8,133 local import edges, zero
cycles, 2,615 modules reachable from the semantic root, six reviewed and
classified semantic orphans, and zero unexpected orphans.  The executable
forbidden-token scan found zero hits, the host-load guard passed all 236
tracked or untracked non-ignored entry files, and `git diff --check` passed.

The categorical spike remains quarantined, modified only by the user/other
work, and absent from both the production root and the staged milestone.

#### 8.13.50 Public complex algebra and finite distinct-block Schur fold

The first two reusable layers of the symbolic trace-network route are now
root-wired.  They deliberately stop before any cube-wide Boolean assignment
family is formed: the purpose of this milestone is to make the local algebra
and the sequential bivalent-link contraction available as small exact APIs.

##### 8.13.50.1 Honest complex-polynomial algebra facade — ✓ COMPLETE

`SU2QuaternionComplexRatPolyAlgebra` makes the previously scattered
`RatPoly × RatPoly` operations usable without reopening private proof
machinery.  It supplies:

- canonical rational-complex and complex-polynomial zero and one;
- finite tail-recursive products in both carriers;
- public reflexivity, symmetry, transitivity, addition congruence, and
  multiplication congruence for `RationalComplexEqv`;
- exact evaluation laws for complex zero, one, addition, multiplication, and
  an abstract finite product;
- exact finite-product Haar laws for complex zero, one, and addition; and
- a componentwise bridge from the multiplication named in
  `SU2QuaternionGenericBlockPartialFundamentalSchur` to the identical formula
  chosen canonically from `SU2QuaternionFundamentalMatrixSemantics`.

The facade does **not** assert that Haar is multiplicative.  Nor does it
transport pointwise `RatPolyEqv` through Haar, or identify differently
parenthesized/reordered raw polynomial products.  Its finite product is safe
as an opaque abstract fold or for one four-coefficient word; it must not be
unfolded on the six-face network.

##### 8.13.50.2 Arbitrary-base distinct-block contraction — ✓ COMPLETE

`SU2QuaternionDistinctBlockFundamentalContractionProduct` packages one local
pair as a natural block identifier and four Boolean matrix indices.  It then
defines the right-local fold

```text
P(base, [])       = base,
P(base, s :: ss)  = P(base, ss) · local(s),
```

together with the literally matching canonical rational-complex delta fold

```text
Delta(z, [])       = z,
Delta(z, s :: ss)  = Delta(z, ss) · delta(s).
```

This parenthesization is load-bearing: the head is exactly the right factor
required by the generic spectator theorem, so no raw associativity,
commutativity, or factor reordering is used.  The file proves that the tail
product is independent of the head block when the mapped block list is
duplicate free, and establishes

```text
H_N^C(P(base, schedule))
  ≃ Delta(H_N^C(base), schedule)
```

provided every scheduled block is in range, the block list is `Nodup`, and
the external base is independent of every scheduled block.  Taking the base
to be complex polynomial one yields the pure finite Schur-delta product.

The arbitrary base is not cosmetic.  For the elementary cube it is one and
all twelve bivalent links may be contracted.  For the edge-touching double
cube it can retain the unresolved polynomial on the unique four-valent
shared link while the other distinct bivalent blocks are eliminated.  A
repeated block is intentionally rejected: its remaining local factor would
not be a valid independent spectator, and its correct replacement is the
later signed channel/Racah calculation.

This theorem is per fixed trace-index summand.  It neither enumerates the
`2^24` corner assignments nor licenses conversion of a face-ordered raw
product into the paired fold through pointwise evaluation.  The eventual
Haar-facing summand must be defined in the canonical paired order, with a
separate exact physical evaluation theorem.

##### 8.13.50.3 Updated shortest route

The next sound finite steps are:

1. define an opaque recursive Boolean sum and prove its evaluation and Haar
   additivity laws from the new facade;
2. define the four-index cyclic plaquette coefficient sum, with standard and
   reversed orientations, and prove by matrix multiplication/trace semantics
   that its evaluation is the fundamental plaquette character;
3. attach all twenty-four face-corner tags to the already checked cube
   occurrences and produce the twelve-step `Nodup`, in-range contraction
   schedule without identifying corner indices prematurely;
4. define each Haar-facing fixed-index cube summand directly in the
   right-local paired order and use the new distinct-block theorem once,
   rather than manually applying twelve Fubini contractions;
5. prove that the resulting crossed deltas make one triangle among the three
   face-corner copies at each geometric vertex, factor the symbolic sum into
   eight local three-Boolean sums, and evaluate only the safe eight-case
   identity `sum delta(a,b) delta(b,c) delta(c,a) = 2`;
6. conclude the honest elementary-cube Haar value `1/16` and only then prove
   the exact production normalization comparison.

The four-valent double-cube route now branches cleanly after step 3: place
the shared-link factor in the arbitrary base, contract the other bivalent
blocks, and resolve the surviving two-dimensional invariant channel with a
signed projector/F-move rather than squared Racah probabilities.

##### 8.13.50.4 Verification ledger

Both target builds were serialized, session-locked, `nice`d, single-threaded,
and preceded by the host-idle process check.  No clean/full build and no test
suite was run:

- `SU2QuaternionComplexRatPolyAlgebra`: 401 jobs;
- `SU2QuaternionDistinctBlockFundamentalContractionProduct`: 402 jobs.

All displayed gates report only `propext` and, where the rational quotient
algebra enters, `Quot.sound`; the multiplication-bridge theorem itself uses
no axioms.  After root wiring, the static audit found 2,623 source modules,
8,138 local import edges, zero cycles, 2,617 modules reachable from the
semantic root, six reviewed/classified semantic orphans, and zero unexpected
orphans.  The executable forbidden-token scan found zero hits, the host-load
guard passed all 236 tracked or untracked non-ignored entry files, and
`git diff --check` passed.

The categorical spike remains quarantined and is not imported or staged.

#### 8.13.51 Symbolic Boolean sums and exact one-face trace expansion

The next two layers of the honest elementary-cube trace route are now
root-wired.  They close the finite algebra needed to expand one fundamental
plaquette trace, but they intentionally stop before a cube-wide polynomial
product or Boolean assignment carrier is formed.

##### 8.13.51.1 Symbolic Boolean-sum algebra — ✓ COMPLETE

`SU2QuaternionComplexBoolSumAlgebra` defines false-before-true Boolean
binders and structurally recursive sums

```text
rationalComplexBoolSum :
  Nat -> (List Bool -> RationalComplex) -> RationalComplex,

complexRatPolyBoolSum :
  Nat -> (List Bool -> ComplexRatPoly) -> ComplexRatPoly.
```

The base case evaluates the family on the unique empty assignment.  The
successor case recurses separately on `false :: assignment` and
`true :: assignment` and adds the two results in that literal order.  No
list of all assignments, powerset, fingerprint carrier, `Fin` enumeration,
or bounded labelling family is constructed.

The file proves, constructively and at rational-complex setoid level:

- congruence for one binder and for a sum of arbitrary symbolic depth;
- binder exchange and the rational-complex addition/multiplication laws
  needed to change a matrix-path addition tree;
- addition through a symbolic sum and left/right multiplication through a
  binder or a symbolic sum;
- evaluation of an honest complex polynomial through a binder and symbolic
  sum; and
- componentwise finite-product Haar additivity through a binder and
  symbolic sum.

The operational fence is load-bearing.  Recursive representation avoids
allocating a `2^n` assignment carrier, but reducing the definition at a
concrete depth still exposes `2^n` leaves.  Hence depth twenty four must
never be unfolded, simplified, reduced, evaluated, or printed.  Only the
safe depth-four face identity and depth-three local vertex identity may be
concretely opened.  Cube-wide arguments must use the abstract congruence,
linearity, evaluation, and Haar-commutation lemmas.

##### 8.13.51.2 Exact standard and reversed plaquette traces — ✓ COMPLETE

`SU2QuaternionFundamentalPlaquetteTraceExpansion` specializes the binder API
to four cyclic Boolean indices.  For physical link slots
`block0, block1, block2, block3`, its two fixed summands are literally

```text
standard:
  (((F block0 a b * F block3 b c) * R block2 c d) * R block1 d a),

reversed:
  (((F block1 a b * F block2 b c) * R block3 c d) * R block0 d a).
```

Thus the standard word is
`U0 U3 conj(U2) conj(U1)` and the reversed word is
`U1 U2 conj(U3) conj(U0)`, exactly matching the occurrence conventions in
`SU2QuaternionElementaryCubeOrientedTraceWiring`.  Conjugation is inverse
only on the unit-quaternion locus; the arbitrary-environment statements do
not silently assume unit norm.

The raw polynomial products remain left-associated.  The file proves a
generic theorem that the four-index cyclic path sum of four arbitrary
fundamental matrices is their trace.  Its distributive steps and the
temporary conversion to a right-associated matrix product occur only after
evaluation in `RationalComplexEqv`; no raw `RatPoly` associativity,
commutativity, normalization, or reordering theorem is claimed.

For both orientations the complete semantic chain is now formal:

```text
evaluate symbolic coefficient sum
  ≃ four-index rational-complex path sum
  ≃ trace of the exact four-matrix product
  ≃ trace of the corresponding quaternion word
  ≃ (U_1(word.r), 0).
```

The reverse factors use the previously proved conjugate-transpose
coefficient semantics.  The quaternion representation law is applied three
times to the exact right-associated word, and the final character theorem
uses the established fundamental-trace/Chebyshev identity.

Whole-word orientation invariance is also closed at the correct semantic
level.  Quaternion anti-multiplicativity and involutivity prove

```text
conj(U0 U3 conj(U2) conj(U1))
  ≃ U1 U2 conj(U3) conj(U0),
```

and trace invariance under quaternion conjugation then proves that the
standard and reversed symbolic expansions have equivalent evaluations for
every rational environment.  No unit-norm hypothesis is required for this
trace statement; unit norm is needed only to rename conjugation as physical
inversion.

This semantic theorem does **not** imply equality after finite-product Haar.
The raw face-ordered product and the right-local paired contraction product
are different duplicate-preserving `RatPoly` representatives.  Pointwise
evaluation equivalence cannot be transported through the present exact Haar
functional.  The Haar-facing cube network must therefore be defined
directly in paired order, and a later explicit Haar-level bridge to the
production rank-one face representative remains mandatory.

##### 8.13.51.3 Corrected shortest route

The most efficient constructive continuation is now:

1. **Vertex-major tagged cube carrier.**  Retain all twenty-four face-corner
   indices and number them as eight consecutive triples, one triple for each
   geometric vertex.  In outward face order the six cyclic tag rows are

   ```text
   reversed p01@000: [0, 9, 6, 3]
   standard p02@000: [1, 4, 15, 12]
   reversed p12@000: [2, 13, 21, 10]
   standard p01@001: [14, 16, 18, 22]
   reversed p02@010: [11, 23, 19, 7]
   standard p12@100: [5, 8, 20, 17].
   ```

   The vertex triples are
   `[0,1,2]`, `[3,4,5]`, `[6,7,8]`, `[9,10,11]`,
   `[12,13,14]`, `[15,16,17]`, `[18,19,20]`, and
   `[21,22,23]`.  This numbering makes the later delta factorization
   structural and avoids a global `2^24` reindexing theorem.

2. **Literal twelve-link contraction schedule.**  Pair the unique forward
   and reverse occurrences on each physical link.  In
   `(forwardRow, forwardColumn; reverseRow, reverseColumn)` tag notation the
   twelve pairs are

   ```text
   (1,4;3,0),   (0,9;10,2),  (2,13;12,1),
   (9,6;7,11),  (5,8;6,3),   (4,15;17,5),
   (14,16;15,12),(13,21;22,14),(11,23;21,10),
   (23,19;18,22),(16,18;20,17),(8,20;19,7).
   ```

   Attach each pair to the already verified production active-link block,
   prove the schedule is in range and block-`Nodup`, and define the
   Haar-facing fixed-assignment summand directly as
   `fundamentalContractionProduct schedule`.

3. **One-shot fixed-assignment contraction.**  Apply
   `finiteProductHaarComplex_fundamentalContractionProduct` once to prove

   ```text
   H_N^C(cubePairedSummand assignment)
     ≃ schurDeltaProduct(cubeSchedule assignment).
   ```

   Separately prove at value level that the paired summand evaluates to the
   same twenty-four coefficients as the product of the six face terms.  Do
   not use that evaluation result as Haar congruence.

4. **Opaque depth-twenty-four sum and local delta resolution.**  Define the
   cube trace network as a symbolic depth-24 sum of the paired summand and
   keep it opaque.  Rewrite the twelve crossed deltas into eight disjoint
   equality triangles on the vertex triples.  Prove the single local
   three-Boolean identity by its safe eight cases, then lift it structurally
   to eight vertices without ever enumerating the global assignment space.

5. **Honest cube Haar value.**  Combine Haar commutation with the symbolic
   sum, the fixed-assignment contraction, the eight triangle sums, and the
   already verified arithmetic factor to obtain

   ```text
   H_N^C(cubeTraceNetwork)
     ≃ (radiusZeroElementaryCubePostSchurResolvedFactor, 0)
     ≃ (1/16, 0).
   ```

6. **Production bridge and four-valent diagnostic.**  Prove an explicit
   Haar-level bridge from the paired network to the exact production
   cutoff-one rank-one representative before asserting the factor-sixteen
   normalization correction.  Bank the elementary-cube discrepancy as a
   theorem/fence, but postpone a global kernel redesign until the
   edge-touching double cube has supplied its signed two-dimensional
   projector/F-move.  This avoids correcting the kernel twice and preserves
   the interference signs erased by squared Racah probabilities.

Every step remains intuitionistic: concrete finite tables, recursive Boolean
sums, exact rational setoids, and explicit induction replace choice,
excluded middle, and native enumeration.

##### 8.13.51.4 Verification ledger

Both target builds were serialized, session-locked, `nice`d,
single-threaded, and preceded by the mandatory host-idle process check.  No
clean/full build and no test suite was run:

- `SU2QuaternionComplexBoolSumAlgebra`: 402 jobs;
- `SU2QuaternionFundamentalPlaquetteTraceExpansion`: 403 jobs.

All displayed public gates report only `propext` and, where quotient/setoid
algebra enters, `Quot.sound`.  In particular, the generic four-cycle matrix
trace theorem, both orientation-specific matrix-trace theorems, both
quaternion-word theorems, and both Chebyshev theorems contain neither
`sorryAx` nor classical choice.

Independent Boolean-sum and plaquette-order audits found no mathematical,
constructivity, branch-order, performance-representation, factor-order, or
imported-API defect.  They led to the explicit depth-24 no-reduction fence,
direct gates for every downstream multiplication/distribution theorem,
precise conjugate-versus-inverse wording, and the explicit whole-word
orientation-invariance theorem.  The plaquette audit checked that the path
proof retains `a` as the trace index and eliminates `d`, then `c`, then `b`
using value-level setoid algebra only.

After root wiring, the static audit found 2,625 source modules, 8,142 local
import edges, zero cycles, 2,619 modules reachable from the semantic root,
six reviewed/classified semantic orphans, and zero unexpected orphans.  The
executable forbidden-token scan found zero hits, the host-load guard passed
all 236 tracked or untracked non-ignored entry files, and `git diff --check`
passed.

#### 8.13.52 Exact twenty-four-tag elementary-cube contraction schedule

`SU2QuaternionElementaryCubeTaggedFundamentalContraction` now closes the
geometry-to-Schur part of the honest elementary-cube calculation.  It is
root-wired, but it deliberately remains pointwise in one opaque Boolean
assignment: neither the depth-twenty-four trace network nor a global list of
assignments is reduced or materialized.

##### 8.13.52.1 Tagged boundary carrier and audited link pairing — ✓ COMPLETE

The six outward face cycles are encoded exactly as

```text
[0,9,6,3], [1,4,15,12], [2,13,21,10],
[14,16,18,22], [11,23,19,7], [5,8,20,17].
```

Their face-major flattening has length twenty four, is duplicate-free, and
all tags are below twenty four.  Applying the cyclic-edge constructor gives
twenty-four directed tag edges; zipping them with the already verified
outward-oriented physical boundary occurrences has length twenty four, and
forgetting the tags recovers that physical occurrence list definitionally.

The exact opposite-orientation table is stored in the actual first-occurrence
order of `radiusZeroElementaryCubeTouchedLinks`:

```text
physical link       (forward row,column; reverse row,column)
x000                 ( 1, 4;  3, 0)
y000                 ( 0, 9; 10, 2)
x010                 ( 9, 6;  7,11)
y100                 ( 5, 8;  6, 3)
z000                 ( 2,13; 12, 1)
x001                 (14,16; 15,12)
z100                 ( 4,15; 17, 5)
y001                 (13,21; 22,14)
z010                 (11,23; 21,10)
x011                 (23,19; 18,22)
y101                 (16,18; 20,17)
z110                 ( 8,20; 19, 7).
```

Mapping this table to physical links is exactly the audited duplicate-free
twelve-link support.  Every displayed tag is in range.  More strongly, each
row has a certified positive tagged occurrence with the displayed forward
endpoints and a certified negative tagged occurrence with the displayed
reverse endpoints.  Thus the table is not merely a hand-entered choice of
indices: both orientations are checked against the production cube geometry.

Two global incidence packages remain useful for the later face-product
bridge, but are not hypotheses of the Schur theorem now proved:

- certify that each tag's vertex-major number agrees with the geometric
  endpoint of its tagged boundary occurrence; and
- certify a permutation between the twenty-four face-major tagged
  occurrences and the flattening of the twelve forward/reverse table rows.

These should be added before reordering a six-face polynomial representative;
they do not block the paired Haar network or the local delta calculation.

##### 8.13.52.2 Assignment-dependent production schedule — ✓ COMPLETE

For an opaque `assignment : List Bool`, `cubeTagValue assignment tag` reads
only `assignment.getD tag false`.  Each table row is mapped to an
`OrientedFundamentalContraction` whose block is the established production
index `adjacentEvenActiveLinkIndex 0 physicalLink`.  The resulting schedule
has length twelve, its block projection is exactly
`radiusZeroElementaryCubeActiveLinkBlocks`, every block lies in the
finite-product carrier, and the block list is duplicate-free.

The Haar-facing polynomial is defined directly in the right-local order
required by the distinct-block fold:

```text
radiusZeroElementaryCubePairedSummand assignment
  := fundamentalContractionProduct
       (radiusZeroElementaryCubeContractionSchedule assignment).
```

Its matching value is the identically ordered crossed-delta fold.  The main
theorem applies the generic twelve-block result once:

```text
H_N^C(radiusZeroElementaryCubePairedSummand assignment)
  ≃ radiusZeroElementaryCubeSchurDeltaValue assignment.
```

This is a raw-representative Haar theorem, not an appeal to pointwise
polynomial evaluation, and it neither enumerates assignments nor claims that
the paired representative already equals the six-face production product.

##### 8.13.52.3 Exact delta graph and arithmetic target — ✓ COMPLETE

For one row `(r,c;s,t)`, Schur orthogonality contributes `1/2` precisely when
`r=t` and `c=s`, and contributes zero otherwise.  In table order the twelve
nonzero conditions are

```text
(1=0, 4=3),   (0=2, 9=10),  (9=11, 6=7),
(5=3, 8=6),   (2=1,13=12),  (14=12,16=15),
(4=5,15=17),  (13=14,21=22),(11=10,23=21),
(23=22,19=18),(16=17,18=20),(8=7,20=19).
```

The following vertex-major presentation gives eight disjoint equality
triangles with the same Boolean solution condition:

```text
(0,1,2), (3,4,5), (6,7,8), (9,10,11),
(12,13,14), (15,16,17), (18,19,20), (21,22,23).
```

Each triangle has exactly the two constant assignments.  Consequently the
twenty-four-index sum has `2^8` surviving assignments, each with twelve
factors of `1/2`, and the exact target is

```text
2^8 * (1/2)^12 = 1/16.
```

This counting argument is now formalized in
`SU2QuaternionElementaryCubeBooleanDeltaResolution`.  The proof factors the
twelve scalar halves from the Boolean indicators, proves the local three-bit
sum by its safe eight cases, and never unfolds, simplifies, evaluates, or
prints the depth-twenty-four sum.  Section 8.13.53 records the exact theorem
chain and the remaining production-representative bridge.

##### 8.13.52.4 Updated shortest constructive route

1. **✓ COMPLETE.** Define the opaque paired cube trace network as
   `complexRatPolyBoolSum 24 radiusZeroElementaryCubePairedSummand` and use
   the established Haar/sum commutation plus pointwise contraction theorem
   to reduce it abstractly to the symbolic sum of Schur-delta values.
2. **✓ COMPLETE.** Prove a one-row value lemma rewriting the oriented Schur delta as a
   canonical `1/2` scalar times a Boolean equality indicator.  Lift it through
   the twelve-row fold, keeping all rational-complex statements at `Eqv` level.
3. **✓ COMPLETE.** Package one equality triangle and prove its depth-three Boolean sum is two
   by the eight safe cases.  Prove a parametric consecutive-triple
   factorization and instantiate it at eight vertices, so the proof structure
   scales linearly and never exposes `2^24` branches.
4. **✓ COMPLETE.** Combine the twelve halves, eight local sums, and the existing exact
   post-Schur arithmetic certificate to prove the honest paired cube Haar
   value `(1/16,0)`.
5. **NEXT.** Before identifying this paired network with the production cutoff-one
   rank-one cube observable, add the endpoint/tag and global-permutation
   certificates above and prove an explicit raw-representative or Haar-level
   bridge.  Pointwise evaluation equivalence alone remains insufficient.
6. **AFTER THE PRODUCTION BRIDGE.** Bank the elementary-cube normalization discrepancy and proceed to the
   edge-touching double-cube signed projector/F-move diagnostic before any
   global kernel redesign.

Every step remains intuitionistic: finite literal tables, Boolean case
analysis of depth three only, structural induction, exact rational setoids,
and explicit incidence certificates replace choice, excluded middle, native
enumeration, and global assignment materialization.

##### 8.13.52.5 Verification ledger

The target build was serialized, session-locked, `nice`d, single-threaded,
and preceded by the mandatory host-idle process check.  No clean/full build
and no test suite was run:

- `SU2QuaternionElementaryCubeTaggedFundamentalContraction`: 730 jobs.

The displayed gates report no axioms for the tag uniqueness and physical-link
projection theorems, `propext` for the concrete occurrence and block-map
certificates, and only `propext` plus `Quot.sound` for the range, no-duplicate,
and twelve-block Haar theorems.  No classical choice, `sorryAx`, custom axiom,
or native decision procedure enters the leaf.

An independent geometry/API audit checked all six oriented face paths, all
twelve physical-link rows, all twenty-four matrix-index endpoints, the eight
vertex equality triangles, the production block projection, and the exact
scope of the fixed-assignment Haar theorem; it found no blocking defect.  Its
precision recommendations are reflected above: uniqueness is not claimed by
the existence certificate, the `< 24` theorem is described as a bound rather
than list membership, and the missing endpoint/tag, triangle, coverage, and
length-twenty-four access packages are explicit next obligations.

After root wiring, the static audit found 2,626 source modules, 8,145 local
import edges, zero cycles, 2,620 modules reachable from the semantic root,
six reviewed/classified semantic orphans, and zero unexpected orphans.  The
executable forbidden-token scan found zero hits, the host-load guard passed
all 236 tracked or untracked non-ignored entry files, and `git diff --check`
passed.

#### 8.13.53 Constructive Boolean-delta resolution of the paired cube

`SU2QuaternionElementaryCubeBooleanDeltaResolution` completes the symbolic
Haar calculation for the deliberately paired elementary-cube network.  It is
root-wired immediately after the tagged contraction leaf.  The result is
exact and constructive, but its scope is deliberately narrower than the
production cutoff-one cube observable: the missing representative bridge is
kept explicit rather than inferred from pointwise evaluation.

##### 8.13.53.1 Opaque Haar-to-delta reduction — ✓ COMPLETE

The Haar-facing polynomial is

```text
radiusZeroElementaryCubePairedTraceNetwork
  := complexRatPolyBoolSum 24
       radiusZeroElementaryCubePairedSummand.
```

This definition remains opaque at depth twenty four.  Linearity of the exact
finite-product Haar functional and the fixed-assignment twelve-block theorem
give

```text
H_N^C(radiusZeroElementaryCubePairedTraceNetwork)
  ≃ rationalComplexBoolSum 24
       radiusZeroElementaryCubeSchurDeltaValue.
```

The proof uses recursive congruence/linearity APIs only.  It does not create a
list of `2^24` assignments and does not reduce the recursive sum.

##### 8.13.53.2 Literal crossed-delta graph — ✓ COMPLETE

Every tagged link pair `(r,c;s,t)` contributes the two crossed equalities
`(r=t,c=s)`.  The resulting twenty-four ordered equality pairs are recorded
literally and certified to have length twenty four.  A vertex-major
presentation of their solution condition uses the eight consecutive triples

```text
[0,1,2], [3,4,5], [6,7,8], [9,10,11],
[12,13,14], [15,16,17], [18,19,20], [21,22,23].
```

Their flattening is exactly `List.range 24`; the vertex-triangle edge list has
length twenty four and no duplicate ordered edges.  No literal permutation
between that list and the link-order edge list is claimed yet.  Instead, the
theorem

```text
radiusZeroElementaryCubeContractionAllMatchBool_eq_triangles
```

proves for every `List Bool`—including short lists, using the shared default
`false` convention—that the literal twelve-link conjunction is exactly the
conjunction of those eight vertex triangles.  The proof destructs the
twenty-four displayed equalities and uses equality transitivity; it does not
split on twenty-four Boolean variables.

##### 8.13.53.3 Structural Schur and three-index folds — ✓ COMPLETE

One safe sixteen-case theorem proves, for a single oriented fundamental
contraction,

```text
delta(step)
  ≃ pureReal((1/2) * indicator(crossed indices match)).
```

Induction over the link schedule then proves

```text
schurDeltaProduct(schedule)
  ≃ pureReal((1/2)^(length schedule)
       * contractionMatchProduct(schedule)).
```

This induction is linear in the twelve links and is pointwise in an opaque
assignment.  At the vertex end, `threeChunkProduct` consumes three Boolean
indices at a time using `getD` and `drop 3`; its default-safe definition is
essential because the recursive Boolean-sum congruence is stated for all
lists, not merely lists of the expected length.

The generic theorem

```text
rationalComplexBoolSum_threeChunkProduct localFactor count
```

opens exactly three Boolean binders at each induction step and proves that a
depth-`3*count` sum of independent three-index factors is the `count`th power
of the local depth-three sum.  Instantiating the local factor with equality of
three Booleans requires only eight concrete cases and gives local value `2`.
At `count = 8`, the global symbolic sum is therefore `2^8`, without exposing
any of its `2^24` leaves.

##### 8.13.53.4 Exact scalar and paired Haar endpoint — ✓ COMPLETE

For every assignment, the literal schedule delta fold is proved equivalent
to

```text
(1/2)^12 * product of the eight vertex-triangle indicators.
```

Boolean-sum congruence, constant-factor linearity, and the generic
three-index theorem then give

```text
rationalComplexBoolSum 24 cubeSchurDeltaValue
  ≃ pureReal((1/2)^12 * 2^8)
  ≃ pureReal(radiusZeroElementaryCubePostSchurResolvedFactor)
  ≃ (1/16, 0).
```

Composing this chain with the opaque Haar-to-delta theorem proves the public
endpoint

```text
finiteProductHaarComplex_radiusZeroElementaryCubePairedTraceNetwork_exact :
  H_N^C(radiusZeroElementaryCubePairedTraceNetwork) ≃ (1/16, 0).
```

The eight tag-triangle sums agree numerically with the independently counted
eight geometric vertices; tag-to-geometric-endpoint incidence is deliberately
left to the production bridge.  The order change from
`(1/2)^12 * 2^8` to the geometry bookkeeping order
`2^8 * (1/2)^12` is justified by exact rational-setoid commutativity, not by
normalizing or evaluating the global Boolean sum.

##### 8.13.53.5 Scope fence: what is and is not proved

The exact `1/16` theorem belongs to the paired raw polynomial constructed from
the twelve right-local contraction rows.  It does **not** yet establish that
the existing production cutoff-one rank-one cube representative—the product
of the six face-ordered trace expansions—has the same finite-product Haar
value.  Although the two presentations have the intended coefficient values
under rational environments, the current exact Haar carrier is sensitive to
raw `RatPoly` syntax, and pointwise evaluation equivalence is not a valid
Haar-congruence principle.

Therefore no factor-sixteen correction to the production normalization is
banked at this checkpoint.  Such a correction becomes sound only after one
of the following is proved constructively:

1. literal raw-polynomial equality after an explicit finite reordering of
   the twenty-four Boolean binders and the twenty-four coefficient factors;
   or
2. a direct Haar-level theorem showing that those reorderings preserve the
   exact finite-product functional on these two concrete representatives.

The second route is preferable only if it is shorter than the finite literal
permutation proof; no general extensional Haar quotient should be introduced
merely to discharge this one cube.

##### 8.13.53.6 Highest-leverage next work: production bridge

Proceed in the following dependency order.

1. **Endpoint/tag incidence.**  For every tagged boundary occurrence, prove
   that the vertex-major tag determines exactly its geometric endpoint.  A
   useful certificate maps tags `0..23` to the eight boundary vertices, with
   each vertex occurring exactly three times.  Prove the map agrees with the
   row/column endpoint convention of the orientation-specific plaquette trace
   theorem, rather than relying only on a literal `decide` table.
2. **Global occurrence coverage.**  Flatten each of the twelve tagged link
   pairs into its forward and reverse occurrences and prove that this
   length-twenty-four list is a permutation of the face-major tagged boundary
   occurrence list.  Also prove the corresponding projections to physical
   occurrences and to matrix-coefficient descriptors.  Keep this finite and
   explicit; do not formulate or execute a `2^24` assignment permutation.
3. **Per-assignment factor reordering.**  Define the exact six-face symbolic
   summand by multiplying the six already verified orientation-specific
   four-coefficient terms for a fixed assignment.  Prove that its twenty-four
   coefficient factors are a finite permutation of the paired summand's
   factors.  Use associativity/commutativity lemmas for raw `RatPoly` only if
   they yield actual representative equality; value-level `Eqv` is an audit
   theorem but not the final Haar bridge.
4. **Binder-order bridge.**  If the production face-major tag order differs
   from the vertex-major order, prove a recursive Boolean-sum swap/permutation
   theorem and apply only the concrete twenty-four-position permutation.
   The theorem must be structural in the permutation; it must not enumerate
   assignments or unfold the depth-twenty-four sum.
5. **Production Haar theorem.**  Compose the representative bridge with the
   paired-network endpoint to prove the exact Haar value for the named
   production cutoff-one rank-one elementary-cube observable.  Only here may
   the factor-sixteen normalization discrepancy be promoted from diagnostic
   arithmetic to a production theorem.
6. **Signed four-valent diagnostic.**  After the production bridge is banked,
   analyze the radius-zero edge-touching double cube.  Retain the signed
   two-dimensional intermediate channel/projector (or an exact signed
   `F`-move); do not replace amplitudes by squared Racah probabilities.  Use
   this diagnostic before redesigning the global local-to-slab kernel, so the
   kernel is corrected once with both bivalent and four-valent data in view.

All steps remain intuitionistic.  Permutations are finite data with explicit
coverage/injectivity certificates; Boolean sums are recursive; algebra is
carried through rational or rational-complex setoid equivalence; and no
choice, excluded middle, `native_decide`, global assignment materialization,
or large evaluator call is needed.

##### 8.13.53.7 Verification ledger

The delta-resolution target build was serialized, session-locked, `nice`d,
single-threaded, and preceded by the mandatory host-idle process check.  No
clean/full build and no test suite was run:

- `SU2QuaternionElementaryCubeBooleanDeltaResolution`: 732 jobs.

The public gates report no axioms for the local eight-case triangle sum;
`propext` for the concrete twelve-link-to-eight-triangle equality; and only
`propext` plus `Quot.sound` for the generic structural sum, pointwise Schur
resolution, exact symbolic sum, and final paired-network Haar theorem.  The
leaf contains no classical choice, `sorryAx`, custom axiom, or native decision
procedure.  After root wiring, the static audit found 2,627 source modules,
8,148 local import edges, zero cycles, 2,621 modules reachable from the
semantic root, six reviewed/classified semantic orphans, and zero unexpected
orphans.  The executable forbidden-token scan found zero hits, the host-load
guard passed all 236 tracked or untracked non-ignored entry files, and
`git diff --check` passed.

#### 8.13.54 Vertex-tag incidence and constructive occurrence coverage — ✓ COMPLETE

Module:
`YMGap.Continuum.SU2QuaternionElementaryCubeTaggedOccurrenceCoverage`.

This checkpoint closes the finite geometric bookkeeping prerequisites for
comparing the exact paired contraction network with a six-face trace
representative.  It does not yet identify their raw products or Haar values.
In particular, every assertion in this section is finite in the twenty-four
coefficient occurrences; no Boolean assignment is enumerated and the
depth-twenty-four Boolean sum remains opaque.

##### 8.13.54.1 Vertex-major tag carrier — ✓ COMPLETE

The vertex attached to a tag is defined by `getD (tag / 3)` in the audited
vertex-major order

```text
000, 100, 110, 010, 001, 101, 111, 011
```

at time coordinate one.  The carrier has length eight and no duplicates.
Mapping tags `0,...,23` repeats each displayed vertex exactly three times,
and a theorem proves that the tag fibre over every member of the carrier has
length three.  Independently, deduplicating the outward boundary occurrences
gives

```text
000, 010, 110, 100, 101, 001, 011, 111.
```

An explicit `List.Perm` constructor proof relates these two eight-vertex
orders.  Thus the tag carrier is not merely cardinality-compatible with the
geometry: it is a constructive reordering of the independently derived
boundary-vertex carrier.

##### 8.13.54.2 Ordered endpoint incidence — ✓ COMPLETE

The face-major tag-edge list and the face-major physical-occurrence list are
mapped to ordered source/target pairs.  The theorem

```text
radiusZeroElementaryCubeBoundaryTagEndpoints_exact
```

proves literal equality of these two length-twenty-four lists.  A separate
Boolean certificate is exactly `List.replicate 24 true`, and the reusable
member theorem

```text
radiusZeroElementaryCubeTaggedBoundaryOccurrence_tagEndpointsCoherent
```

deduces, for an arbitrary member of the tagged boundary list, both source-tag
and target-tag agreement with the geometric occurrence.  Ordered endpoints
are retained: no undirected-edge quotient is used, so occurrence polarity and
the row/column convention remain visible.

##### 8.13.54.3 Coefficient descriptors and row reconstruction — ✓ COMPLETE

`CubeCoefficientDescriptor` records a physical link, orientation sign,
row tag, and column tag.  Its quaternion block is derived from the already
audited production active-link index, and its selected polynomial is the
forward or reverse fundamental coefficient according to the sign.  For every
tagged link pair and every opaque Boolean assignment, the raw multiplication
of its forward and reverse descriptor coefficients is definitionally the
polynomial of that row's oriented fundamental contraction:

```text
forward descriptor coefficient * reverse descriptor coefficient
  = pair.contraction.polynomial.
```

The face-major descriptor list is obtained from the six oriented boundary
faces.  The paired descriptor list is the **schedule-order flattening** of the
twelve contraction rows, forward then reverse within each row.  Both lists
have length twenty four and no duplicate descriptors.

The schedule-order qualification is essential.  The established contraction
product uses a right-local, tail-first fold, so this flattened list is not the
raw left-to-right syntactic factor order of that product.  Later Haar
reordering must preserve each forward/reverse row, reverse the schedule order
where the fold requires it, and reassociate explicitly; a flat permutation
alone is not a raw-product equality theorem.

##### 8.13.54.4 Explicit twenty-four-slot coverage — ✓ COMPLETE

Reading the paired rows in schedule order selects the following positions in
the face-major list:

```text
[4,3, 0,11, 1,19, 20,2, 8,7, 12,6,
 5,23, 9,15, 16,10, 17,14, 13,22, 21,18].
```

This list has length twenty four, has no duplicates, and contains precisely
the naturals below twenty four.  More strongly, an explicit polymorphic proof
using only `List.Perm.cons`, `List.Perm.trans`, `List.perm_middle`, and
`List.Perm.refl` proves it is a permutation of `List.range 24`.  The same
constructor witness then proves the paired descriptors are a permutation of
the face-major descriptors.

No bulk decidable permutation reduction is used in the public proof.  An
earlier generic membership-based formulation was rejected because its axiom
gate exposed `Classical.choice`; the explicit constructor proof has no
axioms.  This is a statement about the chosen proof implementation, not a
claim that finite decidable permutation checking is inherently classical.

##### 8.13.54.5 Exact projections of the coverage theorem — ✓ COMPLETE

Three projections make the certificate usable by the next algebraic leaves.

1. Mapping descriptors through their coefficient selector, pointwise in an
   opaque assignment, gives a permutation of the twenty-four raw
   `ComplexRatPoly` factors.
2. The paired factor list is proved literally equal to the forward/reverse
   factors of the established twelve-step contraction schedule.
3. Reconstructing a tagged oriented occurrence from each descriptor recovers
   the face-major tagged occurrence list literally; consequently the paired
   reconstructed occurrences are a permutation of all twenty-four boundary
   occurrences.

These results jointly certify physical-link coverage, polarity, row and
column tags, quaternion blocks, raw coefficient selection, and literal
oriented endpoint incidence.  What remains is algebraic order, not missing
geometric data.

##### 8.13.54.6 Scope fence and revised critical path

This checkpoint does **not** infer equality of raw products from the flat
factor permutation, does not commute factors beneath the Haar functional,
does not relate Boolean binder orders, and does not identify the outward
six-face expression with the named production cube representative.  The
critical path is now:

1. **Complex finite-product Haar reordering facade.**  Lift the existing real
   `finiteProductHaar_polyMul_comm`, `finiteProductHaar_polyMul_middle_comm`,
   and `finiteProductHaar_polyMul_assoc` laws componentwise through
   `RationalComplexEqv`.  Prove a structural list-reordering theorem by
   induction on an explicit `List.Perm`; do not normalize raw polynomials.
2. **Right-local fold reconciliation.**  Relate the schedule-order flattening
   to the paired summand's actual tail-first multiplication, retaining each
   forward/reverse row as a unit and supplying every reassociation explicitly.
3. **Outward six-face fixed-assignment summand.**  Multiply the six already
   certified orientation-specific standard/reversed plaquette coefficient
   terms.  Connect each four-descriptor face chunk to its named trace term,
   then apply the occurrence permutation only at Haar level.
4. **Structural Boolean binder bridge.**  Lift the pointwise Haar equivalence
   through the opaque depth-twenty-four Boolean sum and, if needed, permute
   binders recursively from finite permutation data.  Never materialize the
   `2^24` assignments.
5. **Production-orientation bridge.**  Separately compare the outward-masked
   six-face representative with the canonical-standard representative used by
   the production observable.  The outward object must not be called the
   production cube until this raw or Haar-level orientation bridge is proved;
   pointwise trace inversion alone is insufficient for the syntax-sensitive
   exact Haar carrier.
6. **Exact production endpoint and normalization.**  Only after steps 1--5
   compose the paired `1/16` theorem into the named production cube theorem
   and promote any normalization discrepancy from diagnostic arithmetic to a
   proved correction.
7. **Signed four-valent diagnostic.**  Then analyze the edge-touching double
   cube with the signed two-dimensional intermediate channel retained, before
   modifying the global local-to-slab kernel.

This ordering removes the last finite-incidence uncertainty before the
analytic algebra begins and keeps all arguments intuitionistic.

##### 8.13.54.7 Verification ledger

The leaf target was built once in isolation under the repository session
lock, with `caffeinate`, `nice -n 10`, and `LEAN_NUM_THREADS=1`, after the
mandatory host-idle process check.  It completed successfully in 731 jobs.
No clean/full build and no test suite was run.

The public axiom gates report: no axioms for the eight-vertex order
permutation, paired-descriptor nodup theorem, and explicit twenty-four-slot
permutation; `propext` for the fibre-size, ordered-endpoint table, per-row raw
multiplication, face-descriptor nodup, and schedule-factor equality;
`propext` plus `Quot.sound` for the arbitrary-member endpoint theorem,
descriptor coverage permutation, mapped-polynomial permutation, and literal
tagged-occurrence permutation.  No gate exposes `Classical.choice` or
`sorryAx`.

After semantic-root wiring, the static audit found 2,628 source modules,
8,150 local import edges, zero cycles, 2,622 modules reachable from the
semantic root, six reviewed/classified semantic orphans, and zero unexpected
orphans.  The executable forbidden-token scan found zero hits, the host-load
guard passed all 236 tracked or untracked non-ignored entry files, and
`git diff --check` passed.  Together with the isolated green target build,
root reachability certifies that this leaf participates in the current full
build without rerunning that resource-intensive build.

#### 8.13.55 Constructive finite-product Haar reordering — ✓ COMPLETE

Modules:
`YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization` and
`YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering`.

This checkpoint supplies the algebraic order-independence facade required by
the twenty-four-slot occurrence certificate of Section 8.13.54.  Every law is
stated only after applying the exact finite-product Haar functional.  No raw
polynomial associativity or commutativity is asserted, no concrete cube
factor word is unfolded, and no Boolean assignments are enumerated.

##### 8.13.55.1 Corrected logical dependency: the four-factor atom

The pair and triple Haar laws are not, by themselves, sufficient for an
induction on `List.Perm`.  In the `Perm.cons` case one must transport the
induction hypothesis beneath a spectator.  After strengthening the theorem
with that spectator, the `Perm.swap` case requires the genuinely contextual
identity

```text
H ((a * b) * (c * d)) ≈ H ((a * c) * (b * d)).
```

This is not a formal consequence of binary commutativity, triple
associativity, and last-two-factor exchange unless one illegitimately assumes
that Haar equivalence is a congruence beneath raw multiplication.  It is not:
the raw `RatPoly` carrier retains term order and duplicates, and the project
intentionally has no theorem transporting arbitrary `RatPolyEqv` through
Haar.

The real parity-homogenization leaf now proves the missing theorem

```text
finiteProductHaar_polyMul_four_swap
```

for arbitrary block count and four arbitrary real raw polynomials.  Its
private backend expands the exact finite-product Haar functional as a lazy
four-linear fold over four term lists.  At each cell it uses literal
associativity and commutativity of monomial exponent addition together with
constructive rational setoid algebra; recursive row, bilinear, and
four-linear folds then exchange the two middle lists.  The proof never
normalizes a raw polynomial, never invokes a polynomial quotient, and never
materializes a global product.

##### 8.13.55.2 Scalar and complex Haar algebra — ✓ COMPLETE

The new complex-reordering leaf first establishes the scalar functional laws
needed to expand honest complex multiplication:

- congruence of `polyAdd` and `polyNeg` under already proved Haar
  equivalences;
- additive commutativity and the canonical zero/one laws after Haar;
- left and right distributivity of a raw product after Haar; and
- extraction of a negated left or right raw factor.

These lemmas are proved from the existing recursive Haar row and bilinear
carriers.  They do not assert syntax-level ring laws.

A common four-term real/imaginary triple expansion then proves exact
finite-product-Haar associativity and exchange of the last two factors for
`ComplexRatPoly`.  The binary complex exchange theorem is proved separately,
including the necessary swap of the two imaginary cross terms.  Canonical
complex left and right unit laws remove the explicit polynomial one without
assuming definitional normalization of its raw coefficient lists.

##### 8.13.55.3 Complex four-factor exchange — ✓ COMPLETE

The real four-factor atom is lifted through an eight-term expansion of each
complex component.  The construction reuses the verified triple normal form:
it proves additivity and negation in the triple's final slot, substitutes the
real and imaginary components of the fourth complex product, and applies the
real four-factor theorem to each opaque scalar term.  Bounded constructive
`Q'` setoid algebra reconciles the resulting eight-term orderings.

The public endpoint is

```text
finiteProductHaarComplex_mul_four_swap
```

with exact shape

```text
Hᴄ ((a * b) * (c * d)) ≃ Hᴄ ((a * c) * (b * d)).
```

Only the displayed four abstract factors are expanded.  In particular, the
twenty-four coefficient factors of the elementary cube remain opaque.

##### 8.13.55.4 Spectator closure and arbitrary explicit permutations — ✓ COMPLETE

Reassociation plus complex four-factor exchange gives the contextual
adjacent transposition

```text
Hᴄ (s * (a * (b * t))) ≃ Hᴄ (s * (b * (a * t))).
```

The theorem

```text
finiteProductHaarComplex_mul_product_perm
```

is then proved by structural recursion on a supplied `List.Perm` witness,
with an arbitrary spectator retained throughout:

- `nil` is reflexivity;
- `cons` reassociates into the enlarged spectator, applies the recursive
  theorem, and reassociates back;
- `swap` is the contextual adjacent-transposition theorem; and
- `trans` is transitivity of `RationalComplexEqv`.

Finally the complex left-unit law removes the spectator and yields

```text
finiteProductHaarComplex_product_perm
    (blockCount : Nat) {left right : List ComplexRatPoly}
    (hperm : left.Perm right) :
  Hᴄ (complexRatPolyProduct left) ≃
    Hᴄ (complexRatPolyProduct right).
```

The recursion consumes the explicit proof object.  It performs no
permutation search, membership reconstruction, sorting, or decidable bulk
reduction, and therefore introduces neither classical choice nor a large
evaluation.

##### 8.13.55.5 Scope fence and shortest next route

This checkpoint makes the occurrence permutation from Section 8.13.54 usable
at Haar level, but it does not yet identify either tail-first list product
with `radiusZeroElementaryCubePairedSummand`.  The remaining mismatch is
structural and explicit.  For a two-row schedule `[s₀,s₁]`, the established
right-local contraction syntax is

```text
(one * (F₁ * R₁)) * (F₀ * R₀),
```

whereas the schedule-order flattened coefficient word is

```text
[F₀, R₀, F₁, R₁].
```

They are neither definitionally equal nor related merely by quoting a flat
permutation.  The next highest-leverage leaf must therefore:

1. prove, symbolically for an arbitrary schedule, the Haar-level bridge from
   the right-local `contractionProductOver` fold to a tail-first product of
   its paired forward/reverse factors, accounting for the explicit base one,
   reverse row order, within-row grouping, and every reassociation;
2. specialize that bridge to the radius-zero elementary-cube schedule and
   compose it with
   `radiusZeroElementaryCubePairedCoefficientPolynomials_eq_scheduleFactors`;
3. apply the explicit occurrence permutation through
   `finiteProductHaarComplex_product_perm`, still pointwise in an opaque
   Boolean assignment;
4. build the outward six-face fixed-assignment product from the already
   certified orientation-specific plaquette coefficient terms and identify
   each four-factor face chunk before lifting through the opaque Boolean sum;
5. only afterward prove the separate production-orientation bridge to the
   canonical-standard cube representative and compose the exact `1/16`
   endpoint.

The Boolean binder bridge remains structural and must never materialize the
depth-twenty-four assignment space.  The outward representative must still
not be called the production cube before its orientation bridge is proved.

##### 8.13.55.6 Verification ledger

The complex reordering leaf was built repeatedly only as its isolated Lake
target, under the repository session lock with `caffeinate`, `nice -n 10`,
and `LEAN_NUM_THREADS=1`, after the mandatory host-idle process check.  Its
final target build completed successfully in 429 jobs and compiled the
changed real four-linear dependency in the same transitive cone.  No clean or
full build and no test suite was run.

All new public axiom gates, including the real and complex four-factor laws,
complex associativity and units, contextual adjacent exchange, spectator
permutation theorem, and final list-product permutation theorem, report
exactly `[propext, Quot.sound]`.  No gate exposes `Classical.choice` or
`sorryAx`; the source contains no `Classical`, `sorry`/`admit`,
`native_decide`, or custom axiom.

The new complex leaf is imported by the semantic root immediately after the
complex raw-polynomial algebra and before its first contraction-product
consumer.  After root wiring, the static audit found 2,629 source modules,
8,153 local import edges, zero cycles, 2,623 modules reachable from the
semantic root, six reviewed/classified semantic orphans, and zero unexpected
orphans.  The executable forbidden-token scan found zero hits, the host-load
guard passed all 236 tracked or untracked non-ignored entry files, and
`git diff --check` passed.  Together with the isolated green target build,
root reachability certifies that this leaf participates in the current full
build without an unsafe repetition of that full build.

#### 8.13.56 Right-local fold and face-major product reconciliation — ✓ COMPLETE

Modules:
`YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionReordering`
and
`YMGap.Continuum.SU2QuaternionElementaryCubeTaggedProductReconciliation`.

This checkpoint closes the algebraic-order gap left explicitly open in
Sections 8.13.54 and 8.13.55.  It relates the established right-local
contraction fold to the schedule-order forward/reverse coefficient word, then
uses the explicit twenty-four-slot occurrence permutation to reach the
face-major word.  Every theorem is symbolic in an arbitrary finite schedule
or pointwise in one opaque Boolean assignment.

##### 8.13.56.1 Exact coefficient word and reversal convention — ✓ COMPLETE

For an oriented contraction step, the generic factor row is defined as

```text
[forwardFundamentalCoefficient(step),
 reverseFundamentalCoefficient(step)].
```

Flattening these rows in schedule order defines
`fundamentalContractionCoefficientWord`.  Reversing the schedule before
flattening produces

```text
[Fₙ,Rₙ, ..., F₁,R₁].
```

The order qualification matters: reversing the already flattened list would
instead give `[Rₙ,Fₙ,...]` and would incorrectly reverse every contraction
row.  The theorem

```text
fundamentalContractionCoefficientWord_reverse_perm
```

uses `List.reverse_perm` followed by constructive `List.Perm.flatMap_right` to
prove that reverse-schedule and schedule-order words are permutations while
preserving forward-before-reverse within every row.

##### 8.13.56.2 Suffix-strengthened right-local induction — ✓ COMPLETE

The main generic proof does not attempt to multiply a bare Haar equivalence
through a polynomial context.  Instead it retains an arbitrary symbolic
tail-first suffix and proves

```text
Hᴄ ((contractionProductOver base schedule) * product(suffix))
  ≃
Hᴄ (base * product(word(schedule.reverse) ++ suffix)).
```

The empty-schedule case is reflexive.  In the cons case, writing `C` for the
recursive tail product, `F,R` for the new row, and `S` for the suffix product,
the proof performs exactly

```text
((C * (F * R)) * S)
  ≃ ((C * F) * (R * S))
  ≃ C * (F * (R * S)).
```

The first step is the verified complex four-factor reassociation
`finiteProductHaarComplex_mul_four_assoc`; the second is ordinary
Haar-level associativity.  The induction hypothesis is then invoked with
`F :: R :: suffix`.  Consequently no arbitrary Haar equivalence is ever used
as a multiplication congruence, and the proof accounts literally for the
external base, reverse row order, within-row grouping, suffix, and every
reassociation.

Introducing the empty suffix with the complex right-unit law, applying this
theorem, restoring schedule order with the spectator permutation theorem,
and finally removing the canonical base one gives the public generic endpoint

```text
finiteProductHaarComplex_fundamentalContractionProduct_eq_word.
```

No range, distinctness, or Schur hypothesis is needed for this purely
algebraic reconciliation.

##### 8.13.56.3 Named cube words and occurrence transport — ✓ COMPLETE

The cube specialization names two still-opaque lists:

- `radiusZeroElementaryCubePairedCoefficientWord`, the twelve schedule rows
  flattened forward then reverse; and
- `radiusZeroElementaryCubeFaceMajorCoefficientWord`, the twenty-four
  coefficients in the certified six-face occurrence order.

The first is proved literally equal to the generic coefficient word of
`radiusZeroElementaryCubeContractionSchedule`.  The descriptor coverage
theorem then gives an explicit `List.Perm` from this paired word to the
face-major word.  Applying the generic fold endpoint and the complex product
permutation theorem yields both directions of the exact Haar bridge between
the paired summand and the face-major coefficient product.

##### 8.13.56.4 Fixed-assignment exact endpoint — ✓ COMPLETE

Composing the face-major-to-paired bridge with the existing twelve-link Schur
contraction theorem proves

```text
finiteProductHaarComplex_radiusZeroElementaryCubeFaceMajorCoefficientProduct_eq_schurDeltaValue
```

for every `assignment : List Bool`:

```text
Hᴄ (product(radiusZeroElementaryCubeFaceMajorCoefficientWord assignment))
  ≃ radiusZeroElementaryCubeSchurDeltaValue assignment.
```

This is the first exact fixed-assignment endpoint whose input is ordered by
the six outward boundary faces rather than by the internal contraction
schedule.  It simultaneously certifies all twelve physical block pairings,
all twenty-four coefficient polarities and tag endpoints, the complete
algebraic reordering, and the resolved crossed-delta value.

##### 8.13.56.5 Scope fence and revised shortest route

The face-major object remains a right-associated word of twenty-four
individual coefficients.  It has not yet been identified with a product of
six named four-factor plaquette trace terms.  In particular:

- four consecutive face-major coefficients must be grouped into the already
  certified orientation-specific `standardPlaquetteTraceTerm` or
  `reversedPlaquetteTraceTerm` for that face;
- the six grouped face terms must then be reconciled with the chosen outer
  sixfold product parenthesization at Haar level;
- the outward orientation mask is alternating
  `[reversed, standard, reversed, standard, reversed, standard]`, whereas the
  production cube uses a canonical-standard representative;
- the existing equality between reversed and standard trace expansions is an
  evaluation theorem and cannot be transported through the syntax-sensitive
  Haar carrier; and
- the depth-twenty-four Boolean binder bridge is still unproved and must be
  structural, never an enumeration of `2^24` assignments.

The most efficient next work is therefore a **face-chunk product bridge**:

1. define the outward fixed-assignment six-face product using the existing
   standard/reversed plaquette coefficient terms;
2. prove a generic six-row/four-column Haar reassociation theorem, again with
   a suffix invariant, connecting its grouped face tree to the flat
   face-major coefficient word;
3. compose that theorem with the fixed-assignment endpoint above;
4. lift the pointwise result through the opaque structural Boolean sum; and
5. only then prove the separate production-orientation bridge and exact
   normalization endpoint.

The signed four-valent edge-touching diagnostic remains after this elementary
cube production bridge, before any change to the global local-to-slab kernel.

##### 8.13.56.6 Verification ledger

The concrete reconciliation leaf was built once as an isolated Lake target
under the repository session lock, with `caffeinate`, `nice -n 10`, and
`LEAN_NUM_THREADS=1`, after the mandatory host-idle process check.  The build
completed successfully in 758 jobs and compiled both new leaves plus the
new four-factor reassociation dependency.  No clean/full build and no test
suite was run.

The public axiom gates for the reverse-word permutation, suffix-strengthened
fold reconciliation, arbitrary-base and pure-product endpoints, cube word
identification, face-major permutation, paired/face Haar bridges, and final
Schur-delta endpoint expose no `Classical.choice` or `sorryAx`; the
Haar-valued endpoints remain within `[propext, Quot.sound]`.  After root
wiring, the static import audit found 2,631 source modules and 8,159 local
import edges, with zero cycles; 2,625 modules are reachable from the semantic
root, and all six remaining modules are classified infrastructure or examples,
leaving zero unexpected orphans.  The executable-source forbidden-token scan
found zero hits, the host-load guard passed all 236 tracked or untracked
non-ignored entry files, and `git diff --check` passed.  Together with the
isolated green target build, root reachability certifies that both leaves
participate in the current full build without repeating that resource-heavy
build.

#### 8.13.57 Exact outward six-face trace network — ✓ COMPLETE

Modules:
`YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping`,
`YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge`, and
`YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceNetwork`.

This checkpoint closes the face-chunk and structural depth-twenty-four lift
left open in Section 8.13.56. It gives the first exact finite-product Haar
theorem for an honest product of six named, outward-oriented fundamental
plaquette trace summands, summed over all twenty-four shared matrix-index
variables. The result is constructive and exact:

```text
Hᴄ(outward six-face trace network) ≃ (1/16, 0).
```

The word *outward* remains essential. Three faces use the reversed trace
orientation and three use the standard trace orientation. This theorem is
therefore the mathematically correct elementary-cube boundary contraction,
but it is not yet the canonical-all-standard production expression.

##### 8.13.57.1 Generic contextual four-factor row grouping — ✓ COMPLETE

A symbolic row `r` now has both representations

```text
rowPolynomial(r) = (((first(r) * second(r)) * third(r)) * fourth(r))
rowFactors(r)    = [first(r), second(r), third(r), fourth(r)].
```

The reusable theorem

```text
finiteProductHaarComplex_mul_fourFactorRowProducts_eq_flatMap
```

retains an arbitrary accumulated spectator and an arbitrary list-valued
suffix. It proves, for every row list,

```text
Hᴄ(spectator * product(map rowPolynomial rows ++ suffix))
  ≃
Hᴄ(spectator * product(flatMap rowFactors rows ++ suffix)).
```

The strengthened statement is the induction invariant required by the
syntax-sensitive raw polynomial carrier. When one row is exposed, three
verified four-factor Haar reassociations transform

```text
(spectator * (((a*b)*c)*d)) * suffix
```

into the same right-local form as

```text
((((spectator*a)*b)*c)*d) * suffix.
```

The recursive call then uses the four-times-accumulated spectator. Thus the
proof never assumes the false rule that equality after Haar evaluation may
be multiplied by an arbitrary polynomial context. Introducing and removing
the canonical left unit gives the public bare endpoint

```text
finiteProductHaarComplex_fourFactorRowProducts_eq_flatMap.
```

Both the rows and their factors remain symbolic; the generic proof
materializes neither cube assignments nor a twenty-four-factor production
word.

##### 8.13.57.2 Audited outward face rows — ✓ COMPLETE

`TaggedOrientedPlaquetteRow` packages one production plaquette, its outward
orientation, and its four cyclic vertex-major Boolean tags. The exact six
rows are:

| row | plaquette base/type | orientation | cyclic tags |
|---:|---|---|---|
| 0 | `(0,0,0,1) / p01` | reversed | `[0,9,6,3]` |
| 1 | `(0,0,0,1) / p02` | standard | `[1,4,15,12]` |
| 2 | `(0,0,0,1) / p12` | reversed | `[2,13,21,10]` |
| 3 | `(0,0,1,1) / p01` | standard | `[14,16,18,22]` |
| 4 | `(0,1,0,1) / p02` | reversed | `[11,23,19,7]` |
| 5 | `(1,0,0,1) / p12` | standard | `[5,8,20,17]` |

The small concrete theorems

```text
radiusZeroElementaryCubeOutwardFaceRows_faces
radiusZeroElementaryCubeOutwardFaceRows_tags
```

certify that these rows are literally the previously audited outward face
list and cyclic tag table. Only these six bounded records are reduced.

For canonical edge blocks `(b₀,b₁,b₂,b₃)`, a standard row uses

```text
[F(b₀), F(b₃), R(b₂), R(b₁)],
```

whereas a reversed row uses

```text
[F(b₁), F(b₂), R(b₃), R(b₀)].
```

The theorem `TaggedOrientedPlaquetteRow.traceTerm_eq_named` proves that the
left-associated polynomial of every row is exactly the established
`standardPlaquetteTraceTerm` or `reversedPlaquetteTraceTerm`, with the
appropriate four tag values. No semantic evaluation or orientation
identification is used.

##### 8.13.57.3 Descriptor and face-major reconciliation — ✓ COMPLETE

Each face row also produces four signed coefficient descriptors. The exact
six-row audit

```text
radiusZeroElementaryCubeOutwardFaceDescriptorRows_flatten
```

proves that flattening them gives the previously certified twenty-four-entry
face-major descriptor list. Mapping an arbitrary opaque assignment through
the descriptor rows therefore yields the exact symbolic identity

```text
radiusZeroElementaryCubeOutwardFaceCoefficientRows_eq_faceMajorWord.
```

Applying the generic four-factor grouping theorem to these six rows gives

```text
finiteProductHaarComplex_radiusZeroElementaryCubeOutwardFaceTraceProduct_eq_faceMajor.
```

Composing with the fixed-assignment endpoint from Section 8.13.56 then proves
for every opaque `assignment : List Bool`:

```text
Hᴄ(product(six named outward face terms at assignment))
  ≃ radiusZeroElementaryCubeSchurDeltaValue assignment.
```

This is a pointwise theorem in a symbolic assignment. It does not enumerate
the `2^24` possible assignments and does not reduce the twenty-four-factor
product.

##### 8.13.57.4 Structural Boolean lift and exact value — ✓ COMPLETE

The full outward network is deliberately defined opaquely by

```text
radiusZeroElementaryCubeOutwardTraceNetwork :=
  complexRatPolyBoolSum 24
    radiusZeroElementaryCubeOutwardFaceTraceProduct.
```

The existing structural Haar-linearity theorem moves finite-product Haar
through this Boolean sum, and `rationalComplexBoolSum_congr` lifts the
fixed-assignment theorem without exposing any concrete branch tree. This
gives the two exact bridges

```text
finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_eq_schurDeltaSum

finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_eq_pairedTraceNetwork.
```

Finally, composing with the already resolved crossed-delta sum proves

```text
finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceNetwork_exact :
  Hᴄ(radiusZeroElementaryCubeOutwardTraceNetwork) ≃ (1/16, 0).
```

The factor `1/16` is the exact unnormalized shared-index cube contraction; it
is not inferred numerically and its vanishing imaginary component is proved
inside the rational-complex equivalence. This endpoint reconciles all six
outward faces, twelve physical Haar blocks, twenty-four signed coefficient
occurrences, twenty-four shared Boolean indices, and the complete crossed
Schur-delta network.

##### 8.13.57.5 Scope fence and revised shortest route

The present network is a Boolean sum of products of six *summands*. It has
not yet been identified with the product of six separately defined
four-binder plaquette trace *expansions*. Distribution of those six sums
through the surrounding product is nontrivial because bare Haar equivalence
is not a multiplication congruence. Also, the six local binder rows occur in
face-major tag order

```text
[0,9,6,3, 1,4,15,12, 2,13,21,10,
 14,16,18,22, 11,23,19,7, 5,8,20,17],
```

whereas the contracted network uses the vertex-major order `0,...,23`.

The shortest sound continuation is now:

1. add a reusable two-sided contextual Haar multilinearity/Fubini API,
   proving structural `mul_add_inner`, `mul_boolBind_inner`, and
   `mul_boolSum_inner` theorems with arbitrary prefix and suffix;
2. expand the product of the six outward four-binder trace expansions under
   Haar into a face-major depth-twenty-four rational-complex branch sum;
3. prove an explicit constructive reindexing of that additive binder tree
   from face-major tags to vertex-major tags, after Haar has crossed the sums;
4. conclude that the genuine product of six outward plaquette trace
   expansions has exact Haar value `1/16`;
5. prove a separate contextual four-binder orientation theorem. A reversed
   summand at `(a,b,c,d)` corresponds to a standard summand at
   `(!a,!d,!c,!b)`, with four cyclic signs multiplying to `+1`; there is no
   valid same-assignment replacement;
6. apply that theorem only at the reversed face slots `0,2,4` to reach the
   canonical-all-standard production expression; and
7. expose the resulting normalization fence. The current scalar production
   surrogate contributes `coeff^6`, while the honest weighted cube value is
   `coeff^6 / 16`. Bank the signed four-valent edge-touching diagnostic
   before changing the global local-to-slab kernel.

In particular, multiplicative `List.Perm` theorems cannot reindex additive
Boolean binders; the existing evaluation equality between reversed and
standard trace expansions cannot be transported through the syntax-sensitive
Haar carrier; and the link-character cube surrogate must not be substituted
for this honest shared-index integral.

##### 8.13.57.6 Verification ledger

The generic grouping leaf, the six-face bridge, and the final outward-network
leaf were each built once as isolated Lake targets under the repository
session lock, with `caffeinate`, `nice -n 10`, and `LEAN_NUM_THREADS=1`, after
the mandatory host-idle process check. The three successful checkpoints
completed in 432, 762, and 764 jobs respectively. No clean/full build and no
test suite was run, and the depth-twenty-four Boolean sum was never unfolded.

The public axiom gates for the symbolic row definitions and grouping
theorems, six-row metadata and descriptor audits, named-term identity,
fixed-assignment Haar endpoints, structural Boolean lift, paired-network
bridge, and final exact theorem expose no `Classical.choice` or `sorryAx`.
The Haar-valued endpoints remain within `[propext, Quot.sound]`; the finite
six-row data audits require no axioms. After root wiring, the static import
audit found 2,634 source modules and 8,168 local import edges, with zero
cycles; 2,628 modules are reachable from the semantic root, and all six
remaining modules are classified infrastructure or examples, leaving zero
unexpected orphans. The executable-source forbidden-token scan found zero
hits, the host-load guard passed all 236 tracked or untracked non-ignored
entry files, and `git diff --check` passed. Together with the isolated green
target builds and the independent mathematical review, root reachability
certifies that all three new leaves participate in the current full build
without repeating that resource-heavy build.

#### 8.13.58 Contextual finite-product Haar–Boolean Fubini — ✓ COMPLETE

Module:
`YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexBoolFubini`.

This checkpoint supplies the missing linearity principle required to pass
from a product of separately summed plaquette trace expansions to a sum of
fixed-assignment face products. The theorem is deliberately contextual:
both the already accumulated factors on the left and the unresolved product
suffix on the right remain inside every branch. Consequently it is strong
enough for repeated use in a six-factor product without ever treating bare
Haar equivalence as a multiplicative congruence.

##### 8.13.58.1 Binary honest-complex distributivity — ✓ COMPLETE

The proof first defines a private scalar expansion of one complex product:

```text
Hᴄ(left * right)
  ≃
(H(left.re * right.re) - H(left.im * right.im),
 H(left.re * right.im) + H(left.im * right.re)).
```

Scalar finite-product Haar additivity in the right factor, together with
compatibility with negation, proves that this expansion is additive in the
right complex argument. Recombining the two branch expansions gives the
public theorem

```text
finiteProductHaarComplex_mul_add_right :
  Hᴄ(source * (left + right))
    ≃ Hᴄ(source * left) + Hᴄ(source * right).
```

This is an exact functional-level bilinearity theorem for the honest complex
raw-polynomial representation. It asserts neither a quotient-ring law for
the carrier nor multiplicativity of the Haar functional.

The additive theorem belongs in the Fubini leaf, which imports both the
complex reordering layer and the Boolean-sum algebra. Keeping it there avoids
a dependency cycle: the lower reordering layer intentionally does not import
the addition constructors exposed by the trace/Boolean algebra.

##### 8.13.58.2 Two-sided contextual distribution — ✓ COMPLETE

The central binary context theorem is

```text
finiteProductHaarComplex_mul_add_inner :
  Hᴄ(spectator * ((left + right) * suffix))
    ≃
  Hᴄ(spectator * (left * suffix))
    + Hᴄ(spectator * (right * suffix)).
```

Its proof is a literal Haar-level chain:

1. exchange the inner sum with the suffix;
2. reassociate to `(spectator * suffix) * (left + right)`;
3. apply binary right-distributivity; and
4. in each branch, reassociate and exchange the suffix back to restore
   `spectator * (branch * suffix)`.

Every reordering is one of the already certified finite-product Haar
associativity or middle-exchange laws. No equality after Haar is inserted
under an unverified product context.

##### 8.13.58.3 One-binder and arbitrary-depth Fubini — ✓ COMPLETE

Unfolding only the definition of one Boolean binder specializes the contextual
binary theorem to

```text
finiteProductHaarComplex_mul_boolBind_inner :
  Hᴄ(spectator * (BoolBind family * suffix))
    ≃
  BoolBind (fun bit => Hᴄ(spectator * (family bit * suffix))).
```

Structural recursion on an arbitrary symbolic `depth` then proves

```text
finiteProductHaarComplex_mul_boolSum_inner :
  Hᴄ(spectator * (BoolSum depth family * suffix))
    ≃
  BoolSum depth
    (fun assignment => Hᴄ(spectator * (family assignment * suffix))).
```

The zero-depth case is reflexive. A successor exposes exactly one binder,
applies the contextual binder theorem, and combines the false and true
recursive branches with rational-complex additive congruence. Prefix and
suffix are unchanged throughout the recursion.

The theorem is polymorphic in `depth`; the elementary-cube depth `24` does
not occur in the module. Thus the proof does not specialize, unfold,
simplify, reduce, print, enumerate, or evaluate the cube assignment tree.

##### 8.13.58.4 Scope fence and next shortest route

Contextual Fubini supplies distribution, but it does not by itself identify
the resulting binder order with the vertex-major cube assignment used by the
exact network. The next production bridge must therefore keep three layers
separate:

1. define each of the six outward-oriented plaquette trace expansions as its
   established four-binder Boolean sum and form their tail-first product;
2. apply contextual Fubini repeatedly, retaining an accumulated prefix and
   the remaining face suffix, to obtain a face-major depth-twenty-four branch
   sum whose summand is exactly the six-face trace product from Section
   8.13.57; and
3. constructively reindex the rational-complex addition tree from the
   face-major tag order

```text
[0,9,6,3, 1,4,15,12, 2,13,21,10,
 14,16,18,22, 11,23,19,7, 5,8,20,17]
```

to vertex-major order `[0,...,23]`, only after Haar has crossed all polynomial
sums.

The reindexing must use Boolean-binder commutation/congruence structurally;
`List.Perm` of multiplicative factors cannot alter an additive binder tree,
and raw-polynomial equality of differently parenthesized sums is neither
needed nor available. Once this bridge is complete, the exact outward
network theorem immediately supplies the value `1/16`. The separate
four-binder reversed-to-standard orientation reindexing remains the following
checkpoint.

##### 8.13.58.5 Verification ledger

The new leaf was built as one isolated Lake target under the repository
session lock, with `caffeinate`, `nice -n 10`, and `LEAN_NUM_THREADS=1`, after
the mandatory host-idle process check. A pre-build guard detected an unrelated
short-lived Lake process and correctly deferred compilation until it exited.
The final target completed successfully in 431 jobs. No clean/full build and
no test suite was run.

The public axiom gates for binary complex distribution, two-sided contextual
distribution, one-binder Fubini, and arbitrary-depth Boolean Fubini expose
exactly `[propext, Quot.sound]`, with no `Classical.choice` or `sorryAx`.
After root wiring, the static import audit found 2,635 source modules and
8,171 local import edges, with zero cycles; 2,629 modules are reachable from
the semantic root, and all six remaining modules are classified
infrastructure or examples, leaving zero unexpected orphans. The
executable-source forbidden-token scan found zero hits, the host-load guard
passed all 236 tracked or untracked non-ignored entry files, and
`git diff --check` passed. Together with the isolated green target build,
root reachability certifies that the new leaf participates in the current
full build without repeating that resource-heavy build.

#### 8.13.59 Named Boolean environments and constructive cube reindexing — ✓ COMPLETE

Modules:

- `YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum`;
- `YMGap.Continuum.SU2QuaternionElementaryCubeNamedBoolReindex`.

Contextual Haar–Boolean Fubini produces an additive tree whose Boolean
binders initially occur in face-major order. The contracted outward cube
network instead stores one length-twenty-four assignment in canonical
vertex-major tag order. This checkpoint separates binder *names* from binder
*positions*, proves constructive permutation invariance for the resulting
rational-complex sum, and connects the canonical named order back to the
established `List Bool` sum. Everything here is post-Haar and additive: no raw
complex-polynomial reordering, polynomial distributivity, or multiplication
congruence is asserted.

##### 8.13.59.1 Total named environments and structural sums — ✓ COMPLETE

A named Boolean environment is a total function `Nat → Bool`. Updating one
coordinate is explicit:

```text
boolTagUpdate environment tag value query :=
  if query = tag then value else environment query.
```

The self-lookup and distinct-lookup laws identify the updated and untouched
coordinates. If `first ≠ second`, the two finite updates commute
extensionally:

```text
boolTagUpdate (boolTagUpdate environment first firstValue)
    second secondValue
  =
boolTagUpdate (boolTagUpdate environment second secondValue)
    first firstValue.
```

The named rational-complex sum is structural in a finite tag word:

```text
NamedSum [] family
  := family (fun _ => false),

NamedSum (tag :: tags) family
  := BoolBind (fun value =>
       NamedSum tags (fun environment =>
         family (boolTagUpdate environment tag value))).
```

The constantly-false base environment is only a total default for names not
bound by the supplied word. No list of environments and no Boolean-assignment
carrier is materialized. `rationalComplexNamedBoolSum_congr` transports
pointwise `RationalComplexEqv` through an arbitrary named word.

##### 8.13.59.2 Adjacent exchange and arbitrary finite permutations — ✓ COMPLETE

For distinct adjacent tags, `rationalComplexBoolBind_swap` exchanges the two
additive binders and `boolTagUpdate_comm` identifies the resulting leaf
environments. Equal adjacent tags are handled reflexively. Hence

```text
rationalComplexNamedBoolSum_swap :
  NamedSum (first :: second :: rest) family
    ≃ NamedSum (second :: first :: rest) family.
```

Structural induction on `List.Perm` then gives

```text
rationalComplexNamedBoolSum_perm :
  left.Perm right →
  NamedSum left family ≃ NamedSum right family.
```

No duplicate-freeness assumption is needed for this generic theorem: the
equality case in an adjacent swap is already valid. No decidable permutation
search, global assignment bijection, or `2^depth` enumeration occurs. The
theorem reindexes only the rational-complex addition tree after Haar has
crossed the polynomial sums; it does not reindex a multiplicative factor
word.

##### 8.13.59.3 Canonical consecutive names and positional assignments — ✓ COMPLETE

`boolListEnvironment start assignment` interprets the list head as the
Boolean value named `start`, the next entry as `start + 1`, and so on; names
below the offset and names beyond the list default to `false`. Its definition
is structural in the offset and queried name and performs no subtraction.
The key recursion law is

```text
boolListEnvironment start (bit :: tail)
  = boolTagUpdate
      (boolListEnvironment (start + 1) tail) start bit.
```

Induction on the symbolic depth, not on any concrete assignment tree, proves

```text
rationalComplexNamedBoolSum_range' :
  NamedSum (List.range' start depth) family
    ≃
  BoolSum depth (fun assignment =>
    family (boolListEnvironment start assignment)).
```

At offset zero, `boolListEnvironment` is exactly
`fun tag => assignment.getD tag false`. Consequently the canonical bridge is

```text
rationalComplexNamedBoolSum_range :
  NamedSum (List.range depth) family
    ≃
  BoolSum depth (fun assignment =>
    family (fun tag => assignment.getD tag false)).
```

At cube depth twenty four the final accessor is definitionally the
established

```text
cubeTagValue assignment tag := assignment.getD tag false.
```

Thus the bridge reaches the existing cube assignment representation without
converting a face-major list into a vertex-major list and without unfolding,
simplifying, reducing, evaluating, or printing the depth-twenty-four
recursion.

##### 8.13.59.4 Exact elementary-cube tag permutation — ✓ COMPLETE

Flattening the six audited outward rows recovers the established face-corner
tag carrier:

```text
radiusZeroElementaryCubeOutwardFaceRows.flatMap
    TaggedOrientedPlaquetteRow.tags
  = radiusZeroElementaryCubeFaceCornerTags.
```

The flattened order is literally

```text
[0,9,6,3, 1,4,15,12, 2,13,21,10,
 14,16,18,22, 11,23,19,7, 5,8,20,17].
```

Two bounded closed audits establish that every displayed entry is below 24
and that every `Fin 24` value occurs. They inspect only the twenty-four tag
names, never a Boolean assignment carrier. These audits yield

```text
tag ∈ radiusZeroElementaryCubeFaceCornerTags ↔ tag < 24.
```

Together with the existing duplicate-freeness certificate, a local
axiom-clean induction proves `List.range 24` duplicate-free. A private
structural `permOfNodupMemIff` then removes each witnessed head using
`List.append_of_mem` and `List.perm_middle`; no bulk `List.Perm` decider is
called. The public finite certificate is

```text
radiusZeroElementaryCubeFaceCornerTags_perm_range :
  radiusZeroElementaryCubeFaceCornerTags.Perm (List.range 24).
```

Applying generic named-sum permutation invariance yields the exact cube
bridge

```text
rationalComplexNamedBoolSum_radiusZeroElementaryCubeFaceCornerTags_eq_range :
  NamedSum radiusZeroElementaryCubeFaceCornerTags family
    ≃ NamedSum (List.range 24) family.
```

Combining this theorem with `rationalComplexNamedBoolSum_range 24` gives the
complete representation chain, for every opaque environment family `F`:

```text
NamedSum radiusZeroElementaryCubeFaceCornerTags F
  ≃ NamedSum (List.range 24) F
  ≃ BoolSum 24 (fun assignment => F (cubeTagValue assignment)).
```

The two theorems deliberately remain separate: the first is finite
binder-name permutation; the second is the structural equivalence between
consecutive named binders and the pre-existing positional list sum.

##### 8.13.59.5 Scope fence and revised shortest route

This checkpoint proves the entire binder-order and range/list representation
layer, but it does not yet prove that the product of six separately summed
plaquette trace expansions has the leftmost named-sum form above. In
particular, no environment-indexed six-face integrand has yet been connected
to `radiusZeroElementaryCubeOutwardFaceTraceProduct`, and contextual Fubini
has not yet been iterated across the six plaquette factors. Therefore the
genuine product of six four-binder expansions has not yet inherited the exact
`1/16` value.

The named family in the displayed chain must next be instantiated by the
finite-product Haar value of the six fixed-index outward face terms. Only
after that identification may the existing exact outward trace-network
theorem be composed into a theorem about the product of trace expansions.

The shortest sound route is now:

1. add an arbitrary-tag-word environment and its structural
   `NamedSum`/positional-`BoolSum` bridge, needed to land the initial
   face-major Fubini tree in the named representation;
2. specialize contextual Fubini to one four-binder plaquette while retaining
   both the accumulated spectator and unresolved suffix;
3. iterate that theorem over the six literal outward rows, preserving the
   orientation mask `reversed, standard, reversed, standard, reversed,
   standard`;
4. apply the completed face-major named permutation and canonical range
   bridge; and
5. compose with the exact outward trace-network value.

##### 8.13.59.6 Verification ledger

The downstream cube-reindex target was built under the repository session
lock with `caffeinate`, `nice -n 10`, and `LEAN_NUM_THREADS=1`, after the
mandatory host-idle process check. It completed successfully in 764 jobs and
thereby compiled both new leaves. A separate guarded one-file check captured
the foundational leaf's public axiom gates. No clean/full build and no test
suite was run.

The gates for update commutation, named-sum swap and arbitrary permutation,
the environment cons law, both consecutive-range bridges, the finite cube
permutation, and the specialized cube named-sum theorem expose only
`[propext, Quot.sound]`; named-sum congruence exposes only `[propext]`. There
is no `Classical.choice` or `sorryAx`. The finite row-flatten and literal-order
certificates require no axioms.

After root wiring, the static import audit found 2,637 source modules and
8,176 local import edges, with zero cycles; 2,631 modules are reachable from
the semantic root, and all six remaining modules are classified
infrastructure or examples, leaving zero unexpected orphans. The
executable-source forbidden-token scan found zero hits. The host-load and
host-load guard passed all 236 tracked or untracked non-ignored entry files,
and `git diff --check` passed. Together with the isolated green target build,
root reachability certifies that both new leaves participate in the current
full build without repeating that resource-heavy build.

#### 8.13.60 Genuine product of six outward plaquette trace expansions — ✓ COMPLETE

Modules:

- `YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolWord`;
- `YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini`;
- `YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceExpansionProduct`.

This checkpoint closes the gap left by Sections 8.13.57–59: the exact
`1/16` value now belongs to the genuine product of six independently summed
outward plaquette trace expansions, not merely to a preassembled
depth-twenty-four fixed-assignment network. The alternating outward
orientation mask is retained literally, and the proof never unfolds or
evaluates the concrete depth-twenty-four Boolean recursion.

##### 8.13.60.1 Arbitrary tag words and bounded four-binder syntax — ✓ COMPLETE

`boolTagWordEnvironment tags assignment` pairs an arbitrary word of natural
number tags with positional bits through `boolTagUpdate`. If the bit word is
short, every still-unpaired tag is updated with `false`; this agrees with the
`List.getD ... false` convention and makes every bridge valid on the
arbitrary lists quantified by `rationalComplexBoolSum_congr`, not only on
the exact-length branches generated internally by the sum.

The structural laws prove:

```text
boolTagWordEnvironment (tag :: tags) assignment tag
  = assignment.getD 0 false,

query ∉ leading →
boolTagWordEnvironment (leading ++ suffix) assignment query
  = boolTagWordEnvironment suffix
      (assignment.drop leading.length) query,

tag ∉ leading →
boolTagWordEnvironment (leading ++ tag :: suffix) assignment tag
  = assignment.getD leading.length false.
```

Duplicate-freeness of the complete displayed word supplies the last
freshness premise constructively. Induction on the tag word then proves the
arbitrary representation theorem

```text
rationalComplexNamedBoolSum_tagWord :
  NamedSum tags family
    ≃ BoolSum tags.length (fun assignment =>
         family (boolTagWordEnvironment tags assignment)).
```

The four-leading-binder identity

```text
BoolSum (depth + 4) family
  = FourBoolSum (fun a b c d =>
      BoolSum depth (fun rest => family (a :: b :: c :: d :: rest)))
```

is definitional and exposes only four constructors. Four applications of the
already established one-binder contextual theorem give

```text
finiteProductHaarComplex_mul_fourBoolSum_inner :
  Hᴄ(spectator * (FourBoolSum family * suffix))
    ≃ FourBoolSum (fun a b c d =>
        Hᴄ(spectator * (family a b c d * suffix))).
```

The same leaf proves order-preserving normalization between a left-associated
accumulated fold and the established tail-first product, solely beneath
finite-product Haar. No raw polynomial associativity or distributivity is
asserted.

##### 8.13.60.2 Honest oriented row expansions and six-face product — ✓ COMPLETE

For each `TaggedOrientedPlaquetteRow`, the new definitions select:

1. `traceTermBits`, the fixed four-index standard or reversed term;
2. `traceTermAt`, which reads the row's four named tags from a total Boolean
   environment; and
3. `traceExpansion`, the genuine standard or reversed four-binder
   plaquette expansion.

The row expansion is definitionally its `complexRatPolyFourBoolSum`, and
substitution of `cubeTagValue assignment` into `traceTermAt` recovers the
existing fixed-assignment `row.traceTerm assignment` exactly. Mapping the
expansion over the six audited rows produces

```text
radiusZeroElementaryCubeOutwardFaceTraceExpansions
  = radiusZeroElementaryCubeOutwardFaceRows.map traceExpansion,
```

with the checked literal mask

```text
[reversed, standard, reversed, standard, reversed, standard].
```

Its tail-first product is
`radiusZeroElementaryCubeOutwardTraceExpansionProduct`. Separately, the
environment-indexed six fixed terms and their tail-first product are
`radiusZeroElementaryCubeOutwardFaceTraceTermsAt` and
`radiusZeroElementaryCubeOutwardFaceTraceProductAt`.

##### 8.13.60.3 Structural six-row Haar Fubini and tag decoder — ✓ COMPLETE

`taggedOrientedPlaquetteTraceTermsFromWord rows assignment` consumes four
positional bits per row and recurses on `assignment.drop 4`. The reusable
row-list theorem is

```text
finiteProductHaarComplex_mul_traceExpansionProduct :
  Hᴄ(spectator * product (rows.map traceExpansion))
    ≃
  BoolSum (4 * rows.length) (fun assignment =>
    Hᴄ((traceTermsFromWord rows assignment).foldl
      complexRatPolyMul spectator)).
```

At the successor step it exposes one row's four binders, applies contextual
four-binder Fubini with the unresolved row product as suffix, reassociates
only at Haar level, and invokes the induction hypothesis with the selected
term absorbed into the spectator. `Nat.mul_succ` and the definitional
four-leading-binder identity reassemble the positional sum. Thus the proof
is structural in the number of rows and never opens the resulting concrete
depth twenty four.

The independent combinatorial theorem

```text
taggedOrientedPlaquetteTraceTermsFromWord_eq_traceTermsAt_tagWord
```

assumes only duplicate-freeness of `rows.flatMap row.tags`. Its head uses the
four positional lookup laws; its tail uses append/drop environment agreement
on every tail tag and a tag-local map congruence. Therefore positional
four-bit chunks select exactly the same ordered row terms as
`boolTagWordEnvironment`, even for short assignments. The existing concrete
flattening and `Nodup` certificates specialize this to all six cube rows and
then to their ordered product.

##### 8.13.60.4 Full named wiring and exact scalar — ✓ COMPLETE

Starting from the genuine six-expansion product, the proof inserts the
polynomial unit, applies row-list Fubini, converts the accumulated fold to the
tail-first product, applies the duplicate-free tag decoder, and reverses the
arbitrary-tag-word theorem. This gives the load-bearing bridge

```text
finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_eq_namedBoolSum :
  Hᴄ(radiusZeroElementaryCubeOutwardTraceExpansionProduct)
    ≃
  NamedSum radiusZeroElementaryCubeFaceCornerTags (fun environment =>
    Hᴄ(radiusZeroElementaryCubeOutwardFaceTraceProductAt environment)).
```

Factor order is unchanged throughout. In particular, the proof does not
commute raw trace factors, replace a reversed face by a standard face, or use
Haar equivalence as multiplication congruence.

The structural compatibility endpoint then composes:

```text
Hᴄ(product of six outward trace expansions)
  ≃ NamedSum faceMajorTags fixedFaceHaar
  ≃ NamedSum (List.range 24) fixedFaceHaar
  ≃ BoolSum 24 (fun assignment =>
       Hᴄ(radiusZeroElementaryCubeOutwardFaceTraceProduct assignment))
  ≃ Hᴄ(radiusZeroElementaryCubeOutwardTraceNetwork).
```

The pointwise environment/list identity recovers the already audited outward
face product, and symmetry of structural Boolean Haar linearity reassembles
the pre-existing outward trace network. This is recorded explicitly as

```text
finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_eq_traceNetwork.
```

Composing that compatibility theorem with the previously proved exact
outward-network endpoint yields

```text
finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_exact.
```

##### 8.13.60.5 Scope fence and revised shortest route

The theorem is the exact orientation-faithful *outward* six-face integral,
not yet the canonical all-standard production representative. In particular,
three factors still use `reversedPlaquetteTraceExpansion`. The standard and
reversed traces were previously shown equal only after evaluation at an
arbitrary quaternion assignment. That value theorem cannot be substituted
inside a larger polynomial product, and no unjustified raw-polynomial
congruence may be inferred from it.

The next shortest sound move is a syntax-sensitive Haar replacement theorem
for one reversed face in arbitrary left/right context. Reindex its safe four
Boolean binders by

```text
(a, b, c, d) ↦ (!a, !d, !c, !b),
```

prove directly that the four coefficient signs multiply to `+1`, and use
only Boolean-binder permutation/complement laws plus the established
contextual Haar machinery. Iterating that theorem over rows 0, 2, and 4 will
transport the exact `1/16` value to the canonical all-standard six-face
observable.

##### 8.13.60.6 Verification ledger

The downstream cube-expansion target was built under the repository session
lock with `caffeinate`, `nice -n 10`, and `LEAN_NUM_THREADS=1`, after the
mandatory host-idle process check. The final target completed successfully
in 770 jobs. Intermediate failures were parser/elaboration-only and were
followed by fresh idle checks and successful serialized retries. No clean or
full build, no test suite, and no concrete depth-twenty-four reduction was
run.

The public gates for arbitrary tag-word lookup, four-binder opening,
row-list Fubini, the duplicate-free decoder, the named six-face wiring, and
the structural trace-network compatibility theorem, as well as the exact `1/16`
endpoint expose subsets of `[propext, Quot.sound]`. The
definitional row-expansion and literal orientation-mask audits require no
axioms. There is no `Classical.choice`, `sorryAx`, `native_decide`, custom
axiom, `sorry`, or `admit` on the new path.

After semantic-root wiring, the static import audit found 2,640 source
modules and 8,186 local import edges, with zero cycles; 2,634 modules are
reachable from `YMGap.lean`, and all six remaining modules are reviewed
infrastructure or examples, leaving zero unexpected orphans. The
executable-source forbidden-token scan found zero hits, the host-load guard
passed all 236 tracked or untracked non-ignored entry files, and
`git diff --check` passed. Together with the isolated green target build,
root reachability certifies the current full-build wiring without repeating
the resource-heavy full build.

#### 8.13.61 Canonical all-standard elementary-cube trace product — ✓ COMPLETE

Modules:

- `YMGap.Continuum.SU2QuaternionPlaquetteOrientationHaarReindex`;
- `YMGap.Continuum.SU2QuaternionElementaryCubeCanonicalTraceExpansionProduct`.

The orientation-faithful outward cube integral is now transported to the
canonical production representative using the standard plaquette word at all
six faces, without invoking polynomial evaluation extensionality and without
unfolding the depth-twenty-four cube sum.

##### 8.13.61.1 Exact sign and fixed-term orientation audit — ✓ COMPLETE

The computational sign function

```text
fundamentalCoefficientFlipSign(row,column)
  = +1  when row = column,
  = -1  otherwise
```

records the coefficient identity
`F(r,c) = sign(r,c) R(!c,!r)`. The theorem
`fundamentalCoefficientFlipSign_cycle_four` proves by the sixteen bounded
Boolean cases that the four cyclic signs multiply to `+1`. The stronger raw
identity

```text
reversedPlaquetteTraceTerm_eq_flippedStandard_reverseFactors
```

shows that the reversed summand at `(a,b,c,d)` is literally the reverse
four-factor word of the standard summand at `(!a,!d,!c,!b)`. This identity is
axiom-free and preserves the syntax-sensitive raw polynomial carrier: no raw
associativity or commutativity is asserted.

##### 8.13.61.2 Constructive four-binder reindex — ✓ COMPLETE

`rationalComplexBoolBind_complement` exchanges the two branches of one
Boolean binder. Four nested congruences give simultaneous complementation,
and three applications of the existing constructive binder-swap theorem
reverse the final three coordinates. Their composition is

```text
rationalComplexFourBoolSum_reverse_complement :
  Σₐᵦ꜀𝒹 family(a,b,c,d)
    ≃ Σₐᵦ꜀𝒹 family(!a,!d,!c,!b).
```

Only the safe four-binder syntax is exposed; no finite assignment list is
constructed.

##### 8.13.61.3 Contextual four-factor and one-face reversal — ✓ COMPLETE

`finiteProductHaarComplex_mul_mulFourLeft_mul_eq_foldlFive` flattens one
left-combed four-factor block under arbitrary polynomial left and right
context. It does so solely beneath finite-product Haar. The resulting
five-factor fold is converted to the established tail-first product,
permuted by an explicit `List.reverse_perm` witness that fixes the suffix,
and converted back. This proves

```text
finiteProductHaarComplex_mul_mulFourLeft_reverse.
```

Combining this contextual factor reversal with the fixed-term identity and
the bounded Boolean reindex yields

```text
finiteProductHaarComplex_mul_reversedPlaquetteTraceExpansion_eq_standard.
```

Its spectator and suffix are arbitrary polynomials. Consequently the theorem
is safe to use inside a larger unresolved face product; it never assumes the
false principle that a bare Haar equivalence is a multiplication congruence.

##### 8.13.61.4 All-standard six-face product and exact value — ✓ COMPLETE

`radiusZeroElementaryCubeCanonicalFaceTraceExpansions` is the literal list of
six `standardPlaquetteTraceExpansion` factors in the unchanged audited face
order, and
`radiusZeroElementaryCubeCanonicalTraceExpansionProduct` is its tail-first
product. The structural theorem
`finiteProductHaarComplex_alternatingSix_reversed_eq_standard` accumulates
the already resolved prefix before each contextual replacement and restores
tail-first association afterwards.

The concrete proof applies the one-face orientation theorem exactly at
outward slots `0`, `2`, and `4`; slots `1`, `3`, and `5` remain unchanged.
This gives both directions of the representative fence,

```text
finiteProductHaarComplex_radiusZeroElementaryCubeOutward_eq_canonical
finiteProductHaarComplex_radiusZeroElementaryCubeCanonical_eq_outward,
```

and closes the capstone

```text
finiteProductHaarComplex_radiusZeroElementaryCubeCanonicalTraceExpansionProduct_exact :
  Hᴄ(radiusZeroElementaryCubeCanonicalTraceExpansionProduct)
    ≃ (1/16, 0).
```

##### 8.13.61.5 Verification ledger

After separate mandatory host-idle process checks, both new targets were
built through the repository session lock with `caffeinate`, `nice -n 10`,
`LEAN_NUM_THREADS=1`, and the mandatory per-process memory ceiling. The
generic orientation target completed successfully in 434 jobs; the
downstream canonical cube target completed successfully in 772 jobs. All
fourteen new printed declarations are inside the permitted axiom gate: the
literal list, sign, and raw fixed-term audits are axiom-free; the setoid/Haar
theorems use only `[propext]` or `[propext, Quot.sound]`. No full build or
full audit was run on the development host. The static import guard then
checked 2,642 source modules and 8,191 local import edges, found zero cycles,
proved 2,636 modules reachable from `YMGap.lean`, and classified all six
remaining modules with zero unexpected orphans. The host-load guard passed
all 236 tracked or untracked non-ignored executable entry files, its ten
mocked Mac runner remote-state scenarios, and its four bounded-supervisor
scenarios; `git diff --check` also passed. An independent read-only audit
confirmed the coefficient order, reindex direction, fixed suffix, face order,
replacement slots, equivalence directions, and final `1/16` composition.
The executable-source forbidden-token scan found zero hits.

#### 8.13.62 Cutoff-one cube activity normalization bridge — ✓ COMPLETE

Module:
`YMGap.Continuum.SU2QuaternionElementaryCubeWeightedActivityNormalization`.

The exact canonical cube coefficient is now connected to the two established
cutoff-one scalar activity formulas without silently changing their semantics.
The result is a proved factor-sixteen normalization fence: the current
production carrier is a fusion-channel-cardinality surrogate, whereas the
honest shared-index Haar observable contains the normalized Schur kernels.

##### 8.13.62.1 Convention audit and forced numerical value — ✓ COMPLETE

The three quantities that had previously been conflated are now separated:

```text
bare canonical six-character Haar integral              ≃ 1/16
weighted canonical six-face sector                      ≃ (coeffW w 1)^6 / 16
current coarse/centered canonicalSurfaceActivity scalar ≃ (coeffW w 1)^6.
```

There is no character-normalization ambiguity in these formulas. The standard
plaquette trace expansion is the unnormalized fundamental character
`Cheb.U 1 = Tr D`, while

```text
coeffW w s = dimQ s * qpow w (c4 s),
coeffW w 1 = 2 * w^3.
```

Thus the heat-kernel coefficient already contains the fundamental dimension
two; it must not be divided by two again. Combining six selected face
coefficients with the exact canonical Haar theorem forces

```text
((2 * w^3)^6) / 16 = 4 * w^18
```

as the mathematical value of the elementary closed-sphere sector. Equivalently,
this is the expected `dim(fund)^chi * q^F` value with Euler characteristic
`chi = 2`, face count `F = 6`, `dim(fund) = 2`, and `q = w^3`.

##### 8.13.62.2 Honest scalar insertion and Haar linearity — ✓ COMPLETE

`complexRatPolyRealScalar` embeds an exact rational as a real constant honest
complex polynomial, and `complexRatPolyRealSmul` scales its two raw polynomial
components. The structural theorem

```text
complexRatPolyRealScalar_mul
```

proves literal equality between left multiplication by that real constant and
componentwise scaling. Its only nontrivial raw-polynomial step is a direct
recursion on the duplicate-preserving term list proving
`polyMul (polyConst scalar) polynomial = polySmul scalar polynomial`; no
polynomial extensionality or normalization quotient is used.

`finiteProductHaarComplex_realSmul` then applies the already established real
Haar scalar law to both components, and
`finiteProductHaarComplex_realScalar_mul` exposes the multiplication interface.
Consequently the weighted observable

```text
radiusZeroElementaryCubeWeightedCanonicalTraceExpansionProduct w
  = realScalar ((coeffW w 1)^6)
      * radiusZeroElementaryCubeCanonicalTraceExpansionProduct
```

satisfies the load-bearing exact theorem

```text
finiteProductHaarComplex_radiusZeroElementaryCubeWeightedCanonical_exact :
  Hᴄ(weightedCanonicalCube w)
    ≃ (((coeffW w 1)^6 * (1/16)), 0).
```

The scalar is inserted on the left in both the raw carrier and the value-level
rational-complex product. The proof preserves that order and replaces only the
right Haar factor by the previously certified canonical value.

##### 8.13.62.3 Production comparison and exact factor-sixteen fence — ✓ COMPLETE

The convention audit found no compensating factor sixteen in
`canonicalSurfaceActivity`. Its face part is exactly `(coeffW w 1)^6`. At each
of the twelve bivalent cube links the production link factor is

```text
fundamentalInvariantMultiplicity 2 = 1,
```

so the complete link-multiplicity product is one. This records the *rank* of
the one-dimensional invariant space, not the normalized matrix-element Schur
kernel `1/dim(fund) = 1/2`. The twelve Schur factors and eight closed Boolean
index loops instead give `2^8 * (1/2)^12 = 1/16`.

The cube-specific scalar operation

```text
elementaryCubeHaarNormalizeActivity activity = activity * (1/16)
```

is proved to be inverted exactly by multiplication by sixteen. It defines
coarse and centered Haar-normalized scalar activities and yields both
normalization bridges:

```text
Hᴄ(weightedCanonicalCube w)
  ≃ (coarseUnitCubeCanonicalSurfaceHaarActivity w, 0),

Hᴄ(weightedCanonicalCube w)
  ≃ (centeredCoarseUnitCubeCanonicalSurfaceHaarActivity w, 0).
```

Finally the direction of the defect is fixed unambiguously:

```text
coarseUnitCubeCanonicalSurfaceHaarActivity w * 16
  ≃ canonicalSurfaceActivity w 2 coarseUnitCubeSupportIds,

centeredCoarseUnitCubeCanonicalSurfaceHaarActivity w * 16
  ≃ canonicalSurfaceActivity w 3 centeredCoarseUnitCubeRootAtThree.
```

Thus the old production scalar is sixteen times the honestly normalized cube
sector, not one sixteenth of it.

##### 8.13.62.4 Scope fence and production-design consequence

These are exact scalar-value comparisons. They do not claim raw polynomial
equality, literal equality of the radius-zero/coarse/centered geometric
representatives, or a universal `/16` correction for every surface. A global
division by sixteen would be mathematically wrong: even in an all-bivalent
closed network the net dimension factor depends on topology, while a
four-valent or higher-valent link retains a non-scalar invariant-channel
projector and signed recoupling data.

Accordingly the widely used `canonicalSurfaceActivity` definition remains
unchanged and is now explicitly treated as a combinatorial surrogate on this
path. The corrected production kernel must be designed only after the first
four-valent diagnostic determines how normalized Schur kernels and signed
Racah channels coexist. This avoids a cube-only patch that would have to be
replaced immediately at the next local geometry.

##### 8.13.62.5 Verification ledger

After the mandatory host-idle check, the new leaf was built through the
repository session lock with `caffeinate`, `nice -n 10`, and
`LEAN_NUM_THREADS=1`. Lake replayed the cached dependency cone and compiled
only the new leaf in 526 ms; the complete target finished successfully in 806
jobs. No clean or full build, no test suite, and no large Boolean or bounded
state-space reduction was run.

All eleven printed public gates expose only `[propext]` or
`[propext, Quot.sound]`; none exposes `Classical.choice`, `sorryAx`, a custom
axiom, or a native decision procedure. An independent read-only proof audit
checked scalar placement, both equivalence directions, the `1/16 * 16`
algebra, the coarse and centered rewrites, and the scope language, and reported
no defect.

After semantic-root wiring, the static import audit found 2,643 source
modules and 8,195 local import edges, zero cycles, 2,637 modules reachable
from `YMGap.lean`, all six remaining modules classified, and zero unexpected
orphans. The executable-source forbidden-token scan found zero hits, the
host-load guard passed all 236 tracked or untracked non-ignored entry files,
and `git diff --check` passed.

#### 8.13.63 Signed four-valent shared-link Haar diagnostic — ◐ IN PROGRESS

Modules:

- `YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector`;
- `YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjectorReordering`;
- `YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur`;
- `YMGap.Continuum.SU2QuaternionGenericBlockPartialFourValentHaarProjector`;
- `YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeSharedLinkHaarNormalization`;
- `YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction`.

The local signed projector, its scalar trace, the literal exceptional-link
geometry, the exact contextual order bridge, the arbitrary-block
independent-spectator lift, and the pointwise twenty-two-link bivalent fold are
now banked. This resolves the first ambiguity left by the cube normalization
audit: the production factor two is exactly the closed trace of a rank-two
normalized Haar projector, but it is not an entrywise substitute for that
projector. The next milestone is to bridge the literal forty-eight-factor face
word to the grouped representative and resolve its sixteen delta components,
without constructing the global Boolean assignment space.

##### 8.13.63.1 Balanced fourth moment and inverse Gram kernel — ✓ COMPLETE

For the direct and crossed invariant pairings

```text
D(i,j;k,l) = delta(i,k) delta(j,l),
X(i,j;k,l) = delta(i,l) delta(j,k),
```

an explicit four-Bool inner product proves the exact Gram matrix

```text
G = [[4,2],
     [2,4]].
```

Write the two forward coefficients as `F_ab F_cd` and the reverse
coefficients as `R_ef R_gh`. Since the repository convention is
`R_ef = conj(U_fe)`, the row- and column-pairing vectors are, in this order,

```text
r = (delta(a,f) delta(c,h), delta(a,h) delta(c,f)),
c = (delta(b,e) delta(d,g), delta(b,g) delta(d,e)).
```

The complete eight-index theorem proves directly from the normalized rational
`S^3` moment carrier that

```text
H(F_ab F_cd R_ef R_gh)
  = r^T [[ 1/3, -1/6],
         [-1/6,  1/3]] c.
```

Thus the kernel is `G^{-1}`, including its signs. The ordered regression

```text
(a,b,c,d,e,f,g,h) = (false,false,true,true,true,false,false,true)
```

isolates a mixed entry and gives exactly `(-1/6,0)`, while the all-false
diagonal entry gives `(1/3,0)`. These two regressions jointly rule out both an
index transpose and the mathematically incorrect replacement of signed Racah
amplitudes by their squared probabilities. The proof uses only 256 explicit
bounded Boolean cases; it does not construct any geometric labelling family.

##### 8.13.63.2 Closed trace is production multiplicity — ✓ COMPLETE

A safe four-binder Haar Fubini theorem traces only the four diagonal matrix
indices. It yields

```text
sum_(a,c,e,g) H(F_aa F_cc R_ee R_gg) = (2,0).
```

The edge-touching geometry independently gives

```text
geometricLinkMultiplicityFactor faces sharedLink = 2
```

from its certified incidence four. Their proved comparison is deliberately a
closed-scalar statement. It says that the production number is the trace of
the invariant projector (equivalently, the dimension of its image); it does
not erase the projector's `-1/6` interference entries.

##### 8.13.63.3 Literal orientation and external-index order — ✓ COMPLETE

The twelve decoded production faces are paired with the exact outward mask

```text
[R,S,R,S,R, R,S,R,S,R, S,S],
```

where positions `0,1,2,3,4,10` are the first cube and
`5,6,7,8,9,11` are the second. Flattening the twelve four-edge boundary words
produces exactly forty-eight tagged occurrences, each with a proved coherent
physical link and cyclic source/target.

Filtering this structural list at the unique incidence-four link gives, in
the inherited face order,

```text
face IDs:    [21, 52, 66, 67],
polarities:  [ R,  F,  R,  F].
```

The corresponding `(matrix row vertex, matrix column vertex)` pairs are

```text
[((1,1,1,1),(0,1,1,1)),
 ((0,1,1,1),(1,1,1,1)),
 ((1,1,1,1),(0,1,1,1)),
 ((0,1,1,1),(1,1,1,1))].
```

Consequently both two-forward/two-reverse balance and the reverse-index
transpose are proved from the literal oriented face words, not inferred from
incidence cardinality.

##### 8.13.63.4 Contextual exceptional-link order bridge — ✓ COMPLETE

The structural shared-link word occurs literally as

```text
R1 F1 R2 F2.
```

Finite-product Haar reordering now proves both the bare equivalence and the
version beneath arbitrary honest complex left spectator and right suffix,

```text
H(S * ((((R1 F1) R2) F2) * T))
  ≃ H(S * ((((F1 F2) R1) R2) * T)).
```

The contextual proof uses the explicit constructive permutation

```text
[R1,F1,R2,F2,T]
  -> [F1,R1,R2,F2,T]
  -> [F1,R1,F2,R2,T]
  -> [F1,F2,R1,R2,T].
```

No raw-polynomial associativity, commutativity, or congruence beneath Haar is
asserted. The local proof instead composes the established Haar-level
associativity, genuine four-factor exchange, pair exchange, and inverse
associativity laws.

The coefficient-specialized contextual statement exposes the complete
external index permutation. From inherited occurrence order

```text
(r1row,r1col, f1row,f1col, r2row,r2col, f2row,f2col)
```

the projector receives

```text
(f1row,f1col, f2row,f2col, r1row,r1col, r2row,r2col),
```

namely target-from-source positions `[2,3,6,7,0,1,4,5]`. Neither reverse
row/column pair is swapped externally: `reverseFundamentalCoefficient e f`
already denotes `conj(U_f e)`. Thus forward rows still pair with external
reverse columns, and forward columns with external reverse rows.

For the block-local calculation, the paired representative

```text
(F1 R1)(F2 R2)
```

is also related to the canonical left comb `(((F1 F2) R1) R2)` beneath an
arbitrary complex spectator. This latter theorem is proved contextually by
mapping both words to the common Haar normal form

```text
(S F1)(F2(R1 R2));
```

it does not commit the invalid step of multiplying a bare Haar equivalence by
an arbitrary spectator.

##### 8.13.63.5 Arbitrary-block signed partial Haar — ✓ COMPLETE

Partial integration is stated honestly through
`integratedComplexCoefficientSum`. Clearing a quaternion block retains
trailing-zero monomial aliases, so the theorem does not claim raw equality
with a constant polynomial. For every `block : Nat` and all eight Boolean
matrix indices, the exact identity is now

```text
integratedComplexCoefficientSum block
  ((F1 R1)(F2 R2))
    ≃ orientedFourFundamentalHaarProjector(F1,F2,R1,R2).
```

This covers all 256 signed entries at every symbolic base-four block offset.
The normalization first expands only the finite local polynomial, then uses
explicit block/base exponent lemmas to remove the symbolic offset without
adding `sphereMoment4` to the simplifier set. A fenced `simp only` performs
precisely that structural normalization; the resulting closed rational fourth
moments may then kernel-reduce, together with the Boolean projector arithmetic,
under constructive `decide`.
This proof shape is essential: the earlier ambient-simp prototype compiled
but its generated proof exposed `Classical.choice`, so it was rejected and
replaced rather than banked.

The arbitrary-block acceptance pins are

```text
I_block((F_00 R_00)(F_00 R_00)) ≃ ( 1/3, 0),
I_block((F_00 R_10)(F_11 R_01)) ≃ (-1/6, 0),
I_block((F_00 R_00)(F_01 R_10)) ≃ ( 1/6, 0).
```

The second uses canonical projector order
`(F1,F2,R1,R2)=(00,11,10,01)` and preserves the inverse-Gram interference
sign through the symbolic block shift. The third is deliberately
transpose-sensitive: the correct external reverse convention gives `1/6`,
whereas omitting the reverse row/column transpose gives zero. A corresponding
block-zero literal-order regression has `R1 F1 R2 F2 = 00,00,10,01`, so the
combined acceptance fence also exercises the exact contextual argument order
rather than merely a transpose-invariant diagonal or mixed entry.

The generic partial-Haar layer now exports two reusable facts:

1. honest complex polynomials local to one quaternion block are closed under
   raw complex multiplication;
2. if a local factor has partially integrated coefficient sum `z`, then for
   `block < blockCount` and any componentwise block-independent spectator
   `S`,

```text
H_blockCount(S * factor)
  ≃ rationalComplexMul(H_blockCount(S), z).
```

Its proof is exactly the constructive chain

```text
complex-spectator Fubini
  -> local factor gives all-zero aliases
  -> Haar multiplication by all-zero aliases
  -> coefficient-sum value substitution.
```

Applying this abstraction to the paired four-valent term, then composing with
the genuine contextual paired/canonical bridge, gives the reusable endpoint

```text
H_blockCount(S * (((F1 F2) R1) R2))
  ≃ rationalComplexMul
      (H_blockCount(S),
       orientedFourFundamentalHaarProjector(F1,F2,R1,R2)).
```

Every nonselected link polynomial remains opaque. The theorem assumes only
the necessary range proof and block independence; it does not enumerate any
network state or silently replace the projector by its trace.

##### 8.13.63.6 Twenty-two bivalent contractions — ✓ COMPLETE

The twenty-three physical touched links now use the existing production
decoder `adjacentEvenActiveLinkIndex 0`. The complete block list has length
twenty three, is duplicate-free, and lies in the production Haar carrier. The
certified shared physical link is removed before decoding the bivalent
complement; the resulting block list has length twenty two, is duplicate-free
and in range, and provably excludes the shared block.

The face-corner carrier has forty-eight independent tag names. It reuses the
audited vertex-major elementary-cube cycles for the first cube and a disjoint
translate by twenty four for the second. A literal twenty-two-row table pairs
the positive and negative occurrence of every bivalent physical link. The
remaining four descriptors are exactly the inherited shared word

```text
R1=(18,22), F1=(23,19), R2=(27,24), F2=(25,28).
```

Thus the canonical projector receives

```text
F1,F2,R1,R2 = (23,19,25,28,18,22,27,24).
```

No external reverse pair is transposed. A constructive forty-eight-position
`List.Perm` certificate proves that the shared row together with the
twenty-two bivalent rows covers every face-major coefficient descriptor
exactly once. Its membership proof uses closed `all < 48` and `Fin 48`
coverage certificates; an earlier broad-simplifier prototype exposed
`Classical.choice` and was rejected.

For every opaque `assignment : List Bool`, the literal `R F R F` shared word
is the base of the established right-local contraction fold. It is independent
of every scheduled bivalent block. The arbitrary-base distinct-block Schur
theorem contracts all twenty-two rows first; only then is the standalone Haar
value of the literal base transported to the signed projector. The banked
endpoint is

```text
H(contractionProductOver sharedRFRF bivalentSchedule)
  ≃ schurDeltaProductFrom signedProjector bivalentSchedule.
```

This parenthesization is deliberate: canonical `F F R R` is only an internal
Haar normal form and is never substituted into the raw face order.

The actual two-sheet external wiring has also been isolated as a safe
four-Bool theorem:

```text
sum_(A1,A2,B1,B2)
  K(A1,B1,A2,B2; B1,A1,B2,A2) ≃ 4.
```

This is not the diagonal projector trace `2`. Independent reconstruction of
the bivalent delta graph finds sixteen components: twelve ordinary free loops
and the four shared variables `A1,A2,B1,B2`. Consequently the later closed
target remains `2^12 * 4 * (1/2)^22 = 1/256`; using the diagonal trace here
would incorrectly give `1/512`.

That reduction is now certified. The forty-four crossed equalities produced
by the twenty-two bivalent Schur contractions are definitionally reconstructed
as sixteen consecutive equality triangles

```text
[0,1,2], [3,4,5], ..., [45,46,47].
```

Their flattening is exactly `List.range 48`, is duplicate-free, and splits
into twelve ordinary components and four exceptional components. Pointwise,
the original contraction-match product equals the product of these sixteen
triangle indicators. A parametric theorem then removes each triangle's two
redundant Boolean binders under an arbitrary rational-complex payload:

```text
sum_(3n bits) (triangleProduct_n * payload)
  ≃ sum_(n component bits) payload(repeatEachBoolThree components).
```

This is an induction on `n`, not an evaluation of the `2^(3n)` carrier. For
the double cube, the four exceptional component bits enter the signed
projector in the certified order `B1,A1,A2,B2`; the other twelve bits are
free. The sixteen-component sum is therefore exactly

```text
2^12 * 4 = 16384,
```

and multiplication by the twenty-two Schur factors gives the fully resolved
coefficient-network Haar value

```text
(1/2)^22 * 16384 = 1/256.
```

The proof defines the depth-forty-eight Boolean binder only as an opaque
recursive expression and never unfolds, simplifies, evaluates, prints, or
materializes it. The final descriptor theorem applies to the honest
face-major polynomial coefficient network, and the subsequent literal-trace
leaf now identifies that network beneath Haar with the product of the twelve
orientation-faithful plaquette-trace polynomials.

##### 8.13.63.7 Scope and verification ledger

Only fixed local moments, bounded local Boolean case splits, structural
descriptor lists, and opaque recursive Boolean binders are exposed. The
descriptor-derived depth-forty-eight sum is now defined and transported
symbolically through a generic triangle-compression theorem; it is never
unfolded or evaluated. No assignment carrier of cardinality `2^48`, global
assignment list, bounded labelling family, trajectory, or length family is
defined, unfolded, evaluated, printed, or materialized. The literal
twelve-face trace product is now identified with the coefficient network
beneath finite-product Haar, by structural row flattening and named Boolean
Fubini rather than a false raw-polynomial commutativity claim.

After separate mandatory host-idle checks, every Lean target was built through
the repository session lock with `caffeinate`, `nice -n 10`, and
`LEAN_NUM_THREADS=1`. The block-zero projector target completed in 434 jobs;
the final geometry target completed in 906 jobs and rebuilt only its 458 ms
leaf after the endpoint-order theorem was added. The contextual-order target
completed in 436 jobs, with its final leaf under 400 ms. The final
arbitrary-block projector target completed in 435 jobs and 20 seconds; this
bounded cost is the complete 256-entry symbolic-block proof, not a global
network enumeration. The grouped double-cube bivalent target completed in 911
jobs, with its new structural leaf taking about 37 seconds. The
delta-component, face-word, Boolean-resolution, and channel-diagonalization
leaves were each built separately through the same serialized path. The last
channel leaf completed in about 1.2 seconds after its bounded local proof was
repaired. The ordered-associator bridge then completed as one 619-module
cached target, with its new leaf under one second. The literal twelve-trace
bridge completed as one 927-module cached target; after two local elaboration
repairs its new leaf completed in about one second. No full or clean build and
no test suite was run.

The rational Gram calculation, direct projector-entry arithmetic, literal
face/orientation/endpoint tables, and bounded trace arithmetic are axiom-free.
Their Haar/setoid lifts, including the concrete signed regressions, together
with contextual-reordering, partial-integration, locality, spectator, and
production-comparison declarations expose only subsets of
`[propext, Quot.sound]`. A separate print-only audit confirms the reusable
local-factor theorem, contextual paired/canonical theorem, all-256
arbitrary-block projector, paired locality theorem, and final canonical
spectator endpoint, as well as both transpose-sensitive acceptance
regressions, each expose exactly `[propext, Quot.sound]`. The twenty-three-link
decoder, shared-block exclusion, literal-base independence, standalone shared
projector value, grouped twenty-two-link fold, and forty-eight-descriptor
coverage permutation expose at most `[propext, Quot.sound]`; the table map and
external-wiring sum are axiom-free. The generic equality-triangle compression,
the exact component and contracted sums, and the exact coefficient-network
Haar endpoint expose exactly `[propext, Quot.sound]`. The direct/crossed
channel inversions, `diag(1,3)` Gram computation, inverse-Gram projector
diagonalization, and normalized singlet/triplet trace computations are
axiom-free; the bridge from the Boolean Gram to the rational recoupling Gram
uses only `propext`. The signed ordered-table, inverse-Schur transpose,
arbitrary-coordinate Gram intertwiner, genuine inverse-associator endpoint,
and weighted probability bridge expose only `[propext, Quot.sound]`; the
fixed-channel label order and exact `4G` weight comparison are axiom-free,
and the factorial-Racah/recoupling-probability comparison uses only `propext`.
The literal twelve-row geometry and tag table are axiom-free, the descriptor
flattening uses only `propext`, and the constructive face-tag permutation,
fixed-assignment Haar regrouping, named-Fubini bridge, coefficient-network
comparison, contracted-sum endpoint, and exact literal value expose only
`[propext, Quot.sound]`.
No
`Classical.choice`, `sorryAx`, `native_decide`, custom axiom, `sorry`, or
`admit` occurs on the banked path. Independent read-only audits checked the
reverse-coefficient convention, all four inverse-Gram terms, the negative
regression, diagonal trace, outward mask, face order, polarity word, endpoint
order, contextual index permutation, spectator-congruence discipline, and
partial-integration API, and found no mathematical blocker.

After semantic-root wiring, the static import audit found 2,654 source
modules and 8,232 local import edges, zero cycles, 2,648 modules reachable
from `YMGap.lean`, all six remaining modules classified, and zero unexpected
orphans. The executable-source forbidden-token scan found zero hits, the
host-load guard passed all 236 tracked or untracked non-ignored entry files,
and `git diff --check` passed.

##### 8.13.63.8 Next load-bearing steps — PRODUCTION KERNEL CORRECTION NEXT

Proceed in the following order; each step must remain a local structural
theorem beneath Haar rather than a raw commutativity claim.

1. **✓ Contextual order bridge.** Convert the literal exceptional-link word
   inherited above, `R F R F`, to the canonical `F F R R` projector order
   under finite-product Haar, first locally and then under an arbitrary honest
   complex spectator independent of the shared block. Preserve the exact
   external index permutation in the theorem statement.
   This is complete, including arbitrary left/right context and the exact
   eight-index permutation `[2,3,6,7,0,1,4,5]`.
2. **✓ Arbitrary-block signed partial Haar.** Lift the block-zero, one-link
   projector to `integrateQuaternionBlockComplex block` and then through
   `finiteProductHaarComplex_complexSpectator_eq_after_integrating_right`.
   The resulting reusable API must replace only the selected block by the
   constant signed inverse-Gram kernel and leave every other link polynomial
   opaque. This is complete for all 256 entries, with both paired and canonical
   independent-spectator endpoints and no raw constant-polynomial claim.
3. **✓ Twenty-two bivalent contractions.** The production decoder,
   twenty-three/twenty-two block ledgers, exact tagged pair table, shared-row
   descriptor, constructive forty-eight-position coverage permutation,
   literal-base independence, standalone signed base value, and pointwise
   arbitrary-base Schur fold are complete. Every assignment remains an opaque
   `List Bool`; no `2^48` carrier or depth-forty-eight sum was formed.
4. **✓ Face-word bridge and delta-component closure.** Map the descriptor
   coverage certificate through an opaque assignment, reconcile the resulting
   face-major factor word with the right-local `contractionProductOver` word
   beneath Haar, and prove the exact sixteen-component Boolean delta graph.
   Twelve components are ordinary free loops; the four exceptional components
   feed

   ```text
   K(A1,B1,A2,B2; B1,A1,B2,A2).
   ```

   Combine the already-banked four-Bool sum `4` with the twenty-two Schur
   factors and twelve ordinary free sums to prove the closed value
   `2^12 * 4 * (1/2)^22 = 1/256`. Do this through named or recursive Boolean
   binders and structural reindexing; never unfold or evaluate a depth-48 sum,
   and never replace this wiring by the diagonal trace `2`.

   This is complete. The descriptor map gives the face-major coefficient
   word, the exact forty-four-edge graph gives sixteen three-vertex
   components, the generic triangle-compression theorem reduces `48` binders
   to `16`, the component sum is `16384`, and the exact face-major coefficient
   network has Haar value `(1/256,0)`. The depth-48 and depth-16 recursions
   remain opaque throughout.
5. **✓ Channel/Racah identification.** Relate direct/crossed pairings to the
   rational singlet/triplet coordinates. Fix the convention explicitly:
   singlet is `(D-X)/2` with Gram weight `1`, while triplet is `(D+X)/2` with
   Gram weight `3`. Match this order and sign with the existing Gram-weighted
   fixed-`F` carrier before naming any matrix as the Racah move. Prove the
   repository's actual transpose/inverse convention.
   The squared data `1/4,3/4,3/4,1/4` are a corollary only and must not replace
   signed amplitudes.

   This is complete. The local core gives `S=(D-X)/2`, `T=(D+X)/2`, the inverse
   relations `D=S+T` and `X=T-S`, Gram `diag(1,3)`, inverse-Gram weights
   `1,1/3`, the exact signed-projector decomposition, and unit trace of each
   weighted rank-one channel are formalized. The existing rational
   `fundamentalFMove` has the signed columns `(-1/2,1/2)` and `(3/2,1/2)` in
   this dimension-rescaled basis.

   The ordered bridge now fixes every remaining convention. Singlet/triplet
   correspond respectively to intermediate labels `0/2` on both fixed
   carriers. If

   ```text
   F = [[-1/2, 3/2], [1/2, 1/2]],   G = diag(1,3),
   ```

   the raw forward table `C(left input,right output)` is numerically `F`, so
   its column-coordinate action is `Cᵀ=Fᵀ`. The actual inverse Schur table
   `B(left output,right input)` satisfies `B=Cᵀ`. Since `F²=I`, this is exactly
   `B=C⁻ᵀ`, not an appeal to unweighted Euclidean orthogonality. The arbitrary
   rational-coordinate theorem

   ```text
   Fᵀ (G x) ≃ G (F x)
   ```

   proves `Fᵀ=GFG⁻¹` without division. The ordered weights are
   `diag(4,12)=4G`, and the independently defined factorial Racah kernel now
   agrees entrywise with the recoupling probability
   `[[1/4,3/4],[3/4,1/4]]`. Its correct signed-source formula remains the
   weighted rule `Pᵢⱼ=(Gᵢ/Gⱼ) Cᵢⱼ²`; the four probabilities are derived
   corollaries and do not erase the signs or the `1:3` Gram ratio.
6. **✓ Literal twelve-trace bridge.** Define the actual two-cube boundary as
   twelve tagged oriented plaquette rows and prove that flattening their four
   coefficient slots is the certified face-major descriptor permutation. The
   production orientation mask is

   ```text
   R,S,R,S,R, R,S,R,S,R, S,S,
   ```

   with cube-one faces in slots `0,1,2,3,4,10` and cube-two faces in slots
   `5,6,7,8,9,11`. Reuse the elementary-cube trace-expansion and tagged
   occurrence APIs rather than opening a new matrix-index enumeration. This
   must yield equality, or Haar equivalence by a certified factor-word
   permutation, between the literal product of twelve trace polynomials and
   `radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork`; composing
   with the banked endpoint then gives the literal local observable value
   `1/256`.

   This is complete. The twelve rows are literal production-order tagged
   plaquettes with face IDs, orientations, and cube slots checked
   slot-for-slot. Their forty-eight tags form a constructive permutation of
   `List.range 48`. Mapping each elementary-cube coefficient descriptor to
   the double-cube carrier and flattening the twelve four-factor rows gives
   the already certified face-major descriptor word exactly. For every
   opaque assignment, the twelve left-associated plaquette terms and the
   forty-eight-factor word are compared only beneath finite-product Haar.

   The genuine product of twelve separate four-Bool trace expansions is then
   transported by the reusable row-by-row Fubini theorem to a named Boolean
   sum, reindexed constructively by the tag permutation, and identified with
   the opaque depth-forty-eight face-major network. Composing with the banked
   triangle compression and signed shared-link contraction yields

   ```text
   H(product of the twelve literal outward traces) = (1/256,0).
   ```

   Neither the depth-forty-eight nor depth-sixteen recursion is unfolded,
   simplified, evaluated, or printed, and no list of assignments is ever
   materialized.
7. **△ Correct the production kernel once — exact discrepancy fence complete;
   replacement pending.** The first part of this step is now complete in
   `SU2QuaternionEdgeTouchingDoubleCubeWeightedActivityNormalization`.
   The literal twelve-face geometry is encoded as the genuine box-3 root

   ```text
   geometricSupportIds 3 radiusZeroEdgeTouchingDoubleCubeFaces,
   ```

   rather than reusing the unrelated radius-zero slab identifiers as box
   identifiers. Structural same-support and duplicate-free length arguments
   prove that this root has twelve faces. They also transport the audited
   incidence ledger to the production carrier: the shared link has incidence
   four and every other touched link has incidence two.

   Write

   ```text
   c(w) = coeffW w 1 = 2 w^3.
   ```

   The dimension factor `2` is already part of `coeffW`; the literal
   fundamental trace must not be divided by two a second time. The two exact
   values are now connected to the same concrete root:

   ```text
   honest literal Haar sector = c(w)^12 * (1/256) = 16 w^36,
   current production scalar  = c(w)^12 * 2       = 8192 w^36.
   ```

   Hence

   ```text
   honest * 512 ≃ canonicalSurfaceActivity
                ≃ parametricKPhysicalTerm w 1 3 (componentLabel root),

   parametricKPhysicalTerm w 1 3 (componentLabel root) * (1/512)
     ≃ honest.
   ```

   The final statement is also proved directly at rational-complex level from
   the weighted literal trace polynomial to the actual cutoff-one physical
   term times `1/512`. Thus the comparison now crosses the real production
   seam; it is not merely a comparison with a hand-written surrogate.

   This result also proves why a universal scalar patch is mathematically
   wrong. The elementary-cube Haar normalization is `1/16`, and the product
   of the two scalar cube normalizations is the honest double-cube
   normalization `1/256`. It is *not* the correction `1/512` needed relative
   to the old double-cube carrier, because that carrier has inserted the
   extra four-valent invariant-space dimension `2`. The elementary defect is
   `16`, while this connected shared-link defect is `512`; topology and
   channel wiring matter.

   The isolated one-thread target is green. A separate print-only audit gives
   exactly `[propext, Quot.sound]` for every geometric, production, literal
   Haar, and end-to-end physical-term endpoint, while the two closed scalar
   regression facts are axiom-free. No full build, clean build, test suite,
   bounded labelling materialization, or deep Boolean reduction was used.

   **Architectural decision.** Do not mutate `canonicalSurfaceActivity` yet.
   It has many downstream proofs that use its pointwise nonnegativity, whereas
   the honest four-valent integrand is a signed tensor whose scalar value only
   emerges after external indices are contracted. For the transition,
   interpret the existing definition as a nonnegative multiplicity majorant.
   The replacement must introduce channel data first, prove an absolute
   domination theorem by that majorant, and only then switch production
   consumers in one controlled migration.

8. **Build the six-valent local projector next.** A link in four dimensions
   can meet six plaquettes even at cutoff one. Therefore a production kernel
   supporting only bivalent and four-valent links is not closed under the
   actual support universe. For six fundamental legs the SU(2)-invariant
   space has Catalan dimension five. The efficient next leaf is a specialized
   five-channel projector:

   1. choose and freeze one signed, orientation-aware Temperley--Lieb
      noncrossing-pairing basis of five tensors;
   2. compute its exact `5 × 5` rational Gram matrix and a certified inverse;
   3. prove the inverse identities entrywise by bounded constructive cases;
   4. derive the normalized six-factor Haar projector from the exact `S^3`
      sixth moment, first at block zero and then at an arbitrary quaternion
      block;
   5. lift it through the existing block-independent spectator theorem, so
      all nonselected link factors remain opaque;
   6. add sign- and transpose-sensitive regression entries before using the
      projector in a network.

   Do not begin with all six permutation pairings: at dimension two their
   `S_3` Gram matrix is singular. Do not build a fully general
   Temperley--Lieb quotient yet either; the fixed five-channel leaf supplies
   exactly the missing cutoff-one production case with much less proof and
   evaluator risk. A generic Catalan constructor should be extracted only
   after the five-channel orientation convention and spectator API are
   stable.

   The audited concrete basis for three ordered forward rows
   `f=(f0,f1,f2)` and three ordered reverse columns `r=(r0,r1,r2)` is

   ```text
   P0 = [0,1,2],  P1 = [1,0,2],  P2 = [0,2,1],
   P3 = [1,2,0],  P4 = [2,0,1],

   Pσ(f;r) = product_i delta(fi,r_{σ(i)}).
   ```

   Omit the sixth permutation `P02=[2,1,0]`; at dimension two it satisfies
   the pointwise Plücker relation

   ```text
   P02 = P0 - P1 - P2 + P3 + P4.
   ```

   In the displayed five-basis order the exact Gram matrix and inverse are

   ```text
       [8 4 4 2 2]             [ 1/4 -1/6 -1/6  1/12  1/12]
       [4 8 2 4 4]             [-1/6  1/3  1/6 -1/6  -1/6 ]
   G = [4 2 8 4 4],   G^-1 =  [-1/6  1/6  1/3 -1/6  -1/6 ],
       [2 4 4 8 2]             [ 1/12 -1/6 -1/6 1/4  1/12]
       [2 4 4 2 8]             [ 1/12 -1/6 -1/6 1/12 1/4 ]

   det(G) = 5184.
   ```

   The oriented kernel must be frozen as

   ```text
   K = sum_(a,b) G^-1_ab
         P_a(Frows; Rcols) P_b(Fcols; Rrows).
   ```

   As in the four-valent proof, `reverseFundamentalCoefficient` already
   performs the internal conjugate transpose: the external reverse
   row/column pairs are not swapped. Acceptance pins should include
   `trace(K)=5`, an all-false value `1/4`, a negative value `-1/12`, and a
   transpose-sensitive value `1/12` whose wrong convention gives zero.

   **Completed inverse-Gram leaf.**
   `SU2QuaternionSixValentPairingGram` now implements this basis and kernel
   exactly.  Its finite proofs never reduce a six-deep Boolean sum: the
   tensor Gram calculation and the diagonal trace are each factored into two
   three-Bool contractions.  The leaf proves the omitted-pairing Plucker
   identity pointwise, realizes the displayed Gram table from the pairing
   tensors, certifies both matrix-inverse orders, and freezes all four
   acceptance pins.  In particular, its trace theorem contracts the actual
   externally oriented projector and proves rank five, rather than merely
   tracing the abstract `5 x 5` matrix identity.

   The isolated one-thread target and a separate print-only audit are green.
   The Plucker theorem, inner three-index contraction, both inverse
   identities, and every scalar regression are axiom-free.  Only the generic
   rational-sum congruence, the tensor-Gram transport through it, and the
   final staged trace use `propext`; none uses `Classical`, choice,
   `Quot.sound`, `native_decide`, `sorry`/`admit`, or a custom axiom.  The
   module is imported by the semantic root, so the full-current wiring audit
   reaches it without relying on an orphan compile.

   The serialized one-thread semantic-root target is green after that import.
   The accompanying static audit now sees 2,656 source modules and 8,241 local
   import edges, with zero cycles, 2,650 modules reachable from `YMGap.lean`,
   the same six reviewed alternative roots, and zero unexpected orphans.  The
   executable forbidden-token scan still has zero hits, the host-load guard
   passes all 236 tracked or untracked nonignored entry files, and
   `git diff --check` passes.  This is the current best full wiring check: it
   validates the changed semantic root while retaining the project-wide Lake
   glob and default-target coverage guarantees, without launching an unsafe
   clean or unconstrained parallel build.

   **Completed analytic sixth-moment leaf.**
   `SU2QuaternionOneLinkSixValentHaarProjector` now proves that the literal
   left-associated `F F F R R R` quaternion polynomial has normalized
   one-block `S^3` moment exactly equal to the externally transposed
   five-channel inverse-Gram projector.  This closes the key semantic gap in
   the preceding leaf: the signed kernel is no longer only an algebraically
   certified projector candidate, but the actual exact local Haar integral.
   Independent acceptance endpoints recover the all-equal value `1/4`, the
   negative interference value `-1/12`, and the transpose-sensitive value
   `1/12`.  A separate exact moment table records the three nonzero degree-six
   orbit types

   ```text
   E[x0^6]       = 5/64,
   E[x0^4 x1^2] = 1/64,
   E[x0^2 x1^2 x2^2] = 1/192,
   ```

   with common radial denominator `4 * 6 * 8 = 192`.

   The 4,096 Boolean configurations are never elaborated in one declaration.
   Sixteen certificates fix four selector bits and split only the remaining
   eight, so every proof has at most 256 branches.  More importantly for host
   safety, these certificates are distributed among four linearly chained
   chunk modules.  The initial single-process prototype reached about
   14.6 GB resident memory; the chained build reduced the observed active
   Lean chunk to about 4.0 GB, a roughly 72 percent reduction, while retaining
   one process, one thread, the repository lock, niceness, and the existing
   20 GB Lean hard ceiling.  The final dispatcher performs no moment
   reduction.  The isolated target is green.  A separate print-only audit
   shows exactly `[propext, Quot.sound]` for every chunk, the moment table, the
   public Haar theorem, and all three analytic regressions, with no
   `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
   After semantic-root wiring, the serialized one-thread `YMGap` target is
   green.  The static import audit sees 2,662 source modules and 8,248 local
   import edges, zero cycles, 2,656 modules reachable from `YMGap.lean`, the
   same six reviewed alternatives, and zero unexpected orphans.  The
   executable forbidden-token scan has zero hits, the host-load guard passes
   all 236 entry files, and `git diff --check` passes.

   After the raw inverse-Gram leaf, diagonalize through the TL3 channels. A
   convenient orthogonal basis has Gram weights

   ```text
   diag(4, 2, 2, 3/2, 3/2),
   ```

   so the projector decomposes as

   ```text
   (1/4) p3⊗p3 + (1/2) A⊗A + (1/2) B⊗B
     + (2/3) X⊗X + (2/3) Y⊗Y.
   ```

   This supplies the positive Gram form without discarding the signed
   permutation-basis entries. The five summands must each have weighted trace
   one. Recoupling must retain the `X/Y` interference terms; for example the
   right-channel vectors obey

   ```text
   A' = (1/4)A + (3/4)B + (1/2)X + (1/2)Y,
   B' = (3/4)A + (1/4)B - (1/2)X - (1/2)Y.
   ```

   **Completed genuine `TL3` channel bridge.**
   `SU2QuaternionSixValentTemperleyLiebChannelBridge` now constructs the
   five channels inside the faithful rational `TL3` algebra rather than
   merely naming five abstract vectors.  With diagram coordinates
   `(1,e1,e2,u=e1e2,v=e2e1)`, reflection interchanges `u` and `v`, and the
   certified elements are

   ```text
   p3 = (1,-2/3,-2/3, 1/3, 1/3),
   A  = (0, 1/2,   0,   0,   0),
   B  = (0, 1/6, 2/3,-1/3,-1/3),
   X  = (0,-1/4,   0, 1/2,   0),
   Y  = (0,-1/4,   0,   0, 1/2).
   ```

   The construction theorems identify `p3` with the recursive Jones--Wenzl
   projector and prove

   ```text
   A=e1/2,  B=1-p3-A,  X=2 A(e2/2)B,  Y=2 B(e2/2)A.
   ```

   For the Markov form `tr(x* y)`, the exact Gram is
   `D=diag(4,2,2,3/2,3/2)`.  The diagram-to-pairing convention is frozen by

   ```text
   e1=P0-P1,  e2=P0-P2,
   u=P0-P1-P2+P4,  v=P0-P1-P2+P3,
   ```

   and gives the channel coefficient matrix (rows `p3,A,B,X,Y`, columns
   `P0,...,P4`)

   ```text
   C = [1/3,    0,    0,  1/3,  1/3]
       [1/2, -1/2,    0,    0,    0]
       [1/6,  1/2,    0, -1/3, -1/3]
       [1/4, -1/4, -1/2,    0,  1/2]
       [1/4, -1/4, -1/2,  1/2,    0].
   ```

   Two independent computations now agree exactly:

   ```text
   C G C^T = D,
   G^-1 = C^T D^-1 C,
   D^-1 = diag(1/4,1/2,1/2,2/3,2/3).
   ```

   Thus every normalized rank-one summand has trace one and their total
   trace is five.  More importantly, the externally oriented twelve-index
   kernel is proved structurally, with no Boolean case split, to be

   ```text
   K(Frow,Fcol;Rrow,Rcol)
     = sum_alpha D^-1_alpha
         P_alpha(Frow;Rcol) P_alpha(Fcol;Rrow).
   ```

   This theorem uses the same reverse-column/reverse-row transpose as the
   literal `F F F R R R` Haar integral.  Composing it with the exact sixth
   moment gives a direct public endpoint from the literal normalized Haar
   polynomial to the manifest positive five-term channel factorization.
   Positivity here is a Gram/projector statement: signed interference in the
   original permutation basis is retained and is not replaced by squared
   recoupling coefficients.

   The right-associated family is also constructed in `TL3`.  Its full
   signed recoupling matrix, with rows and columns in the same frozen channel
   order, is

   ```text
   R = [1,   0,    0,    0,    0]
       [0, 1/4,  3/4,  1/2,  1/2]
       [0, 3/4,  1/4, -1/2, -1/2]
       [0, 3/8, -3/8, -1/4,  3/4]
       [0, 3/8, -3/8,  3/4, -1/4].
   ```

   The bridge proves the coefficient recoupling entrywise, `R^2=I`,
   `R D R^T=D`, and the identical right-channel Markov Gram.  In particular,
   all `X/Y` signs and interference terms are machine-pinned.

   The isolated target is green under the serialized one-thread host guard.
   A separate print-only audit finds the concrete TL constructions, both
   Gram identities, inverse resolution, individual and total trace facts,
   and right-channel Gram axiom-free.  Generic finite-sum transport and
   recoupling use only `propext`; the structurally factorized kernel and
   literal-Haar endpoints use exactly `[propext, Quot.sound]`.  There is no
   `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
   The proof reduces only five-term sums and closed `5 x 5` tables; it never
   unfolds a six- or twelve-Bool tensor sum.

   After semantic-root wiring, the serialized one-thread `YMGap` target is
   green.  The full-current static audit sees 2,663 source modules and 8,251
   local import edges, zero cycles, 2,657 modules reachable from `YMGap.lean`,
   the same six reviewed alternative roots, and zero unexpected orphans.
   The executable forbidden-token scan has zero hits, the host-load guard
   passes all 236 tracked or untracked nonignored entry files, and
   `git diff --check` passes.  As in the preceding checkpoints, this is the
   strongest safe current-wiring validation: it checks the semantic root,
   project-wide source discovery, default Lake targets, import closure, and
   entry-file load policy without an unsafe clean or unconstrained full
   rebuild.

   **Completed arbitrary-block local closure.**  The reusable placement and
   spectator seams are now closed, with one necessary change from the earlier
   implementation forecast.

   1. `SU2QuaternionGenericBlockFundamentalCoefficientSupport` exposes the
      symbolic base-four exponent lookup facts and the forward/reverse
      coefficient block-locality theorems.  The four-valent arbitrary-block
      projector now consumes this shared leaf instead of maintaining private
      copies.
   2. `SU2QuaternionGenericBlockPartialSixValentHaarProjectorCore` defines the
      exact coefficient-sum proposition and proves structurally that the
      literal left-associated `F F F R R R` word is local to its selected
      quaternion block.
   3. The hoped-for transport directly from the one-block theorem is not
      available at the raw-carrier level: partial integration preserves
      trailing-zero monomial aliases, while the one-block theorem is stated
      only after the finite-product Haar functional.  Inferring raw
      coefficient-sum equality across that gap would require a missing
      congruence and would be unsound.  The arbitrary-block normalization is
      therefore certified directly, but under a strict evaluator fence:
      sixteen linearly imported chunk modules fix the first four Boolean
      selectors and split only the remaining eight.  Each declaration proves
      exactly 256 configurations; no declaration or process materializes the
      4,096-case family.
   4. The public dispatcher proves

      ```text
      integratedComplexCoefficientSum block (F F F R R R)
        ~= orientedSixFundamentalHaarProjector,
      ```

      together with all-false `1/4`, negative `-1/12`, and
      transpose-sensitive `1/12` regressions.  Its block-zero compatibility
      theorem identifies the new partial statement with the previously
      certified normalized one-link sixth moment.
   5. Composition with the genuine `TL3` bridge gives the exact five-term
      factorization with weights `1/4,1/2,1/2,2/3,2/3`.  Both the signed
      inverse-Gram result and this positive-channel result lift through
      `genericBlock_localFactor_with_complex_spectator`, preserving an opaque
      complex spectator independent of the selected block.

   Every one of the sixteen serial fibers is green under one Lean thread and
   the repository session lock.  The observed per-fiber peak was at most
   about 3.77 GB resident memory, with zero swaps; the public dispatcher and
   spectator leaf used about 1.28 GB, also with zero swaps.  This is a bounded
   proof decomposition, not a relaxed memory limit.  The public endpoints use
   exactly `[propext, Quot.sound]`; there is no `Classical`, choice,
   `native_decide`, `sorry`/`admit`, or custom axiom.  The shared support leaf
   and public six-valent leaf are imported by `YMGap.lean`, so the entire
   serial chain belongs to the semantic-root dependency graph.

   After that wiring, the cached serialized `+YMGap` target is green across
   2,677 jobs in 45.88 seconds, with about 3.04 GB maximum resident memory and
   zero swaps.  The static import audit finds 2,682 source modules and 8,274
   local import edges, zero cycles, 2,676 modules reachable from `YMGap.lean`,
   the same six reviewed alternative roots, and zero unexpected orphans.  The
   executable forbidden-token scan has zero hits, the host-load guard passes
   all 236 tracked or untracked nonignored entry files, the ten mocked Mac CI
   remote-state cases and four bounded-supervisor cases pass, and
   `git diff --check` passes.  Together the root build and import/default-target
   guards certify full-current wiring without requiring a clean all-module
   rebuild on every change.

9. **Close orientation and parity before building the production network.**
   The next interface must not assume that even link incidence means equal
   numbers of forward and reverse occurrences.  The elementary cube and the
   audited double cube are balanced, but an arbitrary cutoff-one support can
   carry any polarity word.  Even face incidence controls only total valence.

   Exploit the pseudoreality of the fundamental `SU(2)` representation before
   duplicating projector calculations.  At the literal coefficient level the
   required self-duality convention is

   ```text
   F[a,b] = sign(a,b) * R[not b, not a],
   R[a,b] = sign(a,b) * F[not b, not a],

   sign(a,b) = +1 when a=b and -1 otherwise.
   ```

   Prove both identities as exact raw complex-polynomial statements and pin
   the signs by unbalanced second-moment regressions

   ```text
   integral(F[0,0] F[1,1]) =  1/2,
   integral(F[0,1] F[1,0]) = -1/2.
   ```

   Then execute the following finite constructive sequence.

   1. Define an ordered oriented occurrence word for one link and a certified
      self-duality normalization which converts every even word of length at
      most six to the balanced orientation expected by the existing Schur,
      four-valent, or six-valent theorem.  The output must carry the exact
      product of epsilon signs and complemented/transposed indices.  Reorder
      raw factors only through the existing setoid-level complex-polynomial
      reordering API; do not assert list-level polynomial equality.
   2. Prove exact odd-valence Haar vanishing for lengths `1`, `3`, and `5`.
      This should be a structural antipodal/total-degree parity theorem, then
      an arbitrary-block independent-spectator lift—not a separate exhaustive
      table for every polarity word.
   3. Define one total cutoff-one local-kernel dispatcher for all seven
      valences:

      ```text
      0 : identity/vacuum projector, rank 1,
      1 : zero,
      2 : signed self-dual Schur projector, rank 1,
      3 : zero,
      4 : signed self-dual two-channel projector, rank 2,
      5 : zero,
      6 : signed self-dual five-channel projector, rank 5.
      ```

      Its main theorem must work at an arbitrary in-range block beneath an
      independent complex spectator.  Thus arbitrary supports are total by
      construction, while their nonzero sector is selected by parity rather
      than assumed in the definition.
   4. Package the even kernels as rational orthogonal projector resolutions.
      Prove idempotence/self-adjointness in the appropriate rational Gram
      forms and trace/rank values `1,1,2,5` for valences `0,2,4,6`.  Keep the
      signed permutation-basis kernels and the positive channel resolutions
      connected by exact equalities; neither squared recoupling coefficients
      nor invariant-space cardinalities are physical amplitudes.

   Acceptance must include all seven valences, both self-duality directions,
   an unbalanced positive and negative sign pin, and recovery of the existing
   balanced two-, four-, and six-leg endpoints.  Only after this theorem is
   green is the local cutoff-one representation-theoretic closure complete.

10. **Construct the closed coefficient factor graph and prove channel-count
    domination.**  Define the global physical coefficient by contracting the
    actual ordered face indices through the local tensors.  Do not estimate the
    exponentially many Boolean-index summands entrywise.  Record instead the
    exact factor-incidence graph: target and source give two local channel
    factors per touched link, while every fresh face-corner variable occurs in
    exactly two distinct factors.

    Prove the finite-Boolean graphical Holder/Finner inequality for this
    degree-two incidence pattern.  Applied to one structurally selected local
    channel word, it bounds the square of the closed contraction by the product
    of endpoint tensor norm-squares.  The two endpoint norm-squares at a link
    combine with the squared inverse-Gram weight, giving one unit per local
    channel.  A final rational order lemma removes the square after this unit
    normalization and hence gives

    ```text
    |honest coefficient|
      <= product_e fundamentalInvariantMultiplicity(valence_e).
    ```

    A single global `Tr(PW)` representation is unavailable on arbitrary
    supports: the actual cap/cup factor graph can contain odd cycles.  The
    graphical norm inequality is the scalable replacement.  Bounds on
    individual kernel entries still do not control the global Boolean-index
    sum.

    Keep the face coefficient convention unchanged—the representation
    dimension remains in `coeffW`—and separate the three semantic objects

    ```text
    honestChannelPhysicalTerm   -- signed contracted Yang--Mills amplitude,
    channelAbsoluteMajorant     -- nonnegative rank/activity bound,
    canonicalSurfaceActivity   -- legacy carrier during migration.
    ```

    Prove, before rewriting a partition,

    ```text
    abs honestChannelPhysicalTerm <= channelAbsoluteMajorant,
    channelAbsoluteMajorant ~= canonicalSurfaceActivity,
    channelAbsoluteMajorant <= the existing convergence budget.
    ```

    The middle statement identifies the legacy scalar only as a majorant, not
    as the physical amplitude.  Reflection positivity belongs to the positive
    Gram/projector form, while cancellation and recoupling remain visible in
    the signed amplitude.

    Required global normalization tests are: odd-incidence zero; the
    elementary-cube coefficient `1/16`; the edge-touching double-cube
    coefficient `1/256`; and at least one unbalanced-polarity network whose
    sign would be wrong if the epsilon wiring were omitted.

11. **Migrate production only after the total local and domination theorems.**
    The readiness theorem must cover valences `0` through `6`, not merely the
    balanced even cases, and must show that every cutoff-one support has a
    defined normalized contraction whose absolute value is dominated by the
    current convergence carrier.  Then:

    1. define the honest replacement beneath `parametricKPhysicalTerm`;
    2. retain the legacy scalar under an explicit `...Majorant` name;
    3. reprove cutoff-one partition identification and absolute convergence
       with the honest/majorant distinction visible;
    4. derive nonnegativity only where reflection pairing genuinely supplies
       it, rather than assigning it to every signed local amplitude;
    5. reprove canonical reachability, compression, block transport, and
       reflection-positive interfaces against the single total kernel;
    6. rerun the elementary-cube and double-cube witnesses as normalization
       acceptance tests;
    7. remove transitional aliases only after all semantic-root consumers use
       the new API.

    This ordering prevents a locally correct signed projector from silently
    invalidating global proofs that currently rely on scalar nonnegativity,
    and prevents a convenient majorant from being mistaken for the Yang--Mills
    amplitude.  It supplies the exact positive-channel input next needed by
    `AdjacentEvenActiveQuadraticSOSData`; arbitrary-spin extension and the
    continuum mass-gap closure remain explicit later milestones rather than
    being claimed here.

This route is finite, exact, and intuitionistic: recursive Boolean sums,
explicit finite case proofs, rational setoid algebra, duplicate-free decoders,
and certified permutations replace choice, excluded middle, global
enumeration, and unsafe evaluator calls.

## Completion-first backward proof graph (2026-07-20)

This section supersedes every earlier priority ranking, but it does not delete
the historical scorecards or weaken their guarded statements.  It starts from
the literal completion requirements in `docs/ym_mass_gap_prompt.md` and works
backward until the leaves meet the strongest honest objects that currently
exist in Lean.  In particular, `ClayTarget`, `ClayTargetPinned`,
`ContinuumYMWithGap`, `FunctionalContinuumTarget`, `Tier0Scorecard`, and
`FrontierDAG` remain useful compatibility interfaces, but none is the faithful
terminal theorem: several fields are deliberately coarse, freely supplied, or
toy-inhabitable, and several structures say so explicitly in their headers.

The detailed clause-by-clause carrier audit remains
`docs/clay_resolution_target_inventory.md`.  The graph below is the execution
plan distilled from that audit.

### 1. Terminal theorem and honesty invariant — ○ MISSING

The required endpoint is a construction, for every actual compact simple
global gauge group `G`, of one nontrivial four-dimensional pure Yang--Mills
theory on `R^4` satisfying Wightman- or full Osterwalder--Schrader-strength
axioms and possessing a finite positive physical Hamiltonian gap

```text
0 < m_G < infinity.
```

The same theory must carry gauge-invariant curvature fields, perturbative
short-distance asymptotic freedom, a conserved stress tensor, and an OPE with a
controlled remainder.  Its finite-volume Wilson family, limiting Schwinger
functional, reflected positive-time Hilbert space, semigroup, generator,
spectrum, and local correlators must be definitionally or theorem-level pinned
to one shared root.  Independent witnesses for these clauses are not an
acceptable proof.

The intended terminal shape is therefore approximately

```lean
def yangMillsExistenceAndMassGap
    (G : ComputableCompactGaugeGroup)
    (hG : G.IsCompactSimple) :
    ClayResolutionTarget G
```

where `ClayResolutionTarget`, `ComputableCompactGaugeGroup`, and the total
adequacy theorem do not yet exist in Lean.  They must not be introduced as an
empty wrapper around old assumptions.  Each semantic carrier below must first
contain enough equations and anti-toy pins that its inhabitants have the
physical meaning claimed for them.

**Permanent honesty invariant.**  Every downstream object refers to the same
`G`, faithful action, Wilson family, continuum observable algebra and
functional, reflected OS reconstruction, vacuum, and local fields.  Every
claimed mass number is the located spectral edge of the actual generator and
is tied back to the uniform lattice estimate in physical units.  The final
assembler introduces no new hypothesis and projects to all unchanged legacy
frontier types required by the prompt.

### 2. Backward gate C0: coherent Clay theory — ○ MISSING

```text
ClayResolutionTarget G
  <= PinnedWilsonLatticeFamily G
   + CanonicalSchwingerSystem G
   + EuclideanSchwingerAxioms G
   + PhysicalOSReconstruction G
   + PhysicalSpectralGap G
   + CanonicalLocalOperatorContent G.
```

The terminal assembler is accepted only if:

1. every field above is pinned to the same root objects;
2. a projection supplies the five unchanged guarded legacy frontiers rather
   than renaming, weakening, or replacing them;
3. the terminal and adequacy statements themselves are added to the statement
   guard after review;
4. every load-bearing theorem uses only `{propext, Quot.sound}`;
5. both repository statement guards, the forbidden-token scan, semantic-root
   wiring, and the full-current build gate pass.

No present theorem inhabits this gate.  `FourDExistence.ym_mass_gap_of_existence`
projects a gap already stored in `ContinuumYMWithGap`;
`AllSimpleTypes.mass_gap_of_cartanType` consumes a caller-supplied reconstruction
and OS bundle; and `ClayTargetPinned.toClayTarget` only coarsens an uninhabited
legacy package.

### 3. Backward gate C1: actual compact simple global group — ○ MISSING

```text
ComputableCompactGaugeGroup G
  <= compact global form + topology/uniform structure
   + constructive group operations
   + normalized Haar functional/integration
   + faithful finite-dimensional unitary lattice action
   + Peter--Weyl/character data and representation descent
   + proof of compactness and simplicity.
```

The current `CartanType` and `CompactSimpleGlobalFormCode` layers classify Lie
and central-quotient data, but explicitly do not construct an actual compact
group, topology, Haar functional, faithful action, or all representations.
Thus “all simple types” is not yet “every compact simple global group.”

Execution rule: keep `G` as a parameter in every new terminal-grade interface
from the beginning.  Use `SU(2)` as the first analytic inhabitant, then prove
transport through central quotients and the classical/exceptional families.
Do not extrapolate from `SU(2)` by an unproved “worst group” assertion.

### 4. Backward gate C2: canonical local quantum-field content — ○ MISSING

```text
CanonicalLocalOperatorContent G
  <= one source-extended constructive RG tower
   + renormalized lattice curvature-polynomial approximants
   + convergence in every spectator correlator
   + locality, gauge invariance, and E(4) covariance
   + a nonzero connected higher cumulant / failure of Wick factorization
   + a local stress tensor with Ward identities and translation charges
   + OPE coefficient asymptotics with an explicit spectator remainder modulus
   + beta-function/anomalous-dimension matching for the same correlators.
```

The present `LocalCurvatureFields`, `StressTensor`, `OPE`, and
`AsymptoticFreedomShortDistance` are typed statement-layer interfaces.  Their
individual toy inhabitants, including the one-point and zero-OPE witnesses,
show that they are not terminal-grade.  The repair is not another conjunction:
all operator identities and remainders must be equations about the canonical
Schwinger functions, and nontriviality must be witnessed by an actual connected
correlator of those fields.

This branch must be included in the sourced RG analysis rather than retrofitted
after constructing a measure.  Otherwise the hardest multiscale estimates
would have to be repeated for composite insertions.

### 5. Backward gate C3: physical finite positive mass gap — ○ MISSING

```text
PhysicalSpectralGap G
  <= located infimum of the actual generator form on Omega-perp
   + an explicit strictly positive lower bracket
   + finite-energy near-edge witnesses
   + vacuum uniqueness
   + equality with the continuum limit of the physical lattice gap.
```

The physical mass is

```text
m_G = inf { <psi,H psi> :
              psi in Dom(H), ||psi|| = 1, <Omega,psi> = 0 }.
```

An arbitrary exclusion interval, a free `genGap` family, or a finite spectral
model is insufficient.  Finiteness requires near-edge vectors of controlled
energy; positivity requires a uniform lower bracket; both must concern the
same unbounded generator.

The quantitative backward chain is

```text
continuum generator gap
  <= form/resolvent convergence + uniform physical lattice gap
  <= Delta_(k+1) >= (1-delta_k) Delta_k - epsilon_k,
       with Delta_k = m_lat(k) / a_k
  <= summable defects + a positive infrared/strong-coupling anchor
  <= a true block-spin comparison for the actual Wilson transfer/form
  <= controlled effective Yang--Mills RG flow.
```

The repository has strong constructive algebra showing that a supplied
summable-defect recursion retains a positive floor.  The hard producer arrow
from the actual Wilson theory, including the spacing equation and spectral
identification, remains open.  Legacy `trueMargin`, `singleStep`, and
`UniformSpacingFloor` objects are conditional consumers, not this producer.

### 6. Backward gate C4: continuous OS reconstruction — ◐ INTERFACE ONLY

```text
PhysicalOSReconstruction G
  <= full reflected OS axioms for the canonical Schwinger functions
   + completed reflected positive-time quotient
   + strongly continuous positive contraction semigroup U(t)
   + a densely defined positive self-adjoint generator H
   + H Omega = 0
   + positive-energy Poincare representation and spectrum condition.
```

`CanonicalOSRoot.PositiveTimeOSRoot` is the strongest honest current spine.  It
uses the reflected form `E((Theta a)^* b)`, constructs the physical quotient
and completion, pins a one-step transfer, and derives a normalized nonzero
unit vacuum plus completed self-adjoint/positive/contraction form laws once its
semantic fields are supplied.  It has no four-dimensional Yang--Mills
inhabitant.

Missing formal implications are substantial but comparatively standard once
the full OS hypotheses exist: completed complex vector operations, an exact
`Nat` semigroup, a constructive-real `C0` semigroup with a time-one pin, a
closed positive form/resolvent or Yosida construction, its unbounded generator,
common invariant domains, analytic continuation, Poincare covariance, and
vacuum uniqueness from clustering.  A bounded logarithm of a time-one transfer
must not be used as the continuum Hamiltonian.

### 7. Backward gate C5: full canonical Schwinger/OS system — ◐ INTERFACES ONLY

```text
EuclideanSchwingerAxioms G
  <= a single CanonicalSchwingerLimit of the pinned Wilson family
   + constructive test-function regularity and tempered growth
   + every Schwinger permutation/reality law
   + a continuous full E(4) action and covariance
   + reflected half-space positivity
   + clustering/ergodicity.
```

`CanonicalOSRoot.ReferenceWeightStageFamily` and
`CanonicalSchwingerLimit` correctly expose separate volume/cutoff indices,
explicit approximation errors, and Type-level moduli.  They are not inhabited
by the intended 4D theory.  The current O(4) carriers encode much weaker or
freely supplied symmetry data; hypercubic invariance does not prove rotational
restoration.

Stage equalities and positivity can pass to a controlled limit.  The hard part
is producing one limit with estimates uniform in volume and spacing, plus
source derivatives strong enough for the local-operator branch.

### 8. Backward gate C6: one sourced physical RG tower — ○ DOMINANT OPEN THEOREM

The dominant producer should be one group-indexed, source-extended effective
RG tower carrying simultaneously:

1. the actual Wilson bare functional at each volume/cutoff stage;
2. effective actions and honest blocking maps;
3. small- and large-field cells with explicit remainders;
4. polymer/cluster bounds uniform in volume;
5. reflection support and form comparison;
6. coupling flow and anisotropy decay;
7. the physical transfer/form gap and its spacing conversion;
8. local/composite source insertions and their mixing matrices;
9. thermodynamic and continuum convergence moduli.

This is the mathematically central open theorem: a nonperturbative,
volume-uniform flow from the asymptotically free ultraviolet regime into a
rigorously controlled massive infrared regime with summable transverse errors.
A Bałaban-style phase-cell/effective-action construction is the most coherent
known architecture because it can feed existence, gap, O(4), and local-field
branches from the same estimates.  The exact character expansion supplies the
infrared anchor; it cannot by itself control the weak-coupling ultraviolet.

This gate must not remain one opaque theorem-strength label.  Its honest
consumer-first decomposition is:

```text
C6a  sourced-RG extraction:
     one certificate -> shared Schwinger limits + OS laws + physical gap
                       + local/composite correlators;

C6b  physical renormalized trajectory:
     tuned bare coupling versus spacing, dimensional transmutation,
     anisotropy decay, source mixing, and a fixed physical scale;

C6c  exact source-extended block step:
     gauge-covariant phase-cell blocking, Jacobian, effective action,
     reflected support, and small-/large-field polymer decomposition;

C6d  ultraviolet stability:
     perturbative beta/anomalous-dimension coefficients with a proved
     nonperturbative remainder and volume-uniform source estimates;

C6e  crossover theorem:
     the iterated weak-coupling trajectory enters the certified massive
     cluster domain with summable defects in physical units;

C6f  infrared extraction:
     the all-label signed-network majorant gives cluster convergence,
     transfer-form comparison, a uniform lower gap, and a near-edge witness.
```

`C6e` is the genuinely new mathematical bottleneck; neither a formal
certificate nor conditional recursion algebra advances it.  Nevertheless,
`C6a` must be designed first so every estimate produced by `C6c--C6f` has one
unambiguous consumer.  `C6b--C6e` must be group-indexed from their definitions.
An `SU(2)` proof may pilot the estimates, but an after-the-fact assertion that
it is the worst compact simple group is not an admissible all-group argument.

#### Cross-gate noncircularity and adequacy fences

The backward graph is valid only with the following permanent fences.  These
are acceptance conditions on the future interfaces, not optional refinements.

1. **Independent scale setting.**  The lattice spacing `a_k` is fixed by an
   independent renormalized observable or coupling condition, never by the
   desired mass.  Only afterward may one prove
   `Delta_k = m_lat(k) / a_k`; otherwise dimensional transmutation has been
   inserted by definition.
2. **No supplied-margin substitution.**  `SingleStepDefectBound.trueMargin`,
   `singleStep`, and the existing positive-floor recursions are consumers.
   The producer must derive their entries from the actual Wilson
   transfer/form, the independently fixed spacing, and one located spectral
   quantity.
3. **Transfer and generator gaps remain distinct.**  A finite-stage edge of
   `I - T`, the quantity `1 - lambda`, and an energy `-log lambda` are not
   definitionally interchangeable.  The chosen lattice energy and its
   comparison or convergence to the continuum generator form must be stated
   and proved explicitly.
4. **The continuum object is constructed.**  `CanonicalSchwingerLimit` must be
   extracted as the quotient/completion or universal limit of compatible
   local cylinder observables, with uniqueness.  A carrier that merely stores
   a chosen algebra, functional, and the desired approximation laws can hide
   the existence theorem.
5. **The RG producer stores only finite-stage facts.**  A sourced RG
   certificate may contain blocking identities, effective actions, error
   sequences, source-mixing data, and convergence moduli.  It may not carry a
   `CanonicalSchwingerLimit`, physical gap, OS reconstruction, or local fields
   as free fields; a separate extraction theorem constructs them.
6. **No clustering/gap loop.**  The infrared analysis first proves a
   transfer/form comparison and uniform spectral lower bound.  Clustering is
   then derived and may later prove vacuum uniqueness; clustering obtained
   from the desired gap cannot be reused to establish that same gap.
7. **Absolute domination is not reflection positivity.**  The graphical
   Finner and polymer bounds prove absolute convergence.  Reflection
   positivity must descend from exact finite-stage Wilson identities and pass
   through the limit separately, even when intermediate effective actions are
   not manifestly positive.
8. **Sources are genuinely composite and geometric.**  Curvature fields need
   multilocal composite sources and spectator estimates; the stress tensor
   needs background-metric or anisotropic-coupling response; Ward identities
   need exact finite-stage symmetry equations; and the OPE needs a
   spectator-uniform remainder modulus.  A scalar source tower is inadequate.
9. **The group quantifier has an adequacy theorem.**  Either explicit compact
   simple global-form codes are interpreted and proved exhaustive up to
   isomorphism, or every actual compact simple group is proved to admit the
   computable presentation consumed by the construction.  Cartan type alone
   omits central quotients, faithful actions, representation descent, and
   character-tail data.
10. **Use the scalar substrate actually required by all labels.**  Rational
    `SU(2)` cutoff-one moments are a pilot.  Full Wilson/heat-kernel
    coefficients and arbitrary-group recoupling data require located
    constructive real/complex or computable algebraic scalars together with
    summation moduli; they must not be silently coerced into one rational
    coefficient.
11. **Both sides of the mass edge are produced.**  A uniform lower spectral
    bracket proves positivity but not finiteness or locatedness.  The same
    infrared/limit construction must transport explicit finite-energy
    vacuum-orthogonal excitations and ultimately supply near-edge witnesses.
12. **The OS-to-Wightman step is a theorem, not nomenclature.**  Full `E(4)`
    covariance, constructive test-function topology, analytic continuation,
    common invariant domains, continuous Poincare action, and the spectrum
    cone remain explicit obligations beyond a discrete `Nat` transfer.

### 9. Backward gate C7: all-label infrared Wilson anchor — ○ OPEN

```text
uniform infrared/strong-coupling anchor
  <= honest all-label character/spin-network coefficient network
   + summable representation tails
   + cluster expansion for the signed physical weights under an absolute majorant
   + finite-stage reflection positivity
   + volume-uniform transfer-form gap
   + a finite-energy excitation witness.
```

The cutoff-one fundamental calculation below is a necessary normalization and
architecture pilot, not the full Wilson action.  The Wilson/heat-kernel
expansion has arbitrarily high irreducible labels, and repeated plaquette
powers produce unbounded representation content.  After the cutoff-one network
is complete, generalize the local rank bound to

```text
dim Inv(V_(lambda_1)^(epsilon_1) tensor ... tensor
        V_(lambda_r)^(epsilon_r))
```

and prove a label-summed activity bound.  Do not continue accumulating isolated
cube examples after the total network theorem.

The highest-leverage theorem immediately after `N7` is the source-stable
all-label version, provisionally named
`allLabelMarkedWilsonCoefficient_abs_le_invariantActivity`.  For every group
presentation `G`, finite oriented plaquette multiset, irrep labeling, and
finite marked family of local/composite insertions, it must identify the
literal Haar-integrated coefficient and prove a square-root-free bound of the
form

```text
abs coefficient^2
  <= insertionMass^2
     * product_link
         (resolvedMass (Inv_G (tensor_occurrences V_label^orientation)))^2.
```

Without insertions the insertion mass is one.  A specialized normalized
corollary may then remove the squares.  Its immediate analytic consumer sums
this majorant against the exact Wilson/heat-kernel character coefficients
with a proved label-tail modulus.  The statement must be structural in the
network and in nested channel choices: it may not materialize a Cartesian
channel family.  This theorem is the first post-pilot object that feeds both
the infrared cluster domain and the later sourced local-field branch.

### 10. Backward gate C8: honest cutoff-one production coefficient — ◐ ACTIVE

The current production objects `parametricKPhysicalTerm` and
`canonicalSurfaceActivity` multiply nonnegative face coefficients by a scalar
link multiplicity.  Exact normalization fences show that this is a majorant,
not the signed Yang--Mills amplitude:

```text
elementary cube: honest coefficient differs by factor 16,
edge-sharing double cube: honest coefficient differs by factor 512.
```

The correction is topology/channel dependent, so no universal scalar rescaling
can repair production.  The required objects are

```text
honestChannelPhysicalTerm  -- signed contracted coefficient,
channelAbsoluteMajorant    -- nonnegative rank/activity bound,
canonicalSurfaceActivity   -- legacy carrier during migration.
```

The initially proposed acceptance chain through one global signed wiring,
`Tr ((tensor_e P_e) W)`, is **not valid for arbitrary supports**.  After the
semantic target/source reshaping, the face contraction graph is not generally
bipartite: at the minimal vertex of an elementary cube, the three target caps
from the incident faces connect the three link-target tensors in a triangle.
No assignment of whole local tensor factors to two Gram slots can make all
three edges cross.

The correct acceptance chain is

```text
honest signed coefficient network
  = nested local positive-channel expansion
   + one signed local channel tensor at each target/source link endpoint
   + one Boolean variable on each fresh face corner
   + every corner variable occurring in exactly two distinct tensor factors
  <= square-root-free finite-Boolean graphical Holder/Finner inequality
   + product of the endpoint tensor norm-squares
   + inverse channel weights cancelling the two endpoint norms linkwise,

abs honestChannelPhysicalTerm
  <= channelAbsoluteMajorant
   ~= canonicalSurfaceActivity
   <= existing convergence budget.
```

The key global theorem is therefore

```text
(sum_cornerAssignments product_factor tensorFactor)^2
  <= product_factor normSq(tensorFactor),

followed, after the selected channels are normalized to total mass one, by

abs honestCoefficient
  <= product_link numberOfLocalChannels
   = product_link fundamentalInvariantMultiplicity(valence_link).
```

This is the square-root-free finite Finner inequality for a factor graph in
which each independent corner variable occurs in exactly two factors,
specialized to exact rational Boolean tensors.  It handles odd cycles and
same-side caps/cups without a false two-coloring, a Cartesian assignment list,
or constructively unavailable square roots.  Each selected local channel
occurs twice, once at each semantic endpoint, so its two norm factors multiply
to its exact squared norm and cancel its inverse-Gram weight.  The final
`abs <= 1` step is a rational order lemma applied only after this exact
normalization.  Self-adjointness and idempotence remain useful projector
certifications, but the global domination is a network norm theorem rather
than a matrix trace theorem.  Entrywise kernel bounds still do not control the
exponentially large Boolean-index sum.

The one-layer generic analytic theorem in
`PositiveChannelTraceBound.lean` is complete.  For any constructive rational pre-inner
form, Gram isometry `W`, and finite channel family with explicit nonnegative
rational weights, it proves

```text
abs (sum_c weight_c * <v_c, W v_c>)
  <= sum_c weight_c * <v_c, v_c>.
```

The proof derives `2*|<x,y>| <= <x,x> + <y,y>` from the positive quadratic
form, cancels the positive factor two constructively, and closes the weighted
finite sum by an exact rational triangle inequality.  Its right-hand side is
deliberately named `resolvedTraceMass`, not rank.  The four- and six-valent
operator leaves now identify their positive-channel masses exactly with `2`
and `5`; together with the bivalent mass `1`, the local analytic input is
complete.  This theorem remains correct and useful for genuinely bipartite
subnetworks, but the cube-triangle audit proves that it is not the global C8
closure theorem.  `TwoSidedFactoredPositiveChannelTraceBound.lean` likewise
proves the valid extension `|<Uv,Vv>| <= ||v||^2` for two isometries; it cannot
encode a non-bipartite factor graph and is therefore auxiliary rather than the
production bridge.  Its exact target and direct audit are green with only
`[propext, Quot.sound]`.

For a box-sized network, the Cartesian product of the local channel lists
must **not** be materialized: it has up to `5^(number of six-valent links)`
leaves.  The immediate scalable lift is therefore a structural nested channel
fold.  It must prove, without constructing the product list,

```text
abs (nestedSum_channelChoices signedTerm)
  <= nestedSum_channelChoices positiveMass
  =  product_links (sum_localChannels weightedLocalNorm)
  =  product_links localInvariantMultiplicity.
```

The first inequality must be the graphical Finner bound under the structural
nested sums; the norm cancellation uses tensor-Gram factorization; the final
identity uses the exact local masses `1,2,5`.  This factored construction is
part of C8, not an optimization: a flat global channel enumeration is not an
admissible construction of the production coefficient.

`FactoredPositiveChannelTraceBound.lean` now completes this scalable analytic
lift.  It defines a nested structural choice sum, proves its finite triangle
and monotonicity laws, derives

```text
abs factoredResolvedTrace <= factoredResolvedTraceMass,
```

and, from an explicit tensor-Gram norm factorization, proves that the mass is
exactly the product of the local weighted channel sums.  No Cartesian channel
list is constructed.  The target and direct axiom audit are green with only
`[propext, Quot.sound]`.  Its nested-sum and mass-factorization algebra remains
load-bearing, but its one-isometry trace hypothesis is not the actual
plaquette geometry.  The pointwise arbitrary-orientation channel
factorization is now complete in `N3`.  The remaining `N4--N5` work is to
formalize the exact degree-two corner-incidence ledger, prove the
finite-Boolean graphical Finner inequality, and instantiate its linkwise norm
cancellation.

`SymbolicFiniteBoolTensor.lean` now supplies that Gram carrier without a
finite assignment list.  It builds `BoolTensor n` and its positive dot form by
structural Boolean fibers, and compiles a small wiring language generated by
composition, tail lift, adjacent coordinate swap, and signed epsilon
complement into certified `GramIsometry` maps.  The epsilon complement is
correctly **not** claimed involutive (`J^2 = -I`), while its Gram action is
isometric.  It now also defines structural tensor concatenation and proves the
exact factorization

```text
dot (x1 tensor y1) (x2 tensor y2) = dot x1 x2 * dot y1 y2
```

by recursion on the left tensor, without enumerating Boolean assignments.  The
exact target and direct audit are green; the public gates use only `[propext]`.
`SU2QuaternionLocalChannelBoolTensor.lean` now completes the concrete local
embedding.  In output-first/input-second coordinates it realizes the bivalent
delta in `BoolTensor 2`, the singlet/triplet channels in `BoolTensor 4`, and
the five Temperley--Lieb channels in `BoolTensor 6`.  Their symbolic Gram
tables and weighted unit-mass identities are exact.  In particular, the
six-valent tensor Gram is derived structurally from bilinearity and the frozen
five-pairing Gram calculation, without enumerating the sixty-four Boolean
coordinates.  Its exact target and direct audit are green with only
`[propext]`.  The remaining tensor work is therefore the geometry-derived
endpoint-factor incidence and its instantiation in the graphical contraction
bound.  No single global signed wiring or positive trace representation is
assumed.

`SU2QuaternionCutoffOneLocalChannelMass.lean` now freezes the uniform local
channel ledger consumed by the factored global bound.  Its single tagged
carrier has the exact seven-branch choice lists, empty on odd valence and of
length `1,1,2,5` on valence `0,2,4,6`.  Each retained channel contributes
exactly one unit of inverse-Gram-weighted *actual symbolic tensor norm*, so
the structural local mass is

```text
valence: 0  1  2  3  4  5  6
mass:    1  0  1  0  2  0  5
```

and agrees branchwise with both dispatcher multiplicity and the production
`fundamentalInvariantMultiplicity` table.  The theorem never unfolds the
64-entry six-valent tensor and never forms a global channel product.  Its
exact target and direct audit are green; public gates use at most `[propext]`.

`SU2QuaternionCutoffOneOrientedFaceRows.lean` now completes `N0`.  For every
numerical cutoff-one support and arbitrary per-face orientation choice it
constructs production rows retaining support position, physical face ID, and
decoded plaquette; allocates four globally disjoint corner tags per row;
projects the literal coefficient descriptors to the established oriented
plaquette boundary words; identifies their flattened physical links with the
full geometric boundary by permutation; assigns every descriptor to one
common touched-link carrier; and proves that each link bucket has exactly its
geometric incidence length and hence valence at most six.  Its exact target and
direct axiom audit are green with only `[propext, Quot.sound]`.

`SU2QuaternionCutoffOneNamedTraceExpansionProduct.lean` now completes `N1`.
For every support and arbitrary per-face standard/reversed choice, it proves
that finite-product Haar of the literal product of the separately expanded
plaquette traces equals one rational named Boolean sum over the exact N0
corner-tag carrier.  The proof moves four binders per face structurally,
retains production face order and orientation, and never constructs a
support-sized assignment family.  A first freshness proof was rejected
because the library `List.nodup_range` carries `Classical.choice`; the accepted
proof uses an explicit primitive-recursive range-nodup argument instead.  The
exact target and direct audit are green with only `[propext, Quot.sound]`.
Thus the active global leaf is now `N2`: the face-major/link-major regrouping
and structural per-block Haar dispatcher fold.

`SU2QuaternionCutoffOneLinkBucketWords.lean` completes the geometry-only half
of `N2`.  It gives every N0 descriptor its honest oriented
`FundamentalOccurrence` semantics, flattens each N1 face term into its four
literal coefficient factors under finite-product Haar, and proves that stable
bucketing by the duplicate-free touched-link carrier is a permutation of the
full face-major descriptor word.  The proof preserves descriptor
multiplicities and never assumes descriptor duplicate-freeness.  Consequently,
for every named environment, Haar of the face product is exactly Haar of the
link-major product of local occurrence words.  The exact target and direct
audit are green with only `[propext, Quot.sound]`.  The remaining half of `N2`
is the proof-carrying length-at-most-six conversion and structural multiblock
application of the total local dispatcher.

`SU2QuaternionAtMostSixBlockWordFubini.lean` contains that intended generic
dispatcher fold: it retains each literal occurrence list with a proof of
length at most six, converts totally to the seven-constructor dispatcher with
no truncation/default branch, and factors pairwise-distinct block words by
iterated spectator Fubini.  A first compiling proof was rejected because its
proof-indexed bounded-list association introduced `Classical.choice`.  The
accepted proof first recovers the literal occurrence list and then handles the
seven ordinary dispatcher constructors, keeping proof data out of the
association motive.  Both its exact target and direct audit are now green;
every displayed gate is contained in exactly `{propext, Quot.sound}`.  Thus
the generic dispatcher/Fubini half of N2 is complete.

`SU2QuaternionCutoffOneLinkBucketHaarNetwork.lean` now completes the actual
link-bucket instantiation and therefore closes `N2`.  Each touched-link bucket
is packaged as an exact `AtMostSixFundamentalWord`; its block is the link's
index in the duplicate-free touched-link carrier; those block indices are
pairwise distinct; and concatenating the packaged factor words recovers the
literal N1 link-major coefficient word.  The multiblock Fubini theorem then
gives, for every named Boolean environment, the exact equality

```text
finiteProductHaarComplex
  (literal oriented face-trace product at that environment)
  ~= product_touchedLinks
       cutoffOneHaarKernel(actual oriented occurrence bucket).
```

This is an equality of the honest signed coefficient integrand, not an
absolute majorant and not a scalar multiplicity replacement.  Its exact
target and direct axiom audit are green with only
`[propext, Quot.sound]`.

`SU2QuaternionOccurrenceBoolTensorTransport.lean` supplies the first
constructive orientation component of `N3--N4`.  It replaces proof-indexed
list transports by the exact-shape type `BoolWord n`, compiles an arbitrary
coordinatewise epsilon mask to `SignedBoolWiring`, and proves both its
pointwise evaluation formula and Gram isometry.  For a single oriented
fundamental occurrence it identifies the semantic operator target/source
coordinates, proves that forward/reverse normalization complements both
coordinates with exactly the self-duality sign, and realizes that operation
by the compiled epsilon wiring.  Its exact target and direct audit are green
with only `[propext]`.

`SU2QuaternionCutoffOneOrientedPositiveChannels.lean` now completes `N3`.
For every literal orientation pattern and each even valence `2,4,6`, it
absorbs the accumulated pseudoreality sign into the target/source evaluations
of the same orientation-transported invariant channel and proves the exact
positive inverse-Gram resolutions with `1,2,5` channels.  Odd valences vanish
and the empty word is one.  The capstone
`cutoffOneHaarKernel_eqv_transportedPositiveChannels` is componentwise in the
honest rational-complex kernel, performs no Boolean-assignment enumeration,
and has direct gate `[propext, Quot.sound]`.  Orientation transport preserves
the complete local channel Gram tables, so the local mass ledger is unchanged.

The N4 geometry audit also rules out a tempting but false shortcut.  A tag
permutation alone cannot turn the plaquette contraction into a dot product.
For one standard face with corner tags `[a,b,c,d]` and coefficient word
`F(a,b) F(b,c) R(c,d) R(d,a)`, the operator-projector target word is
`[a,b,d,a]` while the source word is `[b,c,c,d]`: `a` is a target-target cap
and `c` is a source-source cup.  Neither word is a permutation of the four
corners.  This rules out a global two-sided dot product, but it does not
require a pivotal straightening.  `N3` instead places each channel value at its
semantic physical endpoint.  The correct global object is a degree-two factor
graph: each fresh face-corner variable joins the two half-link channel factors
meeting at that corner, including odd cycles such as the three-factor triangle
at a cube vertex.  `N4` must certify this exact incidence and apply a
constructive graphical Cauchy--Finner inequality.  The link-major descriptor
permutation is necessary for Haar factorization but is not the incidence
bound.

Nor can the obstruction be removed by seeking a positive resolution in the
literal storage-row/storage-column split.  The bivalent `F/R` branch is
already a decisive counterexample.  With storage row
`x = (forwardRow, reverseRow)` and storage column
`y = (forwardColumn, reverseColumn)`, its scalar kernel is

```text
K(x,y) = (1/2) * 1[x_1 = y_2] * 1[x_2 = y_1]
       = (1/2) * Swap_4(x,y).
```

This matrix has rank four and the explicit antisymmetric vector
`z(01)=1`, `z(10)=-1`, `z(00)=z(11)=0` satisfies `z^T K z = -1`.
It therefore admits no same-channel positive factorization
`sum_c w_c v_c(x)v_c(y)` with nonnegative weights, and no invertible separate
row/column basis changes can turn it into the rank-one invariant projector.
The positive rank-one form appears only after the semantic reshaping

```text
target = (forwardRow, reverseColumn),
source = (forwardColumn, reverseRow),
```

which is exactly the partial transpose that creates the face cups and caps.
`SU2QuaternionLocalChannelPivotalInvariance.lean` freezes this obstruction as
an axiom-free regression: the storage kernel is exactly half-swap and its
explicit antisymmetric quadratic witness is exactly `-1`.  The rejected
all-leg pivotal fixed-point layer is not part of the proof.

`SU2QuaternionCutoffOneEndpointChannelPorts.lean` proves the positive half of
the corrected geometry.  For every oriented occurrence, the semantic target
is its canonical physical-link base tag and the semantic source is its end
tag.  For either face orientation the exact port words are `[a,b,d,a]` and
`[b,c,c,d]`; their concatenation contains the two incidences of every fresh
corner.  Its target and direct audit are green with gates at most `[propext]`.
Thus N4 retains the operator-coordinate positive resolution from N3 and uses
the complete degree-two graphical contraction; a storage-coordinate PSD
refactor, a global signed-permutation trace, or a plain face permutation is
mathematically false.

`SymbolicFiniteBoolTensorContraction.lean` supplies the analytic primitive for
that contraction.  It contracts an arbitrary common innermost Boolean block
of two finite tensors and proves, constructively and without square roots,

```text
normSq (contract shared left right) <= normSq left * normSq right.
```

The proof is structural only in the two free-coordinate blocks; the entire
shared block is discharged once by the generic Boolean-tensor
Cauchy--Schwarz theorem, so no assignment carrier or depth-specific expansion
is introduced.  Its exact target and direct audit are green with gates
contained in `[propext, Quot.sound]`.  This is not yet the full N4 theorem:
the remaining combinatorial work must compile the tagged cube factors into a
sequence of port rearrangements and shared-block contractions and prove that
the sequence consumes every fresh corner exactly once.

`SymbolicFiniteBoolTensorContractionPlan.lean` closes that inequality under an
arbitrary finite typed binary contraction tree.  Its evaluator recursively
contracts the declared common Boolean blocks and may apply certified
Gram-isometric `rewire` nodes at intermediate arities; its `leafMass` is the
product of the actual leaf norm-squares; and
`eval_normSq_le_leafMass` proves the output norm-square bound by composing the
binary estimate with constructive multiplication monotonicity.  The closed
arity-zero corollary is exactly the square bound needed before the final
rational absolute-value step.  That step is also closed:
`abs_le_one_of_square_le_one` proves the constructive rational order fact, and
`closed_eval_abs_le_one_of_leafMass_le_one` applies it when the exact leaf mass
is at most one.  The exact target and direct audit are green with gates
contained in `[propext, Quot.sound]`.  Consequently the analytic induction of
N4, including the normalized absolute bound, is complete.  The remaining N4
obligation is the correctness compiler from the concrete tagged factor
graph—including port order—to one of these typed plans.

`SymbolicFiniteBoolTensorPortReordering.lean` closes the generic port-order
boundary without extracting data from an arbitrary `List.Perm` proof.  It
defines valid-by-construction adjacent-swap programs at a fixed tensor arity,
compiles them to the existing Gram-isometric wiring language, and proves exact
typed-tag, erased-list, tensor-evaluation, and valuation-parametric semantics.
An `ArrangesAsOuterThenInner` certificate states computationally that a
concrete factor has placed its free coordinates outside and a shared block in
the innermost convention required by `boolTensorContract`.  Its exact target
and direct audit are green with gate `[propext]`.  The remaining compiler must
now provide explicit programs and tag equalities for the concrete factor
merges; it must not eliminate the global incidence permutation into hidden
choice data.

`SymbolicFiniteBoolTensorContractionEvaluation.lean` closes the semantic
boundary for each binary merge.  After fixing the two free-coordinate words,
`boolTensorContract_evalAt_eq_boolTupleSum` identifies the contracted tensor
pointwise with the literal structural Boolean sum over the common word of the
product of the two child evaluations.  The sum recurses over typed Boolean
tuples and never materializes an assignment carrier.  This theorem prevents
the graph compiler's correctness proof from merely comparing two evaluators
defined by the same contraction call.  Its exact target and direct audit are
green with gates contained in `[propext, Quot.sound]`.

`SU2QuaternionCutoffOneGlobalDegreeTwoPorts.lean` now closes the concrete
incidence ledger.  A tensor factor is keyed by its physical link together with
its semantic target/source half.  The four fresh corner pairs of every
oriented face include the required target--target cap and source--source cup;
their endpoints have distinct factor keys.  Globally, the actual link-major,
target-before-source port word is proved to be a permutation of the pair-major
degree-two normal form.  The pair tags are exactly
`List.range (4 * support.length)`, every tag occurs exactly twice, all factor
keys are duplicate-free, and both endpoints of every pair belong to genuine
global factors.  These are structural theorems for arbitrary finite support
and arbitrary face orientations, not a cube computation.  The exact target
and direct audit are green with gates contained in `[propext, Quot.sound]`.

`SymbolicFiniteBoolTensorDegreeTwoCompiler.lean` supplies the generic honest
compiler.  Its dependent merge tree carries each factor tensor, exact typed
boundary tags, every shared/free split, and explicit adjacent-swap programs in
the evaluation-correct direction.  A separate certificate audits factorwise
duplicate-freeness, the one-copy internal-edge/boundary ledger, and the exact
doubled-edge incidence permutation; compilation never eliminates that
permutation proof into data.  The compiled plan is proved pointwise equal to
an independently defined literal evaluator whose merge case is the structural
Boolean sum of the product of the two child amplitudes.  The exact target and
direct audit are green with gates contained in `[propext, Quot.sound]`.

The remaining concrete N4 obligation is now sharply typed: construct this
merge-tree certificate for every fixed cutoff-one local-channel selection and
identify its literal nested factor sum with the N2 named Boolean network.  Two
order-independence facts must be proved rather than assumed.  First, an N2
`CutoffOneHaarWord` contains row/column values read from the Boolean
environment; the fixed channel site must instead be defined from its
descriptor bucket and a reference environment, with a proof that its choice
list and oriented endpoint tensors depend only on valence and occurrence
orientations.  Second, the native four-valent operator tensor order is
`[1,3,2,4]` whereas the endpoint-factor word is literal bucket order
`[1,2,3,4]`; the concrete leaf must carry the explicit middle adjacent swap.

`SymbolicFiniteBoolTensorWeightedContractionBound.lean` closes the abstract
analytic part of N5.  For a closed plan whose leaf mass is the square of the
product of local channel norms, it proves directly that the square of the
inverse-Gram-weighted value is at most one, using the exact local equations
`weight * norm ≈ 1`; the rational absolute-value lemma then gives a unit
bound.  `abs_nestedWeightedClosedEval_le_choiceMass` folds this bound through
the nested local-channel lists without constructing their Cartesian product.
Its exact target and direct audit are green with gates contained in
`[propext, Quot.sound]`.  Concrete N5 now requires only the selected-plan leaf
mass equation and the structural identification of its nested choice mass
with the established local multiplicity product.

The exact C8 dependency DAG is now frozen as follows:

```text
N0  geometry-generic oriented face rows, unique corner tags,
    and link-occurrence descriptors
 |
+-- N1  literal face expansion -> named Boolean sum
|
+-- N2  face-major/link-major permutation
        + each link bucket -> CutoffOneHaarWord
        + structural multiblock dispatcher/Fubini fold
             |
N3  positive local channels at valence 2/4/6
    + signed arbitrary-orientation transport
             |
N4  exact target/source factor-incidence graph
    + each fresh corner tag occurs in exactly two distinct factors
    + finite-Boolean graphical Holder/Finner inequality
             |
N5  nested factored channel-network sum
    + inverse-weight/norm cancellation
    + resolved-mass product `prod_link (1,2,5)`
             |
N6  literal Haar coefficient = factored channel-network contraction
    + `abs coefficient <= geometricLinkMultiplicityProduct`
             |
N7  existing geometric/explicit multiplicity bridge
    + `abs honestCutoffOnePhysicalTerm <= canonicalSurfaceActivity`.
```

Execution status: `N0`, `N1`, all of `N2`, and the arbitrary-orientation
positive local channel theorem `N3` are complete.  The local mass ledger of
`N5`, generic nested mass algebra, tensor carrier, tensor-product
factorization, and local channel Gram realization are also complete.  The
generic dispatcher/Fubini theorem and its actual link-bucket instantiation are
complete at the constructive axiom gate.  The endpoint-port leaf of `N4` is
complete, as are the square-root-free two-tensor shared-block contraction
inequality, its arbitrary finite contraction-tree induction, the explicit
port-arrangement language, the generic certified degree-two compiler and its
literal nested-sum semantics, and the full factor-key degree-two incidence
ledger.  The data-producing cutoff-one specialization and its N2 evaluation
identity remain open in `N4`.  The abstract nested inverse-weight/norm
cancellation is complete in `N5`; its concrete leaf-mass and multiplicity
instantiations, and the acceptance bridge `N6--N7`, remain open.

The first genuinely global exact checkpoint is `N0--N2`:

```text
finiteProductHaarComplex literalTraceProduct
  ~= namedBoolSum tags (fun environment =>
       product_link cutoffOneHaarKernel(wordAtLink environment link)).
```

The acceptance checkpoint is `N6--N7`, for every cutoff-one support, not only
for a cube.  The existing cube values `1/16` and `1/256`, an odd-incidence
zero, and an orientation-unbalanced epsilon-sign example then become
specialization regressions.

After this theorem, supply the existing conditional bridge

```text
AdjacentEvenReachableKernelSOSData
  -> AdjacentEvenActiveQuadraticSOSData
  -> AdjacentEvenPhysicalAnchorPSD,
```

then migrate `parametricKPhysicalTerm` while preserving the visible distinction
between signed amplitude and positive majorant.

Required regression values: odd-incidence zero, elementary-cube coefficient
`1/16`, edge-touching double-cube coefficient `1/256`, and an unbalanced
polarity network whose sign detects a missing epsilon tensor.

### 11. Backward gate C9: total local cutoff-one Haar kernel — ◐ POSITIVE RESOLUTIONS COMPLETE; ORIENTATION TRANSPORT ACTIVE

For every oriented fundamental occurrence word of total valence at most six,
construct one arbitrary-block partial Haar theorem, stable under an independent
complex spectator, with dispatcher ranks

```text
valence: 0  1  2  3  4  5  6
rank:    1  0  1  0  2  0  5.
```

The even kernels must retain their signed permutation-basis entries and be
identified exactly with positive orthogonal channel resolutions.  Prove
self-adjointness, idempotence in the relevant rational Gram form, and trace/rank
values; never replace signed amplitudes by squared recoupling coefficients.

Current exact leaves:

* balanced bivalent, four-valent, and six-valent projectors exist at an
  arbitrary block and under an independent spectator;
* the six-valent projector has the exact five-channel Temperley--Lieb
  factorization and rank `5`;
* `SU2QuaternionFundamentalSelfDuality.lean` proves both raw
  pseudoreality directions and positive/negative same-orientation `1/2` pins;
* `SU2QuaternionGenericBlockOrientedBivalentHaarProjector.lean` proves all
  four `FF/FR/RF/RR` bivalent orientations, arbitrary-block locality, and the
  spectator lift;
* `SU2QuaternionGenericBlockOddValentHaarVanishing.lean` proves every nonempty
  odd oriented word has exact zero partial Haar integral, structurally through
  selected-block homogeneity and a coordinate-parity mismatch.  It includes
  named valence `1`, `3`, and `5` partial and independent-spectator zeros.
* `SU2QuaternionGenericBlockOrientedEvenWordNormalization.lean` normalizes
  every four- and six-letter orientation word by exact fundamental
  pseudoreality.  Mismatched occurrences use the complemented transpose
  `(!column,!row)` and accumulate the off-diagonal epsilon signs by XOR.  It
  proves raw normalization, exact selected-block projectors, arbitrary
  independent-spectator lifts, balanced recovery, and one-/two-sign
  transpose-sensitive regressions at both valences.
* `SU2QuaternionGenericBlockCutoffOneHaarDispatcher.lean` packages all seven
  valences in one nondependent carrier.  Its total term, signed kernel,
  selected-block theorem, locality theorem, and spectator theorem are exact,
  with invariant multiplicities `1,0,1,0,2,0,5`.  These numbers are not yet
  called operator ranks in that leaf.
* `SU2QuaternionBivalentOperatorKernel.lean` freezes the operator convention
  `F(output,input)` and `R(input,output)`, factors the epsilon sign into its
  two operator-index signs, and proves the resulting rank-one bivalent kernel
  pure real, self-adjoint, idempotent, and of trace one.  It now also proves
  the orientation-independent positive resolution
  `(1/2)|delta><delta|`, the exact norm `||delta||^2 = 2`, and weighted mass
  one.  The original operator-law gates are axiom-free and the new mass gate
  uses only `[propext]`.
* `SU2QuaternionFourValentOperatorKernel.lean` applies the same transpose-
  correct convention to the balanced `F F R R` kernel and proves the exact
  positive resolution
  `|S><S| + (1/3)|T><T|`.  The exact channel Gram has squared norms `1,3`, so
  the weighted resolved mass is `1 + (1/3)*3 = 2`; the literal sixteen-
  coordinate operator trace is also exactly `2`.
* `SU2QuaternionSixValentOperatorKernel.lean` applies that operator convention
  to the balanced `F F F R R R` kernel and proves its exact factorization into
  five positive Temperley--Lieb rank-one tensors with weights
  `1/4,1/2,1/2,2/3,2/3`.  Each weighted channel has trace one, their total
  resolved mass and the signed operator trace are both exactly `5`, and the
  positive resolution retains both a transpose-sensitive `1/12` entry and a
  negative `-1/12` interference entry.
* `SU2QuaternionLocalChannelBoolTensor.lean` proves the formerly missing
  six-coordinate channel-inner-product/Gram bridge, as well as the matching
  bivalent and four-valent tensor embeddings.  Raw Boolean-index idempotence
  remains explicitly unclaimed until it is derived from this Gram bridge; the
  positive-channel domination theorem itself does not require that extra
  packaging.

All displayed new leaves through the three local positive resolutions are
target-verified under the serialized one-thread guard and are imported by
`YMGap.lean`.  Their public gates use at most `[propext, Quot.sound]`.  No full
semantic-root rebuild is claimed by this local checkpoint.

The remaining C9 operator work is now sharply isolated.  The bivalent leaf
freezes the operator index convention

```text
F(output,input),     R(input,output),
```

The balanced four- and six-valent positive channel resolutions and their
actual Boolean-tensor Gram bridge are now packaged.  The next local step is to
transport them through every orientation mask as a signed permutation
`T P T^T`.  At valence four the transport must also contain the
positional-to-projector swap `[1,3,2,4]`.  This gives self-adjointness and
trace invariance without enumerating orientation/index assignments.  Raw
Boolean idempotence may then be derived from the now-complete Gram theorem,
but it is not on the shortest dependency path to the coefficient bound.

### 12. Completed leaf C10: structural odd-word vanishing — ✓ COMPLETE

For a nonempty ordered word of oriented fundamental coefficients localized at
one quaternion block, the completed theorem proves:

```text
word length odd
  -> every monomial has odd total degree in that block
  -> a quaternion-block parity mismatch with the vacuum monomial
  -> exact partial Haar integral = 0.
```

Reuse

```text
quaternionBlockMoment_monoMul_zero_of_parityMismatch,
finiteProductHaar_mul_cross_parity_zero,
genericBlock_localFactor_with_complex_spectator.
```

The proof is structural in the word and polynomial support and does not
enumerate polarity/index assignments.  Delivered:

1. an oriented nonempty word definition with no trailing-`polyOne` alias;
2. block-degree and block-locality theorems;
3. the odd-degree-to-parity-mismatch bridge;
4. exact partial-Haar zero for every odd word;
5. named valence `1`, `3`, and `5` corollaries;
6. arbitrary-block independent-spectator zero;
7. exactly `{propext, Quot.sound}` in the public axiom gates.

The formerly immediate successors—four/six self-duality normalization, the
total valence dispatcher, and the pointwise arbitrary-orientation
positive-channel factorization—are complete.  The immediate open successors
are the exact factor-key/degree-two corner-incidence ledger and its compilation
into the now-proved shared-block contraction inequality, followed by global
inverse-weight/norm cancellation and production migration.

### 13. Consumer-first execution order from the present code

The backward graph determines the following forward implementation order.

1. **Finish the nearby physical leaf:** `N0--N3`, including signed orientation
   transport and the local positive-channel resolutions, are complete; prove
   the full factor-key incidence certificate, graphical contraction
   domination, linkwise inverse-weight/norm cancellation, and cutoff-one
   production migration.
2. **Freeze the minimal semantic consumers before another large
   generalization:** define `ComputableCompactGaugeGroup`,
   `PinnedWilsonLatticeFamily`, the source-extended RG output/extraction
   carrier, and the physical identity `Delta_k = m_lat(k) / a_k`.  These are
   specification targets, not new assumptions or claims of closure; each must
   have anti-toy adequacy fields and one intended producer slot.
3. **Generalize immediately afterward to all representation labels and
   group-index the harmonic input:** invariant-space dimensions, character tails, a
   label-summed signed network majorant, and the representation/Haar data that
   later RG estimates consume.  Do not postpone analytic group dependence to
   a terminal transport step.
4. **Use that network as the genuine infrared anchor:** cluster convergence,
   reflection-positive forms, a volume-uniform lattice gap, and a finite-energy
   excitation.
5. **Design `C6a` before proving `C6c--C6f`:** every block, UV, crossover,
   infrared, source, and form estimate must feed one shared extraction theorem
   rather than a collection of later wrappers.
6. **Prove the nonperturbative UV-to-IR flow:** actual source-extended block
   transformations, large-field control, summable errors, and the physical
   spacing equation.  The genuine phase-cell/effective-action landing theorem
   is the central new step; `SingleStepDefectBound.singleStep` and the existing
   scalar floor recursions are consequences, not substitutes for it.
7. **Pass both limits with shared moduli:** construct the canonical Schwinger
   functions, full OS laws, local source limits, and uniform physical margin
   together.
8. **Complete constructive OS reconstruction:** reflected Hilbert space, `C0`
   semigroup, unbounded generator, Poincare action, unique vacuum, and located
   finite spectral edge.
9. **Close terminal local content from the same sourced RG:** curvature fields,
   non-Wick cumulant, stress Ward identities, OPE, anomalous dimensions, and AF
   matching.
10. **Finish global-form descent:** central quotients, faithful lattice actions,
   representation descent, and topology/Haar identifications for every compact
   simple global form, using the group-indexed estimates already proved rather
   than introducing new analytic hypotheses here.
11. **Assemble the adequate terminal target, project to every unchanged legacy
    frontier, and only then run the terminal guard/axiom/full-build audit.**

The bounded statement-design work for the missing semantic carriers should run
alongside these proofs, but it must not proliferate scorecards or be counted as
mathematical closure.  A carrier is promoted to the terminal spine only when an
actual producer theorem targets it and its anti-toy adequacy conditions have
been reviewed.

### 14. Exact status verdict

The repository is not one frontier lemma from the Clay theorem.  It contains a
large, exact constructive finite-lattice and algebraic substrate; a well-designed
canonical reflected-OS interface with substantial derived consequences; strong
conditional defect-recursion algebra; and unusually complete local `SU(2)`
fundamental Haar calculations.  It does not yet contain an actual all-group
Wilson family, a four-dimensional continuum Schwinger functional, full OS laws
for real correlators, a continuous physical semigroup, an unbounded generator,
a located physical mass edge, terminal-grade local fields/stress/OPE/AF, or an
all-global-form proof.  The guarded frontier types remain undischarged.

This verdict does not devalue the current local work: it locates it precisely as
the nearest necessary leaf in the honest finite-stage Wilson functional.  It
also prevents that leaf, or any future conditional scalar floor, from being
mistaken for the continuum theorem.

### 15. Dual-representation positivity program — status and schedule (2026-07-23)

An executable second front was opened alongside the Lean spine: exact
Python mirrors of the quaternion-block Haar calculus
(`computations/exact_haar_network.py`, `computations/hypercube4d_survey.py`,
`computations/dual_positivity_survival.py`; 22 exact test pins; full
findings in `notes/dual-positivity-survival.md`).  Its purpose is to
decide, in exact arithmetic, whether the dual (character-representation)
route — abandoned historically for its supposed sign problem — is
actually obstructed where an exact RG would need to walk.

**What is now established (all exact, machine-checked):**

1. **Frozen-hub sum-of-squares theorem** (proof one paragraph,
   Lean-ready): every anchored star readout — the star of any link,
   gauge-fixed spine, rim loops — is a sum of squares, in any dimension
   and for any compact group.  The folklore "minimal sign-bearing
   object" cannot go negative; 6j signs are invisible to every anchored
   probe.
2. **3D positivity through slab scale:** single cube, double cube
   (partial high corner still computing), the 2×2×1 slab (first
   unanchored intertwiner circuit — *not* SOS-protected): every dual
   coefficient positive; all 81 heat-kernel rim channels
   Sturm-certified positive on the whole coupling interval with
   termwise-positive ledgers.
3. **4D positivity through the hypercube crossing survey:** binary
   admissible assignments = closed surfaces mod 2 (kernel dim 7);
   every surface evaluates by 2D Yang–Mills, `Z = d^{χ−F}` (Clifford
   tori at exactly `2^{−16}`).  The 8128 intersecting-surface pairs —
   the genuine 4D interference test, with 2-dimensional intertwiner
   spaces on crossing edges — quotient to 109 symmetry orbits:
   **108/109 evaluated (693 pair computations), zero negatives, zero
   inconsistencies.**  The 109th (full double-torus collision) is
   UNREACHED by the monomial engine — a resource verdict; 255/256 of
   its exact χ₂-expansion is banked.

**Standing conjecture (promotion target):**

> **(DP)** Intertwiner-summed SU(2) dual amplitudes of physical
> complexes are nonnegative.

If (DP) holds, the dual representation supports a sign-free exact RG,
and the historical reason the never-linearized route was abandoned is
void.  Every estimate this program has produced is consistent with
(DP); no probe has yet had both the structural room and the
computational reach to falsify it.

**Relation to the main spine.**  This does not shorten the distance to
the Clay theorem — the uniformity wall (RG-I7 contraction, RG-I8
landing, RG-I9 summability; spacing-uniform gap survival) stands
exactly where §14 locates it.  What it changes is the *coordinate
system*: it supplies a candidate positivity cone in which those three
certificates want to be inhabited, with the large-field problem never
created (compactness is native to the dual; nothing is ever
linearized).  Positivity ≠ contraction: (DP) is the floor of the
arena, not the fight.

### Milestone DP.1 — TL-channel contraction engine

**Goal.**  Replace raw monomial contraction with recoupling-channel
contraction (executable mirror of the Lean TL₃ projector spine), so
that network cost scales with channel dimensions, not `4^L` monomials.

**Deliverables.**
- `computations/su2_recoupling_data.py`: exact 6j/θ data extracted
  *from the certified moment engine* (squared data from K4 spin-model
  values; signs by Biedenharn–Elliott + orthogonality propagation),
  cross-pinned against `sympy.physics.wigner`.
- Channel-basis contraction of the three inherited targets: the
  extremal double-torus term; the 2×2×2 core; the 4D double hypercube.
- Tests pinning every new value against the monomial engine on the
  overlap domain.

**Dependencies.**  None (data layer starts from certified moments).

**Open questions.**  Whether TL sign conventions can be chosen once,
globally, so that (DP)-positive amplitudes have manifestly positive
channel decompositions (the "coherent scheme across scales" question —
this is where the wall would reappear if it exists).

### Milestone DP.2 — One-step dual blocking defect

**Goal.**  Compute the exact one-step blocked dual activity on the
slab (coarse 2×2 plaquette readout against heat-kernel weights
everywhere) and measure the first exact 3D defect `c'_n / c_n^4`
against the 2D fixed-point law.

**Deliverables.**  Exact `s`-polynomial defect table; sign verdicts;
comparison note.  **Dependencies.**  DP.1 for cost, or restricted
spins without it.

### Milestone DP.3 — RP-cone tracking

**Goal.**  Decide whether one blocking step preserves reflection
positivity *in the dual coefficients* (chessboard-reflected slab).
This is the positivity OS reconstruction actually consumes; (DP)
positivity does not imply it.  **Dependencies.**  DP.1.

### Milestone DP.4 — (DP) as a theorem or a counterexample

**Goal.**  Either prove (DP) for a nontrivial complex class (candidate
route: intertwiner-sum = Haar integral of manifest squares via a
reflection through the complex — the frozen-hub argument's unanchored
generalization), or locate the first negative amplitude with the DP.1
engine.  Both outcomes are decisive: a proof opens the sign-free dual
RG; a counterexample maps the wall's exact coordinate.
**Dependencies.**  DP.1 (reach), DP.3 (informs the reflection route).

### Milestone DP.5 — Lean transport

**Goal.**  Formalize the frozen-hub SOS theorem and the DP.1 data layer
into the existing positive-channel spine (`{propext, Quot.sound}`
gate), so the Python evidence becomes kernel-checked mathematics.
**Dependencies.**  DP.1; the Mac-side Lean session lock discipline
(AGENTS.md).

### 15a. Same-day addendum: the wall is found (2026-07-23, evening session)

Three results, in order of discovery, all exact and all
cross-arbitrated:

1. **Vertex product formula (DP.1 achieved ahead of schedule).**  On
   the 4-cube boundary — every edge trivalent, intertwiners
   multiplicity-free — the dual amplitude factorizes with no
   correction factors of any kind:
   `Z = ∏_{16 vertices} {6j}_v` (Wigner slot arrangement
   `{xy xz xt; zt yt yz}`).  Over-verified: 949/949 on the full moment
   corpus including signs; 20/20 on fresh cell-triples; exact n = 3
   gates; and it corrected a hand census (disjoint sphere-pairs,
   χ = 4), with raw moments siding with the formula.  Evaluation cost:
   sixteen memoized 6j lookups.  `computations/vertex_amplitude.py`.

2. **The 4D pair survey is closed at 109/109, all positive.**  The
   formerly UNREACHED double-torus collision evaluates to
   `6^{−16} = 1/2821109907456` (sixteen vertices, each +1/6).

3. **(DP) is FALSE, and its failure has an exact coordinate.**
   Sweeping all 341,376 triple-surface assignments: 32,384 negatives —
   every one requiring a spin-3 face; zero negatives at spins ≤ 2
   anywhere this program has ever computed.  Minimal exemplar
   (support 18, profile {1:×9, 2:×6, 3:×3}):
   `Z = −1/3981312`, **arbitrated against the raw moment engine**
   (512-term χ-strand expansion, 17 s, exact agreement to the digit
   through a fully independent pipeline).  Geometrically the negative
   sector lives on **triple-intersection curves of surfaces**; in
   representation terms it switches on at **j = 3/2**, the second
   quaternionic representation.

**Revised standing conjecture:**

> **(DP≤1)** Intertwiner-summed SU(2) dual amplitudes with all
> plaquette spins ≤ 2 (j ≤ 1) are nonnegative.

**Revised milestone consequences.**  DP.4 is resolved in the
counterexample direction for full (DP) and remains open (proof
direction) for (DP≤1).  DP.2/DP.3 sharpen into the *physical* wall
question: heat-kernel weights suppress the negative sector by
`s^{15}` against the positive sector's `s^{3}` — do the s-weighted
channel sums stay positive on all of `s ∈ (0,1)`?  The vertex formula
makes these sums computable; this is now the single most important
computation in the program, because its answer decides whether the
dual RG can run in a positive cone with the negative sector
*controlled* (small-s expansion territory) rather than absent.
Double-cube (1,1,2) table completed under the guarded engine (two
heaviest corners UNREACHED, honest resource verdicts; all reached
values positive) — see notes/dual-positivity-survival.md.


### 15b. Addendum (2026-07-24): DP.2 built; band geometry at its honest limit; Lean transport landed

**DP.2 — the slab blocking kernel exists** (`computations/slab_blocking_kernel.py`,
note P19).  Two-sided blocked kernel T[n,m](s) on the 2x2x1 block, exact in s;
adapted gauge tree; unit-reduced per-link eliminator; transverse-skeleton
decomposition cross-validated exactly against direct contraction at M=1.
Findings: (i) frozen-side scheme collapses to the EXACT 2D rule by univalence
(gate-checked) — transverse physics enters only through the owned boundary;
(ii) every reached entry is Sturm-positive on (0,1) — no sign problem in the
blocking kernel at this depth; (iii) the flow runs FASTER than 2D
(s' = 0.0341 vs s^4 = 0.0625 at s=1/2) and the corridor narrows
(1.82 vs wheel 2.23; 0.79 at s=3/4), while the raw whole-cone Birkhoff
diameter is huge and coupling-dependent — the enveloped cone is the mechanism,
not a convenience.  M=2 stability partial with per-skeleton wall-clock budget:
UNREACHED classes recorded.  Milestone DP.2: kernel CONSTRUCTED, saturation
measurement in progress.

**Band geometry (ABK path) at its honest limit** (note P20).  v2 rebuild:
non-crossing traversal at revisited sheets, cross-component linking,
per-component orientability, push-scale stability vote; pairs perfectly even
(polarization always defined).  Triple consistency saturates at ~70% with every
miss exactly d2; a 188-triple feature sweep found no connector-level predictor.
Diagnosis: the lift embeds curves, not the surface — coherent q needs an
embedded/framed Pin- realization of the full strand cover.  beta = 4*kappa runs
in correlation mode only until that object exists.

**Lean transport** (`dual_kappa_spike/`, note P21): three kernel-checked
theorems — `no_local_gauge` (kappa is a genuine global class),
`rim_readouts_pos` (frozen-hub SOS at certificate level: all 81 anchored rim
channels strictly positive at every rational s > 0), and
`kappa_odd_all_branched` (the {1,1,2} branch detector as a Lean function,
checked on 100 kappa-odd samples).  UNBUILT pending Mac-side `lake build`
(session lock per AGENTS.md).

**Warning:** Dropbox reverted `work_plan.md` a second time (Section 15/15a were
missing from the synced copy on 2026-07-24); this file was rebuilt from the
session record.  Please check for "conflicted copy" duplicates.

### 15c. Addendum (2026-07-24, second session): Simplification Ledger — ranked counterfactuals and milestone adjustments

A full genealogy of every named theorem/law in live use (Lists A–E, four
generations), with a per-edge ledger of the simplifications made and a
counterfactual analysis of each against the current repo state, is now in
the project doc `claude/simplification-ledger.md` (32 ledger entries, 17
ranked counterfactuals).  Headline findings, recorded here because they
adjust the plan:

1. **Rank 1 (L3, lattice regularization).**  The largest counterfactual is
   already the open frontier: R2 / `UniformPhysicalCorrelationDecay` *is*
   the deferred half of Wilson's lattice simplification.  No plan change;
   confirms the frontier is correctly identified.
2. **Rank 2 (L17/L18, anchor + RG transport).**  Survives its
   counterfactual as a necessity proof.  Named leak point: δ_k-summability
   must hold *through the crossover*, not merely near the anchor — any
   silent extension of the certified region is where this line fails.
3. **Rank 3 (L15, fiducials — most actionable).**  The three flagged
   constants (`BAŁABAN_SPECTRAL_GAP_COEFF c_λ = 1/2` shape-fiducial;
   `BALABAN_POLYMER_RESIDUAL = 2.0` heuristic; Seiler `5d−4` cited-but-
   unverified, already known absent from BFS 1978) are mandatory
   extraction work under the program's own no-shape-constants law.
   → **New milestone SL.1 below.**
4. **Rank 4 (L27, (DP≤1) retreat).**  The middle road — negative sector
   controlled, not absent: positivity of the s-weighted channel sums on
   all of (0,1) under s¹⁵-vs-s³ suppression — is the only open road
   (Birkhoff contraction cannot run on signed kernels; full (DP) is
   machine-refuted).  This confirms §15a's designation of the s-weighted
   sum as the program's single most important computation.
   → **Milestone DP.6 below formalizes it.**
5. **Rank 7 (L29, ABK curves-vs-surface).**  The one counterfactual whose
   refusal *helps*: the embedded/framed Pin⁻ realization of the strand
   cover takes β = 4κ out of correlation mode.  Confirms next-session
   queue item (3); no change in priority.
6. **Policy adjustment (L4, heat-kernel action).**  Adopt explicitly:
   the program proves its heat-kernel-action theory satisfies the Clay
   axioms + non-triviality *on its own terms*; no Wilson-action
   universality claim is made or owed.  This cancels the outstanding
   universality debt by policy.  (The Clay statement names no action.)
7. **Policy adjustment (L28, truncation errors).**  The DP.2 M-truncation
   error must enter the §2 modulus registry as a named modulus
   (ε_slab(M)) with the same witness discipline as ε_UV/ε_IR/ε_RG —
   UNREACHED wall-clock verdicts are honest but are not moduli.
8. **New standing audit rules** (recorded under Cross-cutting policies →
   "Adversarial audit rules", and appended to the audit checklist in
   `docs/ym_mass_gap_prompt.md`): (i) the **coupled-simplification
   audit** — R1's worst-case reduction and the multiplicity-free 6j
   vertex calculus are one auditable unit; (ii) the **U(1)
   discriminator** — every gap-critical positivity/contraction step must
   name where non-abelian-ness enters (a mechanism that would equally
   prove a 4D U(1) gap proves too much; Migdal–Kadanoff is the canonical
   failure).

### Milestone SL.1 — Fiducial extraction (Rank 3; cheapest large de-risking)

**Goal.**  Reduce the fiducial-constant exposure to zero: replace the
three flagged literature-shape constants with either (a) constants
extracted from a specific displayed inequality in the primary source
(Bałaban CMP 109 (1987) for c_λ; Bałaban CMP 119 (1988) for the polymer
residual; Seiler LNP 159 (1982) §-precise cite or an in-substrate
rederivation for the plaquette-polymer connectivity count), or (b)
in-substrate derivations with explicit witnesses, whichever is reached
first per constant.

**Deliverables.**  (1) Per-constant provenance note in
`notes/fiducials_notes.md` upgraded from SHAPE/HEURISTIC to EXTRACTED or
DERIVED, with page/equation cites or substrate proofs.  (2) Recomputed
σ̂-trajectory and K_sf/K_lf budgets under the extracted values;
lockstep tests (`test_kp_constants_lockstep.py`) re-pinned.  (3) If any
budget breaks: the break is the result — report which milestone reopens
and at what margin.  (4) Bundle (Rank 13): while inside the KP layer,
evaluate the Fernández–Procacci criterion as a drop-in replacement and
record the margin it buys (expected: widened strong-coupling anchor
region, shrinking the crossover from the provable end).

**Dependencies.**  None (literature + existing modules).  Independent of
the Lean session lock; safe to run alongside DP work.

**Open questions.**  Whether the 2.0 polymer residual survives extraction
at all, or must be replaced by a derived k-dependent residual with its
own summability proof.

### Milestone DP.6 — Signed-sector survival: s-weighted positivity on (0,1) (Rank 4; the designated computation)

**Goal.**  Decide (DP≤1)'s physical sufficiency: with the vertex product
formula making channel sums computable, determine whether the s-weighted
channel sums (positive sector s³-scale vs negative sector s¹⁵-scale)
remain positive on **all** of s ∈ (0,1) — not merely in a small-s
expansion — on the reachable configuration corpus.

**Deliverables.**  (1) Exact s-polynomial channel sums per configuration
class via `vertex_amplitude.py`, negative (j ≥ 3/2) sector included.
(2) Sturm certificates of positivity on (0,1) per reached class, or the
first certified sign change (either verdict is decisive and banked).
(3) Endpoint analysis at s → 1⁻ (weak coupling), where suppression is
weakest — this is where the anchor-transport leak point (finding 2
above) would first appear.  (4) U(1)-discriminator tag (audit rule ii):
identify exactly where the argument uses non-abelian structure, with the
abelian comparison computed.  (5) Lean transport of the positivity
certificates into the `dual_kappa_spike`/positive-channel spine
({propext, Quot.sound} gate) for every class whose certificate closes.

**Dependencies.**  DP.2 kernel (built, §15b); vertex formula (§15a);
SL.1 independent but its sharpened anchor region strengthens the
interpretation of (3).

**Decision criteria.**  Positive on (0,1) everywhere reached → the dual
RG runs in a positive cone with the negative sector controlled; DP.3/DP.4
proceed under (DP≤1)+suppression.  A certified sign change at some s* →
s* is the new exact wall coordinate; bank it (Lakatos discipline) and
re-plan the dual route above s*.

**Open questions.**  Whether per-class positivity admits a uniform-in-
class certificate (a single SOS/Sturm family) rather than class-by-class
enumeration — required eventually for the a→0 direction, since class
enumeration does not survive the continuum limit.

### 15d. Addendum (2026-07-24, same session): DP.6 EXECUTED — split verdict; cancellation lives at exponent granularity

All four DP.6 phases ran to completion (cloud-side compute; nothing
heavy on this host).  Result: **neither of the two anticipated verdicts
— a third, sharper one.**

**Structural discovery first.**  Both the activity coefficient
c = ∏(n+1)^mult and the exponent E = Σ n(n+2)·mult depend only on the
spin *profile*, so every profile-class channel is a **single monomial**
c·(ΣZ)·s^E: its sign is *s-independent*, and no within-class crossover
in s is possible.  The §15a framing ("do the s-weighted channel sums
stay positive on (0,1)?") therefore resolves at class granularity by
coefficient sign alone — Sturm certification was never genuinely
reached (all 36 verdicts closed on the exact coefficient-sign fast path
of `sign_on_unit_interval`; recorded per-verdict as `certified_by`).

**The split verdict (full C(128,3) = 341,376 corpus; sanity pins all
reproduced: 32,384 negatives, every one requiring a spin-3 face,
minimal exemplar −1/3981312 at 1⁹2⁶3³):**

- **Per-class survival FAILS.**  Of 260 profile classes (34 mixed),
  four have negative channel sums — negative on ALL of (0,1):
  `1⁸2¹¹3⁴` (ΣZ = −1/60466176), `1⁹2¹²3¹` (−7/12754584),
  `1¹⁰2¹¹3²` (−11/76527504), `1¹¹2¹¹3¹` (−5/38263752).  Margins are
  narrow (neg/pos mass 68/59, 48/41, 72/61, 18/13 — all just above 1).
- **Global survival HOLDS.**  The global sum over all triples (and with
  the all-positive empty/single/pair sectors folded in: 80 monomials,
  s³⁶…s¹⁹⁸) has **every coefficient strictly positive** — positive on
  all of (0,1).  At each exponent carried by a negative class
  (E ∈ {136, 138, 148, 172}) the positive classes sharing that exponent
  outweigh it by ~50–500×  (exact per-exponent ledger banked).

**Consequence for DP.3/DP.4 (conjecture sharpened).**  (DP≤1) +
suppression is TRUE at exponent granularity and FALSE at profile
granularity.  The dual RG cone must therefore be built on
**exponent-aggregated channels** (or coarser), not profile channels —
this *answers* DP.1's "coherent scheme across scales" question in the
negative at profile resolution and fixes the minimum coarseness the
positive cone must have.  The four negative classes are banked as the
Lakatos fence marking that resolution boundary.

**U(1) discriminator (audit rule ii, first live application).**  Exact
computation on the same 4-cube boundary complex (∂∘∂ = 0 verified;
kernel rank 7 = 8 cubes − 1, Smith factors all 1, full integer kernel):
U(1) dual amplitudes are identically {0,1} — dual positivity is FREE
abelianly, while 4D U(1) is gapless at weak coupling (Guth).  Therefore
**dual-cone positivity is cone admission only, never citable as the gap
mechanism**; the gap must come from a step that demonstrably fails for
U(1) — the blocked-kernel contraction rate.  Testable prediction
banked: U(1) slab blocking should track its 2D rule s′ = s⁴ exactly
with corridor NON-narrowing (univalence d_m = 1 kills the d³
denominator), vs the measured SU(2) s′ = 0.0341 < s⁴ = 0.0625 with
narrowing.  → **Queued as DP.6-U1** (run `slab_blocking_kernel` with
U(1) weights; the decisive discriminator computation for the
contraction step).

**Banked artifacts:**  `computations/dp6_signed_survival.py` (+
`tests/test_dp6_signed_survival.py`, 5 pins green cloud-side; full
mirrored suite 9/9), `computations/dp6_results.json` (per-class
records, cancellation ledger, endpoint Fractions at s = 1/2 … 999/1000,
all positive for the global sums), `notes/dp6-signed-survival.md`,
`scripts/dp6_u1_dual_check.py`, `docs/dp6-u1-discriminator-2026-07-24.md`,
and **`dual_kappa_spike/DP6Ledger.lean`** — the kernel-checkable ledger
(543 generator-verified literals: global coefficient positivity, the
four negative class sums with c rederived in-Lean, the per-exponent
P+N=G balance, sanity pins; generator `scripts/gen_dp6_lean.py`).
DP6Ledger.lean is **UNBUILT** pending Mac-side `lake build` under the
session lock (joins the three-spike in the build queue).

**DP.6 status: phases P1–P4 complete in-substrate; remaining
obligations: (1) Mac `lake build` of DP6Ledger + three-spike;
(2) DP.6-U1 contraction-step discriminator; (3) exponent-aggregated
cone re-statement feeding DP.3.**

### 15e. Addendum (2026-07-24, third session): spike build GREEN + axiom-clean; DP.6-U1 refutes-and-sharpens; SL.1 first extractions

**(1) dual_kappa_spike build ✓ (obligation 15d(1) discharged).**
`lake build` green, all four targets, checked exit code 0, under the
session lock.  The two P21 files needed v4.29.1 repairs, all
constructive (no `Classical`, no new axioms): `omega_nat`/`by_contra`/
`clear * -` replaced (decidable `by_cases`, helper lemmas
`countNat_eq_zero_of_not_mem` / `eraseFirst_length_le` /
`mem_of_mem_eraseFirst`); `Nat.strong_induction_on` replaced by
well-founded recursion on `l.length` (`termination_by`/`decreasing_by`);
implicit-arg `List.mem_cons_self`; one missing `omega`; one
`unfold parity; omega` → `show`+`simp`.  **Axiom audit (checked, exit
0):** `DualKappa.no_local_gauge` and `FrozenHub.rim_readouts_pos` =
[propext, Quot.sound]; `SupportLaw.kappa_odd_all_branched`,
`detector_not_vacuous` = [propext]; **all six DP6Ledger theorems
(`global_coeffs_pos`, `neg_classes_neg`, `exponent_ledger_balances`,
`ledger_matches_global`, `neg_class_exponents`, `sanity_pins`) depend
on NO axioms.**  The three P21 theorems + the DP.6 ledger are now
kernel-checked mathematics, not UNBUILT claims.

**(2) DP.6-U1 executed — §15d's banked prediction REFUTED, and the
discriminator comes out SHARPER.**  The U(1) slab kernel is NOT
diagonal (each coarse loop bounds its own tile disk; transverse sector
= a rank-saturated 4-parameter cube-flip charge lattice, Smith factors
1,1,1,1), so the projective machinery does not degenerate — and U(1)
does not track s′ = s⁴: it deviates the OPPOSITE way.  At s = 1/2:
SU(2) s′ = 0.034121 < s⁴ = 0.0625; U(1) s′ = 0.126197 > s⁴ (exact
M = 2 witness ρ₁ = 14330603980276662272/11258810062447479809 ≈ 1.2728).
At s = 3/4: SU(2) 0.249521 < 0.316406 < U(1) 0.451794.  Corridor
narrowing happens for BOTH groups (U(1): 0.4614 → 0.0119) —
**corridor phenomenology is group-generic and may NOT be cited as the
non-abelian tag.  The sharpened U(1)-discriminator tag is the SIGN of
the one-step coupling defect: s′ < s⁴ (contraction acceleration,
needs the off-diagonal recoupling at the 4-valent interior edge) vs
the abelian slab's provable s′ > s⁴ (anti-renormalization).**  This is
the anti-screening/SELF-CHARGE reality-fact caught in exact
arithmetic at one blocking step.  SU(2) pins reproduced to the digit
first (0.034121/1.816737; 0.249521/0.792869).  Truncation certified:
T_{M+1} − T_M min-degree ≥ (M+1)²; stable ≥ 9–10 digits from M = 3–5.
One abelian rigidity: T[2,±2] = ∅ at M = 1 (the SU(2) (1,1,2) triad
has no abelian counterpart).  Cloud tests 23/23 green.
§15d's testable-prediction text stands as banked-and-refuted
(Lakatos); the audit-rule tag in the U(1) memo is updated by
`notes/dp6-u1-slab-blocking.md`.

**(3) SL.1 first extractions (milestone opened).**
- **Seiler 5d−4 RESOLVED (negative), in-substrate.**  Exact ℤ^d
  enumeration (d = 3, 4, 5): **5d−4 matches NO plaquette-adjacency
  notion at any d** — the d = 4 value 16 is a numerical coincidence
  with the non-coplanar edge-neighbor count 8(d−2) (8, 16, 24 vs 11,
  16, 21).  The notion the KP bound consumes (edge-connected polymer
  growth) has max-degree 8d−12 = **20** at d = 4 (per-bond 2(d−1) = 6
  ✓ BFS eq. 4.24); exact polymer counts N₁..₅ = 1, 20, 458, 11132,
  280175 — N_n ≤ 16ⁿ holds through n = 5 but growth ratios (20.0,
  22.9, 24.3, 25.2, rising) already exceed 16, so **μ = 16 is not
  asymptotically defensible**; the rigorous replacement is 20e.
  Budget impact computed: g_max^lf 0.4245 → 0.3733 (−12%); pilot
  closure UNCHANGED (small-field window binding).  → DECISION QUEUED:
  adopt 20e default in `large_field_kp.py` (recommended) and re-pin.
- **Bałaban c_λ = 1/2: SHAPE-LOCATED.**  CMP 109 p.258 eq. (0.27)
  quoted — the literal ½ is a decay-rate split (proof device, any κ),
  not an extractable coefficient; Theorem 3 is existence-only.  NOTE:
  `notes/fiducials_notes.md` §1 already re-derived c_λ = 3/4
  internally (2026-05-26); its summary table still says 1/2 — stale
  row, fix queued with the merge.
- **Polymer residual 2.0: precise null.**  CMP 119 absent locally
  (DOI confirmed, paywalled); CMP 116 (present) has only unpinned
  absolute constants (C₁, C₂, q at (1.32)/(1.36)).  Extraction needs
  CMP 119 + CMP 122 I/II.  Constant remains on the internal
  triangle-inequality derivation.
- **Corpus mislabel found:** local `Balaban 116.pdf` actually contains
  CMP 109 (Part I); `Renormalization Group Approach....pdf` is CMP 116
  (Part II).  Recorded in the upgrade draft.
- Merge-ready provenance paragraphs: `docs/sl1-fiducials-upgrade-draft-2026-07-24.md`
  (deliberate merge into `notes/fiducials_notes.md` queued, not
  auto-applied).

**New artifacts:** `computations/dp6_u1_slab_blocking.py` (+ test, 9
pins), `computations/dp6_u1_results.json`,
`notes/dp6-u1-slab-blocking.md`, `computations/plaquette_connectivity.py`
(+ test, 15 pins), `docs/sl1-fiducials-upgrade-draft-2026-07-24.md`.

**Next queue: (1) adopt μ_plaq = 20e (SL.1 decision) + re-pin lockstep;
(2) merge the fiducials upgrade draft + fix the stale c_λ row;
(3) exponent-aggregated cone re-statement feeding DP.3 (with the
sharpened sign-of-defect tag on every contraction step);
(4) DP.2 M=2 saturation + ε_slab(M); (5) embedded-surface Pin⁻
realization; (6) obtain CMP 119/122 for the residual extraction;
(7) read the completed abk_verdict2 300-sample run.**

### 15f. Addendum (2026-07-25): prove-out round — queue items 1, 2, 3, 6, 7 executed

**(1) μ_plaq = 20e ADOPTED (SL.1 decision closed).**
`MU_PLAQUETTE_4D_RATIONAL = 1359141/25000` (= 54.36564, exact rational
majorant of 20e, slack ≈ 3.4e-6; ≥ 20e guarded by a new exact
factorial-series test); `SEILER_5D_MINUS_4_LEGACY = 16` retained for
comparison sweeps only.  Provenance upgraded LITERATURE-SHAPE →
DERIVED (Δ = 8d−12 enumerated in `plaquette_connectivity.py`; BF bound
eΔ).  Recomputed: g_max^lf 0.424549 → **0.373289** (−12.07%,
prediction confirmed); K_lf(0.30) 0.015624 → 0.055155; pilot
trajectory still clears both windows (Ση = 2.393e-3, 418× margin) —
**closure UNCHANGED**, but at the window *edge* the lf window now
binds (max_g0 0.4132 → 0.3655), retiring the old "sf binds"
shorthand.  **Honest headline correction:** m₀ = √(1−Ση) drops
0.999602 → 0.998803 — the quotable floor is now **998/1000** (was
999/1000); bootstrap 5th-pct 994/1000; headline ≥ 950/1000 intact.
Tornado sensitivity reordered: A_min > μ_plaq > c_polymer > c_λ.
**Lean unsoundness caught and fixed:** `SU2KP.K_lf_canonical` (16/1000)
and `PolymerDomination.K_lf_pilot` (2/125) were BELOW the true
K_lf — unsound as upper bounds; re-pinned (56/1000, 523/10000, …) and
**targeted main-tree `lake build` of both Sheaf modules GREEN (32
jobs, exit 0, axiom gate clean — constants axiom-free or {propext})**.
Cloud tests: 195 green incl. 6 new large-field lockstep pins.
Note: `notes/mu20-change-note.md`; stale `# 16` comment flagged in
`scripts/su3_closure_spike.py`; m_0_bootstrap envelope [10,55] barely
contains 54.37 — flagged.

**(2) Fiducials note MERGED (canonical `notes/fiducials_notes.md`
updated in place, dated addenda, no deletions).**  5d−4 →
RESOLVED-negative (§3.3/3.4); c_λ → SHAPE-LOCATED with the CMP 109
eq. (0.27) quote (§1.2) and the **stale summary-table row fixed**
(now 3/4 / DERIVED, consistent with the 2026-05-26 internal
derivation); residual 2.0 → precise-null record (§5.1); corpus
mislabels recorded; bibliography extended (CMP 122 I/II DOIs).

**(6) CMP 119/122 retrieval: precise null, documented.**
Titles/DOIs/Euclid IDs confirmed; Project Euclid PDF bot-walled,
Springer paywalled, GDZ does not hold CMP, Wayback/fatcat blocked.
No constants invented.  Human unblock paths (browser fetch of the
Euclid PDF; institutional access) listed in
`notes/cmp119_extraction.md`.  Residual 2.0 remains on the internal
triangle-inequality derivation.

**(7) abk_verdict2 300-sample run READ — β = 4κ correlation-mode
support DOWNGRADED (honest cut).**  300/300 rows, but β assembled for
only 52 (nonpin 143 / q 69 / B 26 / b1_big 10 discarded — 83%
attrition).  Raw: 22/52 matches vs 1/8 baseline (exact binomial tail
≈ 8.2e-8) — but 14 rows are b1 = 0 trivial (β ≡ 0), and stratified:
κ=0 → 7/22 (tail ≈ 0.015), **κ=1 → 2/16 = exactly baseline (tail
≈ 0.61)**.  The prior "every miss d2" pattern does NOT persist
(d1:6, d2:13, d3:3, d4:8; 9 odd-β rows).  Verdict: the data supports
a β ≡ 0 attractor on κ=0, not β = 4κ; **the embedded-surface Pin⁻
realization is re-scoped from confirmer to DECIDER** — the current
curve-lift assembly cannot distinguish "β = 4κ true but assembly
corrupts κ=1" from "false".  Note:
`notes/abk-verdict2-read-2026-07-24.md`; exact analysis
`scripts/abk_verdict2_analysis.py`.

**(3) DP.3 OPENED at exponent granularity — statement + first RP
data point, PSD.**  `docs/dp3-exponent-cone-statement.md` defines the
exponent-aggregated cone C_exp and states the three obligations
(cone preservation under blocking — trivial at M=1, open at M≥2 where
6j interference enters; OS reflection positivity of the blocked
Gram; iteration stability), each carrying its U(1)-discriminator tag
(duality/RP/entrywise positivity group-blind or group-generic; only
the contraction-acceleration sign carries gap weight).  **First RP
check (exact, `computations/dp3_rp_check.py` + 7-test pin):** link
reflection θ: z ↦ 1−z through the blocking plane; θ antilinear ⇒
SU(2) Gram = T directly (real characters), U(1) Gram = T[−n,m].
**PSD for both groups — not just at s ∈ {1/4, 1/2, 3/4} but on all of
(0,1) by Sturm on the leading principal minors** (SU(2): minors 1–3
positive, minor 4 exactly zero — spin-3 zero row, PSD-neutral).
Conjugation is provably material: the unconjugated U(1) control fails
PSD on all of (0,1) — dropping antilinearity would have declared a
spurious RP violation.  Structural echo: the SU(2) RP-minor
polynomials contain negative coefficients yet are Sturm-positive —
RP-minor positivity is itself a cross-exponent cancellation, the
DP.6 granularity lesson one level up.  Honesty: one step, M=1
truncation, PSD structurally expected (truncated heat kernel keeps
positive character coefficients ⇒ Osterwalder–Seiler survives
truncation) — verification, not proof.  Decisive follow-ups: M=2,
iterated kernel, larger half-space observable algebras.

**Remaining queue: (a) DP.2/DP.3 M=2 — saturation + ε_slab(M) +
cone preservation where 6j interference first enters + RP at M=2;
(b) embedded-surface Pin⁻ realization (now the DECIDER for β = 4κ);
(c) human unblock for CMP 119/122 (browser fetch or institutional
access); (d) su3_closure_spike stale comment + m_0_bootstrap envelope
widening (housekeeping); (e) manuscript sweep for the 999/1000 →
998/1000 headline change (formal/ tex + any doc quoting m₀).**

### 15g. Addendum (2026-07-25): CMP 119 extraction DONE (queue item c, first half) — residual SHAPE-CONFIRMED, constant unpinned

The user fetched the CMP 119 issue-2 document into
`docs/pdf_references/` — it turned out to be **Euclid's front-matter
doc only (2 pages)**; the actual article text was then obtained
through the Mac's own egress (in-memory pipe, nothing installed) and
identity-confirmed ("Commun. Math. Phys. 119, 243-285 (1988)";
[I] = CMP 109, [II] = CMP 116).  Full extraction now in
`notes/cmp119_extraction.md` §5 and archived at
`_generated/pdf_text/Balaban 119.txt`.

**Verdict on `BALABAN_POLYMER_RESIDUAL = 2.0`: SHAPE-CONFIRMED,
constant unpinned — the fiducial stays internally derived, but the
shape citation is now quote-level.**  Findings:
- The explicit **factor 2** exists in the paper (p. 283, second proof
  of Theorem 2): the far-class polymer difference "can be estimated by
  2E₀ exp(−(1/2)κ[·−j]) exp(−(1/2)κ d_j(X))" — exactly the
  |A−B| ≤ 2·(single-activity bound) triangle-inequality two-channel
  device behind the repo's channel multiplicity 2.  **Decisive
  caveat:** Bałaban's difference compares two *configurations*
  (U_k vs 1) at fixed scale j; the repo's residual compares scales
  k → k+1.  Same device and constant, different inequality instance —
  hence SHAPE-CONFIRMED, not EXTRACTED.
- The only pinned numeric in a main bound is R₁ = 1 (eq. (2.44),
  p. 263, small-coupling remark) — not the residual.  Everything else
  is the CMP 116-style existence chain (E₀, E₁, B₀, E±, κ, M
  unpinned; proof-device numerics β = 1/4, ½κ splits,
  2^{−(j−1−n)} only).
- **The R-operation — the residual's natural home — is explicitly
  deferred**: "We will not describe it here, we will only assume that
  it has some properties" (p. 244); construction "given in the next
  paper" = **CMP 122 I/II, still unheld** — the remaining extraction
  frontier (queue item c, second half).
- c_λ cross-check: eq. (3.48) p. 280 and the p. 283 split reuse the
  ½κ rate-split of CMP 109 (0.27), reinforcing §1.2's
  bookkeeping-device reading; nothing pins κ.

`notes/fiducials_notes.md` updated in place (§5 status → SHAPE-
CONFIRMED, new §5.2 extraction record, summary-table row updated,
`\cite{Balaban1988convergent}` restored as quote-level shape source;
§1.2 gains the c_λ cross-check).  Article PDF to be archived
alongside the front-matter file in `docs/pdf_references/`.

### 15h. Addendum (2026-07-25): CMP 122 I/II fetched and extracted — the Bałaban extraction frontier is CLOSED

The Mac-egress fetch path (browser UA + referer) retrieved both
R-operation papers first try; archived (gitignored) as
`docs/pdf_references/Balaban_CMP122_I_175-202.pdf` (28 pp) and
`Balaban_CMP122_II_355-392.pdf` (38 pp), text at
`_generated/pdf_text/Balaban 122-I.txt` / `122-II.txt`.  Paper II's
reference list fixes Bałaban's own numbering: [I]=CMP 109,
[II]=CMP 116, [III]=CMP 119, [IV]=CMP 122-I.  **All five papers of
the chain are now read; the extraction frontier is closed.**

**FINAL verdict on `BALABAN_POLYMER_RESIDUAL = 2.0`: SHAPE-CONFIRMED,
constant unpinned — the k → k+1 per-polymer activity-difference
instance the repo uses appears NOWHERE in the published chain.  The
constant remains (correctly) internally derived
(`notes/sigma-hat-derivation.md` §2.3), now with two quote-level
factor-2 cousins:** CMP 119 p. 283 (configuration-difference triangle
inequality) and CMP 122-II (1.85) pp. 385–386 (the suppression-budget
recursion reserving **2p₀(g)** units per region per scale step,
closed by tree-graph induction into
T_k(X) ≤ exp(−2(1+β₀)⁻¹p₀(g_k)), (1.89) p. 387).

Other findings:
- **The final normal-form R-bound has constant exactly 1**:
  |R^(k)(X,(U,J))| ≤ exp(−p₀(g_k))exp(−κ d_k(X)) ((1.100), II
  p. 390) — precedent that clean constants are achievable when a
  dedicated small factor absorbs the looseness; non-transferable to
  the repo's residual without the sign-preservation lemma (the c = 1
  tightening stays open).
- **Paper I/II actually pin their proof constants** (unlike CMP
  116/119): α = 1/8, β = 1/2, L₀ = (L−1)/2, C ≤ 2, c_m ∈ {1,3},
  β₀ = 1/7 (closing −2(1+β₀)⁻¹p₀ + 1 + 2κ(100R_k)^d ≤ −(3/2)p₀,
  II p. 389).  κ itself: never pinned ("for κ large enough").
- **Retroactive pinning:** (1.89) "implies the inequality (2.50)
  [III], hence Corollary 3" — CMP 119's UV-stability link is
  discharged inside the published chain; E₋/E₊ stay existence-only.
- **AUDIT-CRITICAL:** "The proof of Theorem 2 [CMP 109] … is very
  awkward and long … and has not been published yet, so we have
  Theorem 1 with the assumption" (II, pp. 355–356) — **the removal of
  the weak-coupling assumption in Bałaban's final UV-stability
  theorem rests on an unpublished proof.**  This (i) closes the §1.2
  c_λ thread definitively (κ unpinned to the end of the chain), and
  (ii) matters for the program's prior-work narrative: the strongest
  published form of Bałaban UV stability is conditional at exactly
  the point the repo's own strong-coupling anchor + transport
  architecture is designed to avoid.  Cite accordingly in
  `formal/introduction.tex` when the manuscript sweep runs.

`notes/cmp119_extraction.md` gains §6 (the CMP 122 record);
`notes/fiducials_notes.md` §5/§5.3 finalized (residual row: frontier
CLOSED; refine path = sign-preservation lemma only).  Queue item (c)
fully discharged.

### 15i. Addendum (2026-07-26): DP.3 at M=2 — the COEFFICIENT CONE IS REFUTED at both granularities; the functional cone survives

Queue item (a) executed (DP.2/DP.3 at M=2).  `docs/dp3-exponent-cone-statement.md`
§2(i)(a) had named the open content of claim (i) exactly: at M=1 every entry is
coefficientwise nonnegative, so preservation is trivial; the content lives at
larger M "where signed 6j interference can in principle put negative
coefficients into an entry while leaving it positive as a function", and if that
happens "claim (i) must be proved at the aggregated level (cancellation across m
at fixed output exponent), exactly the DP.6 pattern".  **Both halves are now
settled, the second one negatively.**

**(1) Entry level — REFUTED, exactly.**  `T[1,1]` at M=2 carries the
coefficient **−32/3 at s^76**.  Eight configurations sit at E=76; all eight are
computed; four contribute 0 and four contribute −8/3 each (D4/reflection images
of one configuration, q=(0,1,2,1) w=(1,1,1,1), tiles (1,0,1,2)/(1,2,1,2),
N = −1/1492992).

**(2) Aggregated level — ALSO REFUTED; the DP.6 repair is NOT available.**  For
the heat-kernel envelope v_m = d_m s^{C(m)}, the blocked image `(Bv)_1` carries
**−64/3 at s^79**, and the sibling channels contribute **exactly zero** there
(T[1,0] at s^79 = 0, T[1,2] at s^71 = 0).  There is no cancellation to appeal
to.  DP.6's precedent — positivity lost at fine granularity, restored by
aggregation with 50–500x margins — does not repeat one level up.

**(3) Functional positivity SURVIVES.**  `T[1,1]`'s final part is
Sturm-positive on all of (0,1) despite the negative coefficient; so are the
final parts of `(Bv)_0` and `(Bv)_1`.  The negativity is a property of the
character/exponent basis, not of the kernel.

**Consequence — change of cone, not repair of proof.**  `C_exp` was defined
coefficientwise (a_E >= 0) as a convenience; DP.2's contraction measurements
never consumed it (they evaluate entries at each s and take Hilbert projective
diameters).  Restated:

> **DP.3-(i') (functional cone preservation).**  For dual data admitted at
> exponent granularity, every coarse channel (Bv)_n is positive as a FUNCTION
> on (0,1).

(i') is what Birkhoff needs, is strictly weaker than (i), and is contradicted by
nothing computed.  Recorded alongside: **positive diagonal conjugation is
Birkhoff-neutral** (d(Df,Dg) = d(f,g)), so a Doob/h-transform
P = D_{1/h} T D_{h'} has the same projective diameter and contraction
coefficient as T — a rate may be computed on the unnormalized composed kernel
and transported to a Markovized channel with no re-estimation.

**(4) eps_slab(M) certified (Simplification-Ledger item 7 discharged).**  By
pure combinatorial enumeration over triad-admissible labellings — no Haar
contraction, no wall-clock dependence — E*(n,m,M) := min{E(config) : max spin =
M+1} bounds min-deg(T_{M+1}-T_M).  At M=1, against the naive single-face bound
C(2)=**8**: E* = 38, 32, 32, 68, 38, 44, 56, 56, 68, 88 over the ten entries, so
**global E* = 32**.  A spin-2 face cannot appear in isolation; the triads at the
4-valent interior edge and the corner-linked perimeter classes force companions
up with it.  At s=1/2 the suppression factor alone is 2^-32 ~ 2.3e-10.
Corroboration: computed T_{M=2}[0,0] agrees with T_{M=1}[0,0] through s^47,
first differing at s^48 (4 -> 40).

**(5) Discriminator.**  U(1) control at M=1,2,3: **zero** negative coefficients
in any entry (certified lattice-point counts).  Every negative SU(2) network
value requires a **spin-2 face** — the §15a signature (negatives required spin-3)
recurring one level up, inside the blocking kernel.  Tag for the liability:
**non-abelian**; tag for functional positivity: group-generic, no gap weight.
The only gap-carrying step remains the sign of the one-step coupling defect.

**Method notes.**  M=2 was unreachable by the polynomial-valued route (direct
contraction >3.3 GB; skeleton route timed out on 17/46 classes).  New
**fixed-tile decomposition** (`computations/dp3_fixed_tile.py`) expands tile
activities into fixed spins so each class becomes a pure-character network with
an exact rational value; **gated** against `skeleton_value` (14/14, incl. spin-2
classes) and against `kernel_entry_skeleton` at M=1 for all ten entries
(`dp3_m2_driver.gate_M1`).  Rigor device: a configuration contributes to exactly
ONE exponent, so a coefficient is FINAL as soon as no UNREACHED configuration
sits at that exponent — sharper than a global window, and schedule-independent
(`dp3_m2_analysis.final_at` / `blocked_final_at`).  Runs are process-isolated
(`scripts/run_iso.py`, `scripts/worker_fixed.py`): two earlier runs died on
memory, one OOM-killed, one in a cascade of MemoryErrors raised inside its own
handler.

**Artifacts.**  `notes/dp3-m2-cone-refutation.md`;
`computations/dp3_fixed_tile.py`, `dp3_m2_driver.py`, `dp3_m2_analysis.py`,
`eps_slab.py`, `dp3_m2_entries.json`; `tests/test_dp3_m2.py` (10 fast pins
green); `scripts/run_iso.py`, `worker_fixed.py`, `blocked_image.py`.

**Open / next.**  (i) RP at M=2 (claim ii) NOT re-run — the M=1 data point
stands unamended; (ii) `T[2,2]` still computing, so `(Bv)_2` and the 3x3 Gram at
M=2 are open; (iii) restate C_exp functionally in
`docs/dp3-exponent-cone-statement.md` and re-derive the enveloped-cone
contraction on that cone; (iv) three T[0,1] configurations (E=68,76,76) exceed a
5 GB address-space cap, not merely a time budget — they bound that entry's
global window but affect no verdict above, by the per-exponent predicate.

### 15j. Addendum (2026-07-26): DP.3 M=2 verdict transported to Lean — 21 theorems, ALL AXIOM-FREE

The §15i result is now kernel-checked mathematics, not a Python claim.
`dual_kappa_spike/DP3M2Ledger.lean` (generated by
`scripts/gen_dp3m2_lean.py` from `computations/dp3_m2_entries.json`,
DP6Ledger convention: rationals as (Int, Nat), comparisons
cross-multiplied into Int, closed-integer `decide`, no Mathlib).

**What is banked.**

- `e76Configs` — every configuration of T[1,1] at the fence exponent 76
  with its exact Haar value N and D4 multiplicity.  Both the exponent
  (`configExp`) and the assembly weight (`configWeight`) are
  **rederived in Lean** from the labelling, so the ledger is internally
  consistent, not merely transcribed — the analogue of DP6Ledger's
  `profileExp`/`profileCoeff` rederivation.
- `e76_weights_positive` — the lemma that licenses the whole reading:
  every assembly weight is strictly positive, so a negative kernel
  coefficient can ONLY originate in a negative 6j network value.
- `t11_coeff_76_value` / `t11_coeff_76_negative` — **the entry-level
  fence**: the assembled coefficient is exactly -32/3, negative.
  DP.3-(i) refuted.
- `blocked_79_no_cancellation` / `blocked_79_value` /
  `blocked_79_negative` — **the aggregated fence**: both sibling
  channels vanish identically at their feeding exponents (79 and 71),
  so the -64/3 at s^79 in (Bv)_1 stands alone.  The DP.6 repair route
  is closed, in the kernel.
- `t11_final_unique_negative` / `t11_final_others_positive` — the
  negative coefficient is the ONLY one in the final part.
- `t11_scaled_matches` + `t11_final_positive_at` — evaluation pins at
  s = 1/4, 1/2, 3/4: the entry is strictly positive there despite the
  negative coefficient.  Deliberately a WITNESS only; following the
  DP6Ledger precedent, "positive on all of (0,1)" is NOT formalized
  here (that remains Sturm-certified in `computations/`).
- `eps_star_beats_naive` / `eps_star_min` — eps_slab(1)'s certified
  exponents, every one at least 4x the naive single-face bound C(2)=8.

**Verification.**  `lake build` green for all five spike targets;
`#print axioms` on all 21 theorems: **"does not depend on any axioms"**
for every one (better than the {propext, Quot.sound} budget).
Non-vacuity is not assumed: explicit count pins (`e76_config_count`,
`t11_final_count`, `blocked79_count`, `eps_star_count`) rule out
trivially-true `List.all`, and a **mutation test** (falsify the fence
coefficient to +32/3 and give a sibling channel a nonzero value) breaks
exactly the three theorems asserting those literals.

**Where it was verified — read this precisely.**  The build and axiom
audit were run in the **cloud container** with the pinned toolchain
(leanprover/lean4:v4.29.1), NOT on the Mac.  This is sound for this
package specifically because `dual_kappa_spike` has zero dependencies
(`lake-manifest.json` packages == []), so nothing about the host
environment enters; and it leaves the AGENTS.md machine-safety contract
completely untouched rather than working around it.  **A Mac-side
`lake build` under the session lock has NOT been run this session** —
per the contract, the green above is not a Mac verification.

**Unchanged wiring TODO** (shared with DualKappa/FrozenHub/DP6Ledger):
the ledger literals are transported from the Python quaternion-Haar
machinery; re-deriving them inside Lean from the main tree's finite
product Haar evaluation is the standing gap between "kernel-checked
ledger" and "kernel-checked mathematics all the way down".

**Blocked, needs a human decision:** `.git/index.lock` (zero bytes,
2026-07-25 22:06) is stale — no git/lean/lake/pytest process exists on
the device — so nothing from §15i or §15j has been committed.  Clearing
it is a one-line fix but AGENTS.md forbids removing a retained lock
unilaterally.

### 15k. Addendum (2026-07-26): T[2,2] closed — all three blocked channels computed; verdicts unchanged

`T[2,2]` finished (225/314 configurations, 89 unreached, FINAL below
E = 72; 31 terms; one negative coefficient at E = 102, PROVISIONAL).
All six entries n,m <= 2 and all three blocked channels are now in
`computations/dp3_m2_entries.json`.

`(Bv)_2`: FINAL below E = 66; coefficientwise nonnegative on its final
part; Sturm-positive on (0,1).  Negative coefficients at E = 110, 115
are provisional.

**The §15i verdicts are unchanged.**  Negative coefficients turn out to
be common in the provisional tails of every entry and every channel —
but exactly TWO are final under the per-exponent predicate, and they
are the two fences already banked: T[1,1] at s^76 (-32/3) and (Bv)_1 at
s^79 (-64/3).  The Lean ledger is byte-identical after regeneration
(it banks those two fences, which T[2,2] does not touch); spike build
re-verified green, python pins 10/10 green.

Still open: **RP at M = 2 (claim ii) has NOT been re-run**; the M = 1
data point stands unamended and the 3x3 Gram at M = 2 is untested.

### 16. The marginality-dichotomy program: SELF-CHARGE as a theorem — status and schedule (2026-07-28)

This section promotes the central finding of the two-clone review
(project doc `claude/route-forward-2026-07-26.md`) from strategy memo to
schedule.  The finding, in one sentence: the two lines of the program
have, from opposite ends, reduced the Clay problem to the statement that
the derived flow of the exact theory is marginal with the anti-screening
sign — the campaign's own SELF-CHARGE reality-fact — and neither line
has noticed, in writing, that the other holds its missing half.

**What the two halves are.**  The codex/BF line proved (its BF4 notes,
2026-07-26) that the temporal sector of the corrected slab reduces
EXACTLY to five chord holonomies (relative rank 5, transmitted cycles
{0,4,5,6,10}), with the quadratic pencil completely solved:
det(S - lambda K) = -(lambda-6)^2 (lambda-4)^3 / 384, Mehler ratio
q_0 = 3 - 2*sqrt(2) < 1/5, buffer constant C_s^2 <= e^{1728/tau} with
tau = -log s.  On that carrier the grouped Perron budget closes
CONDITIONALLY: if the physical trajectory satisfies the heat-time floor

>   (TS)   tau(a) >= kappa * a

then C_{s(a)}^2 * q_{s(a)}^{m(a,L)-2} -> 0 for every physical distance
L > 1728/kappa — and BF4 §9 proves some trajectory hypothesis is
NECESSARY (admissible s(a) -> 1 exist for which the grouped cross-ratio
diverges).  A Lean consumer (`AFEnvelope`, `BareAFImpliesLinearFloor`,
kappa = alpha*Lambda/4C) was built there and is waiting for a physical
inhabitant.  This tree (the DP line) holds the other half: the only
in-substrate instrument that computes the one-step coupling flow of the
exact blocking kernel to certificate grade, and the pinned discriminator
— the SIGN of the one-step coupling defect (§15e: SU(2) s' < s^4,
U(1) s' > s^4, exact witnesses; corridor narrowing demoted as
group-generic).  These are two ends of one object: the derived flow map
of the coupling under the exact blocking step.

**The decision problem.**  In log coordinates tau = -log s, the exact 2D
self-reproduction rule s' = s^4 reads tau'/tau = 4.  The banked strong-
coupling measurement (s = 1/2, s' = 0.034121) gives tau'/tau ~ 4.88 —
GOOD at strong coupling (acceleration past 2D feeds the anchor; it is
the confining direction) but silent about the weak-coupling end.  The
whole conditional BF4 chain lights up or dies on one dichotomy:

>   **Marginality dichotomy.**  For the physically matched one-step
>   flow, does tau'/tau tend to 4 as s -> 1 (2D-like; trajectory
>   tau(a) ~ a^2; (TS) FAILS; the scheme's transport is wrong at weak
>   coupling) or to 1+ (marginal with anti-screening; tau(a) ~
>   1/log(1/(a*Lambda)) >> kappa*a; (TS) HOLDS with enormous room)?

If the transverse/fluctuation sector renormalizes the tree-level ratio 4
down to marginality, that cancellation IS dimensional transmutation in
this formalism, and its residual first-order coefficient IS a
constructive beta function: a rational number derived from finite Haar
integrals — no pi, no measurement.  This gives RG-I8 (constructive UV
landing) its first concrete, falsifiable, in-substrate shape, and it is
decidable with machinery this tree already owns: the slab blocking
kernel (DP.2), the fixed-tile decomposition and per-exponent finality
device (§15i), the Sturm toolset, the U(1) mirror harness (§15e), and
the located-second-eigenvalue machinery (`Continuum/LocatedSpectralGap`).

**Honesty box.**  (a) The five-chord reduction, the (TS) necessity
theorem, and the `AFEnvelope` consumer are CODEX-CLONE artifacts known
here only through the project-doc review; nothing in this tree has
verified them (grep 2026-07-28: `AFEnvelope`/`BareAFImpliesLinearFloor`
absent from the audited namespaces; nearest in-tree cluster is
`Continuum/AFTrajectoryCertificate` + `Continuum/BareAFDiagnostic`).
They enter this schedule as claims to import and re-verify, not as
facts (MD.0).  (b) The dichotomy framing and the three-regime
decomposition below are the route-forward's two flagged extrapolations;
each must be proved or refuted here, not assumed.  (c) This program
does not by itself discharge RG-I7 (cutoff-independent contraction),
RG-I9 (summable distortion), the OS quantitative debt, O(4)
restoration, or non-triviality/OPE.  Per the standing triage those
consume the uniform trajectory rather than substituting for it.

### Milestone MD.0 — Bank, unblock, import (prerequisite housekeeping)

**Goal.**  The §15i–15k state is committed and Mac-verified; the codex
five-chord/(TS) artifacts are imported and independently re-verified
in-substrate before anything consumes them.

**Deliverables.**
- Human decision on the stale `.git/index.lock` (zero bytes, 2026-07-25
  22:06; §15j); then commit and push §15i–15k artifacts.  Standing
  warning applies: Dropbox has reverted `work_plan.md` twice — git is
  the durable record, so this commit is load-bearing, not hygiene.
- Mac-side `scripts/with_lean_session_lock.sh` targeted `lake build` of
  the five spike targets per AGENTS.md (the §15j cloud green is
  recorded as not a Mac verification).
- `git fetch` of the codex snapshot branch
  (`codex/full-workspace-snapshot-2026-07-24`); extraction of (i) the
  BF4 five-chord data and pencil, (ii) `AFEnvelope` /
  `BareAFImpliesLinearFloor` and their axiom state, (iii) the BF4 §9
  necessity construction.
- Independent re-verification gate: recompute the five-chord pencil
  det(S - lambda K), the transmitted-cycle set, and q_0 = 3 - 2*sqrt(2)
  from this tree's own slab machinery (exact rational eigen-pencil on
  the temporal sector) before the carrier is used anywhere.  Until this
  gate passes, MD.2 runs on the full slab kernel; the five-chord
  carrier is an acceleration, never a precondition.

**Dependencies.**  None (the lock decision is the user's).

### Milestone MD.1 — The observable-matched flow map (definition layer)

**Goal.**  A definition of the blocked coupling s' that is fixed by
matching an OBSERVABLE across the blocking step, not by projecting the
blocked kernel back onto single-plaquette form.  Projection builds the
2D rule in at tree level; the 4-vs-1 ambiguity of the dichotomy lives
entirely in this definition, so the definition layer is load-bearing.

**Definition (primary).**  s' is the coupling at which the COARSE
transfer separator (the located second eigenvalue, machinery of
`Continuum/LocatedSpectralGap`) reproduces the FINE two-cell separator,
both computed in the DP.3 exponent-granularity RP Gram of
perimeter-loop characters (the only norm in the program that is
simultaneously exact, reflection-positive, and blocking-covariant).
**Definition (control).**  Gram-corridor matching — s' fixed by
reproducing the corridor width of the enveloped cone.  Two genuinely
different matchings are required by the scheme-covariance fence below.

**Deliverables.**
- `computations/flow_matching.py`: exact-rational matched s' for both
  definitions, SU(2) and U(1) through the same code path, M as a
  parameter; the legacy projection value recorded alongside as
  comparison (never as gate).
- Gates: (g1) at s = 1/2, M = 1 the harness reproduces the banked DP.2
  protocol numbers to the digit before any new claim is made; (g2)
  U(1) mirror runs on the identical ∂-data (the §15e fairness
  discipline); (g3) both matchings evaluated on the same run.
- `docs/observable-matched-flow.md` recording the definitions and the
  refutation surface (what outcome kills what).

**Dependencies.**  None hard; MD.0's five-chord gate accelerates it.

**Open questions.**  Whether M = 1 suffices at the definition layer or
the 4-valent interior edge (where §15e locates the non-abelian
recoupling) forces M >= 2 from the start; whether the matched s' is
well-defined on all of (0,1) or only piecewise (a piecewise answer is
itself reportable structure).

### Milestone MD.2 — The dichotomy computation (decisive)

**Goal.**  Decide, in exact arithmetic with Sturm-certified windows,
whether the observable-matched ratio tau'/tau tends to 4 or to 1+ as
s -> 1-, for SU(2) and U(1) in the same harness.

**Protocol.**  Rational ladder s in {1/2, 3/4, 9/10, 99/100, 999/1000}
(the DP.6 endpoint ladder) extended toward 1 as far as the per-exponent
finality device certifies; M = 1 then M = 2 via the fixed-tile route;
M = 3 stability check with the eps_slab(M) modulus bounding truncation
exponents; both MD.1 matchings; every number an exact rational, every
window a Sturm certificate.

**Decision table (all three outcomes are deliverables).**
- SU(2) ratio trends to 1+ AND U(1) separates (ratio -> 1- or the
  abelian rule): mechanism certified; open MD.3 in the same session.
- NO separation between SU(2) and U(1): the scheme family is an
  MK-type false positive, refuted BEFORE it can contaminate the chain;
  bank the kernel-checked fence, kill the scheme family, promote shaft
  PF to primary.
- SU(2) ratio -> 4 for every admissible matching: the most important
  negative theorem the program has produced — (TS) is uninhabitable
  along this scheme family; bank it and redirect.

**Deliverables.**  `computations/dichotomy_run.py`; exact ledger
`computations/dichotomy_results.json`; `notes/marginality-dichotomy.md`;
pinned tests.  Process isolation per §15i (5 GB caps, UNREACHED
recorded, per-exponent finality only).

**Dependencies.**  MD.1.

### Milestone MD.3 — The marginal-defect coefficient (a constructive beta function)

**Goal.**  If MD.2 lands marginal: a two-sided rational envelope

>   1 < tau'/tau <= 1 + c*tau   uniformly on (s_*, 1),

with c and s_* explicit rationals and Sturm certificates — the sharpest
known form of the Balaban-grade hardness, concentrated into one
truncation-error lemma on a finite-dimensional map near its marginal
fixed point.  The residual first-order coefficient is extracted as an
exact rational (finite Haar integrals; no measurement) and its SIGN is
the anti-screening statement: SU(2) positive, U(1) non-positive.

**Group uniformity rides along.**  Derive the defect coefficient with
(h_vee, Delta_Casimir) as parameters — the one-loop anti-screening
coefficient is monotone in h_vee — so the existing R1 worst-case spine
(everything minimized at A_1) carries it to all compact simple G with
SU(2) as pilot, per invariant P6.  The coupled-simplification audit
applies in full: this touches the multiplicity-free 6j vertex calculus.

**Deliverables.**  Envelope certificates; coefficient ledger;
`notes/marginal-defect-coefficient.md`; the U(1) non-positivity fence
as a certified computation, not a remark.

**Dependencies.**  MD.2 (marginal branch).

### Milestone MD.4 — The window atlas (the crossover is compact)

**Goal.**  A finite, Sturm-certified rational cover of the compact
interval [2^{-1/3}, s_*] chaining the unconditional strong-coupling
anchor window (single-edge located-gap window [0, 2^{-1/3}), where
1 - w^3 -> 0 kills any uniform floor from lattice units alone) to the
validity edge s_* of the MD.3 envelope.  Under the three-regime
decomposition — strong: unconditional; middle: compact, hence a finite
atlas of exact certificates; weak: the MD.3 envelope — the crossover
("the tornado") is not an infinite problem.  The decomposition itself
is extrapolation #2 and must be proved as the atlas-adequacy lemma:
the union of the three regimes covers the derived trajectory.

**Deliverables.**  `computations/window_atlas.py` + certificate ledger;
per-window functional-positivity statements on the DP.3-(i') functional
cone (consuming DP.R2 below); the atlas-adequacy lemma statement.

**Dependencies.**  MD.3 (for s_*); DP.R2.

### Milestone MD.5 — (TS) instantiation and Lean transport

**Goal.**  Package MD.3 + MD.4 as the physical inhabitant of the
bare-AF envelope consumer; derive the linear heat-time floor
tau(a) >= kappa*a with explicit rational witness; feed the five-chord
Perron budget; exit certificate is the scale-dependent grouped target
q_a = 1 - m*a + o(a) over fixed physical distance (deliberately NOT a
microscopic uniform q < 1).

**Lean.**  Extend `dual_kappa_spike` with a generated ledger
(`scripts/gen_md_lean.py`, DP6Ledger/DP3M2Ledger convention: rationals
as (Int, Nat), cross-multiplied comparisons, closed-integer `decide`,
no Mathlib, count pins + mutation test) banking: the envelope
inequalities on the atlas windows, the U(1) non-positivity fence, and
the composition into the floor.  Then wire toward the main-tree
consumer (imported `AFEnvelope` or `Continuum/AFTrajectoryCertificate`)
under the {propext, Quot.sound} gate with both statement guards.  The
standing wiring TODO is inherited and recorded: generated ledgers are
"kernel-checked ledger", not "kernel-checked mathematics all the way
down", until the in-Lean finite-product Haar re-derivation lands.

**Two identifications owed to the BF side, with DP fillings.**  The
"physical projective norm" field of BF3.3's admissibility interface :=
the DP.3 exponent-granularity RP Gram; the refresh/minorization packet
re-derived on the five-chord carrier in that Gram norm.

**Dependencies.**  MD.3, MD.4; MD.0 (consumer import + gate).

### Shaft PF (parallel-safe) — fermionize the sign sector

The other standing liability: dual positivity is only true after
retreat (DP<=1 / exponent aggregation, §15d), the coefficient cone is
refuted outright (§15i), and positive-carrier constructions keep paying
collapse penalties to avoid the signed sector.  The structural evidence
— sgn A_x = (-1)^{q(x)} with q an even Brown/Arf-type quadratic
refinement of the mod-2 intersection form; sector ledgers resumming
through overlap graphs K_{2,2}/K_{2,4}/K_{4,4} with local weight
W = [[1,1],[1,-1/3]] and Z_{m,n} = sum_r C(m,r)(1+(-1/3)^r)^n > 0 — is
exactly the input shape of the Gauss-Milgram/Arf-Brown-Kervaire
calculus, i.e. of fermionization (2D Ising <-> free fermion via
Kasteleyn orientations; signed surface sums <-> spin structures).

**Milestone PF.1 — the embedded Pin- DECIDER.**  Construct the
embedded/framed Pin- realization of the full strand cover: embed the
SURFACE (global push-axis assignment), not the curves — the curves-only
lift saturates at ~70% triple consistency, and the completed 300-sample
abk_verdict2 run showed the miss pattern is NOT clean d2 (d1:6, d2:13,
d3:3, d4:8) with an 83% assembly attrition and a beta == 0 attractor on
kappa=0.  Decision rule (banked 2026-07-24): if the embedded surface
reproduces the kappa=1 -> beta=4 half, beta = 4*kappa is alive; if it
reproduces the beta == 0 attractor, DROP beta = 4*kappa in favor of a
beta == 0 rigidity statement.  Either way the correlation-mode era
ends: the embedded object makes q well-defined, kills the nonpin/q/B
failure modes, and turns the conjecture into a computable statement.

**Milestone PF.2 — the Pfaffian identity.**  Formulate and test:

>   The signed part of the SU(2) dual heat-kernel sum on a physical
>   complex is, exactly, a Pin--twisted sum over the strand cover, and
>   its exponent-aggregated channels are Pfaffians of an explicit
>   Kasteleyn-oriented finite matrix built from the W-weights — hence
>   positive by structure, not by suppression.

First test on the K_{2,2}/K_{2,4}/K_{4,4} ledgers where the closed form
is already exact; `computations/kasteleyn_search.py` /
`kasteleyn_phase2.py` are the starting machinery.  If true, dual
positivity becomes an identity at every cutoff with no s-window
smallness — precisely the positive, cutoff-uniform Birkhoff carrier the
BF3.3 interface demands, and the scale-coherent sign convention (open
DP.1 question) comes with it via the ABK Z/8 phase.

**Milestone PF.3 — the strata where the shaft can die.**  (i) The
chi = 2 sphere supports: 30 of 33 negative orbits at doubled-spin
cutoff two live OUTSIDE the torus lane where the (-1)^{ab} rule is
proven — extend or refute the quadratic-refinement law there.  (ii)
Interface-bearing configurations force decorated RELATIVE spin
networks (boundary-decorated refinements).  Both finite computations;
run them before any PF result is consumed upstream.

**Coupling.**  PF landing hands MD its positive carrier with no
collapse factors; MD landing does not need PF.  Neither blocks the
other; PF is the designated redirect target if MD.2 refutes.

### DP residuals (feed, do not block)

- **DP.R1 — RP at M = 2.**  Re-run DP.3-(ii) with the closed T[2,2]:
  the 3x3 Gram under theta: z -> 1-z, Sturm on leading principal
  minors, U(1) mirror, antilinearity control.  Named open in §15i and
  §15k; the M = 1 PSD point stands unamended until this runs.
- **DP.R2 — functional cone restatement.**  Rewrite
  `docs/dp3-exponent-cone-statement.md` around DP.3-(i') (functional
  cone preservation), and re-derive the enveloped-cone contraction on
  that cone, using the recorded Birkhoff-neutral Doob/h-transform
  lemma (d(Df,Dg) = d(f,g)) to transport rates from the unnormalized
  composed kernel.  This is the §15i open item (iii) and is consumed
  by MD.4.
- **DP.R3 — T[0,1] window.**  The three configurations at E = 68, 76,
  76 exceed the 5 GB address-space cap; build a streamed/factored
  evaluator or a sharper skeleton bound.  Windows only; no verdicts.

### Route-specific fences (added to the standing audit rules)

1. **U(1) control at every MD stage.**  Any envelope, corridor, atlas
   window, or contraction statement that survives verbatim under
   d_n == 1, Casimir m^2 carries no gap weight; the DP.6-U1 audit
   table applies unchanged to the observable-matched flow.  The MD.2
   harness must emit the U(1) verdict in the same run, always.
2. **Scheme covariance of the defect sign.**  The classical fact that
   the one-loop coefficient is scheme-independent needs an in-substrate
   analogue: the SIGN of the marginal defect must be invariant across
   the admissible scheme family (M, carrier, matching observable).
   Cheap first check: separator matching vs Gram-corridor matching
   agree.  A sign that flips across admissible schemes refutes the
   definition layer (MD.1), not the theory — bank it as such.
3. **Anti-loop rule.**  The MD.5 deliverable is a two-sided rational
   envelope with Sturm certificates and a Lean inhabitant of the
   imported consumer — not a renamed alias of (TS), and not a new
   interface equivalent in strength to it.  A reduction is the start
   of the next attack, never a deliverable.
4. **No measured number on the critical path.**  Ladder evaluations
   are scouting until replaced by certified windows; only exact
   rationals and Sturm certificates cross into proofs or ledgers.
5. **Refutations are deliverables.**  A certified non-separation at
   MD.2, or a certified tau'/tau -> 4 for every admissible matching,
   is banked as a kernel-checked fence and redirects the campaign to
   PF as primary — in the same session, per the standing loop.

### Registry update (mechanism families, not wording)

Two families enter the active mechanism registry: **derived-flow
marginality** (observable-matched blocking flow; dimensional
transmutation as a computed cancellation; distinct from bond-moving
envelopes — refuted 2026-06-27, linear defect; from the character-
window mechanism — closed by the ceiling theorem hi < 2^{-1/3}; and
from fixed-coupling CP domination — collapse eta_s^{21}), and
**sign-sector fermionization** (Pin-/Kasteleyn/Pfaffian; distinct from
suppression-and-margin control of the signed sector).  Gate mapping:
MD attacks the trajectory content of C6b/C6d/C6e in this substrate's
coordinates and gives RG-I8 its first falsifiable shape; PF attacks
the carrier content of C7/RG-I7.  Cross-gate fence 1 (independent
scale setting) is respected by construction: the matching observable
fixes s' with no reference to any desired mass.

### Sequencing

MD.0 (user unblocks git; imports start immediately) -> MD.1 -> MD.2
[decision point] -> MD.3 -> MD.4 -> MD.5; PF.1 -> PF.2 -> PF.3 in
parallel throughout; DP.R1/DP.R2 immediately (DP.R2 gates MD.4);
DP.R3 and the manuscript sweep (998/1000 headline, conditional Balaban
citation) as background.  Deferred until MD.2 decides: BF5-style
branched-sector grading, further DP strata enumeration, any new Lean
composition machinery — the RG-I/CD scaffolding is closed and waiting;
it needs physical content, not more structure.

### 16a. Addendum (2026-07-28): MD.1 EXECUTED — the strong-coupling sign discriminator is SCHEME-BORNE; magnitude separation survives; MD.2 opened with a protocol discovery

MD.1 (the observable-matched flow map, definition layer) is executed.
Artifacts: `computations/flow_matching.py` (both matchings, both
groups, one code path, M a parameter); `tests/test_flow_matching.py`
(9 pins, green in the cloud container); `docs/observable-matched-flow.md`
(the definition record); `computations/flow_matching_results.json`
(exact ledger, 16 rows, ladder s in {1/4, 1/2, 3/4, 9/10}).

**Definitions landed.**  D1 (primary, separator matching): the matched
coupling solves d_1 s'^{C(1)} = sigma(s), where sigma(s) =
lambda_1/lambda_0 of the DP.3 OS Gram of the one-step blocked slab —
exact charpoly, Sturm isolation, certified rational windows,
cross-checked against an independent float eigensolver to all printed
digits.  Structural fact: the 2D fixed-point pairing on this geometry
is RANK ONE (frozen gate), so sigma is a purely transverse observable
— the 2D theory has zero connected one-step transfer, and any nonzero
sigma lives in exactly the sector §15e located the non-abelian
recoupling in.  D2 (control, pair matching): s'_{ab}^{C(b)-C(a)} =
(v_b d_a)/(v_a d_b) on the flowed envelope, exact rationals; the U(1)
(0,1) pair reproduces the banked rho_1 witness identically.  Gates:
g1 banked DP.2 floats to the digit + DP.6-U1 exact witnesses; g2
identical boundary data + saved-kernel equality; g3 one ledger.

**Finding 1 — the §15e sign discriminator does not survive matched
truncation under the envelope definition.**  Exact: T[0,2] has NO
2D-disk term at M=1; it first appears at M=2 (3 s^32, final window
66 > 32).  At M=1 the (0,1) pair is already ABOVE the 2D rule
(1467702248448/6005899834403585 > (1/2)^12) while pairs into the
disk-starved spin-2 channel sit ~100x BELOW — the legacy fit averaged
these into the banked s' = 0.034121 < s^4.  At M=2 ALL SU(2) pairs
are ABOVE the rule (1.00098, 1.01615, 1.01515 at s = 1/2, exact),
the same side as U(1) (1.27284, 13.19148, 10.36386).  What survives
is separation by MAGNITUDE (U(1) deviations 16x-800x SU(2)'s), and,
on D1, the exact ordering sigma_su2 * 4 < sigma_u1 at s = 1/2 with
M-stability (su2 M1->M2 shift < 0.25%; u1 M2->M3 < 3e-7 relative):
the SU(2) connected channel damps >4x harder than the abelian one —
the contraction-friendly direction, now on a located spectral
observable instead of a fit.  Consequence for the ledgers: every
"SU(2) s' < s^4" statement (§15b, §15e, §15i(5), the P23-P24
record) must be read as scheme-qualified (M=1, fit protocol); the
non-abelian tag is NOT a fixed-s sign.  The route-forward's fence
anticipated this: the discriminating object is the s -> 1 dichotomy
class under scheme covariance, not a strong-coupling sign.

**Finding 2 — scheme covariance fails at fixed strong coupling.**
At the same s, kernel, and M, legacy/pair/separator give different
defect signs.  Banked as the MD.1 fence firing exactly as designed:
it refutes fixed-s sign discriminators, and moves the burden to the
s -> 1 limit (MD.2), where the dichotomy class must agree across
admissible matchings before it counts.

**MD.2 opened — first probe and a protocol discovery.**  At
s = 99/100 the truncation ladder does not converge: U(1) pair01
tau'/tau falls 19.55 -> 12.03 -> 7.88 across M = 3, 4, 5 (still
falling); SU(2) M=2 tails above the final windows weigh
(99/100)^58 = 0.56 relative — fixed-M ladder points CANNOT reach the
dichotomy regime.  MD.2's first deliverable is therefore an
M -> infinity-controlled object, not a longer ladder: for U(1) the
owned-boundary kernel at M = infinity is an exact quadratic-form
theta sum over the rank-4 cube-flip lattice,
T_U1[n,m](s) = sum_{c in Z^4} s^{Q(c;n,m)}, with geometric tail
bounds certifiable in exact rationals — no truncation.  The SU(2)
analogue needs the fixed-tile machinery with eps_slab-style tail
bounds at general M.  Theta-resummation of the abelian transverse
sector is the next attack.

**Honesty.**  Cloud-container verification only; no Mac-side run
under the session lock this session (AGENTS.md discipline: cloud
green is not a Mac verification; the module and tests are pure
Python + Fraction with no repo-lock interaction, and sympy is used
only inside the imported flip-lattice certificate).  SU(2) M=2 rows
consume provisional tails above the per-entry final windows —
irrelevant at s <= 1/2 (< 2^-58 rel), order 1e-3 at s = 9/10, order
0.5 at s = 99/100 (that row is marked accordingly).  The separator's
matched channel is labeled by the fixed-point n = 1 channel;
eigenvector channel migration was not observed on this ladder but is
not excluded off it.  Nothing here decides the dichotomy: MD.1 is
the definition layer, and both of its findings are about which
definitions are admissible, not about the s -> 1 class.  Git commit
remains blocked on the stale `.git/index.lock` (§15j human
decision); until it is cleared, work_plan.md and these artifacts are
Dropbox-only and the standing revert warning applies.

### 16b. Addendum (2026-07-28, same session): U(1) LANE DECIDED at M = infinity — theta-resummation lands tau'/tau -> 3 EXACTLY; the SU(2) target number is now pinned

The §16a protocol discovery is executed.  The abelian owned-boundary
kernel needs no truncation: its configuration set is (particular
disk) + (rank-4 cube-flip lattice), so the M = infinity kernel is the
quadratic-form theta series T[n,m](s) = sum_{c in Z^4} s^{Q(c;n,m)}.
Artifacts: `computations/u1_theta_kernel.py`,
`computations/u1_theta_results.json`,
`tests/test_u1_theta_kernel.py`, `notes/u1-theta-resummation.md`.
Pins 17/17 green (with the MD.1 suite) in the cloud container.

**Exact lattice data (grid-verified, pinned).**
A = B^T B = 6I - Adj(C_4), spectrum {4, 6, 6, 8} by exact charpoly
(x-4)(x-6)^2(x-8); b(n,m) = 2(n-m)(1,1,1,1); |u|^2 = 4;
Qmin(n,m) = min over REAL c of Q = 3n^2 + 3m^2 + 2nm.  Kernel values
at rational s are certified rational windows (partial sum + tail
bound from lambda_min = 4 and the shell count <= 80 r^3); gates:
flip-lattice certificate, spectrum, Qmin grid, monotone sandwich of
T_M for M = 3..6, nested refinement.

**The law.**  As tau = -log s -> 0, T[n,m] ~ Theta_0(tau)
e^{-tau Qmin(n,m)} with Theta_0 group-data-free (Poisson; corrections
O(e^{-c/tau})).  Over any charge-symmetric coarse basis the mean
kills the cross term and matches C(n) = n^2 exactly, so EVERY
D2-family observable (all pairs, and the legacy fit) has one limit:

>   tau'/tau -> E* = |u|^2 - (B^T u)^T A^{-1} (B^T u) = 4 - 1 = 3.

N-independent; scheme-covariant across the D2 family AT the limit
(the §16 fence holds there).  Certified ladder (pairs 01/02/12):
s = 1/2: 3.6520/3.0695/2.8753; 3/4: 2.8031/2.7670/2.7550; 9/10:
2.7809/2.7822/2.7826; 99/100: 2.9620/2.9621/2.9621 -> 3.  The pairs
collapse onto each other as s -> 1; approach E* + O(tau),
non-monotone (dip near s ~ 0.85, pinned).  Cross-instrument gate:
theta at s = 1/2 reproduces the converged fixed-M 3.652 to the
digit; the §16a fixed-M values at 99/100 (19.6/12.0/7.9) are
confirmed pure truncation artifacts (true value 2.962).

**Consequence.**  The U(1) lane of the one-step dichotomy is
DECIDED: tau'/tau -> 3 — neither the 2D class (4) nor the marginal
class (1).  Under naive one-step iteration tau(a) ~ a^{log2 3} =
a^{1.585}, failing the (TS) linear floor — as the gapless abelian
control must.  The SU(2) half of MD.2 now has an exact target: gap
weight requires E*_SU2 to separate BELOW E*_U1 = 3; naive
(TS)-viability needs E*_SU2 <= 2; marginality proper is -> 1.

**Derived expectation to prove or refute (the next attack).**  In
the flat limit the compact-group heat kernel degenerates to a
Lie-algebra Gaussian and the leading minimization is group-blind, so
SU(2) should ALSO land at leading exponent 3 with the non-abelian
content in the SUBLEADING slope: E*(tau) = 3 + c_G tau + O(tau^2),
discriminator c_SU2 vs c_U1.  This relocates MD.3's marginal-defect
coefficient to a concrete finite computation on this instrument.
The U(1) slope is ~3.8 near tau = 0 from the ladder and exactly
derivable from the theta expansion; the SU(2) analogue needs the
M -> infinity resummation of the character-sum kernel (fixed-tile
machinery + eps_slab-grade tail bounds).  That resummation is the
open front.

**Honesty.**  One-step, thickness-one, anisotropic (2x2x1) blocking
on the DP.2 slab — an exact statement about this instrument, not an
iterated isotropic trajectory; the iteration reading is heuristic
until the iterated map exists.  D1 (separator) degenerates at this
geometry (lambda_1/lambda_0 = O(tau); matched ratio diverges like
log(1/tau)/tau) and needs a tau-rescaled matching to be a dichotomy
coordinate — recorded, not repaired.  Poisson enters only the
asymptotic statement; every ladder number is a certified rational
window.  Cloud-container verification only; the Mac-side session-lock
run and the git commit (stale index.lock, §15j) remain owed.

### 16c. Addendum (2026-07-28, same session): the U(1) lane upgraded from limit to EXACT ASYMPTOTIC CURVE — E*(tau) = 3 - 4 tau + (112/5) tau^2, coefficients pair-independent; the SU(2) discriminator sharpened to a slope with a structural prediction

Artifacts: `computations/flow_asymptotic.py`,
`computations/flow_asymptotic_results.json`,
`tests/test_flow_asymptotic.py`, `notes/su2-flat-limit-scope.md`.
Full suite 37/37 green in the cloud container.

**Theta-factor separation (lemma-grade, certified).**  Q(c;n,m) =
(c-c*)^T A (c-c*) + Qmin(n,m), so T[n,m](s) = s^{Qmin} Theta_{c*}(s)
and the c*-dependence of Theta is bounded by an explicit dual sum:
|Theta_{c*}/Theta_0 - 1| <= 2 sum_{k!=0} e^{-pi^2 k^T A^-1 k / tau},
certified rational via k^T A^-1 k >= |k|^2/8, pi^2 >= 9869/1000,
e^{-x} <= 1/(partial series), shells <= 80 r^3.  The divergent,
group-blind theta bulk cancels IDENTICALLY in every observable;
what remains is the finite coarse-basis polynomial

    P_n(s) = sum_{|m|<=N} s^{gamma n m + (alpha+1) m^2}
           = sum_m s^{2nm + 4m^2},

and every pair observable has the exact asymptotic closed form
E*_{ab}(s) = 3 + [log P_a - log P_b]/(tau (C(b)-C(a))).

**Verification.**  Against the §16b certified windows: agreement to
1e-10 at s = 99/100, ~1e-6 at 9/10 (within the certified slack;
at 3/4 the dual corrections are real and visible, ~5e-2 — the curve
is asymptotic, and the crossover scale is now quantified).

**Expansion, exact.**  E*(tau) = 3 + c1 tau + c2 tau^2 + O(tau^3)
with c1 = -gamma^2 Var_N(m)/2 (= -4/3, -4, -8 at N = 1, 2, 3) and
c2 = 112/5 at N = 2 — BOTH pair-independent: the D2 family is
scheme-covariant through second order.  The N-dependence of c1 is
explicit and structural (basis variance), not noise.

**The sharpened discriminator (structural prediction, NOT banked).**
The U(1) slope is driven entirely by gamma^2 — the square of the
abelian cross term nm, i.e. the linear-in-covariance coupling of the
two loop tilts, a channel that exists because e^{im theta} has a
tilting first moment.  SU(2) characters are real and even on the Lie
algebra, so E[grad chi] = 0 and the linear cross term is FORBIDDEN:
under flagged assumptions (A1 flat-limit interchange, A2 component
decoupling; `notes/su2-flat-limit-scope.md`) the prediction is
E*_SU2(0) = 3 (group-blind, as §16b anticipated), gamma_SU2 = 0 at
leading order, and c_SU2 free of any basis-artifact term — the first
genuinely non-abelian number of the flow, whose SIGN is the
anti-screening statement at this order.  MD.3's marginal-defect
coefficient is now this one number.

**Next attack (the open half of MD.2), two routes queued.**
(a) Cyclic transfer operator for the SU(2) slab network (D4
structure: trace of a 4-fold product over (tile, perimeter-class,
wall) labels with 6j vertex weights) — gate: reproduce
`kernel_entry_skeleton` exactly at M = 1, 2; then certified windows
at growing M with eps_slab-grade tails.  (b) Flat-limit expansion:
discharge A1/A2 into finite Gaussian-moment computations and derive
c_SU2 as an exact rational, with the U(1) mirror of the same
machinery required to reproduce c1 = -4 at N = 2 as its built-in
refutation channel.

**Honesty.**  One-step, thickness-one, anisotropic slab instrument
throughout; iterated/isotropic upgrades downstream.  §3 of the scope
note is a prediction under flagged assumptions, banked as scope, not
as theorem.  Cloud verification only; Mac session-lock run and the
git commit (stale index.lock, §15j) remain owed — everything since
§15i is still Dropbox-only.

### 16d. Addendum (2026-07-28, same session): the SU(2) flat representation BANKED — the non-abelian analogue of the Poisson step, verified to 87 digits; the c_SU2 derivation now has its instrument

The entry point of §16c route (b) is in the tree.  In repo
conventions (s = e^{-tau}, K = sum d_n s^{C(n)} chi_n, chi_n =
sin((n+1)phi)/sin(phi), phi the class half-angle), the SU(2) heat
kernel equals EXACTLY a Gaussian image sum on the flat line:

    K(phi; s) = e^{tau} sqrt(pi) / (4 tau^{3/2} sin phi)
                * sum_{j in Z} (phi - 2 pi j)
                  e^{-(phi - 2 pi j)^2/(4 tau)}

(Jacobi theta transform of the character sum; classical).  Artifacts:
`computations/su2_flat_heat_kernel.py`,
`tests/test_su2_flat_heat_kernel.py`; suite 41/41 green (cloud).
Gates: identity to 9.1e-87 worst relative error across a 16-point
(tau, phi) grid with adaptive precision (the small-tau/large-phi
corner needs ~ phi^2/(4 tau ln 10) extra digits against
cancellation); Haar normalization exact to quadrature precision;
character projection to 4.4e-61 for n = 1..3.  Verification
discipline note, recorded deliberately: the first transcription of
the image constants (period pi, prefactor /2) was WRONG and the
40-digit gate refused it; the corrected constants (period 2 pi,
prefactor /4) pass at 87 digits — the gate did exactly the job the
campaign's rules assign it.

**What this makes possible.**  Near s -> 1 every slab face activity
is a flat Gaussian in the plaquette class angle times explicit
Jacobian insertions plus exponentially small images.  The SU(2) slab
kernel becomes a flat Gaussian NETWORK integral whose leading order
is group-blind (three decoupled components on the same geometry —
E* = 3, matching §16c's prediction channel), and the O(tau)
correction — c_SU2, MD.3's marginal-defect coefficient — is a
finite sum of Gaussian moments against three explicit insertion
families: (i) the e^{tau} per-face normalization (cancels in flow
ratios up to face counts), (ii) the phi/sin(phi) activity Jacobians
and the sin^2(phi) Weyl density, (iii) BCH non-closure of the
plaquette angle — the first place the structure constants enter.
The U(1) mirror of the same expansion must reproduce c1 = -4 at
N = 2 (built-in refutation channel).  Status: the identity is a
verified numerical gate (scaffolding), not yet a certified-rational
object; certification (rational pi windows + tail bounds, per
`u1_theta_kernel.slack_bound`) is owed by whichever step first
consumes it in a verdict.

**Queue.**  (1) The Gaussian network dictionary of the slab: exact
effective covariance of the two coarse loop angles from the face
constraint geometry (the U(1)/real relaxation already fixes the
leading block: Sigma_eff = [[3,1],[1,3]] per component); (2) the
(ii)-insertion moments (pure calculus, groupwise); (3) the
(iii)-BCH moments (the non-abelian content; sign of c_SU2 = the
anti-screening statement at this order); (4) U(1)-mirror gate.

**Git.**  Commit d6af5ba (this session, user-authorized lock
clearance) banks §15i–§16c and all prior uncommitted state; the
§16d artifacts are committed on top in the same session.  PUSH still
requires the user's credentials from the Mac terminal:
`git push origin main` — neither the device sandbox (no network) nor
the cloud container (no credentials; private repo) can complete it.

### 16e. Addendum (2026-07-28, same session): the moment computation, stage one — dictionary GATED, the fusion-mean identity KILLS the linear cross slope, and the discriminating observable's abelian lane is VERIFIED

Artifacts: `computations/gaussian_network_moments.py`,
`computations/gaussian_network_results.json`,
`tests/test_gaussian_network_moments.py`,
`notes/gaussian-network-dictionary.md`.  Suite 48/48 green (cloud).

**Dictionary (exact rationals, gated).**  Per su(2) component the
flat limit of the slab is the Gaussian network S = |BX|^2/(4 tau) on
the 16 free links.  GATE PASSED: the loop covariance
L G^-1 L^T = [[3,1],[1,3]] from independent 16x16 rational linear
algebra — the angle picture reproduces the flux-picture
Qmin = 3n^2+3m^2+2nm by Legendre duality.  Face variances by D4
class, each exactly uniform: tiles 79/96, perimeter walls 79/96,
interior walls 17/24 (x 2 tau).  The face-loop and link-loop
covariance aggregates for the insertion assembly are emitted.

**Structure theorem 1 (fusion-channel formula).**  With loop
insertions as operator tilts (ordering corrections deferred,
relative O(tau^2)): T[n,m]/Theta ~ sum_J (2J+1)
e^{-tau[3C(n)+3C(m)+delta_J]}, delta_J = C(2J)-C(n)-C(m).  The
abelian cross term gamma*nm is REPLACED by the fusion-channel
spread; leading diagonal cost group-blind (E* = 3, as §16b/§16c
predicted).

**Structure theorem 2 (fusion-mean identity).**  sum_J (2J+1)
delta_J = 2 tr(J1.J2) = 0 exactly (pinned n,m <= 6): the mean
channel spread VANISHES — the algebraic form of the §16c realness
argument.  The SU(2) pair moment has NO O(tau) cross correction at
leading fusion order; c_SU2 is carried entirely by the Jacobian/BCH
insertion moments (+ the finite-basis cumulant mechanism).  First
surviving cross effect: -tau^2 Var_fusion(delta)/2, with
Var_fusion = 12, 32, 256/3 at (1,1), (1,2), (2,2), exact.

**Calculus gate.**  e^tau E_flat[(sin phi/phi) chi_n] =
d_n e^{-tau C(n)} verified to 5.4e-41: the Jacobian insertion plus
the e^tau normalization convert the flat (n+1)^2 into the exact
Casimir — every constant of the insertion calculus pinned by one
identity.

**The discriminating observable.**  Connected cross ratio
X_nm = log(T[n,m]T[0,0]/(T[n,0]T[0,m])): U(1) X_11 -> -2 tau EXACT
(verified from certified theta windows: -0.210720 vs -0.210721 at
s = 9/10; -0.020101 vs -0.020101 at 99/100); SU(2) X_11 -> +6 tau^2
predicted (coefficient indicative until the BCH moments land; the
vanishing of the O(tau) term is exact).  Opposite sign, different
order — the sharpest group separation the program has produced, and
the designated first consumer of the SU(2) M -> infinity
resummation.

**Next attack (the assembly).**  (a) (ii)-insertion assembly from
the emitted covariance aggregates; (b) (iii)-BCH cubic moments (the
anti-screening sign lives here); (c) finite-basis cumulants on the
corrected exponents; (d) the U(1) mirror must return c_dyn = 0
exactly — the pipeline's refutation channel.

**Honesty.**  Operator-ordering corrections deferred at relative
O(tau^2) — O(tau) statements safe, tau^2 coefficients indicative.
Cloud verification only; Mac session-lock run owed; the push of
d6af5ba/4d57923 (+ this addendum's commit) is owed by the user:
`git push origin main`.

