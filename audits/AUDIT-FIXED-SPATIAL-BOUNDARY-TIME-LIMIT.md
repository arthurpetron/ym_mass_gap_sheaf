# Nested original-observable brackets and a constructive boundary-time limit

Date: 2026-09-16. Classification: PROGRESS after mathematical checkpoint
`bdddddb`; research-cadence-only checkpoint `1efcf5d` is unchanged.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 with the required
QFT axioms and a positive physical Hamiltonian gap for each compact simple
group, for the SAME theory, within the constructive axiom gate. The result
below is a fixed-width one-sided boundary scalar, not that whole target.

## Argument and original consumer

Fix 0<w<1, width, K>=headCutoff(w), and an original signed probe fs.
Keep the existing T_K, ell_K(f)=H[V_K*f], and positive normalization masses.
Write r_n=ell_K(T_K^n sourceProbe)/ell_K(T_K^n 1).

The previous checkpoint constructed comparison brackets [l_n,u_n] with
width q^n*(probeCap fs+probeCap fs). Width decay alone was insufficient:
the intervals could have moved. The two refresh gains are now proved
nonnegative, so l_n<=l_(n+1) and u_(n+1)<=u_n. Scalar endpoint induction
proves nesting for every n<=m. Every r_m therefore lies in [l_n,u_n], and
for arbitrary i,j>=n both inequalities hold:

    r_i <= r_j + q^n*(probeCap fs+probeCap fs),
    r_j <= r_i + q^n*(probeCap fs+probeCap fs).

The existing geometricCutoff provides an executable epsilon-to-time
threshold, including q=0 and zero cap. This constructs a QCauchy datum
and its CReal boundaryTimeLimit. The actual limit representative is within
the geometric error of r_n at every representative index k>=n; the same
limit lies between every pair of computed bracket endpoints.

The original consumer is literal finiteValue at ambient extent=width+steps,
chain start=0, lower probe fs and empty upper probe. Geometry inequalities
are proved from that schedule. The face-membership guard on fs remains.
The exact pin carries the original varying-extent scalar to r_steps,
and then transports the SAME modulus and CReal limit back to that stream.
The spatial V at the terminal boundary and original whole-chain partition
remain present, including zero time length. Only the selected fixed-width
chain has action factors; increasing ambient extent is a faithful recoding,
not a full-box thermodynamic limit.

## Declaration evidence

All module paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `refresh_nested` | `BF4ExactSlabFixedSpatialTransferBracketNesting.lean:62` | Nonnegative gains tighten both endpoints. |
| `iterateBracket_successor_nested`, `iterateBracket_nested` | `BF4ExactSlabFixedSpatialTransferBracketNesting.lean:75`, `:104` | Successor and all-later nesting of actual iterates. |
| `sourceProbeBracket_nested`, `sourceProbeMassRatio_later_bounds` | `BF4ExactSlabFixedSpatialTransferBracketNesting.lean:120`, `:131` | Inhabited source specialization and later-ratio containment. |
| `sourceProbeMassRatio_commonTail`, `sourceProbeMassRatio_twoTime` | `BF4ExactSlabFixedSpatialTransferBracketNesting.lean:155`, `:170` | Paired geometric bounds on the same normalized observable. |
| `geometricCutoff`, `geometric_bound` (existing) | `PositiveContractionResidual.lean:119`, `:126` | Constructive geometric threshold including q=0. |
| `boundaryTimeModulus`, `boundaryTime_budget` | `BF4ExactSlabFixedSpatialBoundaryTimeLimit.lean:35`, `:39` | Explicit time threshold and its rational bound. |
| `boundaryTimeCauchy`, `boundaryTimeLimit`, `boundaryTime_converges` | `BF4ExactSlabFixedSpatialBoundaryTimeLimit.lean:49`, `:63`, `:67` | Actual Cauchy witness, returned CReal and convergence. |
| `boundaryTime_approx_geometric`, `boundaryTime_bracket` | `BF4ExactSlabFixedSpatialBoundaryTimeLimit.lean:75`, `:91` | Geometric representative error and retained brackets. |
| `originalTimeScalar`, `originalTimeScalar_pin` | `BF4ExactSlabFixedSpatialOriginalTimeLimit.lean:40`, `:49` | Existing original action on an admissible explicit box schedule. |
| `originalTimeCauchy`, `originalTimeCauchy_modulus` | `BF4ExactSlabFixedSpatialOriginalTimeLimit.lean:64`, `:85` | Same original stream and unchanged cutoff-independent time modulus. |
| `originalTime_converges` | `BF4ExactSlabFixedSpatialOriginalTimeLimit.lean:94` | Convergence to the SAME boundaryTimeLimit, not a newly supplied scalar. |

## Parameter scope and residue

- q and the time modulus depend on nome and width, not on late K.
- probeCap depends on the fixed signed probe coefficients/spins/factor list.
- The ratio, brackets and returned limit still depend on K. A uniform time
  modulus is not yet a theorem interchanging cutoff and time limits.
- This is one-sided boundary convergence, not stationarity, a bulk vacuum,
  connected-correlation decay, or a physical reflected OS construction.
- General terminal-boundary comparisons, the actual completed cutoff-limit
  operator's power/moment compatibility, uniform width/spacing estimates,
  continuum QFT and the all-group physical gap remain open.

## Next causal proof, not yet checked

Let R(k,n)=originalTimeScalar at cutoff stage k and time n. The new time
modulus A is independent of k. The existing
`BF4ExactSlabAllNomeFaceSetExpectation.finiteCauchy`
(`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:65`)
supplies a cutoff modulus C_n for each fixed-time row at extent=width+n.

For delta=epsilon/4, put a=A(delta), b=C_a(delta). The comparison
R(k,n) -> R(k,a) -> R(j,a) -> R(j,m) would give a rectangular Cauchy bound
when n,m>=a and k,j>=b. The diagonal would have modulus max(a,b).
This argument avoids requiring cutoff convergence uniform in all time
lengths. A fixed probe's extent recoding is already pinned; genuinely
changing or cutoff-dependent insertions are not covered. Joint and iterated
limit theorems remain to be implemented and kernel-checked.

## Verification boundary

Three focused serialized checks passed, one worker with a 20 GiB ceiling.
All 19 public axiom outputs contain only `{propext, Quot.sound}`. Every
check had a fresh process/swap preflight; no competing compiler/test process
was found and recorded swap stayed at 7085.19 MiB. Root/full-tree/full axiom
audit was not run. Three selective-root imports were added, not root-checked.
No old declaration, frontier field, literal hole, new axiom or analytic premise
changed. Independent read-only source review found no mathematical defect.

The first nesting check exposed a dependent index rewrite mismatch; ordinary
scalar endpoint induction removed it. The original scalar Cauchy consumer
initially exceeded the default elaboration heartbeat budget by unfolding
large action expressions. Local irreducibility of the two already-pinned
scalar definitions fixed that without raising its heartbeat or memory limits.
The final logs below supersede those failed attempts; no failed gate is
presented as a completed proof.

Each command used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| BF4ExactSlabFixedSpatialTransferBracketNesting | 7 | `719d76a89af1a5eaebcb283584e5cf9bf745ff4ae1bf889f71402f9b64d21ea2` |
| BF4ExactSlabFixedSpatialBoundaryTimeLimit | 7 | `e252b0131587c6b5c9b56769630f2d191c321e2a74304a13619b10cdac95acb7` |
| BF4ExactSlabFixedSpatialOriginalTimeLimit | 5 | `07e1e2bd20bac3e59bc1c5c95b97ab6bad8582cb6449700c8cb14c3f50ec7217` |
