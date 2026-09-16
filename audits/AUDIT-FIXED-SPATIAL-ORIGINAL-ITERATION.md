# Original finite-chain moments and the actual weighted-step iterate

Date: 2026-09-16. Classification: PROGRESS after `0aff852`.

Whole-project goal: constructively build nontrivial continuum Yang--Mills
on R^4 with the required QFT axioms and a positive physical Hamiltonian
gap for each compact simple gauge group, all on the SAME theory. This
increment closes a finite original-action identification, not that goal.

## Mathematical contraction

Let N be the width-only boxed spatial carrier. The previously constructed
original kinetic and spatial polynomials define

    (T f)(y) = integral_x K(x,y) V(x) f(x) dH(x).

For a chain of n temporal layers, the newly proved identity is

    H_ambient[original endpoint probes * original selected-chain action]
      = H_N[(T^n f) V g].

Here f and g are the explicitly constructed source versions of the original
signed spatial-face probes. Equality is rational setoid equality. Every
finite spin coefficient, sign and repeated factor is retained. The spatial
weights occur once on each of the n+1 slices, including both endpoints.
For n=0 the endpoints coincide and the result is H_N[f V g], with ONE V.

The proof has three substantive parts, not an assumed equality:

1. An injective chronological concatenation embeds (n+1) copies of the same
   boxed source slice in the original ambient coordinates, retaining fringe
   links and exact head/tail/adjacent-pair/final coordinate order.
2. The existing ordered quaternion plaquette pin places the actual signed
   endpoint probes. An induction places the entire compact K/V chain and
   its final insertion into the original ambient action factors.
3. The original action and probes undergo ONE common Haar-preserving temporal
   sweep. Coefficient-sensitive placement permits action insertions; supported
   injective Haar placement and the already checked finite-chain composition
   then give the scalar identity.

## Declaration evidence

Paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `chainLinks` | `BF4ExactSlabFixedSpatialChainCarrier.lean:35` | Computed chronological spatial-link list. |
| `chainLinks_mem_iff` | `BF4ExactSlabFixedSpatialChainCarrier.lean:40` | Inclusive time range and complete boxed spatial membership. |
| `chainLinks_length` | `BF4ExactSlabFixedSpatialChainCarrier.lean:67` | Exactly (n+1)N positions. |
| `chainLinks_nodup` | `BF4ExactSlabFixedSpatialChainCarrier.lean:79` | No repeated coordinate. |
| `embedding` | `BF4ExactSlabFixedSpatialChainCarrier.lean:103` | Actual injection into the original slab. |
| `head_block` | `BF4ExactSlabFixedSpatialChainCarrier.lean:152` | Initial slice agrees with the established single-slice placement. |
| `tail_block` | `BF4ExactSlabFixedSpatialChainCarrier.lean:168` | Removing N positions leaves the time-shifted tail chain. |
| `pair_block` | `BF4ExactSlabFixedSpatialChainCarrier.lean:184` | Initial pair agrees with the established ordered pair. |
| `final_block` | `BF4ExactSlabFixedSpatialChainCarrier.lean:202` | Last N positions give the original final slice. |
| `sourceProbe` / `placeProbes` | `BF4ExactSlabFixedSpatialProbe.lean:52` / `:56` | Actual source expression and face-only time placement. |
| `placeProbes_physical` / `placeProbes_spatial` | `BF4ExactSlabFixedSpatialProbe.lean:67` / `:76` | Physical and spatial conditions for the common original sweep. |
| `sourceProbe_pin` | `BF4ExactSlabFixedSpatialProbe.lean:144` | Signed endpoint polynomial identity under zero padding. |
| `sourceProbe_supported` | `BF4ExactSlabFixedSpatialProbe.lean:189` | N-block support, for all finite probe syntax. |
| `head_polynomial_pin` | `BF4ExactSlabFixedSpatialOriginalIteration.lean:65` | Literal supported head-polynomial placement. |
| `pair_polynomial_pin` | `BF4ExactSlabFixedSpatialOriginalIteration.lean:77` | Literal supported kinetic-pair placement. |
| `tail_polynomial_pin` | `BF4ExactSlabFixedSpatialOriginalIteration.lean:89` | Literal supported lift/tail placement. |
| `chain_pin` | `BF4ExactSlabFixedSpatialOriginalIteration.lean:110` | Whole original action/terminal coefficient pin. |
| `ambientChain_supported` | `BF4ExactSlabFixedSpatialOriginalIteration.lean:137` | Original ambient support for Haar comparison. |
| `swept_chain_iteration` | `BF4ExactSlabFixedSpatialOriginalIteration.lean:147` | Full swept-action equality with any supported source endpoints. |
| `original_chain_iteration` | `BF4ExactSlabFixedSpatialOriginalIteration.lean:182` | Actual original signed spatial-face endpoint moments equal the iterate. |

## Scope, causal consumer and remaining gap

- Guards are width<=extent and start+n<=extent. Nome w is any rational and
  the heat cutoff is arbitrary. No positivity or numerical rate is used.
- The action is precisely `chainIds`, as defined by
  `BF4ExactSlabFixedSpatialChainGeometry.lean:29`. It is NOT a marginal of
  a larger action with surrounding interactions omitted.
- The original theorem requires every source face to belong to
  `spatialFaces width`. Unconditional syntax support alone is not a physical
  face pin. Arbitrary supported source polynomials appear only in the SWEPT
  identity, not as newly declared original gauge-invariant observables.
- Intermediate messages are not subjected to new sweeps or identified with
  fixed original observables. The final equality preserves the whole scalar
  original pairing; unweighted endpoint Haar equality would not suffice.
- The immediate next analytic consumer is
  `BF4ExactSlabAllNomeFaceSetExpectation.lean:65`, `finiteCauchy`, and `:78`,
  `finite_converges`. Apply the original identity both to the probes and to
  the empty/empty partition. For fixed window and probes, this can transfer
  the existing cutoff limit to the WHOLE normalized scalar iterate. That
  consequence is not asserted as proved in this checkpoint. It would not
  imply convergence of the cutoff-dependent messages or operators.
- Stationary normalization, completed OS transfer/vacuum realization,
  quantitative original-Haar contraction or signed-response control,
  uniform volume/spacing passage, continuum QFT/nontriviality and the
  all-group physical Hamiltonian gap remain open. No canonical frontier
  field, literal hole, old statement or analytic premise was changed.

## Verification

Three new modules passed focused serialized one-worker/20 GiB checks via
`scripts/safe_lean_build.py`. All 27 public axiom gates lie within
{propext, Quot.sound}. The initial capstone check needed one explicit type
annotation for reflexivity; the corrected file passed. Two minor linter
warnings in the parallel files were removed and those files rechecked.
Process and swap preflights preceded every check; limits were not raised.

Parallel branches constructed the carrier and probes; a separate source
review checked the n=0 case, endpoint supports and action/weight accounting,
and identified the existing scalar cutoff-limit consumer. No extra analytic
assumption was introduced by that review. Three root imports were added.
Root/full-tree verification and the full axiom audit were NOT run. CI remains
manual-only. Local final log hashes:

| Log in `/tmp/` | SHA-256 |
|---|---|
| `BF4ExactSlabFixedSpatialChainCarrier.log` | `9aa3d301dc5f6a831fc0b47b9b1fe1c2924d2b0ab29a8ae11acf37fd7b4286d0` |
| `BF4ExactSlabFixedSpatialProbe.log` | `33328e23d209a0e4593ff775cce3286e82ae5e65738b51ee58e344aab2faa5e6` |
| `BF4ExactSlabFixedSpatialOriginalIteration.log` | `d3b8260108003a1321784a6e6c18038bdcbbeeb396715887ce4e1af630cbd279` |

## Original scalar cutoff-limit follow-up

Date: 2026-09-16. Classification: PROGRESS after `67e0a60`.
This follow-up discharges the immediate scalar consumer left open above.

`BF4ExactSlabFixedSpatialIterationLimit.lean` proves, for every rational
0<w<1 and fixed geometry/endpoint factors, that the ACTUAL normalized
compact scalar iterate converges to the existing original selected-face
expectation. The numerator and empty/empty partition are independently
pinned by the original-chain identity. The previously constructed
positive-tail reciprocal cancels this SAME compact partition, not a
layerwise normalization or a surrogate denominator.

| Declaration | Module:line (under `lean/YMGap/Continuum/`) | Content |
|---|---|---|
| `endpointInsertion` | `BF4ExactSlabFixedSpatialIterationLimit.lean:54` | Fixed original polynomial while heat cutoff varies. |
| `compactNumerator` / `compactPartition` | `BF4ExactSlabFixedSpatialIterationLimit.lean:58` / `:65` | Actual iterate pairing and empty/empty scalar partition. |
| `compactNumerator_pin` | `BF4ExactSlabFixedSpatialIterationLimit.lean:73` | Same original numerator. |
| `compactPartition_pin` | `BF4ExactSlabFixedSpatialIterationLimit.lean:84` | Same original partition. |
| `compactPartition_floor` | `BF4ExactSlabFixedSpatialIterationLimit.lean:98` | Existing nome/face-count-dependent late-cutoff floor. |
| `compactPartition_reciprocal` | `BF4ExactSlabFixedSpatialIterationLimit.lean:108` | Original reciprocal cancels the actual compact partition. |
| `normalizedScalar` / `normalizedScalar_pin` | `BF4ExactSlabFixedSpatialIterationLimit.lean:122` / `:129` | Actual normalized iterate at headCutoff(w)+stage and exact original-stream pin. |
| `normalizedCauchy` / `normalizedCauchy_modulus` | `BF4ExactSlabFixedSpatialIterationLimit.lean:143` / `:166` | Explicit data; exactly the existing finiteCauchy modulus. |
| `normalized_converges` | `BF4ExactSlabFixedSpatialIterationLimit.lean:177` | Convergence to the pre-existing original expectation. |
| `normalizedLimit_pin` | `BF4ExactSlabFixedSpatialIterationLimit.lean:199` | The completed scalar stream is that SAME CReal. |

The action, geometry guards and probe class are unchanged. The original
endpoint insertion is fixed; only the heat cutoff varies. Intermediate
messages may vary with that cutoff, but their convergence is neither
assumed nor proved. The scalar identity lets the existing fixed-insertion
theorem apply directly to the original observable. This is a contraction
of the proof route, not a new assumption about moving observables.

No long-time limit, stationary normalization/vacuum, T1=1, completed OS
operator, norm contraction, or rate uniform in width/chain length/nome/
spacing is asserted. `partitionFloor`, in
`BF4ExactSlabAllNomeFaceSetReciprocal.lean:39`, is headFloor(w)^faceCount.
Its positivity is not a useful volume-uniform or physical mass-gap estimate.
The next obstruction is quantitative ORIGINAL-Haar boundary forgetting
or signed-response control and the stationary time/OS construction; the
finite-state refresh theorem is not automatically applicable to Haar.
All continuum/QFT/all-group obligations remain open.

The new module developed in parallel with the preceding increment's review
and integration. The parent inspected its source and fixed one missing
namespace and one sequence-type annotation. Its focused serialized
one-worker/20 GiB check passed; all 13 public gates are within
{propext, Quot.sound}, with no final warnings. One root import added;
root/full-tree and full axiom audit NOT run. No old field, hole, axiom or
analytic premise changed. Local final log:

An independent read-only review confirmed the same partition and cutoff,
fixed original insertion, literal inherited stage-index modulus, and n=0
numerator H[fVg]/denominator H[V]. It found no normalization or moving-
observable limit mismatch. The actual cutoff is headCutoff(w)+stage.

`/tmp/BF4ExactSlabFixedSpatialIterationLimit.log`, SHA-256
`7225ea91a54f2b509ebceaca77e515770996b8a2a388e7b9ade89f83179557b0`.
