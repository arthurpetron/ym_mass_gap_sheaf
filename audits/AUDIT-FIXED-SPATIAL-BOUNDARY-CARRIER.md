# Exact fixed-width boundary realization

Date: 2026-09-16. Classification: PROGRESS after `48715db`.

Whole-project goal: constructive continuum quantum Yang--Mills on R^4,
the required QFT axioms and nontriviality, and a positive physical
Hamiltonian gap for each compact simple group, on the SAME theory.
This increment is exact finite SU(2) algebra, not completion of that goal.

## Mathematical result

The previous actual two-layer integral is
`G = integral_middle K01 * V1 * K12`. Its only remaining variables are
spatial links on the endpoint slices, with spatial coordinates <=width.
The finite spatial-base-cutoff action can have boundary-link coordinates
equal to width, so using strictly smaller coordinates would lose variables.

Compute a width-only list of all these links at times 0 and 2. Translate
that list to the actual start time and embed its indices in the original
ambient slab. Reading monomial exponents along this embedding gives a
polynomial on the width-only carrier. Re-embedding reconstructs G, and
the normalized product-Haar values agree. Signed coefficients, term order,
and repeated terms are retained. No positivity or division is used.

## Declaration evidence

Paths in this section have prefix `lean/YMGap/Continuum/`.

| Declaration | Source | Role |
|---|---|---|
| `SliceLink` | `BF4ExactSlabFixedSpatialTwoLayerBoundary.lean:50` | Spatial directions and inclusive width bounds on one slice. |
| `spatialHeat_local` | `BF4ExactSlabFixedSpatialTwoLayerBoundary.lean:112` | Actual original spatial heat uses only its boxed slice. |
| `kineticHeat_local` | `BF4ExactSlabFixedSpatialTwoLayerBoundary.lean:136` | Full finite relative-character heat uses consecutive spatial slices. |
| `middleIntegrand_local` | `BF4ExactSlabFixedSpatialTwoLayerBoundary.lean:154` | All remaining variables lie on the three named slices. |
| `gluedMiddle_local` | `BF4ExactSlabFixedSpatialTwoLayerBoundary.lean:169` | Actual middle schedule removes the entire middle slice. |
| `gluedMiddle_supported` | `BF4ExactSlabFixedSpatialTwoLayerBoundary.lean:194` | No out-of-ambient-carrier exponent tail. |
| `BlockEmbedding.compressExponents` | `SU2QuaternionHaarBlockCompression.lean:36` | Explicit source-coordinate reads. |
| `BlockEmbedding.compress` | `SU2QuaternionHaarBlockCompression.lean:90` | Computed restriction preserving signed coefficient list. |
| `BlockEmbedding.compress_supported` | `SU2QuaternionHaarBlockCompression.lean:93` | Source support. |
| `BlockEmbedding.polynomial_compress_prefix` | `SU2QuaternionHaarBlockCompression.lean:102` | Reconstruction from locality to the embedding image. |
| `BlockEmbedding.haar_compress` | `SU2QuaternionHaarBlockCompression.lean:118` | Supported original Haar transported exactly. |
| `baseLinks` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:79` | Enumeration depends only on width. |
| `baseLinks_mem_iff` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:82` | Enumeration contains precisely the endpoint box. |
| `boundaryLinks_mem_iff` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:101` | Its translated list has precisely the actual endpoint membership. |
| `embedding` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:136` | Constructed injective physical placement with room guards. |
| `embedding_mem_iff` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:148` | Image membership matches proved actual-kernel locality. |
| `kernel` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:173` | Compressed actual `gluedMiddle`, not a surrogate. |
| `kernel_supported` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:177` | Width-only carrier support. |
| `kernel_reconstructs` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:182` | Exact ambient prefix reconstruction. |
| `kernel_haar` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:187` | Bare-kernel original/compact Haar identity. |

## Scope and remaining consumer

1. `embedding` requires width<=extent and start+2<=extent. The spatial
   guard is stronger than the previous window-completeness width<=extent+1:
   this box overcarrier includes unused fringe/corner coordinates, which
   must also be physical. No previous theorem or frontier field was changed.
2. Only the carrier size is independent of extent/start/cutoff. `kernel`
   retains these parameters; equality of its coefficients across placements
   is not proved by this increment.
3. This is a two-endpoint carrier. A single-slice factor pin and repeated
   original weighted composition still need proof. The source review's
   proposed algebra is `T f(x) = integral K(x,y)*V(y)*f(y) dH(y)`, so each
   joining V occurs once. This formula is a proposed next consumer, not a
   new declaration or a proved stationary physical transfer.
4. The existing `original_twoLayer_gluing`
   (`BF4ExactSlabFixedSpatialTwoLayerGluing.lean:188`) allows endpoint probes
   outside the width box. `kernel_haar` does not automatically compress their
   whole weighted pairing. Prove probe locality, enlarge the carrier, or
   explicitly integrate the complementary spectator coordinates first.
5. Finite iteration does not itself require a stationary vacuum. Positivity,
   stationary normalization, original OS identification, useful quantitative
   Haar/covariance estimates, cutoff-dependent insertion control, continuum
   QFT and physical/all-group mass-gap claims remain separate open work.

## Parallel work and independent review

One agent located and implemented the missing exact inverse to the existing
block embedding. The principal agent proved actual-kernel locality and
constructed its geometric placement. A separate read-only agent checked
both the future iteration consumer and the resulting three modules. It
found no mathematical bug and identified the scope boundaries above.
Only the principal agent compiled, serially.

A further reviewer screened the current arXiv math-ph listing at the user's
request. The principal agent rechecked primary passages. The independent
research result is `RESEARCH-MATH-PH-2026-09-16.md`; no cited paper enters
the new Lean theorem assumptions.

## Verification

Each new module passed a focused `scripts/safe_lean_build.py` check with
`--jobs 1 --check-worker-limit-gib 20` and its own `.olean` output. Fresh
process/swap preflights preceded each launch. All 30 public axiom gates
report only subsets of {propext, Quot.sound}. No holes, new axioms, classical
proof dependency, or named analytic assumptions were added.

The boundary and carrier checks initially exposed missing namespace opens,
projection simplification and elaboration issues; these were corrected
before acceptance. Compression passed its first focused check. One scoped
kinetic-locality budget is 1,000,000 heartbeats; worker and memory limits
were unchanged. Three root imports were added, but the root/full tree and
full axiom audit were NOT run. CI remains manual-only.

Terminal log SHA-256:

| Log in `/tmp/` | SHA-256 |
|---|---|
| `BF4ExactSlabFixedSpatialTwoLayerBoundary.log` | `2171bf53acdb973b9944fdef370601b3522dd5e37b9c40576cf520753d7cf911` |
| `SU2QuaternionHaarBlockCompression.log` | `3d85fd843abcd23e3d50958284934964d1bd5f22a47e41404c14865480c10574` |
| `BF4ExactSlabFixedSpatialBoundaryCarrier.log` | `130dc876128f3c73192a4543d14fad37b618763e3ae6889962070d1332ae9c6d` |
