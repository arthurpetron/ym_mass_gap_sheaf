# Original two-sided interior time limit

Date: 2026-09-16. Classification: PROGRESS after `4d820b3`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 with the
required QFT axioms and a positive physical Hamiltonian gap for every
compact simple group, for the SAME theory, within the constructive axiom
gate. This increment is a fixed-width SU(2) interior scalar time limit.

## The mathematical argument

Let u_m=T^m1, ell(h)=H[V*h], and

    B(m,n) = ell((u_m*p)*u_n) / ell(u_m*u_n).

The existing original transfer floor proves every denominator positive.
For the actual signed source probe p, let C=probeCap(fs). Multiply its
certified interval [-C,C] by the certified u_m. This initializes the
relative bracket on (u_m*p,u_m), preserving all shared coordinates.
Weighted symmetry and reciprocal congruence identify the n-step normalized
mass ratio with B(m,n). This is NOT the earlier evolved endpoint ratio.

The existing bracket iteration gives width q^n(C+C); its nesting puts any
two later right boundaries in one common interval. This interval may depend
on m and cutoff K, but its width does not depend on m or late K. Polynomial
commutativity gives B(m,n)=B(n,m). For m,n,i,j>=s, the two comparisons

    B(m,n) -> B(m,j) -> B(i,j)

therefore cost q^s(C+C) each. Both order inequalities have total error
q^s((C+C)+(C+C))=4Cq^s. No strict positivity of q, power monotonicity or
uniform lower bound on all growing partition functions is used. Zero rate,
zero cap and zero boundary lengths are retained by the underlying proofs.

The existing geometricCutoff(q,4C,epsilon) supplies an explicit modulus
for the diagonal B(t,t). middleTimeLimit returns its CReal. Its k-th
representative is B(d_k,d_k), with d_k=QMhat(k)>=k; the same common-tail
bound compares arbitrary B(m,n) to this representative whenever m,n,k>=s.
The result thus controls a rectangle, not only a selected diagonal.

## Original observable and normalization

The m-th complete source slice in the chronological chain is proved to
have the original embedding at start+m. This exact coordinate equality
induces polynomial placement; the existing common-sweep action identity
retains the same signed physical face probe and every selected action
factor. The required guards are width<=extent, start+(m+n)<=extent and
membership of every probe face in spatialFaces(width).

The resulting numerator is the existing original numerator. The product
denominator ell(u_m*u_n) is the same compact partition by terminalPair_total;
the pre-existing original reciprocal cancels it. Consequently
middleRatio_originalFiniteValue identifies the actual normalized ratios,
not merely proportional unnormalized forms. The middle spatial V occurs once.

originalMiddleScalar uses extent=width+(m+n), chain start=0, insertion time=m
and cutoff K=headCutoff(w)+stage. Both geometry inequalities are proved.
Its actual boundary distances relative to the probe are m and n. This is
a recentered fixed-source observable: its absolute time coordinate changes.
It is NOT already a fixed-absolute-coordinate stationary cylinder law.
The original scalar's Cauchy witness, convergence and rectangular estimate
use the SAME constructed middleTimeLimit, without another chosen limit.

## Declaration evidence

All module paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `massRatio_congr`, `middleRatio_iterate`, `middleRatio_swap` | `BF4ExactSlabFixedSpatialMiddleRatioPins.lean:53`, `:76`, `:100` | Exact same-denominator normalized pins and message exchange. |
| `intervalTimesMessage`, `middleBracket` | `BF4ExactSlabFixedSpatialMiddleBracket.lean:56`, `:71` | Certified initial and iterated brackets retaining u_m. |
| `middleBracket_width`, `middleRatio_bounds`, `middleBracket_nested` | `BF4ExactSlabFixedSpatialMiddleBracket.lean:87`, `:104`, `:121` | Exact 2Cq^n width, actual interior scalar and nesting. |
| `middleRatio_right_commonTail`, `middleRatio_commonTail` | `BF4ExactSlabFixedSpatialMiddleBracket.lean:158`, `:183` | One-side comparison and independent four-length 4Cq^s estimate. |
| `middleTimeModulus`, `middleTime_budget`, `middleTimeCauchy` | `BF4ExactSlabFixedSpatialMiddleTimeLimit.lean:38`, `:43`, `:55` | Explicit cutoff-independent modulus and Type-level Cauchy witness. |
| `middleTimeLimit`, `middleTime_converges`, `middleTime_approx_rectangular` | `BF4ExactSlabFixedSpatialMiddleTimeLimit.lean:75`, `:79`, `:88` | Constructed CReal, diagonal convergence and full rectangular control. |
| `middle_block`, `middle_polynomial_pin` | `BF4ExactSlabFixedSpatialOriginalMiddle.lean:72`, `:99` | Exact original middle-slice placement. |
| `swept_middle_pairing`, `original_middle_pairing`, `middleNumerator_pin` | `BF4ExactSlabFixedSpatialOriginalMiddle.lean:113`, `:157`, `:183` | Same chronological action and original numerator. |
| `middleRatio_originalFiniteValue` | `BF4ExactSlabFixedSpatialOriginalMiddle.lean:205` | Same original reciprocal partition and normalized expectation. |
| `originalMiddleScalar`, `originalMiddleScalar_pin` | `BF4ExactSlabFixedSpatialOriginalMiddleTime.lean:40`, `:48` | Literal growing-box original scalar and exact ratio pin. |
| `originalMiddleCauchy`, `originalMiddleCauchy_modulus` | `BF4ExactSlabFixedSpatialOriginalMiddleTime.lean:64`, `:82` | Actual original diagonal Cauchy datum with unchanged explicit modulus. |
| `originalMiddle_converges`, `originalMiddle_approx_rectangular` | `BF4ExactSlabFixedSpatialOriginalMiddleTime.lean:91`, `:106` | Original scalar reaches the SAME limit, including arbitrary late rectangles. |

## Remaining obligations and next consumer

Nome, spatial width, source probe and retained cutoff remain fixed. The
time modulus is independent of late K, but the returned limit still depends
on K. The rate depends on nome and width. No uniform spatial-volume or
lattice-spacing estimate has been proved. Increasing the ambient encoding
extent is not taking the entire ambient-box action to infinite volume.

The source-probe list interface is not an addition-closed observable
algebra. These scalar limits have not yet been assembled into a normalized
positive linear functional, let alone a consistent stationary cylinder law.
The next functional argument needs computed interval certificates for
arbitrary supported slice polynomials, the generic version of this bracket
proof, and same-denominator finite addition/scaling/positivity laws passed
to the limit. Existing interval/square-bound constructors are ingredients,
not an already constructed all-polynomial compiler or limiting state.

Joint interior cutoff passage needs its own original fixed-window cutoff
comparison; the previous one-sided joint-limit theorem does not apply by
renaming its insertion. Multi-insertion/time-shift consistency, connected
correlations, physical reflected OS/vacuum realization, completed cutoff-
limit power/moment compatibility, uniform width/spacing control, continuum
QFT and the all-group physical gap remain open. No frontier field was changed.

## Verification boundary

Five focused serialized one-worker/20 GiB checks passed all 30 public axiom
gates within {propext, Quot.sound}. Fresh process/swap preflight preceded
every check; no competing compiler/test process was found and recorded
swap stayed at 7085.19 MiB. Initial checks exposed missing namespace opens
and dependent arithmetic in the geometric embedding projection; the latter
was resolved by its plain image/list-lookup equality. No resource limit was
raised. Only final successful logs are claimed below.

Independent read-only review checked the two-hop estimate and the actual
recentered original schedule. Five selective-root imports were added;
root/full-tree/full axiom audit was NOT run. No old theorem, frontier field,
literal hole, axiom or analytic premise changed.

Each check used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| BF4ExactSlabFixedSpatialMiddleRatioPins | 3 | `d45adcb62522fa8cf521ca9157144880f42ecb98c33e8ac66da59ec36b63266a` |
| BF4ExactSlabFixedSpatialMiddleBracket | 8 | `c0c6c4a2afb872a277751ca4ebc2c9d1a8b6ddac96b0ceee1fd2caf0b8358977` |
| BF4ExactSlabFixedSpatialMiddleTimeLimit | 7 | `0a8f065074016725e27e017930df2200efbeba28178904e8daf41aaea611794e` |
| BF4ExactSlabFixedSpatialOriginalMiddle | 6 | `5ca1df13b2e9a7c642612fa090981c04d90ce66d65b5a05e0018004fba198687` |
| BF4ExactSlabFixedSpatialOriginalMiddleTime | 6 | `ed42cf131488c59be7fb530ba4c7ccba15108f89deeec52c9af45948dfe4aec6` |
