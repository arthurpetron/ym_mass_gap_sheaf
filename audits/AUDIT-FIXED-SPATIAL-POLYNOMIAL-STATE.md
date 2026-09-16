# Constructed positive rational-linear slice expectation

Date: 2026-09-16. Classification: PROGRESS after `53edc11`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 with the
required QFT axioms and a positive physical Hamiltonian gap for every
compact simple group, for the SAME theory, within the constructive axiom
gate. This increment constructs a fixed-width/cutoff SU(2) slice functional.

## Mathematical contraction

Each coordinate of a Haar-unit quaternion has square cap one. Products
retain that cap even with shared variables and arbitrary powers. The raw
monomial proof retains the actual exponent lists; trailing zero padding is
transported through equality under every Haar insertion. A coefficient c
therefore gives square cap c*c and interval cap c*c+1. Adding the literal
term list computes polynomialCap, independent of carrier size and degree
but dependent on the polynomial presentation. Empty polynomials/carriers,
repeated monomials, and zero or negative coefficients are included.

The previous two-boundary proof needs only support and an interval, so it
now applies to every supported polynomial p. For u_m=T^m1 and ell(h)=H[V*h],
the unchanged scalar is

    B_p(m,n) = ell((u_m*p)*u_n) / ell(u_m*u_n).

The actual positive denominator does not depend on p. Consequently finite
addition, signed rational scaling and normalization hold at identical m,n.
The generic two-hop argument gives the paired error 4*polynomialCap(p)*q^s
for four independently late lengths. Its computed geometric cutoff yields
polynomialCauchy and the returned expectation(p).

Different presentations and sums may have different caps and different
QMhat sampling indices. The limit laws therefore use uniqueness of limits
of the same raw rational sequences, NOT equality between those differently
sampled representatives. Coefficient equality and arbitrary-insertion
Haar-carrier equality both preserve the expectation. Finite certificate
positivity at every actual sampled index gives transitive leEv positivity;
the square certificate is constructed for every supported p. Agreement
with the earlier sourceProbe limit uses the identical raw sequence.

## Declaration evidence

All paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `coordinateSquareBound`, `monomialSquareBound` | `QuaternionHaarSupportedPolynomialInterval.lean:86`, `:217` | Actual supported coordinate/monomial square cap one. |
| `polynomialCap`, `polynomialCap_nonnegative`, `polynomialInterval` | `QuaternionHaarSupportedPolynomialInterval.lean:237`, `:241`, `:250` | Computed cap and constructive interval for every supported polynomial. |
| `intervalMiddle_commonTail`, `intervalMiddleModulus`, `intervalMiddleCauchy` | `BF4ExactSlabFixedSpatialPolynomialMiddleTime.lean:137`, `:155`, `:160` | Generic two-boundary control, explicit modulus and Cauchy data. |
| `intervalMiddleLimit`, `intervalMiddle_converges`, `intervalMiddle_approx_rectangular` | `BF4ExactSlabFixedSpatialPolynomialMiddleTime.lean:177`, `:182`, `:191` | Constructed generic limit and full late rectangle. |
| `middleRatio_congr`, `middleRatio_carrier_congr` | `BF4ExactSlabFixedSpatialMiddleFunctionalLaws.lean:52`, `:65` | Same-weight finite coefficient/carrier congruence. |
| `middleRatio_one`, `middleRatio_add`, `middleRatio_smul` | `BF4ExactSlabFixedSpatialMiddleFunctionalLaws.lean:77`, `:89`, `:110` | Same-denominator finite normalization and rational linearity. |
| `middleRatio_certificate_nonnegative`, `middleRatio_square_nonnegative` | `BF4ExactSlabFixedSpatialMiddleFunctionalLaws.lean:126`, `:139` | Actual positive finite expectation on certificates/squares. |
| `polynomialCauchy`, `polynomialCauchy_modulus`, `expectation`, `expectation_converges` | `BF4ExactSlabFixedSpatialPolynomialState.lean:59`, `:66`, `:73`, `:78` | Unconditional supported-polynomial construction and raw-sequence convergence. |
| `expectation_one`, `expectation_add`, `expectation_smul` | `BF4ExactSlabFixedSpatialPolynomialState.lean:89`, `:99`, `:112` | Constructed normalized rational-linear functional. |
| `expectation_congr`, `expectation_carrier_congr` | `BF4ExactSlabFixedSpatialPolynomialState.lean:123`, `:135` | Presentation and original carrier relations respected. |
| `expectation_certificate_nonnegative`, `expectation_square_nonnegative` | `BF4ExactSlabFixedSpatialPolynomialState.lean:148`, `:159` | Positivity in leEv from actual representatives. |
| `expectation_sourceProbe` | `BF4ExactSlabFixedSpatialPolynomialState.lean:168` | Same previously constructed probe limit. |

## Exact scope and next consumer

The time modulus is independent of late heat cutoff K. The expectation
still depends on K; q still depends on nome and spatial width. This is
neither a spacing-uniform physical gap nor a spatial thermodynamic limit.
Ordinary square positivity is not reflected OS positivity. Coordinate
polynomials are not automatically identified with gauge-invariant Wilson
observables. The previous physical source-probe pin retains its own face
and geometry guards.

The next mathematical consumer is a consistent positive multi-time cylinder
functional for the SAME selected-chain action. Source review identified
the following argument to prove; these are NOT new checked declarations.
For a window of L transitions and polynomial P on its L+1 slices, retain
the half-open action A_L=product_{j<L}(K_j*V_j). Integrate the first L slices
of u_m*P*A_L to obtain F_m, and u_m*A_L to obtain D_m=T^L u_m. The normalized
quantity is ell(F_m*u_n)/ell(D_m*u_n), with the final V occurring once.
Contracting the existing full `chain L 1` instead would retain an extra V;
it cannot be fed directly into this bracket without a new identity.

The existing `partialHaarHeads_certificate` in
`SU2QuaternionHaarCertificateIntegration.lean:91` and support-guarded
`certificate_extend` in `SU2QuaternionHaarCertificateExtension.lean:227`
are ingredients for certified C*D_m +/- F_m. A certificate-preserving
`liftBoundary` producer, exact all-window action pin and window-reversal
proof remain to be supplied. The existing bracket iteration then targets
one boundary comparison, with reversal supplying the other. F_m and D_m
change with m: neither is silently a fixed observable in the one-slice limit.

Finite left/right unit-padding identities must shift the corresponding
boundary length while retaining the action. The two shifted finite ratios
are generally unequal; stationarity is a limit conclusion, not an assumed
finite identity. Internal unit insertion must merge time gaps rather than
delete an action transition. No stationary cylinder measure, joint interior
cutoff limit, reflected OS/vacuum, connected-correlation bound, completed
cutoff-limit power/moment compatibility, uniform width/spacing passage,
continuum QFT or all-group Clay closure follows from this checkpoint alone.
No canonical frontier field or analytic premise was changed.

## Verification boundary

Four focused serialized one-worker/20 GiB checks passed all 30 public gates
within {propext, Quot.sound}; polynomialCap is axiom-free. Initial checks
found a field-notation error and an indirect Classical.choice dependency in
generic conditional simplification of an exponent-list lemma. Explicit Nat
cases removed the latter; final producer and consumer were both rechecked.
Only final successful, axiom-clean outputs are claimed here.

Fresh process/swap preflight preceded each check. No competing compiler or
test process was found; recorded swap stayed at 7085.19 MiB. No resource
limit was raised. The safe-build skill kept verification focused and
serialized. Independent read-only review checked the finite denominator,
different-modulus limit laws and actual square positivity. Four imports
were added to the selective root; root/full-tree/full axiom audit was NOT
run. No literal holes, new axioms, classical input or old field changes.

Each final check used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| QuaternionHaarSupportedPolynomialInterval | 5 | `86fc1fa01e262efce2f139c449f4bf688fc242b267313b02f8f49fc8069a3a47` |
| BF4ExactSlabFixedSpatialPolynomialMiddleTime | 6 | `a9267b7459d2043386650ed79b32896d8b71f31402f37854c7a59ee7ed9a0688` |
| BF4ExactSlabFixedSpatialMiddleFunctionalLaws | 7 | `6009b62390dd5c8ca64140bb1d6fd07ebe5e14e264939e264cef185aa306c506` |
| BF4ExactSlabFixedSpatialPolynomialState | 12 | `477b61bea379561fc4d0efb8822dd819caeacb777330c5b19bc17f475a165d75` |
