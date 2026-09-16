# All-nome original OS tests and the next analytic dependency

Date: 2026-09-15 (local). Parent checkpoint: `f435b72`.

## Whole-project goal

Construct the nontrivial continuum Yang--Mills theory and positive physical
mass gap required by Clay for every compact simple gauge group, with the
repository's constructive witnesses, explicit moduli and axiom gate. The
action, observables, OS reconstruction, time and Hamiltonian must belong to
the SAME theory. This checkpoint removes finite-volume small-nome guards;
it does not prove the continuum target.

## Route contraction: gluing is not the next required compiler

Centered even-slab full-action splitting already exists as `fullHeat_split`,
`lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean:142`, and its mixed
conditional pairing as `fullAction_pair`,
`lean/YMGap/Continuum/BF4ExactSlabSiteMixedSquare.lean:160`. Every action
factor remains; the shared fixed-slice weight occurs once. Neither is a
general adjacent-region physical-time composition theorem.

More importantly, `covariance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabTwoProbeCovariance.lean:153`, already
consumes the original connected determinant bound relative to the SAME
partition square for every 0<w<1. It needs no boundary-kernel composition
or original-state realization of a boundary marginal. The prior boundary
audit's missing gluing declaration concerns one possible operator route,
not a necessary dependency of this correlation route.

The selected mathematical step is therefore the original OS-norm bound on
auxiliary tests. It has a direct existing consumer and does not impose an
unnecessary original-state preimage. The new theorem retains the old lower
locality, reflection-image and temporal-invariance requirements explicitly.

## New dual bound: same action, same norm, both partitions canceled

The full background is L*I*U, with complete original lower and upper heat
products and ALL crossing interface factors. It is not the smaller
bulk-probe spectator background. For K>=headCutoff(w), the new original
positive certificates apply to this full background. Existing retained-tree
Cauchy--Schwarz and pruning then give the raw amplitude estimate.

For the keep-all channel, `full_amplitude_original`,
`lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:148`,
identifies the amplitude with the original numerator of the fixed insertion
upper(e)*p. The changing heat dressing stays inside the finite estimate.
The original numerator limit and reciprocal then give

`testLimit(p,e)^2 <= (cap(theta(p))*cap(p)) * form(e,e)`.

No volume-dependent reciprocal ceiling remains in the coefficient.

| Declaration | Source | Proven content |
|---|---|---|
| `backgroundCertificate` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:59` | Full original L/I/U positive background at late cutoff, every rational 0<w<1. |
| `reference_partition_bound` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:68` | Retained energy bounded by cap product times original partition. |
| `amplitude_partition_bound` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:81` | Original OS diagonal controls the squared test amplitude, with the original partition retained. |
| `rawTestLimit_bound` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:108` | Eventual cutoff estimate passes to the SAME raw limits, threshold max(1,headCutoff(w)). |
| `testLimit_bound` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:164` | Displayed normalized bound, no hsmall/hdelta. |
| `unit_test_pin` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:183` | Original unit test evaluates to one on the unit. |
| `bulkScalar_limit_bound` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:190` | Concrete bulk test has coefficient one; all support/local/reflection/temporal pins supplied. |
| `bulkScalar_limit_null` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:220` | Annihilates nulls of the cutoff-REMOVED original form. |
| `bulkScalar_null_congr` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:226` | Independent of original null-equivalent expressions. |
| `bulkScalarQuotientTest` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:233` | Test on the EXISTING finite-volume original OS quotient, no representative choice. |
| `bulkScalarQuotientTest_embed` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean:237` | Exact original expectation on embedded expressions. |

The bound is a norm AT MOST one for the concrete bulk test, not equality.
Its nontriviality or separation of states is not asserted. Unit normalization
checks the larger family, not that particular test. Existing computational
data are reused: `testLimitCauchy`,
`lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:277`, and
`reciprocalModulus`,
`lean/YMGap/Continuum/BF4ExactSlabOriginalActionReciprocal.lean:79`.

## Independent original site positivity after cutoff removal

| Declaration | Source | Proven content |
|---|---|---|
| `fixedHeatCertificate` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeSiteReflection.lean:42` | All actual shared-slice heat factors, at K>=headCutoff(w). |
| `fullAction_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeSiteReflection.lean:50` | Full original even-slab site-reflected numerator is nonnegative. |
| `finite_site_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeSiteReflection.lean:71` | SAME normalized original action at cutoff headCutoff(w)+n. |
| `site_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeSiteReflection.lean:82` | Existing all-nome face-set expectation retains site positivity after cutoff removal. |

Only the original one-sided polynomial is fixed in this limit. The
cutoff-dependent conditional square is not treated as a fixed insertion.
This is finite-volume site positivity, not an all-nome thermodynamic time pin.

## Precise open analytic edge

`full_connectedNumerator_distance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabTwoProbeDistanceDecay.lean:79`, still
requires the small-nome, heat-remainder and entropy-rate guards. Its
normalized consequence `covariance_distance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabTwoProbeCovariance.lean:168`, inherits them.
The missing producer is a distance-decaying estimate for the ORIGINAL
connected numerator, preserving signed cancellations and its partition
square, with explicit usable nome/volume/physical-scale dependence.

The old full unit-reference remainder cannot simply be made small by
waiting for a later cutoff: `no_eventual_small_intervals`,
`lean/YMGap/Continuum/BF4ExactSlabHeatHaarGuardObstruction.lean:340`, rules
out that proposed family of bounds at w>=7/8. The threshold is
`nomeThreshold` in that module at line 175. This is a refutation of that
remainder estimate, not of an original Yang--Mills gap.

The existing thermodynamic `formSequence`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicReflectedForm.lean:34`, fixes
`nome`, defined as 1/1024 by
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCertificate.lean:32`.
Thus the new all-nome finite-volume results do not automatically extend the
constructed thermodynamic operator. Changing-nome compatibility, centered
spatial decay, physical time/spacing calibration, continuum QFT,
nontriviality and every compact simple gauge group remain open.

## Verification boundary

The site proof was drafted independently while the parent proved the dual
bound; two read-only source reviews challenged the gluing route and checked
the full-background/normalization semantics. Only the parent compiled.
Five focused safe launches, one worker and 20 GiB cap, included two
parameter/namespace corrections and the added unit check. Final 15 public
gates (11+4) depend only on {propext, Quot.sound}. No raised limits or
dependency rebuild; no old statement, frontier field, custom axiom or
literal hole changed. Own/direct artifacts are fresh.

Final log SHA-256 values:

- `/tmp/ym-all-nome-dressed-dual-test.log`:
  `5e9618b012f362a979039c21351235da53871de762909cfdc128523c56e8de1b`.
- `/tmp/ym-all-nome-site-reflection.log`:
  `12102a0b72189ee03e5bf656ea582ace7327b8ae97a79aa1bc1899d7a89aeced`.

Two semantic-root imports added; root/full-tree build and full audit not
run. CI remains manual-only. No canonical Clay-facing atom is declared
closed. Goal remains active.
