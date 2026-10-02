# Quaternion vector heat alignment obstruction

## Result and consequence

The scalar one-link heat alignment cannot be extended to arbitrary supported
quaternion-vector sources and then iterated through a word. An explicit source
violates that proposed vector inequality for EVERY cutoff K>=2 at nome 1/2.
This eliminates that induction step, not the scalar-source whole-word claim,
the existing scalar theorem, or an original interacting Yang--Mills estimate.

## Actual source and operator

For x=(a,b,c,d), `source`
(`lean/YMGap/Continuum/SU2QuaternionVectorAlignmentObstruction.lean:48`)
is A=(0,b,-c,0). Its monomials are padded to four coordinates; padding does
not change their values. `source_supported` (same file, line 73) proves support
on the one-link carrier. `leftMultiply` (line 52) uses the ACTUAL ordered
`PolyQuaternion.mul`, giving

    x*A = (c^2-b^2, ab+cd, -ac+bd, -2bc).

`multiplied_supported` (line 86) retains the same carrier.
`componentPair` (line 59) integrates the original `heatAt 0 1 w K` against a
lower scalar component and its literal upper lift. `vectorPair` (line 64)
sums all four pairings. No abstract replacement operator is supplied.
The original packet identification is `heatAt_zero_one`
(`lean/YMGap/Continuum/SU2QuaternionRelativeHeatPairGeometry.lean:45`).

## Exact channel argument

Each nonzero component of A is a degree-one harmonic; all four components of
x*A are degree-two harmonics. Both sums of their Haar squares are 1/2.
The file checks homogeneity and coefficientwise harmonicity by finite kernel
reflection. It checks the required retained-substitution Haar pairings by
exact rational kernel computation, not an unsupported free-polynomial equality.
`heat_harmonic_reproduction`
(`lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicReproduction.lean:89`)
then supplies the actual packet multipliers.

For arbitrary nome w and EVERY K>=2, `source_heat` (new file, line 121)
proves vectorPair(A)=w^3/2. `multiplied_heat` (line 144) proves
vectorPair(x*A)=w^8/2. At w=1/2, `source_at_half` (line 167) gives 1/16
and `multiplied_at_half` (line 171) gives 1/512. The proposed comparison
requires at least w^3*vectorPair(A)=1/128. `alignment_defect` (line 176)
proves the exact signed slack is -3/512, and `vector_alignment_fails`
(line 184) proves the comparison is false. `no_vector_alignment` (line 195)
uses this supported witness to refute the universal vector statement.

This is not a short-cutoff artifact: K remains arbitrary above two, including
larger cutoffs required by other guards. The existing scalar declaration
`product_alignment_no_error`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatExactAlignment.lean:59`)
is NOT refuted. No claim about scalar sources multiplied by complete unit
words follows from this arbitrary-vector counterexample.

## Verification boundary

The final focused check on 2026-10-02 UTC exited 0 without warnings:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/SU2QuaternionVectorAlignmentObstruction.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/SU2QuaternionVectorAlignmentObstruction.olean --log-file /tmp/ym-vector-alignment-obstruction-20261002-third.log
```

All nine printed theorem gates are within {propext,Quot.sound}; none contains
sorryAx or a classical axiom. Independent Sol review of the FINAL source and
accepted log passed. Earlier failed checks are not proof evidence: the final
file corrects coordinate padding and uses the actual required Haar pairing
instead of a stronger raw monomial-list identity. No new axiom, sorry,
analytic premise, erased witness, resource-limit change or frontier weakening
was introduced.

| Artifact | SHA256 |
| --- | --- |
| Lean source | `968f6429467b215668f6646210df73ae1c08d43ec0534713722ba41b4a1169cc` |
| Accepted focused log | `05d98e52cfe1c0fdf0cb64256f2151b46e78a1db040ceb3f8a929ea5d4cfb64a` |

The check used one capped 20 GiB worker and a 12 GiB OS reserve; preflight
found no competing compiler/runner and zero swap. Memory reported 86 percent
free before and after. One root import is added; full-root/tree/audit/guard
checks were NOT run. CI and the canonical chart block are unchanged.

## Remaining mathematical frontier

The scalar-source whole-word inequality remains unproved. Its proof cannot
use the refuted arbitrary-vector induction. The live original-source consumer
is still `paddedSquare_energy_projection_bound`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareProjectionGain.lean:279`): control
COMPLETE signed debt minus the retained gain relative to OWN variance on a
justified changing family. Physical calibration, nontrivial continuum survival,
full same-theory QFT, every compact simple group and the Clay target remain OPEN.
