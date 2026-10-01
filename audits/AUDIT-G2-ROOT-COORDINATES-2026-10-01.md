# Finite G2 root coordinates and remaining group realization

Date: 2026-10-01 UTC. Finite groundwork: explicit G2 root coordinates,
pairings and simple reflections now have a kernel-checked certificate.
This is NOT a compact-group realization or closure of the every-group
Yang--Mills requirement.

## Explicit finite data

All new declarations are in
`lean/YMGap/RepTheory/G2RootCoordinateCertificate.lean`, namespace
`YMGap.RepTheory.G2RootCoordinates`.

| Declaration and line | Checked claim |
| --- | --- |
| `positiveRoots` :25, `signedRoots` :32 | Six positive and twelve signed integer coordinate pairs, alpha short and beta long. |
| `positiveRootCount_matches_code` :54, `positiveRoots_nodup` :59, `signedRoots_nodup` :62 | Counts match the existing G2 Cartan code; both lists are duplicate-free. |
| `positiveRoot_pairings` :65, `positiveRoot_squaredLengths` :72 | Explicit coroot-pairing and squared-length tables, with alpha^2=2, beta^2=6, alpha*beta=-3. |
| `shortReflection_closes_signedRoots` :81, `longReflection_closes_signedRoots` :85 | Kernel-reduced Bool certificates verify that both reflections preserve the finite list. |
| `shortReflection_involutive` :89, `longReflection_involutive` :96 | The reflections (-a+3b,b) and (a,a-b) are involutions on every integer coordinate pair. |
| `shortReflection_preservesLength` :106, `longReflection_preservesLength` :109 | Kernel-reduced Bool certificates verify length preservation on the signed list. |
| `cartanDeterminant_one` :113, `g2_centerCode_is_trivial` :118 | Closed determinant arithmetic and a separate pin to the preexisting trivial center CODE; no group property is inferred. |

## Actual consumers and missing construction

`CartanType.numPosRoots` in `lean/YMGap/RepTheory/CartanType.lean:92`
and `simplyConnectedCenter` in
`lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:93` consume classification
codes only. The certificate pins those existing codes, but does not supply
root-data provenance to an analytic group instance. A compatible typed
root-datum consumer was NOT FOUND in the targeted RepTheory/RG source review.

`ConstructiveGroup` in `lean/YMGap/RepTheory/ConstructiveGroup.lean:51`
specifies setoid group operations/laws, not compact topology or Haar data.
Actual group/root/weight/representation realization, invariant integration,
heat action, and the original physical Wilson/OS construction beyond SU(2)
remain open. The finite certificate does not instantiate those structures,
derive a compact-group center from a determinant, or close a canonical frontier
field. The chart is unchanged.

## Verification

Luna drafted this small finite task; main inspected it, replaced closed
determinant arithmetic by kernel `decide`, and ran the final focused check.
Sol independently reviewed the coordinate conventions and scope. Terminal
exit zero emitted the target olean. Thirteen gates passed: eleven empty;
the two global involution proofs use only {propext,Quot.sound}. No new sorry,
axiom, Classical dependency, native_decide, analytic premise or frontier
weakening. Main alone compiled with one monitored 20 GiB worker, unchanged
12 GiB reserve and dynamic telemetry. No broad build/audit/guard or raised
limit. Root import registration is not aggregate verification. The
documentation skill labels this as finite groundwork, not group realization.

Accepted log: `/tmp/ym-g2-root-coordinate-second-20261001.log`.
SHA-256: `527bc2e49b87c28f858521600c169952f9e6588deb899845defa46db8e4d42e8`.
