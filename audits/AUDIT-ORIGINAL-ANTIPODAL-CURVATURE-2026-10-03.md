# An actual antipodal sign in the original heat kernel

The continuum Yang--Mills/Clay target remains OPEN. This checked result
prunes pointwise positive curvature of every bare original heat factor,
not a complete interacting or averaged estimate.

## Mathematical result and original-object join

At w=5/8, with c(j)=j(j+2), define the ORIGINAL inclusive character sums

    H_K = sum_(j=0..K) (-1)^j (j+1)^2 w^c(j),
    B_K = sum_(j=0..K) (-1)^(j+1) (j+1)^2 c(j) w^c(j).

The EXISTING fourth-degree Casimir tail starting at five bounds each
absolute tail by 2^-10, for EVERY finite tail length. The concrete
five-term values have H_4>1/5 and B_4-6H_4>1/8. Combining the errors
costs 7*2^-10 and proves H_K>0 and B_K>6H_K for EVERY K>=4.

Exact original packet/character identities identify these sums with
`heatAt 0 1 w K` at lower identity and upper antipode. Both quaternion
blocks have checked unit norm. For the literal upper field D_(4,5),

    h=H_K, Dh=0, 3*D^2h=B_K.

Thus h>0 and D^2h>2h. The actual evaluated polynomial

    2*h^2+(Dh)^2-h*D^2h

is strictly negative at every K>=4. The explicit
K*=max(4,relativeCutoff(5/8,32)) pays BOTH existing relative-derivative
and head guards. No infinite series, source replacement, new positivity
hypothesis or pointwise interpretation of a Haar Certificate is used.

## Declaration anchors

- `lean/YMGap/Continuum/SU2HeatAntipodalPrefixBounds.lean:39`,
  `endpointValue`; :43, `endpointSecondThree`; :48, `witnessNome`;
  :150, `endpointValue_corridor`; :156, `endpointSecondThree_corridor`;
  :162, `endpointValue_positive`; :175, `endpointSecondThree_gt_six_value`.
- `lean/YMGap/Continuum/SU2QuaternionAntipodalHeatJets.lean:46`,
  `antipodalEnvironment`; :52, `upperAngular`; :55, `antipodalEnvironment_unit`;
  :298, `heatAt_antipodal_value`; :310, `heatAt_antipodal_first`;
  :326, `heatAt_antipodal_second_three`.
- `lean/YMGap/Continuum/SU2QuaternionAntipodalCurvatureObstruction.lean:54`,
  `clearedRicciTwo`; :58, `originalValue_positive`; :64, `originalSecond_gt_twice`;
  :105, `clearedRicciTwo_negative`; :124, `guardedCutoff`;
  :126, `guardedCutoff_relative`; :129, `guardedCutoff_head`;
  :133, `guarded_original_negative`; :138, `not_guarded_original_nonnegative`.
- Existing original objects:
  `lean/YMGap/Continuum/SU2QuaternionRelativeHeatPairGeometry.lean:41`, `heatAt`;
  `lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:103`, `logHessianNumerator`;
  `lean/YMGap/Continuum/BondMovingScaledNorm.lean:440`, `tail_modulus`.

## Forward/backward consequence and limits

Do not assert pointwise nonnegativity of this Ricci-two cleared expression
on EVERY original single-heat configuration: an explicit admissible one
refutes it. The algebraic convention is the unit-S^3 Ricci-two test; no
analytic Ricci/geometric identification or logarithmic-generator theorem
was constructed here.

This does NOT reinstate the withdrawn exclusion of all curvature methods
in `audits/AUDIT-CURVATURE-LOWER-BOUND-SCOPE-2026-09-27.md`. A negative
lower-bound coefficient alone still does not determine actual curvature.
The new proof establishes an actual evaluated sign, but only for the bare
factor, not complete interacting V*g_n or an averaged conditional source.

FORWARD NEXT remains cancellation-preserving signed energy/commutator
control against ell(b^2). BACKWARD NEXT remains an actual producer of
s*D<=C*Z1*ell(b^2), or the SAME macroscopic response ratio, on a justified
changing family. No relative bound, survival reserve, cross-scale comparison,
physical calibration, full SAME QFT or every-group construction is supplied.

## Accepted verification

Three serialized focused checks used the monitored launcher, one worker,
12 GiB reserve and 20 GiB hard worker limit. Every fresh preflight showed
86 percent free memory, zero swap and no competing build. The accepted
logs have fifteen DISTINCT permitted gates (4+4+7): fourteen use
{propext,Quot.sound}, one only {propext}. No final errors/warnings.
Development failure logs are NOT accepted evidence.

| Artifact | SHA-256 |
| --- | --- |
| `SU2HeatAntipodalPrefixBounds.lean` | `7f70c35928dfe23e0b576d485fa89e8e8adf8cf3ccb818e25caa4ff961773a57` |
| `SU2QuaternionAntipodalHeatJets.lean` | `9d68258a862bc97ee510389699a888964ff1a6f643f5e89ab5124ce4ae96cc23` |
| `SU2QuaternionAntipodalCurvatureObstruction.lean` | `02097e5cdd37a26b39437ac2bb56b98cfcd7446c8a97a243db1a5d289a3bc95f` |
| `/tmp/ym-antipodal-prefix-20261003-b.log` | `73c9eddda475adb585fbbdeb1e1dce86ee092db31bc055c56aa1dc0070209815` |
| `/tmp/ym-antipodal-jets-20261003-d.log` | `77cede030f112fdbedb86a57aa443226e6a7690ec22035e18c4cdf65c14d4f08` |
| `/tmp/ym-antipodal-curvature-20261003-b.log` | `0c4f42b916306dfab25e3aed2c0ff04d671aa8b4832b44abbadc8acd452f0372` |

Independent Sol mathematical/source review and Luna source/log/hash/chart
checks passed. Root imports registered ONLY; no aggregate/full build,
broad audit/guard, baseline regeneration or progress metric ran. CI stays
off. The canonical chart fence is unchanged (SHA-256
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`)
and was not reprinted: no exact displayed frontier claim closed.
