# Common cutoff control for the original two face margin

The original signed margin now has one constructed cutoff modulus for every
rational coefficient pair in a prescribed square |x|,|y|<=B. This removes
direction-dependent cutoff control inside that square. It does not produce
a positive original margin, a feasible moment evaluation, or a scaling rate.
The physical nome, spatial width, faces, depth and coefficient c remain fixed.

## Exact polarization and cutoff

Let m_k(x,y) be the EXISTING margin c*OWNVar-E for the original family [p,q],
with p!=q, strict spatial padding and the original cutoff headCutoff(w)+k.
`polarization` proves, in the rational setoid rather than structural equality,

```
m_k(x,y) = (x*x-x*y)*m_k(1,0)
         + (x*y)*m_k(1,1)
         + (y*y-x*y)*m_k(0,1).
```

All four profiles share the SAME joint density and partition at each cutoff.
The proof clears its positive Z^2 using the existing original pencil pin,
then cancels Z^2. The mixed anchor retains BOTH ordered cross entries; neither
endpoint mean nor any part of the signed temporal jump is discarded.

For B>=0 and |x|,|y|<=B, the absolute weights are bounded by 2*B^2, B^2 and
2*B^2. Set delta=epsilon/(1+5*B^2), and take the maximum of the THREE constructed
`referenceMarginCauchy.M(delta)` values at the same c and depth. Two-sided
anchor errors, including negative weights, give total error <=5*B^2*delta<=epsilon.
The positive denominator also handles B=0 without dividing by a variance or c.

`uniform_bound` asserts both inequalities for ALL late i,j and EVERY rational
direction in the square. Its modulus is Type-level data, independent of the
chosen x,y. It depends explicitly on w, width, faces, c, depth, B and epsilon;
no beta-, volume-, spacing- or depth-uniform estimate is claimed.

## Original completed consumer

If a SUPPLIED pivot is at least this common cutoff and its original margin
is at least 2*epsilon, `margin_floor` gives margin>=epsilon at EVERY cutoff
beyond the common cutoff, not merely beyond the pivot. With c>=0 and reference
depth s+1, `completed_ratio` directly invokes the EXISTING
`BF4WilsonAllNomeTerminalReferenceEnergyRatio.completed_reference_ratio`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`).
The completed centered ambient norm, one-step time loss and original propagated
coefficient c*(1+comparisonEta)^2 are unchanged.

The old per-direction `Certificate.check` guard is DIFFERENT. The new modulus
is not claimed to dominate that guard, and no old checker, certificate type
or frontier field was weakened. Useful finite positivity remains an input,
not a new assumed all-cutoff analytic estimate.

All new declarations are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoFaceMarginCutoff.lean`,
namespace `YMGap.Continuum.BF4ExactSlabFixedSpatialTwoFaceMarginCutoff`.

| Declaration | Line | Exact role |
| --- | --- | --- |
| `expression`, `expression_within`, `margin` | 99, 103, 108 | Original padded family and existing normalized margin. |
| `polarization` | 131 | Exact three-anchor identity after positive original Z^2 cancellation. |
| `weightCap`, `anchorTolerance`, `anchorTolerance_positive` | 159, 169, 172 | Explicit 5*B^2 error budget and positive rational tolerance. |
| `cutoff` | 249 | Computed maximum of three original QCauchy moduli. |
| `uniform_bound` | 257 | Two-sided cutoff error for every bounded signed direction. |
| `margin_floor` | 295 | Finite positive pivot gives all-late positive margin. |
| `completed_ratio` | 308 | Existing SAME-carrier consumer, with original coefficient and no old-checker claim. |

## Verification and remaining work

The accepted focused command exited zero:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoFaceMarginCutoff.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoFaceMarginCutoff.olean \
  --log-file /tmp/ym-two-face-margin-cutoff-20261002-second.log
```

All twelve public axiom gates are empty or within {propext,Quot.sound}; the
`weighted` and `weightCap` data definitions are axiom-free. The accepted log
contains no error, warning, sorryAx or disallowed axiom. The first draft check
failed on namespace/syntax issues; that log is not accepted evidence.
Independent Sol source review passed the normalization, signed error budget,
constructed maximum and original completed consumer. Independent Luna evidence
review passed the declaration lines, hashes, twelve axiom gates, documentation
scope and byte-identical chart block. Only the main agent
compiled, with the unchanged ONE 20-GiB worker and 12-GiB OS reserve.
Pressure-free memory was 85 percent before and 84 percent after the check;
the preflight found no competing compiler/test/runner and zero swap.

| Artifact | SHA-256 |
| --- | --- |
| source | `bbf718f99d9e2e64db55d5e31ee86870f5f1456fa85555dae6dab4758cd64b34` |
| accepted log | `05768cefad45685958a4a403216b7bf1fb6d96988869b4e4cf6bd25d1a85856b` |

One semantic-root import is registered, not aggregate-checked. No full
root/tree build, audit, guard, progress-metric run, new literature scan or
heavy original-moment evaluation ran. No sorry, axiom, analytic hypothesis,
frontier weakening, raised limit or CI change was introduced.

NEXT is actual useful signed original entries/slack, with cutoff allowance,
on a justified changing family. The new theorem makes one finite-plane error
budget available to searches; it neither normalizes an arbitrary search result
into the chosen square nor produces an accepted useful instance. Larger
families and repeated faces are not covered. An upper temporal-energy estimate
is not an EVERY-state lower gap. Nonzero continuum survival, physical mass,
full QFT, every compact simple group and the Clay endpoint remain OPEN.
No exact displayed chart claim changed; its chart blocks stay unchanged and
no ASCII chart is reprinted.
