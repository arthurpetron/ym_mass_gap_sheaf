# Exact quadratic pencil for the ORIGINAL signed margin

## Mathematical result and actual consumer

Fix the original nome w, cutoff K, spatial width, terminal depth and positional
face list. Put J(p)=the existing collected original joint pairing, Z=J(1),
f_p=the actual fundamental face character and j_p=its COMPLETE temporal jump.
Let A_p=J(f_p), C_pq=J(f_p*f_q), D_pq=J(j_p*j_q). The proved identity is

```
Z^2 * originalMargin(b,c)
  = sum_p sum_q b_p*b_q * [c*(Z*C_pq-A_p*A_q)-(Z/2)*D_pq].
```

Equalities here denote the Q' setoid, not equality of stored fractions.
All sums are over the ORIGINAL list, including repeated positions and every
signed off-diagonal term. Both endpoint sources and the same positive
partition remain. The density is independent of b, not independent of the
nome, cutoff, width, depth or face list. Its raw basis moments are also
independent of c; the pencil entry is linear in c. No replacement measure,
conditional replica, bare eigenmode or Markov-generator identification occurs.

The cleared strict-slack test is acceptance-equivalent to the EXISTING original
finite reference checker. Its producer returns that checker's original
Certificate type, or none; it assumes no successful direction.

## Declarations

Namespace: `YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginPencil`.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `pairing_congr`, `pairing_add`, `pairing_smul` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginPencil.lean:75`, `:89`, `:102` | Original collected pairing preserves coefficient equality and signed linearity. |
| `quadratic` | same file, `:134` | Complete ordered positional quadratic form, no deduplication. |
| `basis`, `pencilEntry`, `pencil` | same file, `:255`, `:265`, `:273` | Actual character basis and coefficient-independent original pencil. |
| `pencil_contract` | same file, `:278` | Full quadratic form contracts to original raw moments and COMPLETE jump square. |
| `pencil_pin` | same file, `:349` | Exactly Z^2 times the existing normalized original margin. |
| `pencil_slack_iff` | same file, `:367` | Both directions of slack comparison after positive Z^2 cancellation. |
| `quadratic_repeated_signed` | same file, `:387` | Kernel-computed `[0,1,0]`, signed-coefficient regression; NOT a YM instance. |
| `pencilCheck`, `pencilCheck_correct`, `pencilCertify` | same file, `:407`, `:415`, `:434` | Original cutoff/depth/padding/slack, identical acceptance and original witness type. |

The original density and checker pins remain
`BF4ExactSlabFixedSpatialCollectedFamilyMargin.density`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCollectedFamilyMargin.lean:169`),
`pairing_pin` (same file, line 268), `finite_margin_pin` (line 316) and
`check_correct` (line 350). No definition or acceptance condition there changed.

## Verification boundary

One focused final check, EXIT 0:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginPencil.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginPencil.olean \
  --log-file /tmp/ym-original-margin-pencil-20261002-final.log
```

All printed gates are empty or within {propext,Quot.sound}, with no error,
warning, sorryAx or disallowed axiom. The signed/repeated regression and
generic quadratic evaluator are axiom-free. Earlier failing drafts are not
verification evidence. An independent full source/sign/consumer review: PASS.
Separate evidence review confirmed hashes, citations and unchanged chart
fences: PASS.
One compiler, the 20-GiB worker ceiling and 12-GiB OS reserve were retained;
pre/post system-free readings were 85%/86%, with zero post-check swap.

One semantic-root import was added. No full root/tree build, audit, guard,
progress-metric run, literature scan or heavy finite evaluation ran. No
frontier field, sorry, analytic premise, safety limit or CI setting changed.
The exact canonical chart is unchanged and was not reprinted.

| Artifact | SHA-256 |
| --- | --- |
| `BF4ExactSlabFixedSpatialFamilyMarginPencil.lean` | `039893a0375b8f9fa5eff8f3c8a482d3c4733ec684ea47fe2b22309ee595fb2e` |
| final log | `8c2b045f3e7bec22dc889599f3c088ccdbd4be71c2551368b96e8610e316eb80` |

## Remaining mathematical input

This enables exact direction testing using common original basis moments.
It does not memoize their computation, bound coefficient bits/intermediate
work/runtime, prove matrix coercivity or produce a useful accepted direction.
The next input remains useful positive ORIGINAL signed slack with its cutoff
allowance on a justified changing family. A single positive direction is one
upper-energy survival input, NOT an EVERY-state lower gap. Physical spacing,
nonzero continuum survival, full QFT, every group and the Clay endpoint remain
OPEN; no proximity claim follows from the reformulation.
