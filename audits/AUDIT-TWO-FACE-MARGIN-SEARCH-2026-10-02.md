# Constructive direction search for the original two face margin

The new algorithm computes a positive rational direction when one exists in a
fixed original two-face margin plane, or proves that the entire rational plane
is nonpositive. It removes direction guessing in that plane, not the missing
original moment estimates or scaling trajectory. No useful accepted original
Yang--Mills instance was evaluated or produced.

## Mathematical classification

Write Q(x,y)=a*x^2+2*b*x*y+d*y^2 and det=a*d-b^2. All tests below are
decidable comparisons of the project's exact rational setoid, not classical
real-number decisions or structural fraction equality.

| Ordered case | Constructed result |
| --- | --- |
| a>0 | (1,0), with Q=a>0. |
| a<=0 and d>0 | (0,1), with Q=d>0. |
| a<0 and det<0 | (b,-a), with Q=a*det>0. |
| a<0 and det>=0 | Every Q<=0, since a*Q=(a*x+b*y)^2+det*y^2>=0. |
| a=0 and b!=0, after the preceding cases | (1-d,2*b), with Q=4*b^2>0. |
| a=b=0 and d<=0 | Every Q=d*y^2<=0. |

Zero and singular pivots are covered without division. The data function
`Binary.direction` is axiom-free; `direction_classify` proves its agreement
with the proof-bearing complete classifier. Five kernel-computed generic
tests cover signed off-diagonal gain, zero pivot, singular rejection, zero
rejection and an axis. These are not physical gauge-theory examples.

## Original carrier and checker

For exactly qs=[p,q] with p!=q, take a and d from the two original diagonal
pencil entries and b=(entry(p,q)+entry(q,p))/2. `pencil_two_faces` retains all
four ordered entries. The constructed original coefficient function gives x
at p, y at q and zero elsewhere. Rejection bounds every original coefficient
function on this plane at these fixed parameters.

`search` uses the EXISTING original density, both endpoint moments, OWN mean
and complete temporal jump. `certify` feeds its constructed coefficients to
the EXISTING `FamilyMarginPencil.pencilCertify` at cutoff headCutoff(w)+pivot
and depth s+1, returning that original Certificate as data on success.
The guards c>=0, epsilon>0, referenceCutoff<=pivot and the full 2*epsilon
slack condition all remain. A positive finite direction alone does not
satisfy them. Fixed witness normalization and supplied tolerance mean this
is not a complete search over certificates, pivots or tolerances.

All declarations below are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoFaceMarginSearch.lean`,
namespace `YMGap.Continuum.BF4ExactSlabFixedSpatialTwoFaceMarginSearch`.

| Declaration | Line | Exact role |
| --- | --- | --- |
| `Binary.completed_square` | 117 | Cleared identity, including singular determinant. |
| `Binary.negative_pivot_direction`, `negative_pivot_nonpositive` | 130, 144 | Explicit positive profile or whole-plane rejection at a negative pivot. |
| `Binary.zero_pivot_direction`, `zero_pivot_nonpositive` | 161, 177 | Complete treatment of a zero pivot. |
| `Binary.classify`, `direction`, `direction_classify` | 199, 218, 226 | Constructed classification, proof-free data computation and their equality. |
| `profile`, `profile_at_first`, `profile_at_second` | 254, 257, 260 | Actual original coefficients; second pin requires distinct faces. |
| `crossEntry`, `pencil_two_faces` | 265, 284 | Both original cross entries and the exact four-term pin. |
| `search`, `certify` | 323, 346 | Computed original direction/rejection and existing certificate consumer. |

The existing normalized margin pin remains `FamilyMarginPencil.pencil_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginPencil.lean:349`),
with `pencil_slack_iff` (:367), `pencilCheck_correct` (:415) and
`pencilCertify` (:434). No original checker or frontier field was changed.
The simple two-variable pin does not apply unchanged to repeated faces or
larger lists; those require multiplicity aggregation or further elimination.
Rejection of this finite plane says nothing about other planes or cutoffs.

## Verification and remaining input

Both focused safe checks exited zero. The accepted final check was:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoFaceMarginSearch.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoFaceMarginSearch.olean \
  --log-file /tmp/ym-original-two-face-search-20261002-final.log
```

All printed dependencies are empty or within {propext,Quot.sound}; no error,
warning, sorryAx or disallowed axiom appears. The data direction function,
basic scalar definitions, profile and all five closed tests are axiom-free.
An independent Sol review passed the complete mathematics, original checker
wiring and final proof-free-data delta. An independent Luna evidence review
passed the source/log hashes, citation lines, axiom output, documentation scope
and byte-identical chart fence. Only the main agent compiled.
The one-worker 20-GiB ceiling and 12-GiB OS reserve were unchanged; pre/post
pressure-free memory was 86/84 percent and swap stayed zero.

One semantic-root import is registered, not aggregate-checked. No full
root/tree build, audit, guard, progress-metric run, literature scan or heavy
original-moment computation ran. No sorry, axiom, analytic hypothesis,
frontier weakening, CI change or canonical chart change was introduced.

| Artifact | SHA-256 |
| --- | --- |
| source | `2e7b460fc987f00f6e1b1249428ce0d0fe9d2fdadf51979f524268fa0b27f680` |
| accepted final log | `46ff0225c160fbec1088583dd66ac3ed949b732555b198748580d8fd3a9a7b56` |

NEXT remains actual useful original moment/slack control with its cutoff
allowance on a justified changing family. Search now consumes its two-face
entries constructively; evaluation cost, useful sign, larger-family control
and physical calibration remain open. A single accepted direction would be
an upper-energy survival input, not an EVERY-state lower gap. Nontrivial
continuum survival, full QFT, every compact simple group and Clay remain OPEN.
No exact displayed chart claim changed, so no ASCII chart was reprinted.
