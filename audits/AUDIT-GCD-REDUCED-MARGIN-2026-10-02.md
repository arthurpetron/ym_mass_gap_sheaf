# Gcd-reduced coefficients in the ORIGINAL finite-margin evaluator

## Outcome and consumer

PROGRESS after `3da7af8`: the actual collector now reduces each newly stored
rational coefficient and every same-key sum by the gcd of numerator magnitude
and positive denominator. This prevents redundant common factors from being
carried across stored terminal steps. It does not bound genuine coefficient
growth or the raw arithmetic performed within a step.

The existing evaluator consumes this collector without a new analytic input.
Its original coefficient, pairing, margin and checker-equivalence proofs all
passed again. BOTH endpoint sources, OWN centering, full signed jump, cutoff
modulus, slack and padding remain unchanged. No useful accepted instance has
been produced; no physical/continuum frontier claim closed.

## Checked declarations

| Declaration | Source | Exact result |
| --- | --- | --- |
| `Q'.reduce`, `reduce_eqv` | `lean/YMGap/Constructive/RationalReduction.lean:46`, `:59` | Computed gcd reduction preserves signed rational value. |
| `reduce_den_le`, `reduce_numAbs_le` | same file, `:78`, `:83` | Reduction does not enlarge either stored denominator or numerator magnitude relative to its input. |
| `reduce_num_zero_iff`, `reduce_coprime` | same file, `:88`, `:113` | Zero detection is unchanged; output numerator magnitude and denominator have gcd one. |
| `reducedAdd`, `reducedMul` | same file, `:120`, `:123` | Exact arithmetic followed by reduction; not a replacement of global `Q'` instances. |
| `collect_coeff`, `collect_reduced` | `lean/YMGap/Continuum/SU2QuaternionSparseCoefficientCollector.lean:126`, `:269` | Every weighted coefficient probe unchanged; EVERY output coefficient coprime. |
| `collect_half_plus_three_quarters`, `collect_signed_cancel`, `collect_sixty_four_halves` | same file, `:276`, `:281`, `:285` | Kernel-computed structural tests: 1/2+3/4=5/4, signed cancellation removes the key, 64 halves store the integer 32. |
| `iterate_reduced`, `terminal_reduced` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCollectedFamilyMargin.lean:115`, `:133` | Stored actual messages have gcd-reduced coefficients at EVERY depth. |
| `numerator_reduced` | same file, `:226` | Actual collected compressed numerator has gcd-reduced coefficients. |
| `check_correct`, `certify` | same file, `:350`, `:366` | SAME original acceptance conditions and existing certificate data. |

The reduction computation itself is axiom-free. Positivity of the divided
denominator is proved separately. Equivalence uses exact integer/natural
division cancellation, and handles zero and negative numerators. To prove
coprimality, numerator magnitude is reconstructed from that same exact
cancellation and the positive gcd; no erased modulus or choice is used.

## Axiom failure caught and repaired

The first compiling draft failed the axiom gate. A focused diagnostic found
that the core lemma `Int.natAbs_ediv_of_dvd` depends on `Classical.choice`.
It was removed from the proof, not quarantined or accepted. The replacement
uses `Int.natAbs_mul`, exact division cancellation and cancellation of a
positive natural multiplier. Earlier draft logs are NOT accepted evidence.

All final public gates lie within {propext,Quot.sound}. `reduce`, `reducedAdd`,
`reducedMul`, `insertKey`, `collect` and the three collector regression
theorems are axiom-free. No sorry, new axiom, classical/native oracle,
analytic premise, erased witness or weakened frontier was introduced.

## Verification and resource boundary

Three serialized focused `scripts/safe_lean_build.py --jobs 1` checks used
`--check-worker-limit-gib 20` and matching `.olean` output paths:

- `/tmp/ym-rational-reduction-20261002-final.log`: EXIT 0, 12 gates.
- `/tmp/ym-reduced-sparse-collector-20261002-final.log`: EXIT 0, 15 gates.
- `/tmp/ym-reduced-collected-margin-20261002-final.log`: EXIT 0, 31 gates.

The 58 final gates contain no errors, warnings, sorryAx or disallowed axiom.
An independent source review confirmed signed/zero semantics, original pins
and the intermediate-work caveat: PASS. Pre/post system-free readings were
86%/85%; post-check swap was zero. A separate Luna review verified all hashes,
declaration citations, final gates and unchanged canonical chart fences: PASS.
ONE 20-GiB worker and 12-GiB OS reserve
were unchanged. No broad build/audit/guard, progress-metric script, literature
scan or heavy finite evaluation ran. No root import was needed: the existing
collector import reaches the new module. CI and canonical chart are unchanged.

| Artifact | SHA-256 |
| --- | --- |
| `RationalReduction.lean` | `1f21fa26fafbf425288cb92ecc22dbe6b0c56178340178ec7186e94afda7fd34` |
| `SU2QuaternionSparseCoefficientCollector.lean` | `085268f0f5397a73747932a394071366dfc0072e040f7744731d3ff5f010253d` |
| `BF4ExactSlabFixedSpatialCollectedFamilyMargin.lean` | `d44b1594f55ec75a241431d13140956bb292b40f098bbc91caefac8e0e9c9a7b` |
| rational final log | `9b00decc482f17aedc3b5dc26535f7c0e15e90cdf7d0eecfa95f237cea254fa5` |
| collector final log | `3f87698f646882e4dacfddce5b4d682e941a6588da86ae276f1507399af636ba` |
| margin final log | `cc6de1d17d23b1e1ba51e70b5df9a0c44f2775cd96796aef5fbb8e2974199441` |

## What remains

Raw RatPoly products, Haar accumulation and projection arithmetic occur
BEFORE collection. They are not made gcd-normalized by this change, and
intermediate expansion can remain enormous. No uniform coefficient-bit,
work or practical-runtime bound is proved. The next mathematical input is
still useful positive ORIGINAL signed slack on a justified changing family,
with physical time/spacing, nonzero survival, QFT and every-group joins open.
Gcd normal form does not determine the sign of `c*OWNVar-E`.
