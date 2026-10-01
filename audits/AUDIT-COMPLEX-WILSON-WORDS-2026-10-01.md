# Complex Wilson word action on the original physical carrier

Date: 2026-10-01 UTC. PROGRESS: the existing buffered real Wilson-word
action now acts on the existing complex physical bond completion, with
complex linearity, a full Hermitian adjoint and original source/vacuum
matrix elements. This independent operator-algebra component requires no
new scaling estimate. It is not a continuum observable algebra or full QFT.

## Checked declarations

All declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSSeparatedWords.lean`.

| Declaration and line | Claim |
| --- | --- |
| `wordAct` :66, `wordAct_append` :69 | Componentwise action of the ORIGINAL real words; list concatenation is operator composition. |
| `wordAct_adjoint` :78 | Word reversal is the full Hermitian adjoint, including BOTH imaginary cross pairings. |
| `wordAct_add` :148, `wordAct_smul` :156 | Additivity and complex linearity preserve both supplied constructive-real scalar Cauchy witnesses. |
| `wordAct_ofSource` :173, `wordAct_source_pairing` :185 | The two original source components are acted on separately; all four matrix-element components use the unchanged original reflected source limits. |
| `letter_norm_bound` :195 | Each one-step-buffered letter retains the original spin-only squared-norm ceiling on the complex carrier. |
| `vacuum_word` :239 | The existing physical vacuum pair evaluates the original normalized Wilson joint limit, with zero imaginary part. |

The real action being extended is
`BF4WilsonAllNomeBondOSSeparatedWords.wordAct`, not a new freely supplied
operator. The SAME physical complex carrier and Hermitian pairing are used
throughout. No representative choice or new analytic hypothesis enters.

## Remaining QFT obligations

The letters are one-step-separated buffered insertions. This result supplies
neither unbuffered equal-time multiplication nor spacelike locality, vacuum
cyclicity, an inhabitant of the canonical OS-root bundle, continuous physical
time, cross-scale carrier maps, or a continuum Wightman/OS theory. All those
broader requirements remain open. The canonical chart is unchanged.

The parallel survival/mass review found no nonredundant unconditional
construction to add: the fixed-nome family floor already exists in
`BF4WilsonAllNomePlaquetteFamilyBondFloor.family_bond_floor` (:217), and
`family_bond_ne_zero` (:228). The upper-rate consumers
`BF4ExactSlabFixedSpatialJointSurvivalCalibration.marginRate_le_of_sampled_response`
(:77) and `logRate_le_of_sampled_response` (:161) still require their sampled
response on the same completion. The scalar lower physical-floor consumer
`SharpContinuumObligation.ContinuumGapTheorem.c_le_physGap` (:116) consumes
the `rate_matched` field of `ContinuumGapTheorem` (:87); it does not construct
a spacing-matched Hamiltonian gap. Cross-scale state/pairing maps, a
spacing-matched LOWER generator gap, and nonzero fixed-physical-time response
with an UPPER rate remain substantive missing inputs. No wrapper around them
is counted as a proof increment.

## Verification

Main's final focused check returned terminal exit zero and emitted the
target olean. Ten gates passed: `sourceWordPair` is axiom-free; the other
nine use only {propext,Quot.sound}. Sol drafted the independent component;
a separate Sol review checked the final Hermitian cross terms, scalar laws,
source/vacuum pins and accepted log. Main inspected and repaired the draft.
Failed draft logs and recovery sorryAx are not accepted evidence.

No new sorry, axiom, Classical dependency, native_decide, analytic field or
frontier weakening. Main alone compiled through the monitored launcher with
one 20 GiB worker, unchanged 12 GiB reserve and dynamic telemetry. No broad
build/audit/guard, raised limit or CI change. Root import registration is not
aggregate verification. The documentation skill separates this fixed-carrier
observable construction from the still-open full continuum QFT requirements.

Accepted log: `/tmp/ym-complex-separated-words-third-20261001.log`.
SHA-256: `433b3cf6f0eccb52139f27e1d2b0098880752455229740cf6b3012371efdaaf2`.
