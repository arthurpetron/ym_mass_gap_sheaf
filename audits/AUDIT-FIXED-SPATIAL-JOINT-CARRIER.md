# Actual cutoff-removed reflected carrier and discrete physical time

Date: 2026-09-16. PROGRESS after `cef8cde`.

WHOLE-PROJECT GOAL: nontrivial continuum Yang--Mills on R^4, required QFT
axioms and a positive physical Hamiltonian gap for EVERY compact simple
group, for the SAME theory, within the constructive axiom gate. This
checkpoint constructs the selected fixed-width SU(2) reflected Cauchy
carrier after heat-cutoff removal; spatial and spacing passage remain open.

## Proved causal argument

The existing jointPairing is the joint heat-cutoff/boundary-time limit of
the original reflected scalar. Its stage-wise symmetry, normalization,
signed-rational bilinearity, positivity and sharp Cauchy--Schwarz pass to
that SAME limit. Products use the generic constructive continuity theorem;
no approximation indices or separately minimized charts are equated.

EXPANSION: retain the actual guarded signed difference x-y and its four
pairing terms. Limiting Cauchy--Schwarz gives B(x,y)^2<=B(x,x)B(y,y).
If B(x,x) is zero in the limit, its right-hand side is zero. The scalar
epsilon-squared argument implies B(x,y)=0 without square roots, division,
representative selection, or a decision about the real norm. In particular,
no finite-stage nullity is inferred from limiting nullity.

CONTRACTION: the limiting radical theorem yields pairing null congruence;
the exact four-term difference expansion yields distance null congruence.
Reflexivity, symmetry, nonnegativity and the factor-two triangle pass
through the unconditional stage-wise distance limits. These proofs supply
every field of the existing SquaredSeminorm interface. The actual distance
retains its separately constructed approximation QCauchy data.

The SAME literal physical advance is nonexpansive for this limiting
distance, by passage of the already proved original distance inequality.
The existing explicit-modulus Cauchy quotient therefore constructs a new
JointCompletion and descends discrete physical time to it. On embedded
presentations the map is exactly physicalTime; on representatives it keeps
the supplied Cauchy modulus unchanged. Zero/addition-of-time laws hold.

The actual scalar time-sum/balance laws, diagonal contraction and even-time
positivity also survive cutoff removal. Original unit normalization proves
its limiting distance from zero is one. The descended unit is fixed and
distinct from zero. This is not a nonconstant-excitation witness, uniqueness
of the vacuum, or metric completeness.

## Declaration evidence

All module paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `differenceSpan` | `BF4ExactSlabFixedSpatialJointPairingLaws.lean:35` | Literal physical signed difference. |
| `jointPairing_symm`, `jointPairing_nonnegative`, `jointPairing_unit_unit` | `BF4ExactSlabFixedSpatialJointPairingLaws.lean:44`, `:52`, `:59` | Same-limit reflected symmetry, positivity and normalization. |
| `jointPairing_cauchySchwarz`, `jointPairing_radical_zero` | `BF4ExactSlabFixedSpatialJointPairingLaws.lean:67`, `:101` | Limiting sharp CS and genuine limiting radical law. |
| `jointPairing_add_left`, `jointPairing_add_right`, `jointPairing_smul_left`, `jointPairing_smul_right` | `BF4ExactSlabFixedSpatialJointPairingLaws.lean:113`, `:123`, `:133`, `:141` | Signed-rational bilinearity on actual physical presentations. |
| `jointPairing_difference_left`, `jointPairing_difference_right`, `jointPairing_difference_diagonal` | `BF4ExactSlabFixedSpatialJointPairingLaws.lean:150`, `:160`, `:171` | Subtraction and exact four-term diagonal. |
| `jointDistSq`, `jointDistSqCauchy`, `distSq_converges_joint` | `BF4ExactSlabFixedSpatialJointSeminorm.lean:33`, `:37`, `:41` | Original limiting squared distance and explicit data. |
| `jointDistSq_refl`, `jointDistSq_symm`, `jointDistSq_nonnegative`, `jointDistSq_triangle` | `BF4ExactSlabFixedSpatialJointSeminorm.lean:46`, `:51`, `:56`, `:62` | Unconditional distance laws. |
| `jointPairing_null_left`, `jointPairing_null_congr`, `jointDistSq_null_congr` | `BF4ExactSlabFixedSpatialJointSeminorm.lean:84`, `:91`, `:104` | Same limiting radical descent. |
| `jointSeminorm` | `BF4ExactSlabFixedSpatialJointSeminorm.lean:117` | Every existing SquaredSeminorm field supplied. |
| `jointPairing_time_sum`, `jointPairing_time_balance`, `jointPairing_advance_contraction`, `jointPairing_even_nonnegative` | `BF4ExactSlabFixedSpatialJointPhysicalTime.lean:46`, `:56`, `:64`, `:74` | Actual limiting scalar time identities and bounds. |
| `jointPhysicalTime_contraction`, `jointTimeNonexpansive`, `jointTimeSemigroup` | `BF4ExactSlabFixedSpatialJointPhysicalTime.lean:82`, `:91`, `:95` | Physical advance is contractive for the SAME limiting distance. |
| `JointCompletion`, `jointEmbedSpan`, `jointCompletedTime` | `BF4ExactSlabFixedSpatialJointPhysicalTime.lean:111`, `:113`, `:116` | New cutoff-removed Cauchy quotient and genuine time map. |
| `jointCompletedTime_zero`, `jointCompletedTime_add`, `jointCompletedTime_embedSpan` | `BF4ExactSlabFixedSpatialJointPhysicalTime.lean:120`, `:124`, `:131` | Descended semigroup and original-presentation pin. |
| `jointTime_cauchy_seq`, `jointTime_cauchy_modulus` | `BF4ExactSlabFixedSpatialJointPhysicalTime.lean:135`, `:140` | Explicit representative map and unchanged modulus. |
| `jointCompletedUnit_fixed`, `jointUnit_distance`, `jointCompletedUnit_ne_zero` | `BF4ExactSlabFixedSpatialJointPhysicalTime.lean:146`, `:154`, `:181` | Fixed nonzero unit, not a non-vacuum excitation. |

## Next mathematical consumers and honest boundary

The previous fixed-stage completions have NOT been identified with this
carrier. Its completed pairing, completed vector operations/centering and
strict unit-complement bound remain to be constructed. The already proved
cutoff-removed strict scalar bound is available for that later extension.
The existing generic scalar completion machinery is reusable: notably
`Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion.lean:39`,
`CReal.ofQ'CauchySeq_family_regPred`, supplies the explicit inner regularity
epsilon.den for a family of actual ofQ'CauchySeq representatives. That is
not by itself a completed pairing or a supplied outer continuity estimate.

A parallel source review identified a separate concrete nontriviality route
to investigate next: a central spatial-face character. The public
`BF4ExactSlabHeatHaarGuardObstruction.lean:71`, `face_character_haar_zero`,
gives its original bare-Haar mean; the private `first_character_pair` at
`:206` contains the fundamental square moment. The existing central ratio
is `BF4ExactSlabFixedSpatialMiddlePairing.lean:125`, `middleRatio`, and
`BF4ExactSlabFixedSpatialWindowPadding.lean:105`, `windowRatio_zero`, pins
the zero-width time window to it. The actual transfer certificates in
`BF4ExactSlabFixedSpatialTransferSandwich.lean:197`,
`transferStepLowerCertificate`, and `:223`, `transferStepUpperCertificate`,
are potential inputs to a depth/cutoff-independent central density comparison.
The source-face moments, explicit central-observable pin and positive
centered-variance estimate are NOT proved in this increment. This is a
source-reviewed next proposition, not a claimed nonconstant state.

Metric completeness/full Hilbert/OS and required gauge algebra, nonconstant
excitations, cutoff-removed completed strict gap, spatial/spacing uniformity,
physical mass calibration, continuum QFT and all-group Clay closure remain
open. No canonical field, literal sorry, axiom, analytic premise or resource
limit changed.

## Verification

Three focused serialized one-worker/20 GiB checks passed all 44 public gates
within {propext, Quot.sound}. Each had a fresh process/swap preflight; all
three passed on their first focused check. Final logs contain no warnings,
errors, sorryAx or classical dependencies. Main alone compiled; parallel
agents used disjoint implementation files or read-only source review.
Three selective-root imports were added. Root/full-tree/full axiom audit
were not run, and no literature scan was performed.

| Module suffix (prefix BF4ExactSlabFixedSpatial) | Gates | Final `/tmp/<module>.log` SHA-256 |
|---|---:|---|
| `JointPairingLaws` | 13 | `46569eb2ed7b97afcd07f021a0704f299b74ff389e1a77845a98de76a1d02a0f` |
| `JointSeminorm` | 11 | `fab317a2deb51bb7eec1619d4218d4b41d819ba16f6aad1f6c18a917a4067c94` |
| `JointPhysicalTime` | 20 | `c407f041c01b919cf557767ef24b7e9c014dd46227aca3df67e5af1aedc60dc1` |
