# Nonzero Wilson excitation and completed norm separation

Date: 2026-09-17 UTC. Base: `f069204`, committed and pushed. The preceding
completion-pairing/scalar-variance turn is classified **PROGRESS**.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills in four
dimensions, with the required QFT axioms, an isolated vacuum and a strictly
positive physical Hamiltonian mass gap, for EVERY compact simple gauge group,
within the stated constructive axiom gate. **That goal remains OPEN.**

## Result and shorter causal route

The positive Wilson scalar variance is now the squared norm of an ACTUAL
nonzero vector on the SAME represented Wilson completion. The vector is
orthogonal to the embedded original unit. Its norm representative and its
QCauchy witness are explicitly supplied. A concrete certificate discharges
all guards at the already used SU(2) nome 1/1024 and source base one.

For arbitrary intrinsic Wilson expressions x and y, the construction returns
centered vectors with pairing exactly
`F(x,y) - F(x,unit)*F(y,unit)`. Independently, zero completed squared norm
is equivalent to equality with the actual completed zero.

The shorter proof does NOT first require a full completed module or a real
scalar action. EXPANSION isolates the actual dense rational identities,
explicit scalar modulus, generic mixed-pairing limit and original plaquette
moment pin. CONTRACTION constructs the rational-approximation stream directly
in the EXISTING completion and identifies its norm with the existing variance.
No new carrier or assumed positive form is substituted.

## Checked declaration map

Paths in this table are under `lean/YMGap/Continuum/`.

| Mathematical step | Declaration and module:line |
| --- | --- |
| Literal intrinsic rational scaling and zero | `smul`, `BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.lean:34`; `zero`, :37 |
| Actual common-chart form -> rational scaling laws | `intrinsicForm_smul_left`, same file:75; `intrinsicForm_smul_right`, :87 |
| Actual signed difference -> form expansion | `intrinsicForm_difference_left`, same file:93; `intrinsicForm_difference_right`, :109; `distSq_diagonal`, :124 |
| Dense zero -> actual distance-to-zero identity | `distSq_zero`, same file:141 |
| Zero norm -> Type-level closeness to constant zero with computed rate | `closeZeroOfInnerZero`, `BF4ExactSlabFixedSpatialWilsonCompletedPosdef.lean:45`; `closeZeroOfInnerZero_modulus`, :51 |
| Dense zero pairings -> completed zero pairings | `completedInner_zero_left`, same file:63; `completedInner_zero_right`, :69 |
| Actual zero identity -> completed norm separation | `completedInner_posdef`, same file:79 |
| Literal rational centering | `centerApprox`, `BF4ExactSlabFixedSpatialWilsonCenterAlgebra.lean:27` |
| Unit normalization -> exact remaining mean error | `centerApprox_unit`, same file:95 |
| Dense bilinearity -> full signed centered pairing | `centerApprox_pairing`, same file:103 |
| Four-term cancellation -> coefficient-square distance | `centerApprox_distance`, same file:118 |
| Actual mean -> actual scalar modulus | `meanCauchy`, `BF4ExactSlabFixedSpatialWilsonCenteredVector.lean:44` |
| Exact coefficient distance + clipped tolerance -> vector Cauchy data | `centeredRate`, same file:49; `centeredStream`, :52 |
| Explicit stream -> vector of the existing Wilson completion | `centeredVector`, same file:64 |
| Actual mean residual tends to zero -> unit orthogonality | `centered_unit_representative`, same file:87; `centeredVector_orthogonal`, :102 |
| Two separate scalar convergences -> original connected form | `centered_pair_representative`, same file:111; `centeredVector_pairing`, :156 |
| Actual intrinsic plaquette -> original first/second moment pins | `form_square_pin`, `BF4ExactSlabFixedSpatialWilsonPlaquetteForm.lean:67`; `form_mean_pin`, :74 |
| Original variance floor -> same intrinsic form variance floor | `form_variance_floor`, same file:93 |
| Actual centered plaquette -> completed excitation | `excitation`, `BF4ExactSlabFixedSpatialWilsonExcitation.lean:50` |
| Same completed self-pairing -> explicit norm representative/modulus | `excitationNorm`, same file:59; `excitationNormCauchy`, :63; `excitation_norm_pin`, :67 |
| Original form variance -> this norm and positive floor | `excitationNorm_variance`, same file:71; `excitation_norm_floor`, :83 |
| Positive floor + actual zero -> nonzero vector | `excitation_ne_zero`, same file:89 |
| Actual vector with orthogonality/floor/nonzero proofs | `excitationCertificate`, same file:103 |
| All original guards discharged -> concrete witness | `concreteCertificate`, same file:127 |

## Explicit witnesses and same-object checks

The vector stream is `x - mean.approx(n)*unit`, with
`mean := intrinsicForm x unit`. The exact distance of two terms is
`(mean.approx(m)-mean.approx(n))^2`. The scalar modulus at
`min(epsilon,1)` suffices because the clipped error's square is at most
epsilon. The generic rational proof is reused unchanged:
`coefficient_square_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointCenteredStream.lean:41`.
No square root or choice of an approximation index from a Prop is used.

The actual supplied streams are passed to `pairSequence_converges`,
`lean/YMGap/Continuum/CRealSeminormPairingCompletionLimit.lean:95`.
The unit residual converges to mean minus itself. For mixed centered vectors,
bilinearity retains both cross terms and the product of the two rational
coefficients. Two independent mean convergence witnesses and actual mixed
pairing convergence give the limit; scalar commutativity cancels the residual
cross term, and intrinsic symmetry identifies the other mean. Equality of
regularized representative indices is never assumed.

The completed-zero theorem instantiates the existing generic
`completedInner_posdef`,
`lean/YMGap/Continuum/CRealSeminormPairingPosdef.lean:71`, with the ACTUAL
dense zero and distance-to-zero law. Its witness preserves the existing
`pairRate`; no norm-separation premise is postulated.

The excitation norm is the actual `representativeInner` of its explicit
stream with itself. `excitationNormCauchy` supplies the modulus for THAT
representative, not a modulus transported along CReal equality. The final
certificate returns the vector as Type-level data; the exact norm and its
modulus are separately exported and pinned to it.

The concrete parameters are existing proved data: `nome`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCertificate.lean:32`, is
`invSucc 1023`; `nome_pos` / `nome_lt_one` are at :36 / :38.
`existingNome_guards`,
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:195`, supplies
the heat-ratio and remainder guards. `existingNome_entropyRate`,
`lean/YMGap/Continuum/BF4ExactSlabSummableCoreRate.lean:37`, supplies strict
entropy smallness for that SAME remainder witness. `origin_physical`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCentralExcitation.lean:43`,
supplies the actual base-one face. No caller-supplied analytic field remains
in `concreteCertificate`.

## Residue and next consumer

Unit-orthogonality does NOT identify a physical stationary vacuum. This
checkpoint does not construct completed time, normalize the excitation,
prove positive-time response, extend the old plaquette-carrier strict bound,
or prove continuum survival. The variance floor depends explicitly on nome
through `starRatio w`; no beta-independent or physical-spacing-uniform mass
claim is made. The general result retains positive base and all original
small-nome/core/entropy guards.

The next operator consumer is `SquaredSeminorm.NonexpansiveSemigroup`,
`lean/YMGap/Continuum/CRealSeminormCompletion.lean:519`. Its actual original
time maps, nonexpansiveness and semigroup laws must be proved on this enlarged
domain before their completion descent is used. The enlarged strict bound
must concern that SAME operator and carrier; the old plaquette-only bound
does not supply it automatically. Completed module/Hilbert structure, base
inclusions and full observable/OS/QFT realization remain separate.

Parallel work advanced the nonconstant-vector and completed-form branches.
Full spatial symmetry, changing-scale original-action control, physical mass
calibration and actual producers for every compact simple group remain open
as recorded in `AUDIT-WILSON-COMPLETION-AND-PLAQUETTE-VARIANCE.md`. The AF
guard obstruction and canonical scorecard fields are unchanged. No canonical
Clay atom is declared closed.

## Verification and review

All six focused checks passed on the first attempt, with 59 public axiom
gates using only {propext, Quot.sound} or no axioms. Logs contain no warning,
error, `sorryAx`, classical-choice or native-reduction dependency. Parent and
three agents developed/cross-reviewed the same-form pins, centering signs,
explicit moduli, quotient identity, concrete guards and honest boundaries.

Main alone compiled, serially, via `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <its olean>` with
fresh process/swap preflights. Swap remained 6869.19 MiB at these preflights;
no competing Lean/test/runner job was found. Root imports added, but root/
full-tree/full-audit/guard checks NOT run. No old proof, sorry, axiom,
canonical field, analytic guard or safety limit changed. CI remains manual;
no routine literature scan ran.

Final logs are local `/tmp/` files; hashes are SHA-256.

| Module suffix after `BF4ExactSlabFixedSpatialWilson` | Gates | Final log | SHA-256 |
| --- | ---: | --- | --- |
| IntrinsicAlgebra | 15 | `ym-wilson-intrinsic-algebra-20260917.log` | `892297262913a829f42b28bc05035fb730bfb5e1641d2e967c5e87d5ffb33d07` |
| CompletedPosdef | 7 | `ym-wilson-completed-posdef-20260917.log` | `eaed55b0e140c79225a76701ec33bfe939552d68dfac29b1c3ffd38c82418a82` |
| PlaquetteForm | 7 | `ym-wilson-plaquette-form-20260917.log` | `c7881daeaa541567bd1188a93a0d523d7a40da7058dc1c95065b6368f16884af` |
| CenterAlgebra | 6 | `ym-wilson-center-algebra-20260917.log` | `8d8efeacac45a7715b8ecc4606821d1fffd2d2dc997e9d00e70f14c5937bb752` |
| CenteredVector | 13 | `ym-wilson-centered-vector-20260917.log` | `c583b81778f6bbf182d5776779b78a4c54bcb9e2f1b754ec84807a43f16b569e` |
| Excitation | 11 | `ym-wilson-excitation-20260917.log` | `c2dff22cdf29b796c679ae2b69403988679c54b8d28a8017874b45204f9305ab` |
