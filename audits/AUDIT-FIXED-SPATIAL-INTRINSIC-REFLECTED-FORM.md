# Intrinsic reflected pairing: chart independence, sharp CS and radical law

Date: 2026-09-16. Classification: PROGRESS after `035d097`.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian mass gap for
every compact simple group, on the SAME theory, within the constructive
axiom gate. The results below concern the selected fixed-width SU(2) action.
They do not complete that target.

## Mathematical result

For rational 0<w<1, fixed width and retained cutoff
K=headCutoff(w)+stage, the existing time-limit reflected form on finite
signed spatial-probe spans is rational-bilinear and symmetric, with
nonnegative diagonal and sharp Cauchy--Schwarz:

    B(X,Y)^2 <= B(X,X) B(Y,Y).

The form has its existing explicit window convergence modulus. The three
limits in this inequality need not have the same polynomial caps or
representative indices. If B(X,X)=0, then B(X,Y)=0 for every physical Y.
The centered inclusion h -> h+1, j -> j+1 preserves the SAME mixed form.

An intrinsic presentation now records each natural-number distance d from
the reflection plane, rather than an offset from an arbitrary window edge.
The finite presentation computes its radius. The returned `pairing` uses
the common radius H=max(radius X, radius Y) and encodes d as H-d. It agrees
with every larger valid chart. Its signed-rational bilinearity, symmetry,
nonnegative diagonal, sharp CS and null-pairing annihilation are proved
for these SAME intrinsic presentations. No chart is selected by choice.

## Causal mathematical argument

1. The actual orientation-correct link reflection is involutive on the
   finite coordinate prefix. Its time-vector sign selector is invariant
   under the reflected block permutation. Thus the two sign corrections
   cancel; no involution is assumed as an extra hypothesis.
2. Reflection permutes the literal selected chain's face list. It preserves
   its heat product. Original Haar invariance, this action identity and
   reflection involution give mixed reflected symmetry. The same partition
   reciprocal multiplies both sides. Literal signed-span placement transfers
   this equality to the finite window ratios.
3. Concatenation adds finite signed spans, and scaling changes only their
   rational coefficients. Exact polynomial identities prove bilinearity.
   Existing convergence and uniqueness pass these laws and symmetry to the
   already-constructed CReal window limit, not to a replacement state.
4. Centered inclusion shifts every schedule by one slice and changes h to
   h+1. It commutes literally with j -> 2*h-j under the half-window guard.
   Both factors of the mixed product share one coordinate lift. The empty
   schedule requires padded coefficient equality, not raw coefficient
   equality: lifting the unit adds zero exponents.
5. Supported padded congruence is proved inside the full-window Haar
   integral containing BOTH terminal messages and the full intervening
   action. Every factor is supported. It does not assert equivalence
   against arbitrary unsupported insertions. The original partition stays
   unchanged. Right padding then left padding remove the two added slices
   from the SAME limiting functional. No finite stationarity is assumed.
6. At each finite symmetric placement, expand the actual signed combination
   sX+rY. Its reflected positivity and mixed symmetry construct the rational
   PreInnerForm.nonnegQuad field. The existing sharp rational CS theorem
   now applies to actual ratios, all with the same partition.
7. General multiplication continuity passes the three raw time sequences
   to their existing limits. This avoids equating their unrelated QMhat
   indices. If the first diagonal is zero, CS bounds the mixed square by
   zero. Applying the eventual estimate at epsilon squared proves the
   mixed value zero, without division, square roots or a positivity decision.
8. Each finite intrinsic distance support has a computed maximum. Encoding
   in chart h+1 is exactly the centered inclusion of encoding in chart h,
   provided h bounds the support. Induction compares all nested charts.
   Each bilinear identity uses one explicit common maximum for all its
   terms. CS additionally moves the two diagonals from their own minimal
   charts into that same common chart. None of these steps equates the
   CReal representatives literally; they prove the required CReal.Equiv.

## Declaration evidence

Paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `reflection_involutive_prefix` | `BF4ExactSlabFixedSpatialReflectedSymmetry.lean:195` | Actual sign-corrected reflection involution. |
| `originalChain_reflection` | `BF4ExactSlabFixedSpatialReflectedSymmetry.lean:213` | Same selected action invariant. |
| `originalChain_reflected_symm` | `BF4ExactSlabFixedSpatialReflectedSymmetry.lean:227` | Original mixed Haar symmetry. |
| `reflectedWindowRatio_symm` | `BF4ExactSlabFixedSpatialReflectedSymmetry.lean:300` | Literal mixed-span ratio symmetry. |
| `mixedReflectedProduct_shift` | `BF4ExactSlabFixedSpatialCenteredWindowShift.lean:183` | One common lift, with all cross terms. |
| `windowRatio_padded_congr` | `BF4ExactSlabFixedSpatialWindowPaddedCongruence.lean:82` | Supported full-integrand congruence, same partition. |
| `windowLimit_padded_congr` | `BF4ExactSlabFixedSpatialWindowPaddedCongruence.lean:111` | Same returned limits, possibly different caps/moduli. |
| `form` | `BF4ExactSlabFixedSpatialReflectedForm.lean:162` | Existing window limit, not an assumed functional. |
| `form_add_left`, `form_add_right` | `BF4ExactSlabFixedSpatialReflectedForm.lean:181`, `:194` | Signed addition in each argument. |
| `form_smul_left`, `form_smul_right` | `BF4ExactSlabFixedSpatialReflectedForm.lean:207`, `:218` | Arbitrary rational scaling in each argument. |
| `form_symm` | `BF4ExactSlabFixedSpatialReflectedForm.lean:231` | Actual limiting symmetry. |
| `form_centered_inclusion` | `BF4ExactSlabFixedSpatialReflectedForm.lean:247` | Enclosing-window change preserves mixed form. |
| `finite_cauchySchwarz`, `form_cauchySchwarz` | `BF4ExactSlabFixedSpatialReflectedCauchySchwarz.lean:147`, `:163` | Actual finite quadratic positivity, then raw-sequence limit passage. |
| `form_radical_zero` | `BF4ExactSlabFixedSpatialReflectedCauchySchwarz.lean:205` | Epsilon-squared null-pairing argument. |
| `radius`, `encodeChart` | `BF4ExactSlabFixedSpatialIntrinsicReflectedForm.lean:46`, `:99` | Computed distance radius and explicit coordinate chart. |
| `pairing`, `pairing_chart` | `BF4ExactSlabFixedSpatialIntrinsicReflectedForm.lean:196`, `:205` | Actual intrinsic pairing and every-valid-chart pin. |
| `pairing_add_left`, `pairing_add_right` | `BF4ExactSlabFixedSpatialIntrinsicReflectedForm.lean:242`, `:260` | Intrinsic addition, common chart computed from three supports. |
| `pairing_smul_left`, `pairing_smul_right` | `BF4ExactSlabFixedSpatialIntrinsicReflectedForm.lean:278`, `:293` | Intrinsic rational scaling. |
| `pairing_cauchySchwarz`, `pairing_radical_zero` | `BF4ExactSlabFixedSpatialIntrinsicReflectedForm.lean:314`, `:333` | Sharp CS and actual null-pairing annihilation independent of chart. |

## Scope and open mathematical work

The group is the actual SU(2) quaternion/character realization. Nome,
spatial width and heat cutoff remain fixed in this time limit. The earlier
fixed-chain cutoff limit is separate; no interchange has been proved here.
The old rate and prefactor still depend on nome and width. There is no
spacing-uniform or physical mass estimate in these results.

The observable domain is the real rational span of scheduled spatial
face-character products. It is not arbitrary coordinate polynomials,
nor a proved complete gauge-observable algebra. The background is the
selected fixed-width action, not the full growing-box action or its marginal.

A physical time shift changes distance to the reflection plane. The proved
centered inclusion only changes the enclosing chart and is NOT that operator.
The actual shift laws, boundedness/radical descent, quotient/completion and
stationary vacuum must therefore still be constructed on the same carrier.
Joint cutoff/time control, spatial/spacing passage, continuum QFT,
physical Hamiltonian gap and all compact simple groups remain open.
No canonical field, literal hole or analytic hypothesis has been weakened.

## Next causal frontier: physical time shift, not chart enlargement

The following is a source-backed plan, NOT a new proved operator instance.
Incrementing each intrinsic distance defines the intended physical shift S.
The next missing identity is B(SX,Y)=B(X,SY), proved by an actual mixed
polynomial translation pin and the existing `windowLimit_shift` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowState.lean:209`.
The present centered inclusion alone does not prove it.

For contraction, `polynomialCap` in
`lean/YMGap/Continuum/QuaternionHaarSupportedPolynomialInterval.lean:237`
depends only on the coefficient list. Prove that the translated products
preserve that list, then use `windowRatio_later_bounds` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowBracket.lean:104`
at bracket time zero to get one actual scalar cap for all physical lags.
Coefficient-list invariance and this physical-lag family remain to be proved.

With a_n=B(S^n X,S^n X), time balance and positivity of X-S^(2n)X
would give 2*a_n<=a_0+a_(2n). The existing consumer
`bounded_midpointDoubling_leEv_anchor` in
`lean/YMGap/Continuum/BoundedMidpointDoublingEventual.lean:55`
requires exactly this inequality, a uniform rational upper cap and
nonnegativity of a_0. It does not require a strict-gap estimate.
Actual time balance would also give radical preservation from the proved
null-pairing law. Neither implication has yet been instantiated here.

Site reflection and time balance would imply positivity of S^2, not
necessarily S. One-step positivity needs an additional genuine identity.
Completion still needs a concrete squared-seminorm instance and the
actual nonexpansive shift, not substitution of an old concrete operator.

## Verification record

Each checked module used the monitored launcher, one worker and a 20 GiB
hard worker ceiling, with a fresh process/swap preflight. Only targeted file
checks were run; no root build, full-tree check or full axiom audit is claimed.
Initial elaboration errors were repaired without adding hypotheses. Explicit
convergence arguments removed a local elaboration timeout without raising
the heartbeat or memory limits. The constructive range duplicate-freeness
proof is used in place of the core convenience theorem.

The six completed checks have 73 public gates, each reporting only
{propext, Quot.sound} or no axioms. No sorryAx or classical dependency occurs
in the final logs. Log SHA-256 values:

| Module suffix | `/tmp/<full module name>.log` SHA-256 |
|---|---|
| `CenteredWindowShift` | `077a3a2a46543e8078ec67bb778aad42a9140ffff9658508d01b6f0b69d2c20a` |
| `WindowPaddedCongruence` | `0a732c5bd1f8650aa5deb61c21c97b7dd3309a5fb4d29ea29a25ab6920c27081` |
| `ReflectedSymmetry` | `29a8879bca8ee18110a8b15c730cf2ed7012d04bac01f5ad4140ed98e1b10260` |
| `ReflectedForm` | `f2dc0aa2d334771bf398e04678d5b0412ab8cc1462a325c711c34c9a9ff88d74` |
| `ReflectedCauchySchwarz` | `65cd0930922b95b0c7c4af63e25e6681fcc7f27aa8285f95720c28931c3a1dcf` |
| `IntrinsicReflectedForm` | `055ffa9c8f47793e879f97d8e80777b0e0d4a21efb76ebfa381b2edcff9af1a1` |

Every suffix has prefix `BF4ExactSlabFixedSpatial`. Parallel agents wrote
independent proofs and reviewed same-object support/placement; only the main
agent compiled, serially. No literature scan, CI change or capacity increase.
Independent final source review checked physical-face guards, common-chart
transport of both diagonals, all signed finite cross terms, the unchanged
partition and the absence of any matching-representative-index assumption.
