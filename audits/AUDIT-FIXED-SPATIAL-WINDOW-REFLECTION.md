# Selected-action reflection positivity reaches the same window limit

Date: 2026-09-16. Classification: PROGRESS after `9c4cc0a`.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian mass gap for
every compact simple group, on the SAME theory, within the constructive
axiom gate. The result below concerns the fixed-width SU(2) selected action,
not that completed target.

## Mathematical result

For every rational 0<w<1, fixed spatial width, retained cutoff
K=headCutoff(w)+stage, half-window h and finite rational sum X of scheduled
spatial face-character products with offsets at most h, the existing
polynomialWindowLimit is nonnegative on the literal reflected product
Theta(X)*X. Reflection sends each offset j to 2*h-j, retaining all signed
coefficients and list order. This includes all mixed terms in a signed sum;
it is not just nonnegativity for individual character products.

`reflectedWindowLimit_nonnegative` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowReflectionPositive.lean:176`
proves this in CReal.leEv for the existing limit and its existing explicit
modulus. It assumes neither a positive reflected form nor a replacement
stationary state.

## Causal proof: unchanged action to a conditional square

At even extent E=2*(radius+1), select exactly
chainIds E width start (2*depth), with start+depth=radius+1. Its spatial
time interval is closed at both ends; its temporal face interval is
half-open. Reflection sends spatial base time t to E-t, and temporal
base time t to E-(t+1), preserving the actual selected physical face list.
Duplicate-freeness and the physical involution prove the lower-to-upper
permutation. Physical clipping is itself invariant, so this geometric
theorem does not require width containment.

Partition THIS list into lower, fixed and upper factors L,W,U. All original
shared links remain. U is the reflection of L, L is one-sided (not strictly
lower-local), and W is fixed-slice-local. W occurs once. For any supported
one-sided signed polynomial p, exact coefficient algebra and the existing
conditional integration give

    H[(Theta(p)*p)*(L*(W*U))] = H[C(p*L)^2 * W].

The actual original central heat product has a constructed square
certificate at K>=headCutoff(w). It proves the right side nonnegative.
Neither p nor L is assumed positive. The generic selected-list theorem's
reflection-permutation hypothesis is supplied by the proved chain geometry,
not left as a new analytic obligation.

The existing reciprocal normalizes precisely this partition. Its positivity
therefore proves finiteValue(Theta(p)*p)>=0. Each representative of the
existing fixed-chain cutoff expectation is nonnegative as well. This is
cutoff removal at a FIXED chain, distinct from the fixed-cutoff time limit
below; no interchange of these limits is asserted.

## Causal proof: fixed observable while both time boundaries recede

For diagonal index t choose

    start  = width+1
    radius = width+t+h
    depth  = t+h
    E      = 2*(width+t+h+1).

The chain is centered, with exactly t+(2*h+t)=2*depth transitions.
Place a schedule at start+t. Original geometric reflection then sends
its offset j to 2*h-j, independent of t. The source insertion
reflectedWindowProduct width h xs is thus FIXED throughout convergence.
Only the original ambient placement varies. In particular, the old
originalWindowScalar's automatic ambient extent is not silently assumed
to be reflection-centered.

The new bilinear span identity appends each pair of schedules before
applying the original-window theorem. Coefficient-sensitive linearity then
assembles all signed cross terms. Both sides use the same action, cutoff
and partition. Applying finite RP to the ENTIRE original signed sum, and
transporting its literal reflection image, proves every diagonal window
ratio nonnegative. Evaluating that statement at the existing QMhat indices
proves the returned CReal nonnegative; no new limit or modulus is selected.

The auxiliary heat-dressed polynomial varies with t only inside the finite
positivity proof. It is not the fixed observable passed through convergence.

## Declaration evidence

Paths in the table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `selectedIds_reflect` | `BF4ExactSlabFixedSpatialChainReflection.lean:99` | Actual selected-chain reflection closure. |
| `selectedLower_reflection_perm` | `BF4ExactSlabFixedSpatialChainReflection.lean:156` | Supplies the generic positivity theorem's reflection premise. |
| `selectedHeat_split` | `BF4ExactSlabSiteSelectedHeatAction.lean:173` | Same original selected action factors as L*(W*U). |
| `selectedAction_dressing`, `selectedAction_square` | `BF4ExactSlabSiteSelectedHeatAction.lean:186`, `:214` | Exact coefficient/Haar identities, including W once. |
| `fixedHeatCertificate`, `selectedAction_nonnegative` | `BF4ExactSlabSiteSelectedHeatAction.lean:240`, `:249` | Constructed original central certificate and reflected positivity. |
| `originalChain_nonnegative` | `BF4ExactSlabFixedSpatialChainReflectionPositive.lean:50` | Actual chain instance, with no supplied symmetry premise. |
| `originalChain_finiteValue_nonnegative`, `originalChain_expectation_nonnegative` | `BF4ExactSlabFixedSpatialChainReflectionPositive.lean:61`, `:76` | Same partition and existing fixed-chain cutoff limit. |
| `placed_reflection`, `placed_oneSided` | `BF4ExactSlabFixedSpatialWindowReflection.lean:193`, `:240` | Literal physical face reflection and one-sidedness. |
| `windowRatio_span_mul_originalFiniteValue` | `BF4ExactSlabFixedSpatialWindowProbeSpan.lean:215` | Full signed bilinear original-observable pin. |
| `placedSpan_reflection`, `placedSpan_oneSided` | `BF4ExactSlabFixedSpatialWindowReflectionPositive.lean:98`, `:114` | Reflection/locality for the entire signed sum. |
| `reflectedWindowRatio_nonnegative`, `reflectedWindowLimit_nonnegative` | `BF4ExactSlabFixedSpatialWindowReflectionPositive.lean:144`, `:176` | Fixed observable, all diagonal terms, and the existing time limit. |

## Parameter and scope boundaries

- The group realization is the actual SU(2) quaternion-Haar/character one.
- Finite positivity assumes 0<w<1 and the explicit cutoff threshold
  headCutoff(w). No small-nome restriction is imposed.
- The time-limit theorem fixes nome, spatial width, half-window, signed
  schedule sum and retained cutoff stage. It uses the old time modulus,
  whose q and prefactor still depend on nome and width.
- Fixed-chain cutoff removal and fixed-cutoff time passage are separately
  proved. Joint removal, interior cutoff compatibility and interchange are
  not supplied by these theorems.
- Only the selected fixed-width action is used, not the full growing-box
  action or its interacting marginal.
- The time-limit RP domain is the real rational span of scheduled spatial
  face-character products, not all supported coordinate polynomials or a
  proved complete gauge-observable algebra.
- Depth zero keeps just the central spatial weight. h=0 keeps the probes
  on the fixed slice. Width zero has no selected face factors, but does
  NOT imply the inclusive-fringe source coordinate carrier is empty.

## Next mathematical frontier and existing consumers

The next step is the MIXED reflected form on a compatible half-space
observable carrier, not another assumed-positive bundle. In particular,
enlarging the centered window means h->h+1 AND shifting every offset j->j+1.
Changing h alone moves the observables relative to the reflection plane.
The source shift pin followed by the existing `windowLimit_pad_left` and
`windowLimit_pad_right` should be the next proof to supply, not an assumption:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowState.lean:193` and `:180`.
Mixed-form symmetry/bilinearity and carrier-equivalence compatibility remain
to be composed before quotienting.

The existing generic `CRealGNSFormData` in
`lean/YMGap/Continuum/BF4PhysicalCutoffLinearGNSForm.lean:343` already has a
CReal-valued positive symmetric bilinear form on a rational module.
`CRealPreHilbertData` in
`lean/YMGap/Continuum/BF4PhysicalCutoffLinearRadicalDescent.lean:189` adds sharp
Cauchy--Schwarz and radical descent. These interfaces are possible consumers;
their old concrete physical cutoff instances are NOT substituted for this
new time-limit form. In particular, the Q'-valued `GNSData` in
`PositiveTimeOSRoot` at `lean/YMGap/Continuum/CanonicalOSRoot.lean:268` is not
automatically the present CReal-valued form.

No physical OS quotient/completion, time-shift transfer/vacuum, same-operator
connected-correlation gap, width/spacing-uniform estimate, continuum QFT or
all-group Clay theorem is constructed here. No canonical frontier field or
analytic premise changed. Independent review confirmed the complete signed
sum and fixed-observable placement; these next-step suggestions are planning,
not additional checked theorems.

## Verification boundary

Six focused checks passed all 63 public axiom gates within
{propext, Quot.sound}; the schedule/mirror-span maps are axiom-free. Checks
were serialized through the safe-build skill, one worker with a 20 GiB hard
limit. Fresh process/swap preflight preceded every check; observed swap stayed
7077.19 MiB and no competing compiler/test was found. No limits were raised.

Initial targeted checks exposed list-append association, missing namespace
opens, a tuple projection needing explicit simplification, and method-name
resolution between reflection images and coefficient equality. Final outputs
are clean. No literal proof holes, custom axioms or classical input were added.
Six selective-root imports were added; root/full-tree/full axiom audit was NOT
run. No routine literature scan occurred.

All commands used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| BF4ExactSlabSiteSelectedHeatAction | 24 | `a8e89998d8018519274667007f3bc74f0ec74fc5b5fcc995e32d7549c32cdd9b` |
| BF4ExactSlabFixedSpatialChainReflection | 13 | `6cb9c54509748c5369a3c362c7a4d8643fd0205bab32a54e2b7d86443ff2fb24` |
| BF4ExactSlabFixedSpatialChainReflectionPositive | 3 | `4f195a7b2c498c0207389e0bd637e13e51939dc90e8d8755765e4b38dbbadc29` |
| BF4ExactSlabFixedSpatialWindowReflection | 11 | `6c26f857ab19fdee692ab76f26439f51bdb115f2e26f4a2e75d136524dbc6007` |
| BF4ExactSlabFixedSpatialWindowProbeSpan | 5 | `55ca7308c9e1bd317dbafe777edd82c25833fa59c2acd6669e2863ceee8bbb2b` |
| BF4ExactSlabFixedSpatialWindowReflectionPositive | 7 | `b5f62752c1877e15a2468f89538025ecad4bc198874bac5ac4b9bed91bdba2a4` |
