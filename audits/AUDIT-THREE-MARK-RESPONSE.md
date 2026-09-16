# Exact three-mark cancellation in the original face response

Date: 2026-09-15 (America/Los_Angeles). Base: `ceebcbf`.

PROGRESS: exact original-action cancellation and a cutoff-limit invariance
theorem. OPEN: a spatially decaying bound on the remaining signed response.
The whole-project target remains constructive continuum Yang--Mills on R^4,
the required QFT axioms, and a positive physical Hamiltonian gap for every
compact simple group. No canonical frontier atom is closed here.

## 1. Mathematical argument

Write C_S(p,q)=M_S(pq) Z_S-M_S(p)M_S(q) for the original unnormalized
connected numerator, and let f be the inserted full heat face. The existing
response is exactly

    response_S = C_(S+f) * Z_S^2 - C_S * Z_(S+f)^2.

This is `BF4ExactSlabConnectedFaceResponse.response_identity`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:90`.
The action, probes, face factor and partition functions are the existing
ones; no reference law or conditional-update operator is substituted.

Three cases now have proved cancellation:

1. A literal link cut separates p from q AND the inserted face. The old
   and new connected numerators both vanish by disjoint Haar factorization.
2. The symmetric cut separates q from p AND the inserted face.
3. A cut separates the inserted face from BOTH probes. Here the probe
   covariance need NOT vanish. If S=A++B and insertion is on the B side,

       C_S     = C_A * Z_B^2,       Z_S     = Z_A * Z_B,
       C_(S+f) = C_A * Z_(B+f)^2,   Z_(S+f) = Z_A * Z_(B+f).

   Substitution cancels the response exactly, with C_A retained.

All retained action faces are included in these cuts. Disjointness of
high-spin tails alone is not sufficient. The underlying exact factorization
is `BF4ExactSlabDisconnectedHaarCancellation.partition_factorizes`,
`lean/YMGap/Continuum/BF4ExactSlabDisconnectedHaarCancellation.lean:53`, and
`BF4ExactSlabSpectatorResummation.numerator_spectator_factorizes`,
`lean/YMGap/Continuum/BF4ExactSlabSpectatorResummation.lean:79`.

## 2. New declarations and actual consumer

| Declaration | Source | Checked content |
|---|---|---|
| `BF4ExactSlabResponseProbeSeparation.response_zero_of_left_separator` | `lean/YMGap/Continuum/BF4ExactSlabResponseProbeSeparation.lean:101` | The p-separation case for the same old/new actions. |
| `BF4ExactSlabResponseProbeSeparation.response_zero_of_right_separator` | `lean/YMGap/Continuum/BF4ExactSlabResponseProbeSeparation.lean:113` | The q-separation case. |
| `BF4ExactSlabResponseInsertionSeparation.response_zero_of_insertion_separator` | `lean/YMGap/Continuum/BF4ExactSlabResponseInsertionSeparation.lean:101` | The insertion-separation case without assuming zero probe covariance. |
| `BF4ExactSlabThreeMarkResponseExpansion.responseCoefficient` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean:45` | Finite differences of the existing response as its old action list varies. |
| `BF4ExactSlabThreeMarkResponseExpansion.responseKeep` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean:49` | Three computed separator tests, with the same fixed marked supports. |
| `BF4ExactSlabThreeMarkResponseExpansion.responseSelections` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean:54` | Actual positional selection list filtered by those tests. |
| `BF4ExactSlabThreeMarkResponseExpansion.responseCoefficient_zero_of_discard` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean:89` | A found separator kills the coefficient because it restricts to every subselection. |
| `BF4ExactSlabThreeMarkResponseExpansion.response_filtered` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean:105` | Exact reconstruction of the original response as the filtered signed sum. |
| `BF4ExactSlabThreeMarkResponseExpansion.retained_three_no_cuts` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean:115` | No enumerated cut separates any of the three marked bipartitions in a retained selection. |
| `BF4ExactSlabThreeMarkResponseExpansion.covariance_response_bound_of_filtered` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean:132` | A SUPPLIED bound on that signed sum passes to the same original cutoff-limit covariance. |
| `BF4ExactSlabThreeMarkResponseExpansion.covariance_invariant_of_insertion_separator` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean:160` | Actual cutoff-removed covariance is unchanged by a disconnected spectator insertion, for every rational 0<w<1. |

The existing analytic consumer is
`BF4ExactSlabConnectedFaceResponse.covariance_response_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`.
The new general consumer changes its finite hypothesis only by a PROVED
equality; it does not manufacture the missing coefficient. Both partition
squares stay in the finite estimate. Only p and q remain fixed through the
limit; the cutoff-dependent inserted heat remains inside the finite sum.
The invariance corollary supplies the zero bound using the proved separator
cancellation, then applies the existing constructive CReal uniqueness lemma.
No new limit, reciprocal, choice or selected representative is introduced.

## 3. Scope and checks against overstatement

- The raw identities hold for arbitrary rational w and finite K. Positive
  physical-law/cutoff-limit claims use the explicit 0<w<1 hypotheses and
  physical face-membership guards of the existing expectation construction.
- Repeated identifiers are permitted. Appending an already-present id
  inserts another factor; it is NOT set union. Positional multiplicities
  are preserved by the finite Mobius identity.
- Empty selections are not discarded automatically. The inserted face can
  already couple overlapping probes with no old interaction face selected.
- The support lists of general polynomial probes need not themselves be
  connected. Failure of the three cut searches must not be restated as a
  claim that one literal physical component meets all three support lists.
- Detached spectator components can remain in raw coefficients. This
  increment does not replace them by one, bound them absolutely or supply
  their full response-family resummation. Existing two-probe spectator
  resummation is reused only where its actual hypotheses hold.
- All cancellations are signed and precede the absolute-value estimate.
  No upper bound for the remaining coefficients or their normalized sum is
  proved. No new non-abelian coercivity mechanism or beta-uniform gap is
  asserted by these structural Haar/factorization arguments.

NEXT: a useful spatial bound on the surviving original signed sum, with
explicit coupling/scale dependence and the required cutoff/volume control.
Preserve or exactly resum spectator partition factors before estimating.
The previous absolute-window obstruction still excludes that generic shortcut;
this exact filter does not repair its constants. Temporal composition on a
single stationary physical carrier, physical spacing/time calibration,
continuum QFT/nontriviality and the all-group target remain open.

## 4. Parallel review and an intentionally unbuilt alternative

Two agents independently supplied the probe and spectator-insertion proofs.
The parent integrated their finite-difference filter and actual limit
corollary. A third agent independently reviewed the three modules, including
overlapping supports, duplicate ids, empty selections, hereditary separators
and the still-present spectator factors.

That review also rejected an unnecessary new dual-self-test separation
wrapper: `BF4ExactSlabPlaquetteNullQuotient.null_iff_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteNullQuotient.lean:119`, already
gives quotient separation. `testLimit (lower f) e` uses the same expression
as the existing form, by `BF4ExactSlabDressedDualTestCutoffLimit.testLimit`,
`lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:274`, and
`BF4ExactSlabPlaquetteReflectedForm.form`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean:49`.
Packaging that again would not prove physical transfer injectivity or
same-carrier temporal composition. No such additional module was built.

## 5. Verification

Six focused serialized launches used `scripts/safe_lean_build.py`, one worker,
and the mandatory 20 GiB ceiling. Probe separation passed first check.
Insertion separation needed its existing support namespace opened. The
combined module needed explicit arguments to the existing Boolean lemma,
then passed; the added cutoff-limit invariance corollary also passed.
All three final logs are clean. All 11 public gates report exactly
{propext, Quot.sound}; no new custom axiom, literal hole or classical input.
No existing statement or canonical frontier field changed.

Direct dependency artifacts were newer than their sources; no dependency
rebuild or raised limit. Three root imports were added. Root/full-tree
compilation and a full axiom audit were NOT run. Final local log hashes:

- `/tmp/BF4ExactSlabResponseProbeSeparation.log`:
  `377fc49aa0b04d17e70e209efdbd644345a27f940df21ba4e7732056cdca6c2f`.
- `/tmp/BF4ExactSlabResponseInsertionSeparation.log`:
  `5d5fc8e8656a90df8ecf749fcda7739b9ced943c9f071ba808278add7f7543a8`.
- `/tmp/BF4ExactSlabThreeMarkResponseExpansion.log`:
  `511ca3ae99e76eea014c789302cd3fc87ddc98526780cfd371923313bfa97b7a`.

CI remains manual-only. The whole-project goal remains active.
