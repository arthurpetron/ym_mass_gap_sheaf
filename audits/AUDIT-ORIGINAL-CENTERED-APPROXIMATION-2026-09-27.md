# Centered approximation in the original full-action completion

## Constructed result

Given a Cauchy representative X in the existing original fullData form F,
apply the existing finite mean subtraction to every X.seq(n). The resulting
`centeredCauchy X` is Cauchy with EXACTLY X.modulus. Every output term is
orthogonal to the actual constant U. No input term is assumed centered.

If the completed class of X satisfies `<[X],embed(U)>_F=0`, then the
centered sequence represents that same class. `centeredNullModulus` returns
Type-level closeness data with the explicit rate

    X.modulus(epsilon/10).

This is a rate for squared-distance closeness between X and its centered
sequence. It is not a separately returned finite-mean convergence rate.
The construction acts on a supplied representative; it does not select one
from an arbitrary quotient. Its carrier, partition and centering operation
are the original ones at K=headCutoff(w)+stage, 0<w<1 and finite extent.

## Proof and normalization

The existing exact identity `B(Cp,Cq)=B(Cp,q)` gives self-pairing of the
centered difference against the original difference. Positivity of their
residual square proves nonexpansiveness without changing the form.
Consequently centering preserves the original Cauchy modulus.

The exact correction norm is

    dist_F(p,Cp)^2 = inversePartition * B(p,U)^2.

The constant has squared norm Z, not one. Completed orthogonality implies
that the finite pairings B(X.seq(n),U) tend to zero; the displayed correction
norm therefore tends to zero. The existing `recoverNullModulus` obtains its
computable rate from the two Cauchy moduli. The existential eventual index
is used only within a proposition proof, never extracted into data.

| Declaration | Source |
|---|---|
| `centered_distSq_le` | `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:84` |
| `centeredCauchy` | `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:98` |
| `centeredCauchy_modulus` | `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:105` |
| `centeredCauchy_term_centered` | `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:108` |
| `self_center_distance` | `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:113` |
| `centeredNullModulus` | `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:182` |
| `centeredNullModulus_modulus` | `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:187` |
| `centeredCauchy_same_class` | `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:192` |

## Consumer and open boundary

The result supplies actual centered dense approximations for a future
original-action polynomial coercivity estimate. It proves neither that
estimate nor a completed lower energy inequality. The next analytic work
remains a useful retained-exterior signed numerator/two-star bound or a
sharper direct centered estimate. No new conditional gap wrapper is needed
to stand in for that missing work. Physical scaling, nontrivial continuum
survival, full same-theory QFT structure and every-group Clay closure remain
open. Canonical chart markers are unchanged.

## Verification and collaboration

All eight printed axiom dependencies passed a focused monitored check with
one worker capped at 20 GiB, within `{propext, Quot.sound}`. No errors or
warnings in the final check. The first check of the final direct proof
found an unavailable scalar congruence name and two incorrectly named
arguments; these were corrected without changing the statements.

Sol explored a scalar-rescaled auxiliary-form draft but did not verify it;
that draft was replaced locally by the direct original-form proof above.
A separate Sol review confirmed genuinely completed orthogonality, correct
unnormalized partition factor, no representative choice and the exact
meaning of the recovered null rate. No normalized form was retained.
No new source hole, axiom, analytic field or canonical frontier edit. No
full-tree build/audit or routine literature listing refresh was run.
