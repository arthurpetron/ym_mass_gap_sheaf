# BF4 observable-matched trajectory: first exact step

**Date:** 2026-07-26
**Status:** constructive cutoff-one step proved; weak-coupling trajectory and
AF envelope remain open

## 1. Why this step is necessary

`BF4BlockOperatorExtensionalFence.lean` proves that the existing
`SlabScalePair.couplingFlow` field is not recoverable from the raw corrected
slab operator: extensionally different stored flows can produce the same
kernel. Consequently a physical BF4 trajectory cannot be obtained by reading
that field. The next coupling has to be *derived from the pushed law*.

The first executable realization is now
`BF4ObservableMatchedOneStep.lean`. It starts from the exact globally
link-glued cutoff-one physical pushforward and defines the next coupling by
matching a gauge-invariant observable.

## 2. Exact construction

Fix:

- a fine rational coupling \(s\ge 0\);
- a corrected-slab coarse half-extent \(h\);
- the forced fine half-extent \(2h+1\);
- a finite nonempty atlas \(A\) of strictly positive coarse candidate
  couplings;
- a rational observable \(O\) on the common coarse edge-labelling space.

The geometry satisfies the exact blocking relation
\[
  2\,\mathrm{centralExtent}(h)+1
  =
  \mathrm{centralExtent}(2h+1).
\]
For each \(s'\in A\), the module computes
\[
  D_O(s,s')
  =
  \left|
    \mathbb E_{\operatorname{push}_{s\to s'}}[O]
    -
    \mathbb E_{\operatorname{coarse},s'}[O]
  \right|
\]
in exact `Q'` arithmetic. The first term uses the actual total physical
cutoff-one kernel and its blocked normalized mass; the second uses the
normalized coarse Gibbs mass at label cutoff four.

A constructive finite argmin returns
\[
  s'_A=\operatorname*{argmin}_{u\in A} D_O(s,u)
\]
together with membership and minimality certificates. The physical scale
pair and kernel are then rebuilt from this selected coupling. In particular,
the output coupling is a theorem of the observable-matching problem rather
than an input `couplingFlow`.

## 3. Exact discriminator

The module also returns a `Type`-valued computational certificate for exactly
one of
\[
  s'_A<s^4,\qquad s'_A\simeq s^4,\qquad s^4<s'_A.
\]
Here \(s^4\) is only the exact two-dimensional heat-kernel
self-reproduction reference. No four-dimensional self-reproduction rule is
assumed.

The certificate is deliberately branch-neutral. Its construction proves
that the proposed SU(2)/U(1) discriminator is an exact finite decision problem
once the physical observable and candidate atlas are supplied; it does not
invent the SU(2) sign.

## 4. Constructive audit

The new declarations are computable and use no `Classical.*`,
`native_decide`, `sorry`, custom axiom, or `noncomputable` declaration.
Their axiom profiles are within the project gate
`{propext, Quot.sound}`. The root build and frontier statement guards pass.

## 5. Precise residual

This closes the *constructor* for one exact finite step, not the physical
trajectory. The remaining obligations are now concrete:

1. Instantiate \(O\) with the DP exponent-granularity reflection-positive
   separator observable, rather than an arbitrary rational labelling
   observable.
2. Build the U(1) physical pushforward on the same geometry and run the same
   comparison harness.
3. Supply refining positive atlases near \(s=1\), prove stabilization or a
   constructive Cauchy modulus for their argmins, and then iterate the derived
   step.
4. Prove the weak-coupling marginal defect envelope, with the non-abelian and
   abelian signs separated.
5. Only then instantiate `AFEnvelope` on this action-linked trajectory and
   apply `BareAFImpliesLinearFloor`.

Thus the old free-flow obstruction has been removed at \(M=1\), while the
remaining Clay-level content is exposed rather than assumed.
