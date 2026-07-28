# BF4 observable-matched trajectory: first exact step

**Date:** 2026-07-26
**Status:** finite matching and U(1) reflection/CP proved; fixed-nome
signed-charge tails, off-diagonal finite-atlas score tubes, outer-cutoff
nesting/tensor control, located-argmin stability, and the conditional matched-AF
consumer are formalized; the finite-Fubini/Haar outer lift is proved, while
fixed-nome normalized Boolean-event convergence is proved; outer
exponent-Gram transport, spacing-uniform score tubes, the Yang--Mills cubic
law, and physical spacing remain open

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

## 4. Scheduled finite trajectory and atlas order

`BF4ObservableMatchedTrajectory.lean` iterates the one-step constructor over
supplied schedules of corrected-slab geometries, positive candidate atlases,
and observables. Starting from a strictly positive coupling, every successor
is produced recursively by the exact argmin. At every finite step the module
proves:

- strict positivity and membership in that step's atlas;
- global minimality of the physical matching defect;
- the exact comparison trichotomy against the preceding coupling's fourth
  power;
- transfer of any certified candidate error bound to the selected error.

For two finite atlases \(A\subseteq B\), the selected defects obey the exact
order bound
\[
  D_O(s,s'_B)\le D_O(s,s'_A).
\]
If a `DefectSafeRefinement` additionally certifies that the old selected
coupling remains a minimizer after enlargement, the two optimal defects are
semantically equal.

This is the spacing-finite refinement theorem, not an atlas-limit theorem.
Monotonicity of scalar defects alone does not imply convergence of their
argmin couplings. The missing implication requires identifiability or
coercivity of the physical separator observable, with an explicit
constructive modulus. The exact consumer is already proved:
`couplingAt_succ_distance_le_of_identifiability` converts a bound
\[
  |u-u_*|\le C\,D_O(s,u)
\]
and a candidate defect certificate \(D_O\le\varepsilon\) into
\[
  |s'_{\!A}-u_*|\le C\varepsilon
\]
for the recursively selected coupling. The coercivity inequality itself is
the remaining Yang--Mills analysis.

## 5. Constructive audit

The new declarations are computable and use no `Classical.*`,
`native_decide`, `sorry`, custom axiom, or `noncomputable` declaration.
Their axiom profiles are within the project gate
`{propext, Quot.sound}`. The root build and frontier statement guards pass.

## 6. Precise residual

This closes the *constructor* for one exact finite step, not the physical
trajectory. The remaining obligations are now concrete:

1. Remove the finite exponent-coordinate and spin/charge cutoffs with a
   quantitative modulus, and prove that the resulting Gram pencil has the
   required located physical separator.  The finite all-coordinate
   regrouping is now exact.
2. Prove reflection positivity and cutoff convergence for the
   gauge-constrained U(1) Gram, so that its finite comparison branch has a
   stable continuum meaning.  The same-geometry signed-charge law and its
   normalized pushforward are now exact.
3. Supply refining positive atlases near \(s=1\) and prove a constructive
   Cauchy modulus for their argmins from a Yang--Mills-specific
   identifiability/coercivity estimate. Finite iteration and defect
   antitonicity are now proved.
4. Prove the weak-coupling marginal defect envelope, with the non-abelian and
   abelian signs separated.
5. Only then instantiate `AFEnvelope` on this action-linked trajectory and
   apply `BareAFImpliesLinearFloor`.

Thus the old free-flow obstruction has been removed at \(M=1\), while the
remaining Clay-level content is exposed rather than assumed.

## 7. Exponent-Gram and U(1) milestone

`BF4ExponentGramMatchedOneStep.lean` replaces the pointwise-observable
surrogate by the actual reflected-law bilinear form
\[
 \sum_\phi f(\phi_-)\,g(\theta\phi_+)\,\mu(\phi).
\]
Lower-half states are grouped by their exact total Casimir exponent.  At
fixed cutoff the module constructs the complete Cartesian list of exponent
coordinates, proves that every bounded lower state occurs below its computed
ceiling, and minimizes the full finite \(L^1\) Gram-entry discrepancy.  The
normalized-mass form is proved equal to the existing full OS quadratic, so
the actual diagonal entries used by the matcher are nonnegative.

`BF4U1SameCarrierPushforward.lean` constructs the control theory on the same
corrected-slab cells.  Alternating natural labels encode signed charges,
link factors impose exact oriented charge conservation, and face factors are
\(w^{q^2}\).  The vacuum proves strict partition positivity.  The dyadic
block is literal addition of the four nondegenerate face charges; a proved
\(|q_1+\cdots+q_4|\le4K\) bound shows that its totalization fallback is never
used on a physical fine state.  Its supported Dirac kernel and blocked mass
are nonnegative and exactly normalized.

Finally `BF4SU2U1ExponentGramDiscriminator.lean` runs both physical laws
through the same finite exponent-coordinate list and positive coupling
atlas.  It returns a computational `Type`-valued certificate for the exact
finite ordering of the independently matched SU(2) and U(1) couplings.
No weak-coupling sign is claimed until cutoff/spacing convergence and a
located separator bound are proved.

## 8. All-label U(1) reflection positivity and block CP order

The finite U(1) control theory now has a genuine reflection-positive
same-carrier interpretation.  `BF4U1ReflectionCovariance.lean` proves the
orientation-correct action of time reflection on signed face charges:
spatial faces retain their charge and time-oriented faces acquire charge
conjugation.  The full Haar-constrained physical term and bounded carrier
are invariant under this involution.

At a fixed central boundary,
`BF4U1TwistedReflectionGram.lean` factors the physical weight into a
nonnegative boundary weight and two half amplitudes.  The orientation sign
makes the raw kernel a charge-conjugation-twisted Gram.  This is not discarded:
global charge conjugation is proved to permute the exact half-state carrier,
and every conjugation-even coefficient is regrouped into an ordinary
weighted sum of squares.

`BF4U1TwistedPhysicalReindex.lean` then proves that lower state, central
boundary, and reflected upper state form an exact Cartesian reindexing of
the complete bounded physical carrier.  Consequently both the unnormalized
physical quadratic and the normalized-mass quadratic are nonnegative for
every conjugation-even half observable.

Heat-exponent indicators and arbitrary finite rational linear combinations
of them are conjugation-even.  `BF4U1ExponentGramPositivity.lean` therefore
proves positivity of their genuine all-label normalized quadratics and
identifies the existing coarse discriminator diagonal with this
orientation-correct form.

Finally `BF4U1BlockReflectionCP.lean` proves that the direct four-face BF4
charge sum:

- intertwines fine and coarse time reflection;
- commutes with global charge conjugation;
- is exactly lumpable on lower and reflected-upper half observables; and
- sends the fine normalized law to the already-defined blocked mass through
  the supported deterministic kernel.

Thus the blocked reflection quadratic is exactly the fine reflection
quadratic of the pulled-back observable.  Arbitrary finite exponent packets
of the actual blocked law are nonnegative, and every diagonal
`u1BlockedExponentGramEntry` used by the SU(2)/U(1) discriminator is
nonnegative.  This closes the finite-cutoff same-carrier CP-order
obstruction constructively; every new dependency gate is contained in
`{propext, Quot.sound}`.

The next analytic layer is now split precisely. The actual signed-label
one-coordinate heat series has a fixed-nome quantitative cutoff, and a
separate finite-slab theorem amplifies any one-charge tail through the genuine
normalized reflection quadratic and deterministic BF4 block. A located-margin
consumer also stabilizes the literal SU(2)/U(1) argmins once uniform score
tubes are supplied. What remains is to connect these layers into
spacing-uniform physical score tubes, prove the corresponding SU(2) tail and
Yang--Mills separator, and derive the cubic AF and spacing certificates on the
exact matched trajectory.

## 9. Fixed-nome U(1) cutoff and finite-slab amplification

`U1SignedChargeHeatTail.lean` proves a constructive Cauchy modulus for the
actual label order \(0,+1,-1,\ldots\), using
\(2w^{M+1}/(1-w)\). `BF4U1ExponentGramCutoffTailBridge.lean` lifts a supplied
one-charge tail through the genuine normalized slab sum, its exponent-Gram
diagonal, and the deterministic BF4 block. The amplification is the finite
state count. `BF4U1SignedChargeTailInstantiation.lean` supplies that datum
constructively for every fixed slab with \(0<w<1\), rescaling the tolerance by
the exact positive state count before selecting the signed-charge cutoff.
`BF4U1ExponentGramOffDiagonalCutoff.lean` extends this to arbitrary
left/right exponent coordinates after the deterministic BF4 pullback.
`BF4U1ActualExponentGramScoreTube.lean` pays both blocked/coarse entry errors
and the finite-coordinate count, then takes a constructive maximum over the
finite atlas. It produces an actual `AtlasScoreTube` for the literal U(1)
score at fixed outer charge carrier, provided the fine nome and all atlas
candidates are strictly below \(1\). These results do not yet provide an
outer-carrier limit or a cutoff uniform as \(w\to1\).

## 10. Located stability of the matched comparison

`BF4ExponentGramLocatedStability.lean` proves that a two-sided uniform score
error \(\varepsilon\) cannot change the finite argmin when the named limiting
minimizer has margin \(\delta>2\varepsilon\). The theorem simultaneously
stabilizes the exact SU(2)/U(1) comparison branch. It is a consumer: the
limiting scores, cutoff score tubes, and located Yang--Mills separator margin
are not constructed by the module.

## 11. Conditional matched-AF consumer

`BF4MatchedPhysicalAFBridge.lean` routes its trajectory weight through a
literal finite observable- or exponent-Gram-matching argmin rather than the
Padé formula. Its parameterized geometry, atlas, coordinates, and observable
are nevertheless supplied data, so this wrapper does not certify that the
family is the genuine continuum trajectory. Given a
`CubicMarginLaw` for that output and a separate `PhysicalSpacingEnvelope`, it
constructs an `AFEnvelope` and invokes `BareAFImpliesLinearFloor`. Neither
physical certificate is inhabited here, so this is not an instantiation on
the nonperturbative four-dimensional continuum trajectory.

## 12. Outer-cutoff directed system and tensor tail

The fixed-slab state-count amplification is not uniform when a separate outer
charge carrier grows. `BF4U1OuterCutoffNesting.lean` proves the exact
replacement algebra: the smaller carrier is the old-label filter of every
larger carrier, the physical term is cutoff-independent, and the larger
partition is the smaller partition plus a nonnegative new sector.

`BF4U1OuterCutoffUniformTensorTail.lean` then avoids counting outer states.
For fixed \(0<w<1\), it bounds the signed one-coordinate shell above \(M\)
uniformly in every outer \(K\ge M\), supplies a cutoff-independent
one-coordinate heat ceiling, and tensorizes them through the recursive union
envelope
\[
  E_0=0,\qquad E_{d+1}=T_w(M)H_*(w)^d+H_*(w)E_d.
\]
`BF4U1OuterCutoffFiniteFubiniTail.lean` completes the finite Fubini step on
the literal `boundedEdgeLabellings` carrier and proves that the genuine
Haar-constrained new-sector mass is no larger than this envelope. In
particular, for every \(K\le L\),
\[
  Z_{L\setminus K}\le E_{\#\mathrm{faces}}(w,K),
  \qquad Z_L\le Z_K+E_{\#\mathrm{faces}}(w,K).
\]
`BF4U1OuterCutoffTensorTailModulus.lean` additionally factors \(E_d\) as
the one-charge closed tail times a fixed finite-dimensional coefficient and
constructs an explicit retained-charge cutoff after rescaling the requested
tolerance by \(1+C_d(w)\). The result is uniform in the later outer cutoff,
but remains fixed-nome and fixed-face-count.

`BF4U1OuterCutoffNormalizedEventTail.lean` then proves the exact nested
quotient algebra
\[
 \left|\frac{a}{d}-\frac{a+b}{d+n}\right|\le n
 \quad(a\le d,\ b\le n,\ d\ge1),
\]
and applies it to every Boolean event of the canonical normalized slab law.
The probability change from cutoff \(K\) to any \(L\ge K\) is bounded by the
same tensor envelope with constant \(1\); the tensor cutoff therefore gives
an explicit normalized-event Cauchy modulus.

The next exact bridge is to construct the corresponding limit object and
transport this modulus through the cutoff-dependent BF4 block-pullback and
coarse exponent-Gram coordinates. The current theorem remains fixed-nome,
fixed-half, and finite-volume.
