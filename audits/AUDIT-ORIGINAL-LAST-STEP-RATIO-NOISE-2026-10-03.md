# Original last-step ratio-noise and actual-source reconstruction

## Result and boundary

Three focused checks passed fifteen permitted axiom gates.

The original last-step score can be controlled by the conditional noise of
the actual incoming ratio, with a computed geometric reconstruction error.
The actual outgoing reciprocal removes the leading A² without division.
The resulting bound joins the existing exact-gradient consumer, retaining
the outgoing reciprocal correction and the original source and action.
This supplies a finite local representation of the cost, not a useful
relative noise estimate on a changing family. No continuum/Clay node closes.

## Forward: one original transition, not accumulated-history noise

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRatioNoise.lean:58`
`lastStepRatioNoise` uses the original T and incoming terminal a=g_d:

    A=T(a), b_phi=T(a*phi), N(phi)=A*T(a*phi²)-b_phi².

`:62` `lastStepRatioNoise_pin` pins the literal one-step outputs.
`:73` `lastStepRatioNoise_certificate` constructs N>=0 under the original
positive K*V*a law. `:103` `lastStepRatioNoise_score_certificate` gives

    Score(A,b_phi)² <= L(w)²*A²*N(phi).

It specializes the original block-score theorem at one step, with supplied
center zero only to remove the generic shifted-polynomial wrapper; it does
not reset the actual source's OWN center. The full K,V,a factors remain.
There is no claimed numerical ordering against the older paired budget.
Here L(w)=relativeCap(w,32); score bounds retain 0<w<1,
K>=relativeCutoff(w,32), an active output block, and an angular coordinate
plane in that block. Noise positivity needs the existing headCutoff guard.
The reconstructed source is supported on the original finite slice.

## Reconstruction: explicit error, not a source-norm inverse

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepErrorBudget.lean:56`
`lastStepErrorBudgetMultiplier` constructs, for arbitrary supported signed a,

    P(a)=2*(T1)*[(Ta)²+(T1)*T(a²)].

`:62` `lastStepErrorBudgetMultiplier_supported` and `:77`
`lastStepErrorBudgetMultiplier_certificate` supply support and positivity.
`:156` `lastStepScoreBudget_error_certificate` constructs

    J(a,e) <= P(a)*T(e²).

Its positive difference is the exact sum

    (T1)*I[K*V*(lift(Ta)*e+lift(Te)*a)²]
      +2*(T1)*T(a²)*[(T1)*T(e²)-(Te)²].

The second bracket is the actual Schur certificate. Neither a nor e is
required positive; no variance or excitation norm is divided out.

All remaining new declarations are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRatioRefinement.lean`.
`:71` `incomingNumerator` keeps c=T^r(g_n*psi). `:87` `incomingRatioError`
keeps a=g_(n+r) and phi_k=blockConditionalRatio(n,r,psi,k), so e_k=c-a*phi_k.
This is the INCOMING reciprocal, not the outgoing (n,r+1) ratio.
`:103` `incomingRatioError_square_certificate` constructs

    e_k² <= rho^(2k)*c²,    rho=mixRate(w,width),

as a polynomial cone certificate before selecting a weight. The depth
guard 1<=n+r is explicit. The fresh positive window and its finite
reciprocal are constructed from original messages, not assumed analytic
inputs. `:166` `incomingErrorEnvelope` keeps P(a)*T(c²). `:183`
`incomingRatioError_budget_certificate` uses original transfer positivity
to obtain J(a,e_k)<=rho^(2k)*P(a)*T(c²).

## Backward join: actual score, outgoing multiplier, exact gradient

`:281` `original_lastStep_incomingRatio_score_square_le` uses the exact split

    Score(A,Tc)=Score(A,T(a*phi_k))+Score(A,T(e_k)).

An asymmetric square triangle retains leading factor 1+eta and correction
factor 1+1/eta. For any certified SAME output weight M its bound is

    H[M*Score(A,Tc)²]
      <= (1+eta)*L²*H[M*A²*N(phi_k)] + rho^(2k)*C(M),
    C(M)=(1+1/eta)*L²*H[M*P(a)*T(c²)].

`:274` `incomingScoreErrorCoefficient` defines that actual coefficient.
`:481` `incomingScoreErrorCutoff` computes a geometric cutoff, without
dividing by C or a source norm. `:489`
`original_lastStep_incomingRatio_score_tolerance` makes the correction <=
epsilon for all later k in a FIXED window/weight/source. This is an
additive tolerance, not epsilon times the surviving norm.

`:359` `original_lastStep_incomingRatio_reciprocal_score_le` constructs the
ACTUAL outgoing window certificate 1-(A*G_l)²>=0. Multiplication by N>=0
and the original W gives

    H[W*G_l²*A²*N(phi_k)] <= H[W*N(phi_k)].

No A inverse or weight substitution is used. Incoming k and outgoing l are
independent. `:431` `original_lastStep_incomingRatio_gradient_le` feeds
this to the existing
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreBudget.lean:71`
`exact_score_reciprocal_plane_le`. The full finite cleared gradient is bounded
by (1+sigma)*(1+eta)*L²*H[W*N(phi_k)] plus the geometric incoming correction
and the actual outgoing reciprocal correction. Choosing W=Vbar² retains
that literal projected weight; Vbar² is not silently identified with V.

## Unpaid analytic input and next frontier

The complete signed consumer remains
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:324`
`original_block_exact_score_cost_relative_tolerance`, with its actual
`:218` `exactScoreSignedBulk` and BOTH signed Taylor terms. The macroscopic
response consumer remains
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio`. The alternative initial-energy consumer
is unchanged at
`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`
`completed_reference_ratio`.

The next analytic input is useful control of the actual interacting
H[Vbar²*N(phi_k)] and the retained signed remainder difference against the
SAME surviving norm/partition on a JUSTIFIED changing family. None is
proved here. A bare reference-kernel Poincare estimate cannot be substituted
for the original conditional K*V*a law. The fixed-window error coefficient
is not a scaling-uniform coefficient. The fixed-M cutoff does not by itself
give a diagonal onset when the outgoing degree l also changes. Zero input
is harmless; a zero surviving norm is not cancelled or equated with zero
input. No exact martingale-weight identity or spatial-weight conversion is
asserted. Nontrivial survival, physical calibration, canonical OS/continuum,
full QFT and every compact simple group remain OPEN.

## Verification

Serialized monitored checks, one compiler, 20 GiB cap, 12 GiB OS reserve:

- RatioNoise: exit 0, four permitted axiom gates;
  `/private/tmp/ym-last-step-ratio-noise-20261003.log`.
- ErrorBudget: accepted second check exit 0, four permitted axiom gates;
  `/private/tmp/ym-last-step-error-budget-20261003-2.log`.
  First check rejected an invalid support projection; it was replaced by
  the explicit supported-one/map proof before accepting the result.
- RatioRefinement: accepted second check exit 0, seven permitted axiom gates;
  `/private/tmp/ym-last-step-ratio-refinement-20261003-2.log`.
  First check rejected one wrong namespace and two unavailable helper names;
  corrections use already-existing constructive lemmas, not new axioms.

All fifteen accepted gates use only {propext, Quot.sound}. No new sorry,
admit, custom axiom, Classical, noncomputable, unsafe, native_decide or
resource-option inflation occurs. Independent Sol mathematical reviews
passed source/depth/weight/rate and both consumer joins; Luna performed
static declaration and forbidden-marker inventory. No aggregate/root build
or full audit is claimed. Root registration only; CI and canonical chart
claims unchanged, so no ASCII reprint.

Source SHA256:

- RatioNoise: `e2c90b9e543978ff954044c4d225429bf5f594fe8fa20f7e729b721d0de985ca`
- ErrorBudget: `cfd3fd4f5268c5f4ed50c52060cc6aee8ba4a9f9773fc26a8c1fde1858a81720`
- RatioRefinement: `321ce1a323e5fa60e5bdf10d79ad0d78d931298ffc429e25f9659eb11d504b85`
