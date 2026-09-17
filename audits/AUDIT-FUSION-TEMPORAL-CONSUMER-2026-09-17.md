# Fusion insertion versus the same-observable temporal consumer

Date: 2026-09-17. Reviewed source baseline: `39dc67d`.

WHOLE-PROJECT GOAL: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT axioms, isolated vacuum
and positive finite physical Hamiltonian mass gap. **OPEN.**

This is a source/mathematical-direction review, not a new decay proof or a
kernel-checked counterexample. No canonical field or analytic guard changes.

## 1. What the checked fusion formula actually changes

`signedSource_fusion`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialObservedFusionSource.lean:219`,
relates T(f*chi_1) to c_1*T f plus retained bulk and cutoff edge. It adds an
observable to f. It does not identify T(f*chi_1) with another temporal iterate
of the original f. `observedFusionError`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialObservedFusionBoundary.lean:61`,
retains c_1*D(Tf,Tg). The bound `observedFusion_small` at :234 controls the
edge relative to the original partition squared, but does not bound the
coupled baseline and bulk or supply a time-decay factor.

The input functional is `inputNumerator`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowInput.lean:88`.
Its window length permits observations over the entire window, including
its first slice. Window length is therefore not an empty separation gap.
Calling fusion a temporal recurrence or growing only the right-window
length would not fill the existing time-decay consumer.

## 2. The actual same-observable channel already exists

`separatedMessage`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedWindowPins.lean:53`,
is the original iterate across d empty transitions of
`observedMessage(w,K,width,m,L,p)`. Its unobserved reference is exactly
`terminalMessage(w,K,width,m+L+d)` by `separatedMessage_one` at :69.
No observation is inserted at an intermediate step.

For the fixed right-window numerator J and partition functional Z, set

    f_d = separatedMessage(w,K,width,m,L,d,p),
    u_d = terminalMessage(w,K,width,m+L+d),
    D_d = J(f_d)*Z(u_d) - Z(f_d)*J(u_d).

`separatedPartition_eq` at :82 and the three pins
`windowRatio_separated_joint`, `windowRatio_separated_left`,
`windowRatio_separated_right` at :112, :133, :164 identify the joint and
both marginal ratios on ONE original total chain, with denominator
Z(u_d). These are existing checked declarations, not new prerequisites.

`separated_input_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedCovariance.lean:54`,
already proves the normalized absolute connected bound with envelope

    (cq+cq)*mixRate(w,width)^d*(cp+cp).

The source supports signed observations and all nomes in (0,1), above the
constructed cutoff. The rate depends on spatial width.
`no_width_uniform_computed_rate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean:132`,
rules out upgrading THIS computed rate to a width-independent subunit rate.
It does not rule out a sharper bound on the same D_d.

The outstanding forward proposition is spatially/regulator-controlled decay
of that same channel (or a sufficient original temporal-norm estimate),
with a nome-dependent rate common to the required spatial/cutoff/boundary
regulators at that nome, and time-independent observable prefactors. No
common dimensionless subunit rate across decreasing spacing is demanded
here. This review constructs no such estimate. Fusion is one possible internal analysis tool;
it is not a required substitute for the already pinned temporal channel.

## 3. Minimal Wilson coverage and the limiting consumer

`expand_source`, `expand_within`,
`lean/YMGap/Continuum/BF4WilsonExpressionExpansion.lean:143`, :178,
expand current Wilson expressions into finite signed lists of timed words
while retaining their source polynomial and time support. Words include
arbitrary source loops, spins, finite products and offsets. This avoids
requiring a bound on every arbitrary quaternion polynomial. It does not
reduce arbitrary source loops to elementary plaquettes.

`connectedScalar_selected_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.lean:127`,
pins the actual finite reflected joint and both unit marginals to one
selected-action covariance. This identity uses only 0<w<1. In contrast,
`connectedScalar_uniform_bound` at :177 uses the explicit small-nome guards.

The same-object limiting moment estimate is
`centeredTimeMoment_le_geometric`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonDenseGap.lean:66`.
`evenMoment_first_le` at :86 then removes the expression-dependent
prefactor using positivity and dyadic Cauchy--Schwarz of the SAME even
moments; `dense_unitComplement_twoStep_bound` at :112 gives the strict
form conclusion. These existing theorems retain their small-nome guards.
They are not a currently instantiated consumer at new nomes: the compatible
larger-domain limiting form and convergence/moduli must also be supplied.

## 4. Execution decision and evidence boundary

Keep the original action and explicit gap channel as the primary forward
target. Do not add another compiler merely assuming its decay, and do not
claim that insertion fusion is temporal iteration. The previous fusion
edge bound is retained unchanged. Independent backward proofs with supplied
inputs can proceed, but cannot replace the missing interacting estimate.

Parent and parallel reviewers inspected the cited sources. No Lean check
was needed for this review and no new axiom-status claim follows from it.
No new sorry, analytic oracle, frontier type or CI/resource change. The
whole-project scaling, survival, physical-generator, full QFT and all-group
joins remain open.
