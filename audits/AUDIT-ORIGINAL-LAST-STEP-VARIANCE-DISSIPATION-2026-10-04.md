# Original last-step innovation and same-source variance dissipation

## Result and scope

Four focused checks passed fifteen permitted axiom gates, without errors
or warnings in the accepted runs. Independent mathematical review passed
the actual-source, partition, weight and error joins below.

The new finite estimate retains the positive last-step conditional noise
alongside the ACTUAL outgoing source's square. It is stronger than dropping
that noise from an upper filtered-variance comparison. All K,V, terminal
messages, source, supplied center and chronological partitions are original.
This supplies norm-loss currency; it does not prove small loss or survival.

## Forward: actual last innovation and terminal bracket

Write ell(p)=H[V*p], a=g_d, A=T(a), b_phi=T(a*phi),
N_phi=A*T(a*phi^2)-b_phi^2, Zi=ell(a^2), Zo=ell(A^2).

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lean:86`
`lastStepNoise_endpoint_pin` proves the exact identity

    ell(N_phi)+ell(b_phi^2)=ell[a*g_(d+2)*phi^2].

The actual gap-two terminal bracket at d-1 constructs
l*a <= g_(d+2) <= U*a. Its relative width gives
U <= (1+comparisonEta(w,width,d-1))*l. Multiplication by the original
certified a*phi^2 gives the upper endpoint comparison; multiplication by a
gives Zo >= l*Zi. Weighted transfer symmetry pins Zo=ell(a*g_(d+2)).

`:202` `lastStepNoise_dissipation_cleared` therefore proves, for d>=1,

    Zi*[ell(N_phi)+ell(b_phi^2)]
      <= (1+eta)*Zo*ell[(a*phi)^2].

The factor is LINEAR 1+eta, not squared. Phi may be signed.
No stationary terminal eigenpin or variance inverse is assumed.

Now c=T^r(g_n*psi), d=n+r and phi_k=G_in,k*c. The actual positive-window
multiplier certificate constructs (a*G_in,k)^2<=1. Hence
ell[(a*phi_k)^2]<=ell(c^2). `:329` `lastStepRatioNoise_endpoint_le`
retains the constructed U endpoint; `:352`
`lastStepRatioNoise_dissipation_cleared` supplies

    Zi*[ell(N_k)+ell(b_phi,k^2)] <= (1+eta)*Zo*ell(c^2).

This specialization does not silently identify b_phi,k with T(c).

## Reconstruction: original weighted norm, no source inverse

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepReconstructionNorm.lean:84`
`original_step_one_upper_certificate` integrates the COMPLETE original step
interval to construct stepCap(w,width)*one-T(one)>=0.
`:106` `original_step_weighted_square_le` applies the actual weighted Schur
theorem at A=one. Its bound is ell[(Tp)^2]<=stepCap^2*ell(p^2), retaining
one original V in both norms, not an ordinary-Haar norm substitution.

`:138` `incomingRatioError_weighted_square_le` consumes the existing actual
polynomial certificate e_k^2<=rho^(2k)*c^2, e_k=c-a*phi_k.
`:164` `incomingRatioError_transferred_square_le` proves

    ell[(T e_k)^2] <= rho^(2k)*stepCap(w,width)^2*ell(c^2).

Rho=mixRate(w,width). The error coefficient does not contain cutoff,
depth, source, source norm or an inverse excitation. Nome/width dependence
is explicit and can deteriorate along a changing family.

## Backward join: actual b=T(c), same projected weight

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepOriginalDissipation.lean:75`
`incoming_source_reconstruction_pin` and `:91`
`outgoing_source_reconstruction_pin` prove c=a*phi_k+e_k and
b=T(c)=T(a*phi_k)+T(e_k), coefficientwise on the original carrier.

`:106` `original_lastStep_noise_variance_loss_le` joins the constructed
noise inequality and error estimate by asymmetric Young, for delta>0:

    Zi*[(1+delta)*ell(N_k)+ell(b^2)]
      <= [(1+delta)*(1+eta)*Zo
          +(1+1/delta)*rho^(2k)*stepCap^2*Zi]*ell(c^2).

The original source b, not its polynomial-ratio approximation, appears
on the left. No division by Zi, Zo, ell(c^2) or ell(b^2) occurs. Signed
and zero sources are admitted; the supplied chronological center is unchanged.
The only additional scalar inversion is delta; the original constructed
positive-window reciprocal is retained.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedNoise.lean:73`
`spatialFringeMass_weighted_insert_le` extends the existing square comparison
to a certified fringe-independent insertion. `:116`
`lastStepRatioNoise_fringe_independent` constructs this independence for
the literal noise using actual one-step outputs. `:156`
`lastStepRatioNoise_projected_weight_le` proves

    H[Vbar^2*N_k] <= spatialCeiling(w,width)*ell(N_k).

No positivity or output-independence premise is supplied for N_k: both
are constructed from the original transition and supported incoming source.
Vbar^2 is compared to, never identified with, V.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepOriginalDissipation.lean:192`
`original_lastStep_projected_noise_variance_loss_le` joins this ACTUAL
projected-noise estimate to the same-source retained-loss bound.

## Next analytic frontier; no false closure

Zo here is ell[(Ta)^2]. It is NOT the outgoing Rayleigh partition
ell[(Ta)*T(Ta)]. Conversion to that consumer retains the already explicit
partition costs. The projected ceiling depends on nome/width; it is not
a spatially uniform coefficient. Eta also names terminal depth explicitly.
The noise can be large when the norm decrement is large. No argument here
makes either small relative to the SAME surviving norm.

The existing exact-score consumer remains
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRatioRefinement.lean:431`
`original_lastStep_incomingRatio_gradient_le` and the COMPLETE signed cost at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:324`
`original_block_exact_score_cost_relative_tolerance`. The new estimate pays
their literal projected noise in actual norm-loss currency; it does not
cancel the retained mixed-minus-diagonal Taylor remainder. Replacing exact
angular energy by a noise envelope can add slack; no automatic negative-
square cancellation of that slack is claimed.

Still missing: a useful ORIGINAL signed noise-plus-remainder estimate,
or the alternative initial-energy signed-defect estimate, on a JUSTIFIED
changing family. Nontrivial survival, physical calibration, same-theory
OS/continuum passage, full QFT and every compact simple group remain OPEN.
No canonical chart atom changes, so no ASCII reprint. No Clay closure.

## Verification

Serialized monitored checks, one compiler, 20 GiB cap, 12 GiB OS reserve:

- ReconstructionNorm: accepted second check exit 0, four permitted gates;
  `/private/tmp/ym-last-step-reconstruction-norm-20261003-2.log`.
  The first check rejected an Eq-versus-coefficient-equivalence transport;
  the exact head-add equality is now rewritten before coefficient transport.
- NoiseDissipation: accepted second check exit 0, four permitted gates;
  `/private/tmp/ym-last-step-noise-dissipation-20261004-2.log`.
  The first check rejected one pattern-lambda layout; no statement changed.
- ProjectedNoise: accepted third check exit 0, three permitted gates;
  `/private/tmp/ym-last-step-projected-noise-20261004-3.log`.
  The first check exposed a missing defining namespace; the second passed
  with an unused-hypothesis warning. Its binder was renamed `_hp`, preserving
  the support hypothesis and argument position; no linter was disabled.
- OriginalDissipation: accepted second check exit 0, four permitted gates;
  `/private/tmp/ym-last-step-original-dissipation-20261004-2.log`.
  The first check rejected one lambda layout and a missing explicit
  weightedMass unfolding at the Young join; both transports are now explicit.

All fifteen accepted gates use only {propext, Quot.sound}. Failed-run
elaborator placeholders were rejected; no source sorry/admit, custom axiom,
Classical, noncomputable, unsafe, native_decide or resource-option inflation
was introduced. Sol independently reviewed the finite mathematics and both
original-source joins; Luna implemented the bounded projected-weight leg.
Every preflight found no competing compiler/runner, zero swap and healthy
memory pressure. No aggregate/root build, progress-metric/guard run or full
audit is claimed. Root registration only; CI and canonical chart unchanged.

Accepted source SHA256:

- NoiseDissipation: `d0a61a22edad95d75e53afb645ee3109ab918b057e953c60ca30718aef73f84f`
- ReconstructionNorm: `35c0ac339d6c36d88b7dc655234d87b19adb82ef4c726e1cfd5ad5715da2d6e2`
- ProjectedNoise: `cc22bc46896d59eac331f7aaef8ddc95ab4515334c12bc0af4344615ed3b5bf1`
- OriginalDissipation: `96ff413f946da011889a038edcbb0df0e8f90f2480449ccd4035eafd8f62f915`
