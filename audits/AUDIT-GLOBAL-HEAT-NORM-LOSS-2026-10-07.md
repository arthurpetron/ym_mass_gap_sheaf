# Complete angular energy versus actual projected-source norm loss

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4, every compact simple group, SAME-theory QFT axioms and
a finite positive physical Hamiltonian mass gap.

## Decision before the proof experiment

The per-plane score ceiling from commit 1a46ec3c repeats one global loss
at every active plane. Test a genuinely summed alternative first on the
original product heat, then on the actual interacting transfer output.
For u=w^2 and total Casimir E, the finite geometric sum gives

    (1-u)*E*u^E <= u*(1-u^E).

An omitted cutoff path has attenuation zero, so its angular contribution
vanishes. Original full-path input pairings are proved nonnegative, and
the existing Casimir/output path identities supply the operator join:

    (1-w^2)*Angular(P f) + w^2*H[(P f)^2] <= w^2*H[f^2].

This has no link-count factor, derivative cap, positive heat floor,
cutoff-largeness guard, source inverse or assumed joint orthogonality.
The endpoints w=0, w=1 and the constant/omitted channels must be covered.

Concrete consumer: use `TransferSmoothing.transferStep_projected_full_heat`
to retain the COMPLETE original spatial source
q=familyProject(fringeBlocks, V*f). Then the same bound controls Angular(T f)
by H[q^2]-H[(T f)^2]. This is an actual interacting transfer-output theorem,
not an identification of H[q^2] with the original V-weighted or completed
OS norm. No V factor is deleted.

Decisive scope test: this unweighted integrated inequality cannot be multiplied
by the output-dependent Vbar^2*Gout^2 or applied directly to the y-dependent
conditional residual A(y)*V*c-b(y)*V*a. Those insertions destroy the diagonal
mass argument. A weighted conditional matrix/tensorization estimate, or the
tighter combined signed-score route, is STILL needed. Do not replace the
existing score producer or claim regulator-uniform conditional control.

Verification budget: root alone runs serialized focused checks under the
safe launcher, one 20-GiB worker with 12-GiB OS reserve and fresh live capacity
checks. Sol owns only the scalar source; root owns the operator/source joins.
No full-tree audit, raised limits, new assumption bundle, axiom or sorry.

## Observed evidence

Four serialized focused checks passed. Their sixteen printed declarations have
exactly {propext, Quot.sound}; no full-root/tree build or audit was run.

- `lean/YMGap/Continuum/SU2HeatProductReversePoincare.lean:38`,
  `casimir_power_le_mul_geomSum`, proves the finite geometric payment.
  `:82`, `qpow_squared_reverse_poincare`, and `:103`,
  `product_squared_reverse_poincare`, retain both nome endpoints, zero
  Casimir and the literal coordinatewise cutoff.
- `lean/YMGap/Continuum/SU2QuaternionProductHeatReversePoincare.lean:47`,
  `productMap_square_grouped`, derives squared output attenuation on the
  SAME computed path tree. `:75`, `productMap_angular_norm_loss_le`, sums
  the scalar estimate against proved nonnegative original path pairings.
  It does not assume a joint eigenbasis or discard cross terms by fiat.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferReversePoincare.lean:84`,
  `transferStep_angular_projected_norm_loss_le`, joins the estimate to the
  actual interacting transfer with q=Pi_fringe(V*f). The complete spatial
  source remains; neither norm is ell_V[f^2] or the completed OS norm.

Focused logs and SHA-256:

- `/private/tmp/ym-oct7-product-rpi-scalar2.log`:
  `5d6e58dfdb9fff4110061516064da822ccc962cac8a0bb7dffc53a97457d8eba`.
- `/private/tmp/ym-oct7-product-rpi-operator2.log`:
  `b5ceb876409a32571f30f85ef978c24ced0128784865e0e199227ac28e2f7f7e`.
- `/private/tmp/ym-oct7-product-rpi-transfer2.log`:
  `837a277d54423f5f031adfea955074c00b14e0dba695fc8793511d2b5a8ab3cf`.
- `/private/tmp/ym-oct7-weighted-norm-loss-obstruction2.log`:
  `562f0fd68dfa535a1f60df64c6d7cc4061812a677250faea87e9e85396d29707`.

The initial elaboration failures were repaired with an explicit zero-power
identity and the missing defining namespace opens. Failed runs are not proof
evidence. No source sorry/axiom/classical input, compiler limit raise or
canonical frontier-field change. Fresh capacity checks found no competing
compiler, zero swap and 87--88% free memory before the one-worker launches.

## Decisive weighted-shortcut test

On the LITERAL P=productMap 1 (1/2) 1 [0], x=polyVar 0,
h=1+x/2 and f=1-x/4, the checked output is 1-x/32. The actual weighted
input/output squares are 61/64 and 4065/4096, respectively. Their loss
is -161/4096. The weight and probe have constructed floors 1/2 and 3/4.

Evidence in `lean/YMGap/Continuum/SU2QuaternionWeightedNormLossObstruction.lean`:
`:52`, `weight_floor_certificate`; `:65`, `probe_floor_certificate`;
`:73`, `literal_output_coeff_pin`; `:83`, `weightedInputSquare_pin`;
`:86`, `weightedOutputSquare_pin`; `:94`, `weightedLoss_negative`;
`:100`, `weighted_reverse_poincare_false`. The last declaration rules
out the proposed weighted reverse-Poincare law for ANY nonnegative
angular cost. Ten gates pass. This is NOT an interacting K(V input),
gauge-invariant physical-state, completed OS or Yang--Mills counterexample.

The first diagnostic check found integer-only normalizer constants and
recursion-depth failures from squaring the fully expanded map. Tiny
coefficient canonicalization and a single staged literal output pin repair
both without a limit raise. The failed run is not proof evidence.

## Interpretation and next decision

PRUNE insertion of an arbitrary positive output weight into the Haar law.
CONTINUE only the actual action-specific signed-score/conditional join.
The new estimate removes the active-count factor for the integrated output
heat energy, NOT for the weighted conditional score. The latter retains
the coupled residual A*Db-b*DA and the output factor Vbar^2*Gout^2.
Separate bounds for a and c do not control that residual's cross term.
Its existing original-source derivative identity is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:159`,
`lastStep_sourceDerivative_carrier`.

Independent read-only review located the exact evolving-terminal variance
balance ALREADY in the original action:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lean:86`,
`lastStepNoise_endpoint_pin`. It keeps ell[N]+ell[b^2]=ell[a*T^2a*phi^2]
for a=g_d, A=Ta, c=a*phi, b=Tc, N=A*T(a*phi^2)-b^2, ell[p]=H[V*p].
`:202`, `lastStepNoise_dissipation_cleared`, already controls the actual
terminal mismatch with comparisonEta, without an eigenvector assumption.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialScoreDissipation.lean:138`,
`original_lastStep_score_dissipation_le`, already consumes it per plane;
`:281`, `activePlaneCount`, records the current summed multiplicity.
No new stationary-law or conditional-balance wrapper is needed. The
smaller missing estimate is a JOINT all-plane conditional-score bound
that retains D(Va), D(Vc) and the terminal mismatch without charging the
same global loss at each plane. This review adds no new proof declaration.

STOP extending generic smoothing wrappers here. A weighted conditional
matrix/covariance estimate must use the actual K*V source coupling, or the
existing tighter combined signed-energy route must bound its literal cost.
No quantitative AF/volume/scaling bound or completed OS comparison follows.
In particular 1-w^2 tends to zero as the nome tends to one; absence of an
explicit link-count factor is not a coupling-uniform coercivity constant.
The broad project chart and all outstanding Clay requirements stay OPEN.
