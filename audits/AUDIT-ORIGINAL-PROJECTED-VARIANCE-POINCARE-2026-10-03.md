# ORIGINAL own-variance endpoint and projected BF4 Poincare

## Outcome and actual scope

PROGRESS after `ffa8f9e`: the missing endpoint is proved, not supplied:

```text
H_n[W * determinant(n, productHeat, p)]
  = jointSquare(p) - jointSquare(S_ids p),
provided p is actually independent of every inactive LOWER input.
```

The selected updates construct independence of the active inputs. In the
actual BF4 application, lower-fringe projection constructs the remaining
independence. No inactive upper output is deleted. The mean is the ORIGINAL
own conditional mean, not an assumed stationary Wilson mean.

The checked product-angular bound therefore gives

```text
H_N[W * projectedReferenceVariance(Q_K, kernel_L)]
  <= (1-w^2) * sum_active H_2N[(kernel_L * lift W) * Gamma_input(Q_K)]
  <= (1-w^2) * sum_active H_2N[(kernel_L * lift W) * Gamma_input(Y_K)].

H_N[W * projectedActiveVariance_K]
  <= (1+eta)*(1-w^2) * sum_active H_2N[(kernel_L * lift W) * Gamma_input(Y_K)].
```

Y_K is the COMPLETE original first source derivative; Q_K is its actual
lower-fringe projection. Original action, incoming source and both transfer
terms remain at K. Only the auxiliary reference kernel uses L. There is no
link-count prefactor and no mass/norm inverse. The cutoff is computed for
the FIXED original source; no changing-source/coupling/spacing uniformity
follows. W is arbitrary certified supported output data, including zero.

The whole-project goal remains OPEN: nontrivial constructive continuum
Yang--Mills on R^4 for every compact simple gauge group, SAME-theory required
QFT axioms and a finite positive physical Hamiltonian gap. No exact
canonical chart claim changes; its fenced bytes are unchanged and no chart
is reprinted. This is finite conditional reference heat, not an interacting
OS transfer gap.

## 1. Genuine independent-head lift

`lean/YMGap/Continuum/SU2QuaternionIndependentHeadsLift.lean:75`
`independent_head_partial_drop` proves coefficient equality ONLY between
the two reduced-head representations, using zero head exponents and the
actual unit Haar moment. `independent_head_lift` (:82) proves equality
under EVERY original insertion, even one using the integrated head.
`independent_heads_lift` (:105) iterates actual partial-head support and
degree shifts plus `lift_carrier`. Explicit zero padding is never asserted
to be a raw full-polynomial coefficient equality. Empty heads/tail remain.

## 2. OWN mean and same-law variance endpoint

`lean/YMGap/Continuum/SU2QuaternionProductHeatConditionalVariance.lean:58`
`product_conditional_unit` derives all-insertion mass one from the actual
distinct product marginal, with supported-carrier promotion; no coefficient
unit is assumed. `sweep_all_lower_independent` (:69) uses literal updates for
active inputs and the explicit inactive-input premise for the others.

`joint_sweep_square_mean_pin` (:85) applies the independent-head lift to the
original sweep, retains the SAME joint weight, removes its product heat via
the actual upper marginal, and identifies its output with the original
own mean using `hybridMap_carrier`. Both square factors are transported;
the same shared output weight surrounds them.

`determinant_sweep_loss_pin` (:137) combines the actual unit pin, that mean
square and original second-moment Fubini. This exact identity needs no
positive kernel, late cutoff or sign condition on W. It does need the
inactive-input premise; arbitrary p does NOT qualify automatically.
`conditional_variance_angular_poincare` (:166) composes the identity with
the checked joint estimate, at `jointPoincareCutoff` of p itself.

## 3. Actual original-source BF4 consumer

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVariancePoincare.lean:58`
`projectedSourcePoincareCutoff` computes the auxiliary onset from the complete
Q_K and the actual active list. `projected_source_inactive` (:65) constructs
the necessary lower independence with `familyProject_independent` and the
literal active/fringe partition.

`projected_reference_variance_angular_le` (:73) therefore bounds the OWN
`projectedReferenceVariance` without an unprovided endpoint premise.
`projected_angularEnergy_le_source` (:101) sums the actual coefficient-one
fringe contraction with all reference/action/output weights retained.
`projected_reference_variance_source_energy_le` (:136) pays reference
variance by genuine Gamma-input energy of COMPLETE Y_K.
`projected_active_variance_source_energy_le` (:155) composes the existing
near-unit K/L comparison with factor 1+eta. It requires BOTH near-unit
cutoff guards and the source-dependent auxiliary onset; L need not equal K.

## 4. Remaining producer and downstream consumer

Gamma(Q_K) is SECOND derivative. It is NOT the existing Q_K-square budget
`projectedDerivativeAngularBudget` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean:146`.
That file's `projectedDerivativeSignedBulk` (:362) retains both Taylor
remainders, and `original_block_projectedDerivative_cost_relative_tolerance`
(:472) still needs a useful signed bulk relative estimate.

Retain the stronger projected Gamma(Q_K) bound when its cancellation helps;
the comparison with Gamma(Y_K) is optional, not a required weakening.
The next producer must control the ACTUAL weighted source energy or its
signed cancellation with original drift/remainders against the SAME
surviving norm, then justify the changing family/window. The present theorem
supplies no such estimate. Generic positivity is not a reverse bound on
angular energy independent of source degree. No continuum survival,
physical calibration, full QFT or every-group closure is claimed.

## 5. Verification boundary and independent reviews

Three final focused checks completed successfully, with 14 printed gates
ALL within `{propext, Quot.sound}`. No warnings/errors or `sorryAx` appear
in the accepted logs. Initial diagnostics were missing namespace opens
only; no mathematical hypotheses or statements were weakened.

Common invocation, replacing the named file and accepted log below:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 12 \
  --check-worker-limit-gib 20 --status-seconds 300 \
  --log-file /tmp/<accepted-log> \
  --check lean/YMGap/Continuum/<module>.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/<module>.olean
```

| Module | Gates | Accepted log |
| --- | ---: | --- |
| SU2QuaternionIndependentHeadsLift | 3 | `/tmp/ym-independent-heads-lift-20261003-2.log` |
| SU2QuaternionProductHeatConditionalVariance | 5 | `/tmp/ym-product-heat-conditional-variance-20261003-3.log` |
| BF4ExactSlabFixedSpatialProjectedVariancePoincare | 6 | `/tmp/ym-bf4-projected-variance-poincare-20261003-1.log` |

Fresh process/swap/pressure checks preceded EVERY launch: no competing
compiler/runner/test, zero swap and 76--77% system memory free. One compiler,
20 GiB limit and 12 GiB reserve throughout. Every check finished in its
initial tool call; no artificial waits or heavy/full jobs were started.

Independent Sol reviews PASS: the endpoint uses own conditional mass/mean,
active/fringe premises are constructed on lower coordinates only, original
K/reference L are distinct, and the energy is SECOND derivative rather than
Q^2 or surviving norm. Reviews are mathematical source inspection, separate
from the kernel checks. Root imports registered only; full root/tree build,
full axiom audit, guard or metrics run NOT performed. CI remains manual-only.
No sorry, new axiom, changed frontier field or new assumed analytic input.

### SHA-256 of final sources

```text
0609973e8a62eb806c544b4b738577b48c898ed4dba7a79583e05fa1bd70521a  SU2QuaternionIndependentHeadsLift.lean
f8b0450a8dccb1b7f33923543b8d68edc27c49aadc8cd4914b6f70c6f5c3db90  SU2QuaternionProductHeatConditionalVariance.lean
0a90583732881d24521dfb39a6ef87b97c21c89554e70b17b403fcdffc69e77b  BF4ExactSlabFixedSpatialProjectedVariancePoincare.lean
```

### SHA-256 of accepted logs

```text
8ef5c501144e67d1736615317b016c4ffed8e96846e995a6619d61b9d14299da  ym-independent-heads-lift-20261003-2.log
1086b756f8216da191a379ef2591abe2e8d96d394be21151a09caf2bed36f37a  ym-product-heat-conditional-variance-20261003-3.log
aa2e91069472897947aeeaf89b49c702a3e8122b50c9d432bce7a27396630066  ym-bf4-projected-variance-poincare-20261003-1.log
```
