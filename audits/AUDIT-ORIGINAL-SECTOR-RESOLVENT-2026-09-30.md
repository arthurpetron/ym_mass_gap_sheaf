# Constructed resolvent of the original witnessed sector derivative

Date: 2026-09-30. Scope: the original all-nome Wilson completion at fixed
nome and width, every positive rational lambda, and the EXISTING witnessed
time-range sector and derivative domain. No action, transfer, time unit,
carrier, vacuum or boundary-kernel replacement.

## Mathematical increment and source evidence

Write T=T(1), h_k=2^(-k), and
`U_k(lambda)=h_k*((1+lambda*h_k)I-root k)^(-1)`.
The previously checked adjacent estimate telescopes to

    ||U_k x-U_(k+l) x||^2 <= h_k^2 ||x||^2.

`lean/YMGap/Continuum/BF4WilsonAllNomeResolventLimit.lean:65`, `tail_bound`,
and line 92, `pair_bound`, supply the one- and two-sided tails. Line 107,
`cauchyModulus`, is computed from the supplied original norm ceiling and
does not depend on lambda. Lines 168 and 186, `resolvent` and
`resolventCertificate`, construct the actual limit R_lambda, its original
output representative, exact pin and all-tail convergence modulus.
Representative independence is proved, not assumed.

For the EXISTING bounded quotients `Q_k=2^k*(I-root k)*T`,

    Q_k U_k x = T(x-lambda U_k x),
    ||U_k x|| <= ||x||/lambda.

Evidence: `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResolventLaws.lean:208`,
`dyadic_quotient_equation`; line 160, `dyadic_norm_bound`.
`lean/YMGap/Continuum/BF4WilsonAllNomeResolventEquation.lean:114`,
`quotient_distance_bound`, allows the moving input to pass to the limit.
Line 159, `equation_error_bound`, gives explicit squared-error factor
`2+4*lambda^2`; line 174, `equationModulus`, supplies its rate. Line 193,
`resolvent_equation`, proves

    A(R_lambda x) = T(x-lambda R_lambda x).

Here A is the existing bounded derivative of T applied to a preimage;
this is NOT a bounded full-carrier Hamiltonian. Symmetry, rational linearity
and the 1/lambda norm ceiling also pass to the actual limit.

The missing range join is constructive. Set `r_k=1/(1+lambda*h_k)`.
The exact identity

    U_k x-r_k*root k(U_k x) = h_k*r_k*x

is `lean/YMGap/Continuum/BF4WilsonAllNomeResolventRange.lean:77`,
`dyadic_root_residual`. The root term has explicit original T-preimages;
the residual tends to zero. Lines 154 and 184, `rangeModulus` and
`resolventRange`, diagonalize those witnesses into a `RangeLimit` for
R_lambda x, for every supplied original representative. No common bound
on the preimages, choice of representatives or ambient injectivity is used.

For a sector input x, BOTH u=R_lambda x and v=x-lambda*u now have range
witnesses. Therefore the original equation constructs an existing
`SectorDerivative.DomainPoint`, with H u=v:
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorResolvent.lean:61`, `domainPoint`.
Positivity of the original difference graph proves positive-shift uniqueness:
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorShiftInjective.lean:82`,
`input_injective`. Consequently `SectorResolvent.inverse_right` at line 78
and `inverse_left` at line 88 prove

    (lambda I+H) R_lambda x = x             (every sector state x),
    R_lambda (lambda u+H u) = u             (every existing domain point).

The derivative output is also recovered (`inverse_left_output`, line 94).
`norm_bound`, line 100, retains 1/lambda; `certificate`, line 114, returns
the actual domain point as Type-level data. Equality is equality of original
vectors, not equality of presentation witnesses. The supplied sector data,
not an arbitrary quotient representative selection, construct every witness.

## Verification boundary

Six final focused checks exited 0, serialized through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20
--status-seconds 300`, retaining the 12 GiB reserve and live telemetry.
Live preflight found no competing compiler/test/runner and zero swap use.
No thresholds or limits were raised. Sol supplied positive-shift uniqueness
and independently reviewed range/sector scope without running builds.

All 56 printed gates are within `{propext, Quot.sound}`: 54 report both,
`equationFactor_nonnegative` only propext, `equationFactor` none. The final
checks followed all source edits. No new sorry, axiom, classical dependency,
native decision procedure, weakened frontier or canonical-field change.
No full root/tree build, audit or guard was run. Root imports were registered
without compiling the large root file.

Final logs and SHA-256:

| Focused log in `/tmp/` | SHA-256 |
| --- | --- |
| `ym-wilson-resolvent-limit-20260930.log` | `de93bf7361873a19e4735ba43da5072cd5383a77bbfb0d858527d0405b2e712a` |
| `ym-wilson-dyadic-resolvent-laws-20260930.log` | `fd5669b4fbc05f2c6a138f8c2d4da5c8b810becf9819b4c15189931e80d8cc29` |
| `ym-wilson-resolvent-equation-20260930.log` | `60d41c35e2d5e40ec7ec3d50030ef636440421e6f191053769bf9a7489ff4ba4` |
| `ym-wilson-resolvent-range-20260930.log` | `fbfe2c57e83e2aa62b67053f16d53329f4ad503283ca1d9a34272e97a5227584` |
| `ym-wilson-sector-shift-injective-20260930.log` | `a8f24204267b6730611e20822e86d85f9b8a101edcb3c7188a5087c60ed47183` |
| `ym-wilson-sector-resolvent-20260930.log` | `dcac7db294cc9cf7b68d80f1e0e03da76e25248279f312cdbaa302f15d660144` |

## Retained open obligations and next priority

The positive-parameter resolvent of the existing sector derivative is now
CONSTRUCTED. This does not identify that sector or derivative with the
physical reflected OS objects of a limiting Yang--Mills theory. Inverse laws
are NOT asserted on the ambient carrier, whose boundary time kernel remains.
The 1/lambda ceiling for lambda>0 is not a spectral exclusion interval above
the vacuum; it asserts no positive physical mass. The original fixed-parameter
form margin has not been made spacing- or volume-uniform.

Return to the original signed-source relative bound `E(x)<=c*B(x,x)` on a
justified scaling family. Its existing consumer is
`BF4WilsonAllNomeSectorSourceTransfer.relative_derivative_bound`;
the unresolved original-weight/partition/terminal-factor comparison is
recorded in `AUDIT-SIGNED-ANGULAR-ORIGINAL-WEIGHT-SEAM-2026-09-30.md`.
Physical reflected-form and observable identification, spectral calibration,
nontrivial continuum survival, full QFT axioms, every compact simple group
and the Clay theorem remain OPEN. The canonical chart is unchanged.
