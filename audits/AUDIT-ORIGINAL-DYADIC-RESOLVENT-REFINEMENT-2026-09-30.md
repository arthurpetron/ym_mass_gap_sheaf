# Original dyadic resolvent: sharp adjacent refinement

Date: 2026-09-30. Scope: the SAME original all-nome Wilson completion,
at fixed nome and width, all root depths, every original vector and every
positive rational resolvent parameter lambda. No action, transfer, carrier,
vacuum or boundary-kernel replacement.

## Proved mathematical increment

For delta>0 and b>=0, construct the actual inverse of
`(delta+b)I-bR` by the already constructed normalized geometric series at
`r=b/(delta+b)`, scaled by `1/delta`. Both inverse equations, norm ceiling
`1/delta` and computed original output representatives are proved:
`lean/YMGap/Continuum/BF4WilsonAllNomeShiftedRootResolvent.lean:118`,
`inverse`; lines 131, 140, 148 and 196, `inverse_right`, `inverse_left`,
`inverse_norm_bound` and `inverseRepresentative_pin`.

Write Q=root(k+1), D=I-Q, alpha=lambda*h, and

    A=(1+alpha)I-Q^2,     B=(2+alpha)I-2Q.
    C=alpha^2 I + 3 alpha D + alpha QD + 2 QD^2.

The original root-square identity gives `AB=C+2D^2`.
Only FOUR original mixed moments are needed for
`<Cz,D^2z> >= 0`: powers `(Q,D)=(0,2),(0,3),(1,3),(1,4)`.
Consequently the direct norm expansion gives

    ||ABz||^2 = ||Cz||^2 + 4<Cz,D^2z> + 4||D^2z||^2
              >= 4||D^2z||^2.

This short argument replaces the previously proposed product of two positive
polynomials; it makes no general positive-operator-product inference.
Evidence: `lean/YMGap/Continuum/BF4WilsonAllNomeResolventSquareComparison.lean:74`,
`denominatorProduct_pin`; line 181, `positiveNumerator_cross_nonnegative`;
line 245, `positive_square_comparison`. The input is the already proved
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDefectDecay.lean:181`,
`moment_nonnegative`.

For the CONSTRUCTED z=A^(-1)B^(-1)x, commutation obtained from inverse
uniqueness gives `ABz=x` and

    A^(-1)x-B^(-1)x = D^2z.

These are exact vector identities on the original completion:
`lean/YMGap/Continuum/BF4WilsonAllNomeAdjacentRootResolvent.lean:120`,
`inverseProduct_pin`; line 126, `inverse_difference`; line 136,
`inverse_difference_bound`; line 156, `scaled_difference_bound`.

Finally construct

    R_k(lambda)x = h*((1+lambda*h)I-root k)^(-1)x,  h=2^(-k).

The half-step denominator is exactly B/2. The proof identifies the actual
next approximant, not a differently parameterized surrogate. Thus

    ||(R_k(lambda)-R_(k+1)(lambda))x||^2 <= h^2 ||x||^2 / 4.

Evidence: `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResolvent.lean:42`,
`atStep`; line 46, `atStep_equation`; line 67, `half_step_pin`; line 103,
`dyadic_step_bound`; line 113, `dyadicRepresentative`; line 119,
`dyadicRepresentative_pin`.

## Verification boundary

Four final focused checks exited 0, serialized through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20
--status-seconds 300`, retaining the 12 GiB reserve and live telemetry.
Process preflight found no competing compiler/test/runner. No safety
threshold, worker count or memory ceiling was raised.

All 39 printed gates are within `{propext, Quot.sound}` (38 report both;
`dyadicStep_positive` reports only propext). No new sorry, axiom, classical
dependency, native decision procedure or canonical-field change.
No full root/tree build, full audit or guard was run. Root imports were
registered but the large root file was not recompiled.

Final logs and SHA-256:

- `/tmp/ym-wilson-shifted-root-resolvent-20260930.log`:
  `f1ad37f70ac6936be2a7d50d049ed699ac82edb82c8e0a01493751b67cef2c9d`.
- `/tmp/ym-wilson-resolvent-square-20260930.log`:
  `49e76e50cdfe58297498b224770885f6db493c4d3fb03a975bd970232b912e8c`.
- `/tmp/ym-wilson-adjacent-root-resolvent-20260930.log`:
  `bf155275fdc4e5379fc94706c2f624444b52d99cef8e22eac6e7e576a374458f`.
- `/tmp/ym-wilson-dyadic-resolvent-20260930.log`:
  `dc7ae1665574a16807b0ea5148cf25acb19e46a7172b27d228994d2b54a941cb`.

## Next consumer and retained boundaries

Next: telescope the adjacent estimate with an explicit geometric tail, form
the actual represented norm limit, and supply its original sector witness
and equation `A_derivative u=T(f-lambda*u)`. These are not yet proved here.
The existing intrinsic sector-domain characterization can consume that
equation together with the required range witnesses.

The bound is independent of positive lambda in the ORIGINAL norm, but h is
the constructed root time, not a justified physical lattice spacing. It
does not bound a physical mass, assert a full-carrier generator inverse, or
discard the original time kernel. lambda=0 is not admitted.

The independent source review
`audits/AUDIT-SIGNED-ANGULAR-ORIGINAL-WEIGHT-SEAM-2026-09-30.md` locates the
missing original numerator/partition/terminal-weight comparison behind the
angular Taylor route. It supplies no signed scaling estimate.
Physical reflected OS identification, justified scaling survival, physical
time/mass calibration, full QFT, every-group and Clay conclusions remain
OPEN. No canonical displayed chart claim changed; no chart was reprinted.
