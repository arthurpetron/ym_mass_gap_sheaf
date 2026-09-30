# Constructed bounded root inverses on the original carrier

Date: 2026-09-30. Scope: every original all-nome Wilson completion, at fixed
nome and width, every constructed root depth, explicit rational 0<=r<1.
No carrier/action/transfer/kernel replacement and no new analytic premise.

## Mathematical increment

Write R for the existing `root depth`, and B for the original pairing.
Construct the finite normalized geometric sums

    C_0 x = 0,
    C_(n+1) x = (1-r)x + r R(C_n x).

The exact convexity identity

    ||(1-r)x+r y||^2 + r(1-r)||x-y||^2
      = (1-r)||x||^2 + r||y||^2

and the proved root contraction give ||C_n x||^2<=||x||^2.
The exact finite tail is `r^n R^n C_k x`, hence its squared norm is
at most `r^(2n)||x||^2`. The original representative supplies a rational
norm ceiling; `geometricCutoff` supplies the outer Cauchy modulus, including
r=0 and zero-norm inputs. The existing diagonal construction costs epsilon/16.

The resulting SAME-carrier limit C satisfies

    C x = (1-r)x + r R(C x),       ||C x||^2 <= ||x||^2.

Symmetry and finite root commutation pass through actual represented pairing
limits. They give rational linearity and root commutation. Consequently
`J=(1-r)^(-1) C` is the explicit two-sided inverse of `I-rR`, with squared
norm cap `(1-r)^(-2)||x||^2`. Its output Cauchy representative is computed.
Inverse uniqueness also transports any supplied commutation with `I-rR`
to J; this is needed for comparing adjacent root depths.

## Declaration evidence

- `lean/YMGap/Continuum/BF4WilsonAllNomeRootResolventPartial.lean:222`,
  `partial_norm_bound`; line 257, `partial_tail_bound`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeRootResolvent.lean:81`,
  `seriesModulus`; line 138, `convergenceModulus`; line 152,
  `outputRepresentative`. These retain both original and outer moduli.
- Same module, line 268, `resolvent_equation`; line 347, `inverse_right`;
  line 354, `inverse_left`; line 361, `inverse_norm_bound`; line 380,
  `inverse_commutes_of_defect_commutes`.

## Exact verification boundary

The two final focused file checks exited 0, serialized through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20
--status-seconds 300`, with the launcher's 12 GiB reserve and pressure/swap
monitoring. Live process/memory preflight found no competing Lean/Lake/test
or runner process. No worker count, memory limit or safety threshold was raised.

All 37 printed gates (11 finite, 26 limit/inverse) report exactly
`[propext, Quot.sound]`. No new sorry, custom axiom, classical dependency,
native decision procedure or frontier weakening. No full root/tree build,
full axiom audit or guard run was performed.

Final logs and SHA-256:

- `/tmp/ym-wilson-root-resolvent-partial-20260930.log`:
  `854d9e0dac5ff5d6649548f23216a44d09183dbbdcf54db52b4681942508512c`.
- `/tmp/ym-wilson-root-resolvent-20260930.log`:
  `baada5bb94e3fd56bd91a108fc40cf4774276f30cdf7f04d34df78de572e2db5`.

## Next actual consumer — mathematical plan, NOT yet a Lean theorem

For lambda>0 and h=2^(-k), use the constructed inverse to form
`R_h = h*((1+lambda*h)I-root k)^(-1)`.
Let Q=root(k+1), D=I-Q, alpha=lambda*h, A=(1+alpha)I-Q^2,
B=(2+alpha)I-2Q. Root squaring and inverse algebra suggest

    (R_h-R_(h/2))x = h D^2 z,     x=AB z,
    z=A^(-1)B^(-1)x.

The finite positive-coefficient identity

    AB-2D^2 = alpha^2 I + alpha D(3I+Q) + 2D^2 Q

and the corresponding product `(AB-2D^2)(AB+2D^2)` reduce the desired
sharp squared norm comparison to existing original mixed-moment positivity,
`BF4WilsonAllNomeDyadicDefectDecay.moment_nonnegative`.
The proposed result is `||(R_h-R_(h/2))x||^2 <= h^2||x||^2/4`.
It would supply a geometric refinement modulus without a spectral theorem.
The actual operator identity, polynomial comparison and resulting limit
still require Lean proofs. Sector range witnesses and the equation
`A_derivative u = T(f-lambda*u)` are additional required joins.

The inverse norm cap proved here depends explicitly on r and diverges as
r approaches 1; it is not a spacing-uniform generator or physical mass bound.
The full ambient transfer still has its original boundary kernel. No
injectivity or density of its range in the whole carrier is claimed.

Primary signed source/scaling estimate, physical reflected OS identification,
physical time/mass calibration, continuum survival, QFT/every-group/Clay remain
OPEN. The canonical diagram state is unchanged and is not reprinted.
