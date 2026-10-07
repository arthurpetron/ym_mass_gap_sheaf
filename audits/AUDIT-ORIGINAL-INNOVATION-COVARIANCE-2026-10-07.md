# Original nonunit innovation and geometric covariance (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms,
and a positive physical Hamiltonian mass gap.

Continuation from `ba69eaf8`. The recent-commit review and primary
direct-score/signed-remainder route remain recorded in
`AUDIT-RECENT-COMMITS-AND-CENTERED-SIGNED-PRODUCER-2026-10-07.md` and
`AUDIT-CONDITIONAL-GRUSS-AND-ORIGINAL-SCORE-2026-10-07.md`.

## Nonunit tower: direction and retained history

For inner/outer partial Haar integrals, put

```
J=W*lift(R), a=Iinner(W), b=Iinner(W*p), e=b-a*phi,
A=Iouter(R*a), v=Iouter(R*a*phi), z=Iouter(R*e),
C=A*Iouter(R*phi*e)-v*z.
Nfull=det(J,p), N1=det(R*a,phi).
```

The exact polarization identifies `Nfull-(N1+2*C)` with
`det(J,p-lift(phi))`. A two-copy square constructs its positive certificate.
The direction is `N1+2*C <= Nfull`, NOT an upper bound on Nfull by N1
plus small error. The residual retains historical variance; it is not
asserted to vanish when e vanishes. No unit-mass or exact-quotient premise.

- `lean/YMGap/Continuum/SU2QuaternionUnnormalizedVarianceTower.lean:127`,
  `innovationCovariance`, names C; `:139`, `innovation_certificate`,
  constructs the shared-tail certificate from the actual W and R.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockInnovationTower.lean:136`,
  `originalInnovationCovariance`, uses a=T^t(g_n), b=T^t(g_n*psi), R=K*V.
  `:244`, `original_block_innovation_certificate`, pins Nfull to
  `blockNoise(t+1,g_n,psi)` and N1 to `blockNoise(1,T^t(g_n),phi)`.
  The previous window is extended into the final output slice; the new
  step inserts its middle spatial V once. No outside endpoint V is inserted.
  `:287`, `original_block_ratio_innovation_certificate`, permits the
  existing finite reciprocal polynomial without identifying it with b/a.

## Constructed geometric signed-covariance estimate

Given an actual source interval |psi|<=c, depth 1<=n+t, and finite
phi=G_k*b, the source endpoints c*a plus/minus b and reciprocal defect
endpoints rho^k plus/minus (1-a*G_k) multiply to give
`c*rho^k*a plus/minus e`. These are original-Haar positive-cone witnesses,
not an assumed reconstruction inequality.

rho is exactly `mixRate(w,width)`: the previous terminal mass cancels in
`blockWindow_radius_pin`. Nome/width dependence remains explicit; there is
no uniform strict rate along a changing AF family. K,n,t do not occur in
rho under the stated positive-window/cutoff guards.

The constructed positive cap is `L=2^(-k)+c*rho^k`, including c=0 or rho=0.
Multiply both error endpoints by the actual original K*V and apply Gruss
to W=stepWeight*a, d=stepWeight*e, f=phi. This gives

```
C^2 <= (L^2*A^2-z^2)*N1.
```

In `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockInnovationCovariance.lean`:

- `:98`, `blockReconstructionDefect`, names the original middle-slice e.
- `:118`, `original_reconstruction_relativeInterval`, constructs exact
  c*rho^k endpoints from `blockRelativeCertificates`,
  `multiplierErrorInterval` and `RelativeInterval.mul`.
- `:159`, `innovationRelativeCap`, supplies the positive L.
- `:197`, `original_innovationCovariance_gruss_certificate`, constructs
  the covariance-square certificate with z^2 retained.
- `:287`, `original_innovationCovariance_weighted_bound`, proves
  `H[Lambda*C^2] <= H[Lambda*(L^2*A^2-z^2)*N1]` with literal
  `Lambda=spatialFringeMass^2*Gout^2`. Gout uses terminal depth n+t+1;
  its degree kout is independent of k. Both factors are certified squares.
  No identification of Vbar^2 with V or with a surviving excitation.

## Vacuum cancellation constrains the next estimate

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockInnovationTower.lean:149`,
`originalInnovationCovariance_one`, proves C=-N1 on the constant input,
for ANY polynomial phi, with no support/positivity premise. The existing
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalNoiseVacuumObstruction.lean:40`,
`blockNoise_one`, makes Nfull zero on that input. The new result does not
assert that a finite reconstructed vacuum has zero N1.

Thus multiplicative absorption of negative C into N1 with a coefficient
strictly below one would require N1=0 in this vacuum case. The covariance
identity, not a numerical counterexample, is checked. This is not a no-go
on the vacuum complement or an exact limiting ratio. Small reconstruction
amplitude and small history are different questions.

## Verification boundary

Completed by 2026-10-07 17:20:00 UTC. Three serialized focused checks:

| Checked module | Gates | Log in /private/tmp | SHA256 |
| --- | ---: | --- | --- |
| SU2QuaternionUnnormalizedVarianceTower | 2 | ym-oct7-nonunit-variance-tower.log | 029aa97332b92130a7607f793818b4e651826575c27274a10a24f5d17a13a4c4 |
| BF4ExactSlabFixedSpatialBlockInnovationTower | 4 | ym-oct7-original-innovation-tower.log | 30c66fc161ce6668ae7919f4e6b8ec6ea92a3f863aa30567f704b981982e40f6 |
| BF4ExactSlabFixedSpatialBlockInnovationCovariance | 5 | ym-oct7-original-innovation-covariance.log | 356005e9332e8ea816d93cdf108e96196dde5a03e1e74f2b2529f0ad1ecc27d5 |

All eleven new printed gates use only {propext, Quot.sound}. No sorry,
axiom, classical input, native_decide, canonical field change or raised
heartbeat limit. Independent read-only review checked signs, history,
original moments, supports, zero caps, parameter dependence and exact weights.
Every launch had a fresh process/pressure/swap preflight, one monitored
compiler, 20-GiB worker ceiling and 12-GiB OS reserve. Swap stayed zero.
No full-root/tree build, full audit, or hashed-baseline regeneration.
The umbrella import addition is not a claim of a checked umbrella build.

## Repointed analytic work; no broader closure

Use the nonunit tower on these windows, not normalized unit-mass premises.
Do not pay its entire historical residual as reconstruction error, or infer
multiplicative covariance absorption from the new square bound. A correctly
vacuum-compatible centered covariance estimate in last-noise units and its
literal weighted normalization remain missing for such a comparison.

The primary route remains a useful COMBINED direct-score/signed-remainder
bound in SAME surviving-form units on a justified family. It retains exact
source cancellation before reciprocal evaluation; its one-step pairing cost
is not an all-vector changing-action two-step norm comparison. Independent
AF survival, actual coarse map/comparison, useful delta budget, physical
calibration, SAME continuum OS/QFT construction, every group and Clay remain
OPEN. No broad canonical chart node changes; no chart reprint.
