# Scaled imaginary shifts and Cayley operators

Date: 2026-10-01 UTC. PROGRESS after `bc30e91`: the actual derivative on
the original complex physical carrier now has constructed inverses for
input plus/minus i*t*output for every positive rational t. They construct
C_t=(I-i*t*A)(I+i*t*A)^(-1), its two-sided inverse and full Hermitian
pairing preservation. No physical-time or continuum limit is inferred.

## Same graph and parameter normalization

Let R_t=(I+t*A)^(-1), J_t=I-R_t and D_t=R_t^2+J_t^2. The previously
constructed D_t inverse supplies the real preimages. In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.lean`,
`output_resolventDomain` (:88) proves t*output(Dom_t x)=J_t x.
`plusDomain` (:149) and `minusDomain` (:153) are pairs of those ORIGINAL
domain classes. Resolvent/complement commutation cancels the cross terms;
`plus_right` (:158) and `minus_right` (:176) prove surjectivity on EVERY
existing complex physical class. Neither domain nor carrier is replaced.

In `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayley.lean`,
`shift_pairing` (:123) uses the original graph symmetry scaled by t to
cancel all real and imaginary cross pairings. `plus_left` (:203) and
`minus_left` (:206) give the other inverse laws on the SAME graph domain.
`cayley` (:210), `inverse_right` (:215), `inverse_left` (:219), and
`pairing_preserved` (:224) construct the actual unitary Cayley operator.
`cayley_add` (:236) and `cayley_smul` (:244) prove complex linearity by
surjective physical pairing tests, retaining both scalar Cauchy witnesses.
No linearity of a freely supplied inverse or representative choice is assumed.

## Actual next consumer and open scope

The next consumer is local Cayley consistency on the EXISTING linked
second-domain points, followed by a quantitative product-Cauchy construction.
The sign convention gives C_t x-x approximately -2*i*t*A x, so the factor
two must be retained when calibrating the product parameter. Those product
limits and physical-time identification are NOT supplied here.

Primary useful JOINT signed-error/SAME-variance scaling on a justified
changing family, continuum survival, physical mass, full QFT, field/UV
identification, every group and Clay remain OPEN. No frontier field or
displayed chart claim changes; no ASCII reprint.

## Focused verification

Both final focused checks returned terminal exit zero and emitted target
oleans. All 24 gates use exactly {propext,Quot.sound}: eleven shifts and
thirteen Cayley. Independent mathematical and source/log/hash reviews passed.
No new sorry, axiom, Classical dependency, native_decide, analytic premise or
frontier weakening. Draft heartbeat timeouts were repaired with explicit
original bilinear scale lemmas, not raised limits; failed logs are not evidence.

Main alone compiled through the safe-build skill with one monitored 20 GiB
worker, unchanged 12 GiB reserve and dynamic telemetry. Preflight found no
competing compiler/test/runner, 85 percent pressure-free memory and zero swap.
No broad build/audit/guard, progress-metric script, raised limit or CI change.
Root imports are registration only, not aggregate verification. The
documentation skill keeps parameterized operators separate from a physical
time group or continuum Hamiltonian.

| Accepted log under `/tmp/` | SHA-256 |
| --- | --- |
| `ym-scaled-physical-imaginary-shifts-first-20261001.log` | `7a98feba67f3438e91bc9a4204de64b3bcf2c34f4acb1a970a23e4e18355817a` |
| `ym-scaled-physical-cayley-third-20261001.log` | `387dc03626d0a2193f972f6bc8ddb77cf2c387a60d209a5aed255d7fea123cc2` |
