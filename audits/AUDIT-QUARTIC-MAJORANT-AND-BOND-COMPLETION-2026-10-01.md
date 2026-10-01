# Scalar quartic majorant and physical bond completion

Date: 2026-10-01 UTC. Two supporting results are kernel-checked: a short
signed-polynomial majorant for the proposed low-spin quartic estimate, and
the represented completion of the original physical bond form. Neither
supplies the missing original energy versus centered variance bound along
a justified physical scaling family. The continuum and Clay target remain open.

## The checked scalar estimate

For rational n>=0 and 0<=A,V<=1, write d=1-A, e=1-V and

    P = (n-2)-4(n-1)A+6n A^2 V-4(n+1)A^3 V^3+(n+2)A^4 V^6.

The new theorem proves

    P <= n*d^4 + 12*e*d + 15*(n+2)*e^2.

Its proof is one exact polynomial identity. The right side minus P is

    2*d^3*(1+A)
      + 6*n*A^2*d^2*e
      + 12*e*d^2*(1+A+A^2)
      + 15*(n+2)*e^2*d*(1+A+A^2+A^3)
      + 4*(n+1)*A^3*e^2*(2+V)
      + (n+2)*A^4*e^3*(V^3+3V^2+6V+10).

Every displayed term is nonnegative under the stated guards. This retains
the signed cancellations before taking an upper bound; no large Taylor
expansion or presumed sign of an interacting remainder is used.

The definitions and literal formula pins are
`SU2HeatQuarticCoefficientMajorant.quarticP_formula`
(`lean/YMGap/Continuum/SU2HeatQuarticCoefficientMajorant.lean:94`) and
`quarticMajorant_formula` (same file, line 109). The checked inequality is
`quarticP_le_majorant` (same file, line 217). These are scalar declarations;
their types do not yet mention a heat prefix, source or interacting variance.

## Reviewed analytic continuation, not yet kernel checked

The intended next join uses the actual coefficients
a_j=(j+1)*w^(j*(j+2)). For 2<=j and j+2<=K the candidate second-fusion
coefficient is

    b_j = 6*a_j-4*(a_(j-1)+a_(j+1))+a_(j-2)+a_(j+2).

With n=j+1, A=w^(2n-3), V=w^2, its proposed exact factorization is
b_j=w^(j*(j-2))*P. This identity and the complete finite character expansion
are still to be formalized, including spins zero and one and all cutoff
boundary terms. They are not supplied by the new scalar theorem.

The independently reviewed paper calculation gives, for h=1-w and n>=3,

    P <= n*(148*h^2 + 16*n^4*h^4).

Indeed d<=2nh, e<=2h and n+2<=5n/3 in the checked majorant suffice.
If w^(4j)>=1/2, the proposed relative coefficient bound is then
b_j<=(296*h^2+32*n^4*h^4)*a_j. These specialized consequences have not been
kernel-checked in this increment.

A moving high-spin tail is also required. The reviewed block argument for
q=w^(L^2)<=1/8 gives the candidate finite bound

    sum_(k=L)^K (k+1)^2*w^(k*(k+2)) <= 8*L^3*q.

Blocks [rL,(r+1)L) contribute at most (r+1)^2*L^3*q^(r^2), which is at
most L^3*(4q)^r. Existing block-reindexing proofs in
`lean/YMGap/Continuum/HarmonicLowerSixSquareRootBlockTail.lean:180` and
`HKConvGen.geoTailBase_series_le`
(`lean/YMGap/Continuum/HeatKernelConvGen.lean:401`) are proof ingredients,
not this theorem. The crude one-index ratio in
`BondMovingScaledNorm.tailTerm_ratio_gen`
(`lean/YMGap/Continuum/BondMovingScaledNorm.lean:323`) is insufficient at
the proposed L approximately h^(-2/3): its polynomial factor does not tend
below one. Use blocks or a sharper ratio; do not reuse that guard silently.

The diagnostic schedule h=2^(-3m), L=2^(2m), m>=2 suggests an o(h) tail.
`ReciprocalBernoulliUpper.oneSub_pow_le_recip_bernDen`
(`lean/YMGap/Continuum/ReciprocalBernoulliUpper.lean:144`) supplies the
one-block ingredient for q<=2^(-2^m). The schedule is arithmetic testing
data, NOT a justified physical Yang--Mills scaling trajectory.

## Positivity and normalization needed by that route

For a selected link, put J=H[W*a*lift(a)] and
Gamma_j=H[W*a*lift(a)*chi_j]. Spectral positivity gives Gamma_j>=0 and
J<=I_w with the same signed endpoint source; these are existing declarations
`SU2QuaternionProductHeatPositive.character_insertion_nonnegative`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatPositive.lean:175`) and
`SU2QuaternionHeatFusionQuadratic.vacuum_le_prefix`
(`lean/YMGap/Continuum/SU2QuaternionHeatFusionQuadratic.lean:85`).

The additional upper bound |Gamma_j|<=dim(j)*J requires a pointwise
certificate for the WHOLE background W*a*lift(a), not just PSD of W.
`QuaternionHaarSharpCharacterInterval.character_weighted_haar_bound`
(`lean/YMGap/Continuum/QuaternionHaarSharpCharacterInterval.lean:63`)
already supplies it. For the original uncentered endpoint source, the proof
of `BF4ExactSlabFixedSpatialHeatNomeComparison.affine_original_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialHeatNomeComparison.lean:135`,
certificate construction at lines 143--153) constructs that certificate
from the original spatial, terminal and spectator heat factors, with
0<w<1 and headCutoff(w)<=K. It cannot be reused for a centered signed source
without an additional certificate. No new wrapper is needed here.

The planned low/high split can therefore pay a dimension-weighted tail by
J<=I_w without an inverse heat floor, once the missing coefficient and tail
proofs are supplied. It still does not compare the mixed full-word moment
to SAME interacting centered variance, or prove physical scaling survival.

## Represented completion of the physical bond form

`BF4WilsonAllNomeBondOSCompletion.Rows` and `Close` carry Type-valued
Cauchy and asymptotic-closeness moduli for the physical bond distance
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSCompletion.lean:75`, line 84).
`rowSetoid` (line 116) uses propositional truncation of the explicit Close
witness only to define the quotient relation. It is defined from physical
source distances, not by declaring two rows equal when their limits agree.

`close_limit_eq` (line 149) and `closeOfLimitEq` (line 171) prove both
directions and construct the reverse modulus. `toSectorRep` (line 145)
and `fromSectorRep` (line 255) retain original range and approximation
witnesses before quotienting. Neither chooses a representative from a
quotient. `rowsOfConvergent` (line 220) provides the generic construction
that keeps large dense-source witnesses abstract during proof checking.

`toSector_fromSector` (line 282) and `fromSector_toSector` (line 287)
give inverse maps between the physical Cauchy-row quotient and the quotient
of existing witnessed time-sector states by underlying-vector equality.
`toSector_isometry` (line 315) preserves their squared distance.
`constant_distance` (line 349) and `constant_pairing` (line 365) recover
the ORIGINAL physical bond form on finite sources.

This is a fixed-nome, fixed-width represented completion isometry. It does
not extract a Cauchy modulus or RangeLimit witness from a quotient class,
select representatives of an arbitrary quotient-valued sequence, delete
the original ambient time kernel, construct a time-zero multiplier action,
or instantiate the canonical continuum OS root. Full limiting observable
identification, physical spectral calibration and QFT requirements remain open.

## Verification

Two final focused checks passed. The scalar module printed four gates:
two empty axiom sets and two {propext, Quot.sound}. The physical completion
printed 23 gates, all {propext, Quot.sound}. No sorry, new axiom, classical
shortcut, native_decide or weakened canonical field was introduced.

Early completion attempts hit a dependent-conversion heartbeat limit.
A temporary local increase did not resolve it and was reverted; abstracting
the generic convergent-row construction did. The final check passed at the
default heartbeat setting. Only the main agent compiled; parallel agents
supplied proofs and independent algebra/source reviews.

Checks used one worker, a 20 GiB ceiling, 12 GiB OS reserve and dynamic
safety telemetry. Preflight found no competing Lean/Lake/test/runner process;
the initial memory check reported 91% free. No broad root build or audit was
run. Root imports and supporting documentation were updated; canonical
chart labels, states and frontier fields are unchanged.

Final logs and SHA-256:

- `/tmp/ym-quartic-coefficient-majorant-20261001.log`:
  `31e8977619926028172b5c64ff3c3bf25195c1a0428f1b4abe1a9f4108830fa0`.
- `/tmp/ym-bond-os-completion-20261001.log`:
  `e7ff734d203ad9e1709dfabee4e67175e90bacca02f13b0eebe8f5b79ce6e3b5`.
