# Exact all-degree reproduction by the original two-link heat packet

Date: 2026-09-21 UTC. WHOLE-PROJECT GOAL remains OPEN: constructive,
nontrivial continuum Yang--Mills on R^4 for every compact simple group,
with same-theory QFT axioms, isolated vacuum and finite positive physical
mass gap. This increment closes the local SU(2) diagonal normalization
left open in the preceding selection and lowering checkpoints.

## Exact result and hypotheses

Let p be any rational polynomial homogeneous and harmonic of degree n
in its head quaternion. All its retained-variable coefficients may be
arbitrary and signed. Define the explicit polynomial

    S(p) = dropHeadPolynomial
             (translatedHeadPolynomial (coordinateVariable 1) p).

The normalized ordinary-character identity is coefficient-exact:

    (n+1) * partialHaarHead[relativeCharacter(n) * p] = S(p).

This identity needs no constraint on the retained quaternion and no
remaining Haar integration. With at least one retained quaternion, the
FULL original finite packet has the arbitrary-boundary identity

    H_(b+1)[(relativeHeat(w,K) * p) * liftHead(r)]
      = if n <= K
        then w^(n*(n+2)) * H_b[S(p) * r]
        else 0.

The latter theorem requires b>0 for the existing off-diagonal radius/Haar
identification; K and w remain explicit. It is a finite polynomial identity
for any rational w, not a positivity or uniform limiting estimate. S(p)
really substitutes the retained link and preserves all other coefficients;
it is not a renamed or freely supplied diagonal output.

## Causal argument and source map

1. Drop the integrated head before asserting coefficient identities.
   Both x_i and y_i then map to the same retained coordinate. Sol's
   `substituteRetained_head_coordinate` and
   `substituteRetained_tail_coordinate` are at
   `lean/YMGap/Continuum/SU2QuaternionDroppedHeadSubstitution.lean:168`
   and `lean/YMGap/Continuum/SU2QuaternionDroppedHeadSubstitution.lean:176`.
   The arbitrary degree-zero endpoint is
   `substituteRetained_degree_zero` at
   `lean/YMGap/Continuum/SU2QuaternionDroppedHeadSubstitution.lean:137`.
   No raw pre-drop padding equality is asserted.
2. Substitute into the existing Euler identity. `substitute_lower_euler`
   and `substitute_lower_degree`, at
   `lean/YMGap/Continuum/SU2QuaternionHarmonicPowerSubstitution.lean:36`
   and `lean/YMGap/Continuum/SU2QuaternionHarmonicPowerSubstitution.lean:58`,
   show S(lower p)=n*S(p). `substitute_lowerIter` at line 72 and
   `drop_lowerIter` at line 87 give the factorial after exactly n steps.
   This avoids a separate multinomial repeated-derivative theorem.
3. The actual radial recurrence gives
   `sphereFourDenominator n = 2^n*(n+1)*hermiteFactorial n`:
   `radial_factorial`,
   `lean/YMGap/Continuum/SU2QuaternionHarmonicPowerSubstitution.lean:94`.
   Constructive positivity cancels the existing explicit factorial in
   the checked lowering result. `harmonic_power_substitution`, same
   file at line 105, therefore proves
   `2^n*(n+1)*partialHaarHead[p*(x.y)^n] = S(p)`.
4. The ACTUAL ordinary-character recurrence leaves just its leading
   power in this pairing. `harmonic_character_power`,
   `lean/YMGap/Continuum/SU2QuaternionHarmonicCharacterLeading.lean:73`,
   proves the stronger power-shifted recurrence for total degree at most
   the harmonic degree. The lower recurrence term vanishes by existing
   harmonic orthogonality. `harmonic_character_leading`, same file at
   line 106, supplies the exact coefficient 2^n at matching degree.
5. `character_harmonic_reproduction`,
   `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicReproduction.lean:46`,
   composes these identities into the dimension factor n+1.
   `character_harmonic_boundary_reproduction`, same file at line 70,
   retains an arbitrary boundary using the original partial Haar Fubini
   law. `heat_harmonic_reproduction`, same file at line 89, joins the
   existing FULL packet selection and its original
   `coeffW(w,n)=(n+1)*w^(n*(n+2))` to obtain the stated result.

The factorial is reused from `hermiteFactorial`,
`lean/YMGap/Continuum/SU2QuaternionGaussianHermiteOrthogonality.lean:262`.
The result does not assume a delta kernel, an identity at nome one, a
supplied reproducing formula or a positive finite heat truncation.

## What this closes and what it does not

The all-degree local diagonal reproducing/dimension normalization
obligation recorded in `AUDIT-ALL-LABEL-TWO-LINK-SELECTION-2026-09-21.md`
and `AUDIT-HARMONIC-LOWERING-2026-09-21.md` is now discharged. These older
reports are historical checkpoints, not the current status of that join.

Sol's bounded next-consumer review identifies the existing exact chain:
`productMap_pairing`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:247`,
exposes the literal product kernel; `heat_exposed`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHeatPairGeometry.lean:89`,
performs padding-aware exposure of one selected pair. The already-proved
fundamental plaquette specialization is `productMap_plaquette_of_perm`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatPlaquette.lean:186`.
The next algebraic work is an all-label selected-factor pairing, with
the reindexed harmonic/substitution and all untouched kernel factors
retained in the boundary. This review does not establish that new join.

The result remains local and harmonic. The actual all-block product
kinetic map and a sufficient polynomial/harmonic decomposition still
need to be joined to it. Inactive slots are Haar projections, not angular
heat evolution on the entire polynomial space. Reuse the existing
original terminal-source fringe reduction `energy_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:129`.

For the required original-weight estimate, V_K*g_K*f changes with K.
The exact result for a given polynomial does not supply a uniform bound
on that changing family. Cutoff control, a useful finite-time comparison,
the SAME-variance small one-step rate, spatial/scaling survival, physical
mass calibration, canonical full OS/QFT and every compact simple group
remain OPEN. No frontier field, analytic premise, hole or axiom was
introduced, removed or weakened. No continuum mass-gap claim is made.

## Verification and division of work

Four final focused checks passed 19 printed gates (8, 6, 2, 3), all within
`{propext, Quot.sound}`. `dropHeadPolynomial_congr` has no axiom dependencies;
the substitution-addition gate uses only `propext`. The dependency-complete
target `+YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction:olean`
passed. Final logs contain no errors, warnings, classical dependencies or
`sorryAx`. Checks were serialized under the safe launcher with one capped
20 GiB worker. No full-root build, full-tree audit or guard was run;
automatic CI remains manual-only.

Final logs:

- `/tmp/ym-gap-dropped-head-substitution-check.log`
- `/tmp/ym-gap-harmonic-power-substitution-check.log`
- `/tmp/ym-gap-harmonic-character-leading-check.log`
- `/tmp/ym-gap-relative-harmonic-reproduction-check.log`
- `/tmp/ym-gap-harmonic-diagonal-producers-build.log`
- `/tmp/ym-gap-harmonic-power-substitution-build.log`
- `/tmp/ym-gap-relative-harmonic-reproduction-build.log`

Sol supplied the bounded dropped-substitution draft, independently reviewed
the three main proofs (PASS), and inventoried the next product-map consumer.
Main supplied the
Euler/radial cancellation, character recurrence, actual full-packet join,
integration fixes and serialized verification.
