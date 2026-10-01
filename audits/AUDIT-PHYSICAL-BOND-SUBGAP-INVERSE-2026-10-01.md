# Rational subgap inverse on the physical bond completion

Date: 2026-10-01 UTC. The constructed original-sector inverse now acts
on EVERY vacuum-orthogonal class of the completed physical bond carrier,
not merely on an injected represented subspace. Its domain, pairing and
shifted derivative are the existing physical bond objects.

## Constructed operator and laws

Write H for the existing derivative of bond time translation and delta for
the original `BF4WilsonAllNomeLogCoreGap.coreMargin`. For every rational
0<=a<delta the construction supplies a domain point u=R_a x and proves

    (H-a*I) R_a x = x,
    R_a (H-a*I) u = u,
    ||R_a x||^2 <= (delta-a)^(-2) ||x||^2.

The first law covers every centered physical bond class. The second covers
every centered class of the existing derivative domain. The output remains
vacuum-orthogonal. In particular a=0 is included.

The sole new module is
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSSubgapResolvent.lean`:

- `CenteredBond`, line 50, is the ordinary orthogonal subtype.
- `resolventDomain`, line 117, returns the actual domain class.
- `resolvent`, line 128, takes its original physical input vector.
- `input_orthogonal`, line 132, preserves the vacuum complement.
- `inverse_right`, line 148, proves surjectivity with the constructed inverse.
- `shiftedCentered`, line 164, retains centeredness of shifted domain values.
- `inverse_left`, line 202, recovers every centered domain class.
- `norm_bound`, line 215, proves the stated original squared-norm cap.

Dependent quotient recursion first constructs each source row's original
range witness and subgap domain point. Original subgap injectivity proves
that different representatives produce the same domain class. Orthogonality
is a Prop proof, not an erased data witness. No representative selector,
new analytic hypothesis, altered norm or smaller carrier is used.

## Scope and verification

Nome and spatial width are fixed; delta retains both dependencies. The
statements concern rational real shifts and dimensionless lattice time.
They do not assert a complex resolvent, full spectral calculus, an inverse
on the ambient time-kernel states, physical mass calibration or continuum
reconstruction. The source-specific energy/variance scaling input is still
open; the accompanying source review is
`audits/AUDIT-ACTUAL-SOURCE-MOMENT-INPUTS-2026-10-01.md`.

The final focused check exited successfully with eight printed gates, all
exactly {propext, Quot.sound}. No sorry, axiom, Classical, native_decide,
noncomputable declaration or canonical field was added. Verification used
one worker, a 20 GiB worker ceiling, 12 GiB OS reserve and live monitoring.
Preflight found no competing compiler/runner and reported 90 percent memory
free. No full root build, tree audit or guard was run. The root import is
registered but not checked as an aggregate. No canonical chart state changed.

Final log: `/tmp/ym-bond-subgap-resolvent-20261001.log`.
SHA-256: `f10251fcf32b78333aaa958788718b7fef66cb08639ff32aca2b8af9a7a6d668`.
