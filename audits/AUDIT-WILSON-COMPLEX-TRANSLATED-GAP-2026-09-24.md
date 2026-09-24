# Audit: translated complex Wilson gap

Date: 2026-09-24 UTC

## Scope

The checked target is
`YMGap.Continuum.BF4WilsonAllNomeComplexGap.complex_twoStep_translated` at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:132`.  It starts from
the existing complex vacuum-orthogonality witness, transports that witness
through the existing componentwise completed time map, applies the already
checked same-carrier `complex_twoStep_form_gap`, and exposes the exact
correlator indices `n` and `n+2` by the checked semigroup law.

This is a fixed coupling/width/nome statement.  It is not a continuum-time,
Hamiltonian, spacing-uniform, thermodynamic, or Clay mass-gap theorem.

## Verification

Command:

```text
python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.olean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-wilson-complex-gap-check-9.log
```

The monitored check completed successfully.  The declaration reports in the
log contain only `{propext, Quot.sound}`; no `sorryAx`, `Classical`, warning,
or error was reported.  Log SHA-256:

`b1f2e65653c2753e274858a61570dc539f2fb222e62e5e21102f3cc4315d8834`

## Boundary

The theorem strengthens the SAME complex fixed-parameter correlator API.  It
does not alter any chart marker: spatial/spacing control, scaling survival,
thermodynamic/continuum passage, physical mass calibration, full OS/QFT
structure, and every compact simple group remain open.
