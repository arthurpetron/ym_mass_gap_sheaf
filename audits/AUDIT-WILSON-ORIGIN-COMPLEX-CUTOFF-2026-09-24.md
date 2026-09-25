# Audit: origin plaquette complex-rate cutoff

Date: 2026-09-24 UTC  
Scope: `BF4WilsonAllNomeOriginComplexCutoff`

## Checked declarations

`YMGap.Continuum.BF4WilsonAllNomeOriginComplexCutoff.origin_twoStepRate_positive`
(`lean/YMGap/Continuum/BF4WilsonAllNomeOriginComplexCutoff.lean:42`) specializes
the existing same-carrier plaquette rate-positivity theorem at the explicitly
padded width `width + 2`.  The origin face is supplied by
`originFace_mem (width + 1)`, and the active-link premise is discharged by
`plaquette_active_after_padding (by omega : 1 < width + 2) originFace
(originFace_mem 0)`.  No new rate, transfer, carrier, or continuum object is
introduced.

`YMGap.Continuum.BF4WilsonAllNomeOriginComplexCutoff.origin_complexRateCutoff_bound`
(`lean/YMGap/Continuum/BF4WilsonAllNomeOriginComplexCutoff.lean:53`) consumes
that strict positivity in the existing `complexRateCutoff_bound` theorem and
returns the explicit `HKConvGen.powBaseCutoff` bound for every positive
rational error target.  The modulus remains dependent on nome, width, and the
chosen error target.

## Verification

Command:

```text
python3 scripts/safe_lean_build.py --check \
  lean/YMGap/Continuum/BF4WilsonAllNomeOriginComplexCutoff.lean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-origin-complex-cutoff-check.log
```

The monitored source check exited 0.  The log printed no warnings, errors,
`sorryAx`, or classical axioms.  Both declarations audit to exactly
`{propext, Quot.sound}`.  No existing chart node changes status: this is a
finite fixed-parameter coefficient modulus, not spacing control, scaling
survival, a physical mass, a continuum limit, or an all-group result.

## Honest boundary

The theorem proves positivity and a cutoff only after the explicit two-layer
padding.  It does not prove a width-uniform lower rate: the preceding
`no_width_uniform_computed_twoStepRate` obstruction still applies to the
computed comparison certificate.  The next frontier remains a same-object
relative loss/variance estimate or direct response along a justified changing
scale family.
