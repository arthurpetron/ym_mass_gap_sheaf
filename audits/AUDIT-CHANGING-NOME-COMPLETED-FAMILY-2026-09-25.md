# Audit: explicit changing-nome completed SU(2) family

Date: 2026-09-25 UTC  
Module: `lean/YMGap/Continuum/BF4PhysicalChangingNomeDynamicFamily.lean`

## Exact declarations

The module defines the nonconstant nome schedule
`changingNome (scale : Nat) : Q' := Q'.invSucc (scale + 2)` at
`lean/YMGap/Continuum/BF4PhysicalChangingNomeDynamicFamily.lean:36--37`.
Its constructive side conditions are:

- `changingNome_pos` at `:39--41`;
- `changingNome_lt_one` at `:43--47`;
- `changingNome_le_half` at `:49--53`; and
- `changingNome_nonconstant` at `:55--57`.

The independent spacing schedule is `changingSpacing` at `:59--61`, with
`spacing j = Q'.invSucc (j + 1)`.  Its spacing-to-zero witness
`changingSpacingToZero` is at `:63--70`; the modulus is explicitly
`epsilon.den` and the proof uses `HalfPow.invSucc_den_le`.

`changingNomeDynamicFamily` at `:72--82` inhabits
`DynamicVacuumSectorCompletedFamily 0`.  Its `completedGap` field is the
existing `completedSectorContraction` applied at each scale, so the family
has a completed strict contraction at every scheduled nome.  The projections
`changingNomeDynamicFamily_rate`, `changingNomeDynamicFamily_spacing`, and
`changingNomeDynamicFamily_nome` are at `:84--94`.

The one-step form certificate is `changingNomeFormGap` at `:97--103`.
`changingNomeFormGap_rate` at `:105--108` identifies its rate definitionally
with the same `cutoffUniformRate (changingNome scale)`, and
`changingNomeFormGap_margin_positive` at `:110--112` proves the strict
positive lattice margin.  These declarations expose the form-level input for
a future relative-loss compiler without asserting any relation to the
vanishing spacing.

The same-object channel is
`changingNomeMovingCubeChannel` at `:96--98`.  Its positive zero-time
response is `changingNomeMovingCube_zero_isPositive` at `:100--105`, and its
scale/time connected-square decay is
`changingNomeMovingCube_connectedSq_decay` at `:107--118`.

## Verification

The focused command was:

```text
python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 8 \
  --check-worker-limit-gib 12 \
  --check lean/YMGap/Continuum/BF4PhysicalChangingNomeDynamicFamily.lean \
  --check-output /tmp/ym-changing-nome-family.log --status-seconds 20
```

The check exited successfully.  The printed axiom dependencies for every
load-bearing declaration in the module are contained in `{propext,
Quot.sound}`; no declaration reports `sorryAx`, `Classical.choice`,
`Classical.em`, `native_decide`, or a custom axiom.

## Scope boundary

This is an inhabited changing-nome completed-family data record and a
concrete same-object RC channel.  It does not establish a physical-rate band,
a changing-family observable/response pin, spatially uniform bounds, an
Osterwalder--Schrader/GNS identification, thermodynamic or continuum limits,
the full QFT axioms, an all-compact-simple-group theorem, or the Clay mass-gap
conclusion.
