# Audit: fixed-parameter complex Wilson relative loss

## Scope

This audit covers
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexRelativeLoss.lean`.
The carrier is the existing all-nome Wilson completion complexified into two
copies.  The result is fixed in nome and width and is not a continuum or
physical-mass statement.

## Checked declarations

- `complex_twoStep_relative_loss` (`lean/YMGap/Continuum/BF4WilsonAllNomeComplexRelativeLoss.lean:53`) converts the existing same-carrier strict two-step form bound into the explicit deficit inequality
  `(1-r) * ||x||² <= ||x||² - <x,T²x>` on every complex vacuum-orthogonal state.
- `complex_twoStep_relative_loss_margin_positive` (`:62`) proves the associated rational margin is positive from the existing strict rate inequality.

The conversion retains the same completed pairing and uses no new carrier,
representative choice, or continuum identification.  It is the concrete
fixed-parameter shape consumed by the relative-loss bridge specification.

## Verification

Focused command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 40 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeComplexRelativeLoss.lean \
  --check-output /tmp/ym-gap-complex-relative-loss.log
```

The command exited 0.  Both printed axiom reports contain only
`{propext, Quot.sound}`; no `sorryAx`, classical axiom, or custom axiom occurs.

## Boundary

The margin depends on the nome and width, and the theorem has no bridge
inhabitant connecting this Wilson carrier to an OS carrier.  Therefore it does
not close spacing control, thermodynamic/continuum passage, physical mass, or
the Clay target.
