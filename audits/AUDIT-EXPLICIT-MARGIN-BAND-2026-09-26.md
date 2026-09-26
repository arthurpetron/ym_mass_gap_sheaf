# Audit: explicit margin-band compiler (2026-09-26 UTC)

## Scope

This increment refines the changing-family physical-calibration obligation.
It does not claim a changing-family denominator estimate, spatially uniform
rate, OS/GNS identification, continuum limit, physical mass, all-group result,
or the Clay theorem.

## Checked declarations

| declaration | source | role |
|---|---|---|
| `one_add_sub_self_eqv` | `lean/YMGap/Continuum/BF4PhysicalCubeCutoffUniformGapAlgebra.lean:28--36` | Scale-free denominator-minus-numerator identity for a denominator presented as `1 + numerator`. |
| `one_sub_divPos_eqv_inverse` | `lean/YMGap/Continuum/BF4PhysicalCubeCutoffUniformGapAlgebra.lean:42--55` | Scale-free rational identity `1 - p/q ≈ (q-p)/q` for `0 < q`. |
| `ExplicitMarginInverseLaw` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorExplicitMarginBand.lean:35--47` | Same-family input exposing a positive denominator and exact lattice-margin reciprocal law. |
| `ExplicitMarginDenominatorBand` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorExplicitMarginBand.lean:49--65` | Same-family lower/upper product inequalities against the scheduled spacing. |
| `ExplicitMarginDenominatorBand.toPhysicalRateBand` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorExplicitMarginBand.lean:71--95` | Equality-and-order compiler into `DynamicVacuumSectorPhysicalRateBand`. |
| `ExplicitMarginDenominatorBand.toContinuumGapTheorem` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorExplicitMarginBand.lean:97--105` | Delegates to the existing physical-rate-to-continuum-gap interface. |
| `changingNomeMarginDenominator` | `lean/YMGap/Continuum/BF4PhysicalChangingNomeExplicitMarginLaw.lean:27--31` | Concrete BF4 denominator along the nonconstant changing-nome schedule. |
| `changingNomeExplicitMarginInverseLaw` | `lean/YMGap/Continuum/BF4PhysicalChangingNomeExplicitMarginLaw.lean:42--65` | Exact reciprocal margin law for the definitionally same completed changing family. |
| `changingNomeExplicitMarginDenominatorBand_toPhysicalRateBand` | `lean/YMGap/Continuum/BF4PhysicalChangingNomeExplicitMarginLaw.lean:75--78` | Specialized consumer exposing the two remaining denominator-versus-spacing fields. |

## Verification

Both source files were checked individually with the monitored wrapper, one
Lean worker, an 8 GiB worker ceiling, and an 8 GiB reserve:

```text
python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 8 \
  --check-worker-limit-gib 8 --check \
  lean/YMGap/Continuum/BF4PhysicalCubeCutoffUniformGapAlgebra.lean

one_add_sub_self_eqv depends on axioms: [propext]
one_sub_divPos_eqv_inverse depends on axioms: [propext, Quot.sound]

python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 8 \
  --check-worker-limit-gib 8 --check \
  lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorExplicitMarginBand.lean

ExplicitMarginDenominatorBand.toPhysicalRateBand depends on axioms:
[propext, Quot.sound]
ExplicitMarginDenominatorBand.toContinuumGapTheorem depends on axioms:
[propext, Quot.sound]

python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 8 \
  --check-worker-limit-gib 8 --check \
  lean/YMGap/Continuum/BF4PhysicalChangingNomeExplicitMarginLaw.lean

changingNomeExplicitMarginInverseLaw depends on axioms:
[propext, Quot.sound]
changingNomeExplicitMarginDenominatorBand_toPhysicalRateBand depends on axioms:
[propext, Quot.sound]
```

No `sorryAx`, `Classical.*`, `native_decide`, or custom axiom was reported.

## Remaining typed input

The compiler requires an inhabitant of `ExplicitMarginInverseLaw` and an
`ExplicitMarginDenominatorBand` for the actual changing family.  Those fields
are intentionally not fabricated here.  In particular, the finite algebra
identity is generic and does not itself prove that the dependent BF4
`gapDenominator (changingNome scale)` has the required scale comparison with
`changingSpacing.spacing scale`.
