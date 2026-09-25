# Audit: dynamic Markov-form Cauchy--Schwarz bridge

## Scope

This audit records the new scale-indexed bridge from a completed one-step
form-gap witness and a completed Markov-form Cauchy--Schwarz witness to the
literal squared-norm estimate.  The existing adaptive Markov-form theorem now
supplies the Cauchy--Schwarz family constructively.  This remains a certificate
compiler only: no physical-rate band, thermodynamic limit, continuum
construction, or Clay conclusion is supplied.

## Declarations

| declaration | location | result |
|---|---|---|
| `DynamicVacuumSectorCompletedFormGapFamily` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:51` | Scale-indexed `CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData` on the dynamic family's actual nome and completed carrier. |
| `DynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:56` | Scale-indexed `CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData` on the same completed carrier. |
| `canonicalDynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:66` | Inhabited by `centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData`, itself supplied by the adaptive completed Markov-form theorem. |
| `channel_completed_norm_gap_of_formGap_and_markovCS` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:78` | Kernel-checked same-object estimate `⟨Tv,Tv⟩ ≤ rate² ⟨v,v⟩` for every channel vector and scale, using `centralPhysicalVacuumSectorCylinderCompletedTransfer_norm_gap`. |
| `channel_completed_norm_gap_of_formGap` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:105` | Same estimate with the canonical Cauchy--Schwarz producer discharged. |
| `marginalHalfGeometricCompletedFormGapFamily` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:79` | Inhabited `w = 1/2` form-gap family on the explicit geometric-spacing family. |
| `marginalHalfGeometricCompletedFormGapFamily_rate` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:85` | Pins its scale-wise rate to `cutoffUniformRate (1/2)`. |
| `marginalHalfGeometricMovingCube_completed_norm_gap` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:143` | Non-vacuous literal moving-centered cube channel estimate at every geometric scale. |

The form-gap family is redeclared in this namespace so the bridge can be
checked independently of the heavier relative-loss staging import.  Its fields
still name the same completed carrier and transfer objects.

## Verification

Focused monitored command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 40 \
  --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean \
  --check-output /tmp/ym-gap-dynamic-markov-form-cs-bridge.log --status-seconds 30
```

The declarations report only `{propext, Quot.sound}`.  No `sorryAx`,
`Classical`, custom axiom, `native_decide`, or `noncomputable` declaration is
introduced by this bridge.

## Boundary

The Cauchy--Schwarz obligation is now discharged for the dynamic family, and
the fixed-`w = 1/2` geometric form-gap family supplies a concrete moving-cube
norm-gap instance.  The margin is still fixed in lattice units while spacing
tends to zero.  Consequently this bridge does not change the canonical chart:
spatial/spacing-uniform control, scaling survival, thermodynamic/continuum
passage, physical mass, and every-group construction remain open.
