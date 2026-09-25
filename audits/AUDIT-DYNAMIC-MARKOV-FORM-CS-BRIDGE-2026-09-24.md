# Audit: dynamic Markov-form Cauchy--Schwarz bridge

## Scope

This audit records the new scale-indexed bridge from a completed one-step
form-gap witness and a completed Markov-form Cauchy--Schwarz witness to the
literal squared-norm estimate.  It is a certificate compiler only: no
Cauchy--Schwarz family inhabitant, physical-rate band, thermodynamic limit,
continuum construction, or Clay conclusion is supplied.

## Declarations

| declaration | location | result |
|---|---|---|
| `DynamicVacuumSectorCompletedFormGapFamily` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:44` | Scale-indexed `CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData` on the dynamic family's actual nome and completed carrier. |
| `DynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:53` | Scale-indexed `CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData`; this is an explicit open input, not an inhabitant. |
| `channel_completed_norm_gap_of_formGap_and_markovCS` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:65` | Kernel-checked same-object estimate `⟨Tv,Tv⟩ ≤ rate² ⟨v,v⟩` for every channel vector and scale, using `centralPhysicalVacuumSectorCylinderCompletedTransfer_norm_gap`. |

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

The declaration reports only `{propext, Quot.sound}`.  No `sorryAx`,
`Classical`, custom axiom, `native_decide`, or `noncomputable` declaration is
introduced by this bridge.

## Boundary

The missing `DynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily`
inhabitant remains the next analytic obligation.  Consequently this bridge
does not change the canonical chart: fixed-parameter completed contraction is
still checked, while spatial/spacing-uniform control, scaling survival,
thermodynamic/continuum passage, physical mass, and every-group construction
remain open.
