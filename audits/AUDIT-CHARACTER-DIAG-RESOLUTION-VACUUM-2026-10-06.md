# Audit: vacuum defect of `WilsonSpectralBridge.CharacterDiagResolution` (2026-10-06 PT)

**DEPRECATED (for physical operators with an invariant vacuum). This tag is recorded here
only.**  The structure's docstring is not edited, to avoid any rebuild hazard on the shared
olean chain; `WilsonSpectralBridge` has many downstream consumers.

## Defect

The fields `parseval_self : ∀ x, ⟨x,x⟩ = Σ_{i<N} cᵢ(x)` and
`parseval_T : ∀ x, ⟨Tx,x⟩ = Σ λᵢ cᵢ(x)` range over excited modes only
(λᵢ = w^{c4(i+1)} ≤ w³) and are stated for ALL x.  Together they force
`⟨Tx,x⟩ ≤ w³⟨x,x⟩` for every x (`wilsonTransferFormGap` derives exactly this).  So if the
operator has a vector Ω with T Ω = Ω and ⟨Ω,Ω⟩ > 0, the structure is uninhabitable.
`GNSDynamics.TransferOperator` has a `vacuum` field but no `T vacuum = vacuum` axiom, so
there is no formal contradiction; the defect is semantic.

## Consumers (grep of the worktree at a2e3906a)

| Declaration | Use | Status |
|---|---|---|
| `WilsonSpectralBridge.wilsonTransferSpectralBridge`, `wilsonTransferFormGap` | hypothesis P | form gap for ALL x; vacuous for any op with a normalized fixed vacuum |
| `CharacterDiagResolutionProof.wilsonCharacterDiagResolution` | constructor from `schur_self`/`schur_T` ∀x | the same Schur hypotheses are ∀x, so the same defect |
| `PhysicalWilsonBridge.physicalCharacterDiagResolution` (+ form gap) | constructor | same |
| `PhysicalCharCoordinateMap` (instance at `charTransfer`) | **inhabitant** | consistent only because `WilsonSchurIdentities.charTransfer` has `vacuum := 0` on a vacuum-free excited-character space |
| `WilsonOperatorNormGapHandoff`, `WilsonLinkedOSReconstruction` (`WilsonCharacterOS4Pin` / `WilsonCharacterSquarePin`) | hypotheses on the physical `P.op` | vacuous if `P.op` fixes a normalized vacuum |
| `Rubric.ReconstructionScorecardFinal.OpenPhysicalWilsonBridge` (abbrev, "HISTORICAL OPEN TOKEN") | open token | uninhabitable for a physical op with a vacuum; already flagged historical |
| `ReconstructionCapstone`, `WilsonParsevalExt`, `SymbolTypedParsevalClose`, `WilsonSchurIdentities`, `WilsonLinearFC`, `LinearTransferOperator`, `ContinuousFunctionalCalculusForm`, `Rubric.FrontierDAG`, `Rubric.ReconstructionScorecard` | open/import or docstring mentions | inherit the same caveat where they assume P for a physical op |
| `SpectralHalvingMargin` | docstring only | unaffected |
| `SpecMaxRateFamily.CharacterDiagNormResolution` | **replacement**: fields restricted to `perp x` | correct form |

## Decision

DEPRECATED for physical (vacuum-carrying) operators; use `CharacterDiagNormResolution`
(restricted to `perp`).  Theorems remain valid as stated: they are vacuous, not false.
