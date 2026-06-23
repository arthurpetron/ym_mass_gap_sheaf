# Correction: the SZZ character-surrogate Wave 2/3 interacting chain is inadequate (2026-06-23)

Honesty correction. On close inspection while assembling Wave 3, the Wave-2 interacting construction
(`CharChainWilson.lean`) was found to be STRUCTURALLY INADEQUATE as a model of the Shen–Zhu–Zhu (SZZ)
strong-coupling Bakry–Émery mechanism. Wave 3 was therefore NOT merged. The Lean is sound (the theorems
are honestly conditional), but the framing of the named obligation overstated what it is. This documents
the defect and the genuine requirement.

## The defect

`CharChainWilson.chainW β` is defined as `{ L := wilsonW β, ... }` — the **off-diagonal-only** Wilson
coupling, with the free Casimir diagonal DROPPED (the file's own comment: "to keep a valid generator we
use the FULLY off-diagonal Wilson coupling as the only generator and carry the diagonal Casimir energies
through the curvature floor abstractly"). Consequences:

- `wilsonW β` couples states 0↔2 with rate β; `−L` has spectrum `{0, 0, 2β}`, so `chainW`'s real excited
  spectral gap is `2β` (small at strong coupling), NOT the free Casimir gap `3/4`.
- `WilsonHessianSmall C β` is DEFINED as `chainW.CD(3/4 − Cβ)`. For a reversible chain `CD(K) ⟹ gap ≥ K`,
  so `WilsonHessianSmall ⟹ 3/4 − Cβ ≤ 2β ⟹ β ≥ 3/(4(C+2))`.
- Therefore `WilsonHessianSmall` is satisfiable (and true) ONLY for `β ≥ 3/(4(C+2))` — β BOUNDED BELOW,
  the OPPOSITE of the small-β strong-coupling regime. At genuine strong coupling (β→0) it is FALSE /
  uninhabitable.

So the named obligation is NOT "the O(β) Hessian smallness estimate" it was billed as; it is the
unsatisfiable-at-strong-coupling assertion that the BARE off-diagonal chain already has the free `3/4`
gap. The free `CD(3/4)` floor (`charChainMode_free_CD_floor`) is genuine but lives in a DIFFERENT
generator (`charChainMode`, the diagonal chains) and was never combined with the interaction in one
generator. A Wave-3 conditional inhabitant built on `WilsonHessianSmall` is consequently vacuous /
misleading at the regime of interest, and was not merged.

## What IS still genuine

- WAVE 1 (`CharChainFree.lean`): `charChain_free_CD : (chainOf casimirGap).CD casimirGap` — the FREE
  SU(2) heat-kernel curvature `CD(3/4)` on the diagonal character chain. UNCONDITIONAL, axiom-clean,
  correct. This stands.
- WAVE 2 partial: `charChainMode_free_CD_floor` (free multi-mode floor on the diagonal chains) and the
  genuine off-diagonal `wilsonW`/`chainW` as a valid `RevGen` — these are sound. What is WRONG is the
  INTERPRETATION of `WilsonHessianSmall` as the SZZ estimate and the downstream conditional gap.

## The genuine requirement (what a faithful surrogate needs)

The SZZ mechanism is `K_S = (group Ricci) − (interaction Hessian)` ON ONE GENERATOR. A faithful surrogate
must use the COMBINED generator `L = L_free(diagonal Casimir) + β·W(off-diagonal Wilson)` in a SINGLE
`RevGen`, and prove `CD(K_S)` for THAT generator — which requires the free curvature `3/4` and the
interaction `O(β)` to be computed together (the multi-mode `Γ₂` on the combined chain). That is exactly
the heavy multi-mode Bochner/Parseval step the Wave-1/Wave-2 agents repeatedly avoided (Wave 1: 2-state
per mode; Wave 2: off-diagonal only). It is research-grade formalization, NOT assembly.

Only on the combined generator is the `O(β)` Hessian-smallness obligation the genuine (satisfiable at
small β) SZZ estimate; the split-generator shortcut produces a false/backwards obligation.

## Verdict / recommendation

- Wave 3 NOT merged (vacuous at strong coupling).
- `CharChainWilson.lean` (already merged) is sound but its header overstates `WilsonHessianSmall`; an
  in-file CORRECTION note is added flagging the inadequacy and pointing here.
- Genuine completion = redo the interacting chain on the COMBINED generator (free Casimir diagonal +
  Wilson off-diagonal) with `CD(K_S)` proved on it — the heavy multi-mode `Γ₂` step. This is the real
  difficulty (consistent with the standing functional-form verdict that even the fixed-spacing geometric
  gap is genuine work; the continuum remains wrong-form for curvature).
- The honest banked result of the geometric-surrogate effort is WAVE 1: a genuine free `CD(3/4)` anchor
  at the `RevGen` level. The interacting surrogate is OPEN (needs the combined-generator multi-mode CD).

Process note: this should have been caught at the Wave-2 checkpoint (the `chainW := wilsonW` definition
drops the free diagonal). It was caught at the Wave-3 assembly. The lesson: verify a named obligation is
SATISFIABLE in the intended regime before building conditional results on it.
