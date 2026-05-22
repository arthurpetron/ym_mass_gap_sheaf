/-
Root aggregator for the `YMGap` Lean library.

Each phase's constructivity-critical modules are imported here so
`lake build` covers the whole library.

Currently populated:

  * Milestone 1.1 — SU(2) Casimir spectrum (RepTheory).
  * Milestone 2.1 — Sheaf framework: site, bound-witness presheaf
    with flabbiness, summability-certificate record, domination
    gluing on the buffer overlap, and the named compatibility
    predicate type.  See `formal/sheaf-framework.tex` and
    `docs/sheaf-framework.md`.
-/
import YMGap.RepTheory.SU2
import YMGap.Sheaf.Site
import YMGap.Sheaf.BoundWitness
import YMGap.Sheaf.Summability
import YMGap.Sheaf.Gluing
import YMGap.RG.InductiveState
import YMGap.RG.BlockSpin
