# sub_papers/ — publishable artifacts extracted from the mechanization

Each subdirectory holds an `Outline.md` for one candidate-publishable
mathematical artifact discovered or produced in this repository's Lean
development. The outlines are written to be self-contained: a
mathematician with the outline (and read access to the cited Lean
declarations) should be able to write and submit the paper.

**Honesty tiers** (every outline states its tier and its
literature-check obligations; a novelty claim is NOT asserted until the
checks in the outline are done):

- **Tier A** — candidate-novel theorem-level mathematics.
- **Tier B** — known mathematics, novel constructive/mechanized
  treatment (ITP / constructive-analysis venues).
- **Tier C** — methodology.

| # | Directory | Tier | One-line content |
|---|---|---|---|
| 1 | 01-character-tail-su2-worst-case | A | SU(2) dominates all compact simple G for heat-kernel character tails; exact SU(3) certificate |
| 2 | 02-mk-bond-moving-spectral-ledger | A | Migdal–Kadanoff bond-moving: sharp summability no-go, graded cure, gap-edge and vacuum-normalization theorems |
| 3 | 03-pentagon-rigidity-squared-racah | A | Squared-Racah axioms admit a permutation model that provably fails the pentagon |
| 4 | 04-os2-reflection-vs-product | A− | Reflection positivity vs character-product positivity: a separation of OS2 forms, proved constructively |
| 5 | 05-lean4-dependency-free-bishop-reals | B | Mathlib-free Bishop reals with explicit moduli in Lean 4 (exp/log/trig/π/roots) |
| 6 | 06-constructive-kotecky-preiss | B | Kotecký–Preiss cluster expansion with moduli-as-data; Bishop-functional finite/infinite-volume states |
| 7 | 07-constructive-gns-transfer-calculus | B | Constructive GNS completion and located transfer calculus for lattice YM |
| 8 | 08-penrose-deletion-contraction | B (in progress) | Penrose tree-graph inequality by deletion–contraction over computable Ursell sums |
| 9 | 09-machine-checked-frontier-method | C | Machine-checked frontier enumeration of an open problem: the method |

Provenance: extracted 2026-07-03 from the `lean/YMGap` development
(toolchain `leanprover/lean4:v4.29.1`, Mathlib-free; axiom gates
`∅`/`[propext]`/`[propext, Quot.sound]` per `lean/AXIOM_AUDIT.md`).
All listed results are valid in MLTT/HoTT (propext = univalence for
mere propositions; Quot = set-quotient HIT); several are axiom-free.

Relationship to the main program paper (`work_plan.md` Milestone 12.1):
these are spin-offs. The main paper claims the fixed-spacing closure
and the frontier reduction; each sub-paper is a self-contained result
that stands regardless of the Yang–Mills program's eventual fate.
