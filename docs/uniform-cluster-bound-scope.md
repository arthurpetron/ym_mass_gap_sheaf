# Scope: genuinely inhabiting `UniformClusterBound` (the Λ→∞ continuum-oracle, 2026-06-22)

Target: the thermodynamic-limit oracle `ClusterGapReduction.UniformClusterBound` — the volume-uniform
(Λ→∞), fixed-spacing strong-coupling cluster bound (the project's stand-in for Osterwalder–Seiler /
Seiler / Shen–Zhu–Zhu). Currently inhabited only by DEGENERATE witnesses (constant-in-Λ family,
`tailConst=0`). This scopes a GENUINE inhabitant. (Read-only mapping; no code changed.)

## What's already genuine (the payoff is real)

- **The bridge is PROVED**: `UniformClusterBound → IsPositive continuumRate` (`clusterBound_continuum_mass_isPositive`,
  `converges`, `floor_persists`), axiom-clean. So a genuine inhabitant WOULD yield an honest Λ→∞
  positive mass at fixed spacing — the architecture is sound and the win is real.
- **The KP limit engine is PROVED**: `KPLimit.crealOfGeoIncrement` (two-sided geometric single-step
  increment ⇒ `CReal` limit with explicit `HalfPow` modulus) and `KPIncrement` packaging ("ratio
  `r≤1/2` ⇒ geometric increment `C·(1/2)^Λ`"). The engine is ready to CONSUME a real cluster bound.
- **One genuine strong-coupling atom**: `HeatKernelGap` (`sep = w³ < 1`, `gapMargin = 1−w³ > 0`,
  monotone, closed form) — a real compact-operator gap.
- **OS2 reflection positivity PROVED** unconditionally (Schur/SOS), but it's positivity, not a gap/rate.

## The bottleneck (decomposed; from the mapping)

`UniformClusterBound` needs four fields; their genuine status:
1. **Per-volume located gaps from a real transfer operator** — PARTIALLY blocked. The abstract
   `LocatedSpectralGap` machinery is real; `diagOp` is genuinely self-adjoint; but eigenvalues are
   INPUTS — no file builds the finite-volume Wilson transfer matrix from group integration. Concrete
   instances hardcode `sep=1/2`. Tractability: medium (rep-theoretically standard but real work).
2. **The volume-uniform floor `∀Λ, floorRate ≤ gapMargin(Λ)`** — THE genuine wall. Currently vacuous
   (the family is Λ-constant). With a real Λ-dependent operator this IS the strong-coupling
   cluster-expansion theorem: a Λ-INDEPENDENT positive gap-margin lower bound. **Rigorously KNOWN**
   (OS 1978, Seiler LNP 159, Shen–Zhu–Zhu — volume-independent constants exist) but **NOT formalized**;
   needs a convergent polymer/KP estimate for real SU(2) activities, which the repo only SCAFFOLDS
   (hardcoded `SU2KP` rationals, all-hypothesis `KPIncrementData`, zero-activity `constData`).
3. **Geometric tail `tailConst·(1/2)^Λ`** — tractable ONCE #2 exists (the KP engine consumes it);
   needs the connected-correlator decay, a corollary of the same expansion as #2.
4. **`modulus`** — SOLVED (`HalfPow`).

So the obligations collapse to ONE genuine new theorem: **the volume-uniform strong-coupling cluster
bound** — a Λ-independent gap floor (#2) + its geometric connected-correlator tail (#3). #1/#3/#4 are
done or follow from #2's machinery.

## Honest verdict

`UniformClusterBound` is blocked on the **strong-coupling cluster expansion** — a LARGE,
known-but-unformalized constructive-analysis build (convergent polymer/KP expansion for real SU(2)
activities, with volume-independent constants). Unlike the matched-retune sharp-CLT wall (blocked by
the absence of CReal integration) and the `TrueRGComparison` crossover (genuinely OPEN mathematics),
this wall is **rigorously known mathematics** — provable in principle — but its formalization is a
major multi-wave undertaking. The KP *engine* and the *bridge* are ready; the analytic *input* (the
expansion) does not exist in Lean.

META-PATTERN: every genuinely-open Clay direction scoped so far bottoms out on a hard
constructive-analysis wall — the sharp local CLT (matched-retune leaf), the strong-coupling cluster
expansion (this oracle), the a→0 crossover (`TrueRGComparison`), O(4) restoration. The architecture
(bridges, engines, OS2, finite-volume GNS) is genuine and proved; the analytic inputs are uniformly
the walls.

## Options

- **(A) Non-degenerate floor upgrade (tractable now, modest):** replace the fiat constant floors
  (`1/2`, `999/1000`) in the degenerate inhabitants with the PROVED `HeatKernelGap` floor `1−w³`.
  Genuine improvement (grounds the floor in real math, removes the "constant 1/2" embarrassment), but
  the family stays Λ-constant ⇒ the Λ→∞ uniformity content remains vacuous. Honest cosmetic upgrade.
- **(B) The strong-coupling cluster expansion (the wall, the real prize):** formalize a convergent
  KP/polymer expansion for SU(2) heat-kernel activities at strong coupling, deriving the
  volume-uniform gap floor + geometric tail ⇒ genuine `UniformClusterBound` ⇒ genuine Λ→∞ fixed-spacing
  gap (the OS/Seiler/SZZ result). LARGE multi-wave build; rigorously known so provable in principle;
  the highest-value genuine continuum-construction advance available, but a major commitment.
- **(C) Hold / redirect:** accept the honest map — all continuum directions are analytic walls; the
  fixed-spacing finite-volume content is the genuine proved core; Clay continuum is open.

Recommendation: (B) is the only route that genuinely advances the continuum-construction distance, and
it is the most-tractable of the walls (known mathematics). But it is a major undertaking — commit only
deliberately. (A) is a small honesty upgrade worth doing regardless if continuing here.
