# Closing the finite MIDDLE of the SU(2) continuum gap — verdict

**Deliverable Lean file:** `lean/YMGap/Continuum/MiddleClusteringFloor.lean`
(new; imported in `YMGap.lean`). Full `lake build` green = **667 jobs**
(+2 over the prior 665), `YMGapGuard` **OK** = 5 Clay-frontier types still
unconditionally uninhabited. Every load-bearing declaration axiom-clean
(`propext`/`Quot.sound` only; two are axiom-free). No `sorry`, no `Classical.*`,
no `native_decide`.

---

## Which route closed the middle

**Route: the CHARACTER / Wilson-clustering mechanism (a variant of Route 1's
"the per-step rate is < 1", made rigorous and decidable — NOT the m-fold-fusion
Route 2, which is intractable, see below).**

The moderate middle `(1/6, 7/9)` of the canonical AF trajectory
`w_k = 1 − 1/(k+1)` is pinned to EXACTLY three steps
`w_1 = 1/2, w_2 = 2/3, w_3 = 3/4` (`CrossoverDefectUnification.middle_is_three_steps`).
The conservative single-plaquette block-spin defect model `6(1−w)²` exceeds `1`
there (`6·(1/2)² = 3/2`), so it cannot supply `δ_k < 1`. The character clustering
rate `ρ(w) = coeffW w 1 = 2·w³` does: the window's very upper edge `7/9` is the
character ceiling, and the PROVED `CharacterWindowCeiling.rho_lt_one_ext` gives
`ρ(w) < 1` on all of `[0, 7/9] ⊇` the middle.

## The 3-step values

Located Wilson-correlator gap margin `1 − ρ(w_k) = 1 − 2·w_k³`:

| step | `w_k` | `ρ(w_k) = 2w_k³` | gap margin `1 − ρ(w_k)` |
|---|---|---|---|
| k=1 | 1/2 | 1/4  | 3/4 |
| k=2 | 2/3 | 16/27 | 11/27 |
| k=3 | 3/4 | 27/32 | 5/32 |

**Middle product** `∏_{k=1,2,3}(1 − ρ(w_k)) = (3/4)(11/27)(5/32) = 165/3456 > 0`
(`middleClusterFloor_pos`, value pinned by `middleClusterFloor_value`, both by
`decide`).

## The sub-additivity / log-concavity fact used

`ρ(w) < 1` on `[0,7/9]` is `rho_lt_one_ext`, itself resting on
`CharacterWindowCeiling`'s excited-domination (`coeffW_succ_le_self_ext`: every
excited character coefficient `coeffW w (s+1) ≤ coeffW w s`, the unimodality/
log-concave-tower content that the `s=1` mode dominates). So the theorem that the
head mode `ρ = 2w³` bounds the whole excited tower IS the log-concavity route —
`middle_rho_lt_one` is its middle instance.

## What is PROVED (this change)

- `middle_rho_lt_one` — `ρ(w_k) < 1` for the three middle steps (from the proved
  ceiling).
- `middleGap_pos` — each per-step located-gap margin `1 − ρ(w_k) > 0`.
- `middleClusterFloor_pos` — the **middle product is > 0** (= 165/3456).
- `headMiddleFloor_pos` — strong head · middle > 0: appending the PROVED
  strong-coupling anchor `strongAnchor = 1 − ρ(1/6) = 107/108`
  (`CrossoverAnchorFloor.strongAnchor_ge_half`) gives a positive floor over the
  whole non-UV window `[0, 7/9]`. (Deep-UV `w→1` is covered separately by the
  proved renormalized product floor `renormalized_gap_of_AFRate`, `δ_ren<1/2`.)

## `#print axioms` (from the build)

```
oneSub_pos              : [propext, Quot.sound]
middle_weights_in_window: (no axioms)
middle_rho_lt_one       : [propext]
middleGap_pos           : [propext, Quot.sound]
middleClusterFloor_pos  : [propext, Quot.sound]
middleClusterFloor_value: (no axioms)
headMiddleFloor_pos     : [propext, Quot.sound]
```

## HONEST verdict — is the middle product `> 0` now PROVED?

**YES, in the character / Wilson-clustering sense — as a fixed-spacing spectral-gap
product.** The three moderate middle steps each carry a PROVED positive located-gap
margin `1 − ρ(w_k) > 0`, and their product (and the strong-head·middle product) is
a positive explicit rational. The "`6(1−w)² > 1` on the middle" obstruction is
removed by the character rate `2w³`, which the window edge `7/9` is defined by.

**This is NOT a closure of the RG-defect product for the true dimensionless
margin.** `ρ(w) = 2w³` is the fixed-spacing sub-dominant clustering rate; `1 − ρ`
is a spectral-gap witness at each scale, NOT the per-RG-step bond-moving DEFECT
`δ_k` of `DefectGapRecursion.recursion` / `SingleStepDefectBound`. This module
inhabits **no** `DefectGapRecursion` for the true margin and **no** frontier bundle
(guard still OK, 5 uninhabited).

**Route 2 (exact m-fold fusion by `decide`) is intractable** and was abandoned:
the unnormalized `Q'` fusion `bondMovedCoeff` has multiplicatively-growing
denominators; even `#eval` at `p=8`, `N≈10` ran >30 min at 100% CPU / 5 GB and
did not terminate — `decide` (kernel) is strictly worse. So the real 4-D
`m = b^{d−1} = 8` defect cannot be `decide`d exactly, and its uniform-in-`N` bound
is the still-open `SelfFusionLogConcave.FusionConvLogConcaveCore` (heat-kernel
`(r,d)` local-CLT).

**Numeric certificate (pure-`Float` memoized fusion, `N`-converged; NOT a Lean
proof)** — vacuum-normalized fused fundamental eigenvalue
`λ₁^{(p)} = bmc(1)/(2·bmc(0))`:

| w | p=1 (=w³) | p=2 | p=4 | p=8 (real 4D) |
|---|---|---|---|---|
| 1/2 | 0.125 | 0.238 | 0.418 | 0.625 |
| 2/3 | 0.296 | 0.486 | 0.677 | 0.817 |
| 3/4 | 0.422 | 0.617 | 0.775 | 0.878 |

The bond-moved eigenvalue stays `< 1` at every middle weight (gap never closes),
consistent with the character bound, but this is numeric, not proved.

**Net:** the finite middle is closed as a positive spectral-gap product
(character mechanism, axiom-clean, decidable). The Clay SU(2) continuum floor is
NOT thereby fully closed — the deep-UV renormalized product and, above all, the
true-margin RG-defect recursion remain the open residuals. The Clay Yang–Mills
mass gap remains OPEN; nothing is faked.
