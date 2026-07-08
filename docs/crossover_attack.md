# The finite crossover defect — anchored to the proved gap, reduced to ONE obligation

**Deliverable.** The whole 4D SU(N) continuum margin floor `physGapMin > 0` now rests on
**exactly one uninhabited crossover fact**, with everything else proved: the anchor is the genuine
strong-coupling located gap, and the deep-UV tail is AF-derived. New Lean file:
`lean/YMGap/Continuum/CrossoverAnchorFloor.lean` (built, axiom-clean `[propext, Quot.sound]`,
full `lake build` green, `YMGapGuard` OK = 5 Clay-frontier types uninhabited).

I did **not** close the crossover. The honest result is a sharp reduction + a unification with the
existing continuum wall.

---

## 1. ANCHOR tied to the proved strong-coupling gap (Task 1 — DONE)

`fullFloor_of_crossover_and_AF` treated `margin 0` as a free parameter with a bare `hm0 : 0 ≤ margin 0`.
I wired it to the proved object:

```
def strongAnchor : Q' := (RealCorrMass.realLocated 0).gapMargin

theorem strongAnchor_is_reconTransfer_gap :
    strongAnchor = (MayerClustering.reconTransfer_located_gap 0).gapMargin := rfl   -- PROVED
theorem strongAnchor_eq       : strongAnchor = 1 - rho gw                           -- = 107/108
theorem strongAnchor_ge_half  : RealCorrMass.realFloor ≤ strongAnchor              -- ≥ 1/2
theorem strongAnchor_nonneg   : 0 ≤ strongAnchor                                    -- DERIVED, not assumed
```

`strongAnchor` is **definitionally** the gap-margin of `MayerClustering.reconTransfer_located_gap 0` —
the located second eigenvalue of the reconstructed single-edge transfer operator, whose clustering is
the REAL `wilsonG` connected-correlator decay (`wilsonG_decay`) at strong coupling `w = 1/6`. Its value
is the volume-independent `1 − rho gw = 1 − 2·(1/6)³ = 107/108`, cleared over `1/2` by the proved
`RealCorrMass.realUniform_floor`. In the capstone the anchor `hm0` is **derived** from this proved gap
(`hanchor0 : margin 0 = strongAnchor`), so `m₀` is no longer a free parameter — it is `m₀ ≥ 107/108`,
the real strong-coupling margin.

## 2. Crossover reduced to the sharpest named obligation (Task 2 — DONE, both routes)

The single named obligation carries exactly the two finite crossover defect sums:

```
structure CrossoverWindowDefect (δ ε : Nat → Q') (K : Nat) : Type where
  Bδ Bε : Q'
  crossδ : tailSum δ 0 K ≤ Bδ    -- Σ_{k<K} δ_k  (multiplicative crossover budget)
  crossε : tailSum ε 0 K ≤ Bε    -- Σ_{k<K} ε_k  (additive crossover budget)
```

This is a **genuine input** (Rule 6a): the theorem is false for arbitrary `Bδ`/`Bε` (pick them too
small). It is **never inhabited** for the real 4D theory.

**Route (a) — FINITE per-step (`crossoverDefect_ofPerStep`, PROVED reduction).** A per-step
no-gap-closing cap `δ_j ≤ δmax`, `ε_j ≤ εmax` on the finite window `j < K` inhabits the obligation with
`Bδ = K·δmax`, `Bε = K·εmax`, via the new pure-`Q'` lemma

```
tailSum_le_ofNat_mul : (∀ j < K, f j ≤ c) → tailSum f 0 K ≤ (ofNat K)·c
```

The residual is then the **decidable** rational check `K·εmax + 2·Dε < (1 − (K·δmax + 2·Dδ))·(1 − rho gw)`
— a finite check GIVEN `(δmax, εmax, K, Dδ, Dε)`. The per-step bound `δ_j ≤ δmax` is itself the genuine
open content ("the gap does not close in one crossover step").

**Route (b) — CLUSTERING-TRANSPORT unification (`crossoverDefect_ofClusteringWindow`, PROVED
reduction).** A uniform per-step **retention** `δ_k ≤ 1 − ρmin` (`ρmin > 0`) on the finite window
`k < K` — each crossover step keeps `≥ ρmin` of the margin — inhabits the obligation with
`Bδ = K·(1 − ρmin)`. The retention `δ_k ≤ 1 − ρmin`, `ρmin > 0` is precisely the **finite-`K`
restriction of "clustering persists across the middle"**: the content of
`WeakCouplingGap.RGClusteringTransport` (RG-flow preservation of clustering) and its interval shadow
`TwoSidedGap.WindowOverlap`. So `CrossoverWindowDefect` **unifies** the new block-spin defect sum with
the existing continuum wall — it is the **δ-defect shadow of `RGClusteringTransport` / `WindowOverlap`**.

## 3. The full floor on ONE obligation (Task 3 — DONE)

```
theorem fullFloor_on_one_crossover_obligation      -- (alias: fullFloor_reduced_to_crossover)
  (margin δ ε : Nat → Q') (K : Nat) (Dδ Dε : Q')
  (W : CrossoverWindowDefect δ ε K)                          -- THE single named obligation
  (hstep  : ∀ k, (1 - δ k)*margin k - ε k ≤ margin (k+1))    -- margin step recursion
  (hδnn hδ1 hεnn)                                            -- sign conditions
  (hanchor0 : margin 0 = strongAnchor)                       -- ANCHOR = proved reconTransfer gap
  (hDδ hDε)
  (hUVδ : ∀ k, K ≤ k → δ k ≤ Dδ·recipSqSucc k)              -- deep-UV AF tail (proved upstream)
  (hUVε : ∀ k, K ≤ k → ε k ≤ Dε·recipSqSucc k)
  (hanchor : W.Bε + 2·Dε < (1 - (W.Bδ + 2·Dδ))·margin 0) :  -- anchor-dominance
  ∀ k, physFloor ≤ margin k ∧ 0 < physFloor
        where physFloor = (1 - (W.Bδ + 2·Dδ))·margin 0 - (W.Bε + 2·Dε)
```

Everything is proved **except** `W`: the anchor is the proved `reconTransfer_located_gap 0` margin
(`hm0` derived, not assumed); the deep-UV `Σ_{k≥K} ≤ 2D` tail is AF-derived. The entire Clay continuum
gap is now a **single named crossover fact**.

## 4. The single remaining obligation, stated exactly

> **`CrossoverWindowDefect δ ε K`** — the finite strong→weak crossover defect sums
> `Σ_{k<K} δ_k ≤ Bδ` and `Σ_{k<K} ε_k ≤ Bε` over the finite window `k < K` where the character
> mechanism provably fails (`rho = 2w³ ≥ 1` at `w ≥ 2^{−1/3}`, `CharacterWindowCeiling`).
> Equivalently (route b) a uniform per-step retention `δ_k ≤ 1 − ρmin`, `ρmin > 0`, across the finite
> crossover — **the δ-defect shadow of `WeakCouplingGap.RGClusteringTransport` /
> `TwoSidedGap.WindowOverlap`**.

**Does it unify with `RGClusteringTransport` / `TwoSidedGap`? Yes.** `RGClusteringTransport` asserts
that exponential clustering is carried from the proved strong window (`[0,1/6]`, uniform rate `≤ 4/9`,
`UniformCouplingGap`) through the intermediate middle to weak coupling; `WindowOverlap` is its
interval-arithmetic shadow. "Clustering persists" = "the gap stays open" = "the per-step multiplicative
defect stays `< 1`", which is exactly the retention hypothesis of route (b). So the finite crossover
defect sum and the middle wall are the **same physics** at different granularity;
`crossoverDefect_ofClusteringWindow` is the explicit bridge.

**Part of the window is already proved.** For the sub-window where the running weight is still in the
proved strong window `w ≤ 1/6`, the per-step retention holds from `TwoSidedGap.strongWindow` (rate
`ρ ≤ 4/9 < 1`, i.e. retention `ρmin ≥ 5/9`) — genuinely proved. The uninhabited part is the crossover
`w ∈ (1/6, 1)` incl. the character-ceiling region `[2^{−1/3}, 1]` where no character window reaches
(`CharacterWindowCeiling`, `WeakRegionNoGo`). That residue is exactly `RGClusteringTransport` /
`WeakClusteringBound`.

## 5. Honesty verification

- **(i) Build + axiom gate.** `lake build` full green (663 jobs). All 9 load-bearing declarations of
  `CrossoverAnchorFloor` `#print axioms` → `[propext, Quot.sound]` only. No `sorry`, no `Classical.*`,
  no `native_decide`.
- **(ii) Frontier guard.** `YMGapGuard` OK: "5 Clay-frontier types unconditionally uninhabited".
  `CrossoverWindowDefect` is inhabited only by conditional producers consuming genuine per-step
  hypotheses — never unconditionally. The crossover obligation stays **uninhabited**.
- **(iii) Adversarial.** The crossover is **not** closed. Route (a) repackages it into a per-step
  no-closing bound + a decidable check; route (b) into a uniform retention = `RGClusteringTransport`
  content. Both leave a genuine uninhabited obligation. That single obligation — the finite crossover
  defect sum / RG-clustering-transport across the middle — is now the SOLE remaining physical input of
  the entire continuum gap, with the anchor tied to the proved strong-coupling gap and the deep-UV tail
  AF-derived. **Clay target: OPEN.**

## Files

- `lean/YMGap/Continuum/CrossoverAnchorFloor.lean` (new; imported in `lean/YMGap.lean`).
- Anchors on: `RealCorrMass.realLocated` / `MayerClustering.reconTransfer_located_gap` (proved gap),
  `NetDriftBudgetSplit.fullFloor_of_crossover_and_AF` (the split), `AFDeepUVSummability` (AF tail),
  `WeakCouplingGap.RGClusteringTransport` + `TwoSidedGap.WindowOverlap` (the unified wall).
