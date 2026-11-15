# ROUTE SCOPE — an SU(2)-specific strong-coupling seed beyond w = 1/55 (2026-11-15)

**Label: SCOPING / ANALYSIS ONLY. No Lean was written. No theorem is claimed. Every number below is a back-of-envelope ESTIMATE unless it cites a proved repo lemma.** Box only.

## Background and goal
- The current seed comes from the cluster-count method (`StrongCouplingNomeThreshold`): `T(δ) = 625·(2δ+δ²)·(1−δ)^(−48) < 1` with `δ = heatRemainderBound w = 128·w³`. Proved for `w ≤ 1/55`, with a proved no-go for `w ≥ 1/54` (true threshold ≈ 0.01819). Even with `K = 625 → 1`, guards 1 and 2 cap it at `w < 0.198`. (The brief says ≤ 0.072; whichever figure is used, it is far below 1/2.)
- Goal: an SU(2)-specific route that reaches `w ≈ 0.45–0.5`, the first crossover step towards `afNomeSchedule.nome 0 ≈ 0.5145`.
- Sanity rule (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved): with `t = −4 ln w`, 4D U(1) is massless at `w = 1/2` and at `0.5145`, and confined only for `w ≤ 1/8`. **Any route whose U(1) analogue gives a gap at `w > 1/8` is wrong.**

## Verified repo facts used throughout
- `BondMovingStep.lean:259` is `def coeffW (w : Q') (s : Nat) : Q' := dimQ s * qpow w (c4 s)`. Here `dimQ s = s+1` (`RGTransport.lean:188`) and `c4 s = s*(s+2)` (`RGTransport.lean:196`), so `coeffW w s = (s+1)·w^{s(s+2)}`. The index `s` is twice the spin (`s = 1` is the fundamental). `coeffW_zero` (:266) gives 1, and `coeffW_one` (:272) gives `dimQ 1 · heatKernelSep w = 2w³`.
- `heatKernelSep w = w³` (`HeatKernelGap.lean:78`). This is the per-link transfer eigenvalue ratio of the spin-1/2 mode.
- The current method already uses the SU(2) exponent: `heatRatio w = 32w³` and `heatRemainderBound w = 128w³` (`QuaternionHaarCharacterInterval.lean:80–88`). Its loss is in the constants:
  - `heatTermBound w n = coeffW w n · characterCap n`, where `characterCap n = 2·16^n` (`BF4ExactSlabFixedSpatialPlaquetteBoundary.lean:61`). The true sup is `|χ_s| ≤ s+1`. At `s = 1` the cap is 32 instead of 2, a 16× loss.
  - The entropy is `K = (D+1)² = 625` with `D = 24` (`ClusterCount4DProgress.lean:44,300`).
  - The collar factor is `(1−δ)^(−48)`.
- The U(1) comparison coefficient is `w^{n²}` (charge `n`, two reps ±n). So `u₁(U(1)) = w`, while `u₁(SU(2)) = w³` at the same `w`.
- **Key consequence for the sanity check.** A criterion that is group-blind except through the leading activity `u₁` maps SU(2) at `w` to U(1) at `w³`. SU(2) at `w = 1/2` has `u₁ = 1/8`, which is exactly U(1)'s confinement edge `w = 1/8`. So reaching SU(2) `w = 1/2` with group-blind counting would make the same counting prove U(1) confinement right at its numerical edge. That would need an essentially sharp expansion, which cluster expansions never are.

---

## Route (i): SU(2) character / polymer expansion with exact coefficients

**Key inequality.** Expand each plaquette weight as `W(U_p) = Σ_s coeffW w s · χ_s(U_p) = 1 + f_p`. Haar-integrate the links using orthogonality (`∫ χ_s(UV) χ_{s'}(V⁻¹W) dV = δ_{ss'} χ_s(UW)/d_s`). Only closed, fusion-compatible plaquette surfaces survive. The polymer activity is then `|z(X)| ≤ Π_{p∈X} ε(w)`, with `ε(w) = c·w³ + O(w⁸)` and `c ∈ [1, 4]` (normalized `u₁ = w³` up to the dimension factors `(s+1)²`). The Kotecký–Preiss condition (Dobrushin form, already the shape of `SizeWeightedPolymerKP.Cond`) is

  `Σ_{X ∋ p} |z(X)| · e^{a|X|} ≤ a`, which is roughly `K_eff · c · w³ < 1`.

A uniform-in-width seed then follows as in the current chain: a width-independent rate feeds `UniformSeedGap` through `uniformSeedGap_iff_chainSeedSlot`.

**Repo lemmas it would reuse** (names grepped):
- Coefficients: `coeffW`, `coeffW_zero`, `coeffW_one`, `coeffW_nonneg`, `coeffW_pos` (`FusionResidualBound.lean:157`), `coeffW_logConcave` (`FusionResidualBound.lean:499`), `coeffW_superLogConcave_wsq` (`LaplaceMarginDeep.lean:219`, the super-geometric tail), `coeffW_one_mono` (`UniformCouplingGap.lean:103`), `heatKernelPacket` / `coeffAt_heatKernelPacket` (`Z4FiniteBoxHeatKernelPacketState.lean:64`).
- Fusion / selection rules: `fusionProduct`, `fusionProduct_nonneg` (`BondMovingStep.lean:140,145`), `FusionLogConcave`, `VacuumStability`.
- KP machinery: `SizeWeightedPolymerKP.kpw_main` (:242), `prod_le_sum` (:274), `z4_cond` (:405), `SignedPolymerKP`, `z4ClusterCountBound` (`ClusterCount4DProgress.lean:302`), `FiniteSizeGeometricSum.entropyRate`. Note that `SizeWeightedPolymerKP` itself lists the grouping step and the 625ⁿ identification as OPEN.
- Target slot: `StrongCouplingNomeThreshold.guards_of_delta_le` / `uniformSeedGap_of_guards` if the result can be phrased as new guards; otherwise `UniformSeedGap.uniformSeedGap_iff_chainSeedSlot` directly.

**Decidable checks needed.**
- `ε(w)` bound at a target rational `w` (for example 1/4 or 1/3): a truncated sum `Σ_{s≤3}(s+1)² w^{s(s+2)}` plus a geometric tail from `coeffW_superLogConcave_wsq`. Denominators are about `4^{15}`. This is **cheap** (the same order as `threshold_inv55`, about 1.7 GiB peak with the overlay).
- The KP numeric condition `K_eff · ε(w) · e^{a} ≤ a` at fixed rationals is **cheap**.
- The entropy count `K_eff` must be **proved structurally, not by enumeration**. Enumerating 4D plaquette animals or surfaces by `decide` is infeasible in memory. That is the real cost.

**Back-of-envelope reach (ESTIMATES; SU(2) bound, with the U(1) analogue in brackets):**

| Step | Assumption | SU(2) reach | U(1) analogue |
|---|---|---|---|
| repo today | `T(128w³) < 1` | 0.0182 (proved ≤ 1/55) | — |
| (a) exact character sup only | `δ = 8w³` in the same `T` | ≈ 0.046 | — |
| (a′) plus Haar-normalized activity | `δ = w³` in the same `T` (K = 625) | ≈ 0.092 | — |
| (b) tree-graph KP, `K = e·D ≈ 65`, `c = 4…1` | `K·c·w³ < 1` | 0.157 – 0.248 | 0.004 – 0.015 |
| (b′) `K = 24`, `c = 4…1` | same | 0.218 – 0.347 | 0.010 – 0.042 |
| (c) closed-surface entropy `μ = 30 / 20 / 10 / 8` (no repo theorem) | `μ·w³ < 1` | 0.322 / 0.368 / 0.464 / 0.500 | 0.033 / 0.050 / 0.100 / 0.125 |

- **Sanity check:** passed at every row except the last. At `μ = 8` the U(1) analogue reaches 1/8, the numerical confinement edge, which is not credible for a cluster expansion. So **0.5 is effectively out of reach**, and 0.45 needs `μ ≲ 11`, a near-sharp surface count.
- **Realistic reach: 0.25–0.35**, about 15–20× the current 1/55. That is above 1/8, so per the sanity rule it would be genuine non-abelian content: it uses the Casimir exponent `s(s+2)`, which U(1) lacks. It does not reach 0.45–0.5.

**Main risks / obstructions.**
1. `characterCap = 2·16^n` lives inside the quaternion-polynomial `Interval` machinery ("valid under arbitrary Haar insertions"). Replacing it with `|χ_s| ≤ s+1` needs a real sup bound on SU(2) characters as class functions, not as polynomial coefficients. This is a medium risk and may need a new carrier.
2. A Haar-orthogonality closed-surface reduction for multi-plaquette clusters is not in the repo. `WilsonConnCorr.lean:530–545` names exactly this ("multi-plaquette Mayer / Dobrushin-ratio induction") as an OPEN obligation with no inhabitant. This is the biggest piece.
3. The entropy constant: the jump from 625 to about 24–65 needs a new animal / tree-graph count. The surface entropy (row (c)) has no repo support at all.
4. The output must land in the repo's seed slot (the BF4 slab `relativeRate` form). The current chain gets there through slab-specific collar factors, and re-deriving them with sharper constants may reintroduce losses.
5. Sanity: the route is group-generic except through `coeffW`, so its U(1) analogue is the same proof with `w^{n²}`. The estimates above put that at `w ≲ 0.05 < 1/8`, so the route is consistent with the numerics.

---

## Route (ii): Dobrushin uniqueness / transfer-matrix comparison on single time-slabs

**(ii-a) Dobrushin key inequality.** The single-link conditional law has a Haar density proportional to `Π_{p∋ℓ} W(U_p)`. Changing a neighbouring link `ℓ'` changes one factor, so `C_{ℓℓ'} ≤ tanh(ln R(w)/2)` with `R(w) = sup W / inf W`. Each link has `6·3 = 18` neighbours, which gives the condition

  `α(w) := 18 · tanh(ln R(w) / 2) < 1`,

and then exponential decay of local correlations, uniform in volume, at rate `α`. A cheap rational version uses `R ≤ (1+a)/(1−a)` with `a = Σ_{s≥1}(s+1)² w^{s(s+2)}`.

**(ii-b) Transfer-matrix key inequality.** In temporal gauge, `T = M^{1/2} K M^{1/2}`. Here `K = ⊗_ℓ e^{(t/4)Δ_ℓ}` has eigenvalue `w^{s(s+2)}` per spatial link. On the gauge-invariant complement of the vacuum, `‖K‖ ≤ w^{12}` (the smallest loop is 4 links at `s = 1`). `M = Π_{p spatial} W(U_p)` is a multiplication operator. The gap needs `‖T|_{Ω⊥}‖ ≤ r·‖T‖` with `r < 1` uniformly in volume.

**Repo lemmas it would reuse.** `heatKernelSep`, `heatKernelLocatedGap` (`HeatKernelGap.lean:222`), `TransferCorr.reconTransfer` (:117), `PushedReconTransferGap.reconTransfer_located_gap_gen` (:216), the `BF4ExactSlabFixedSpatial*` slab stack (`BF4ExactSlabFixedSpatialSpatialDenseGap.timeRate w hd = entropyRate 625 (adjustedCoreRate w hd)`), `SizeWeightedPolymerKP` (Dobrushin-form KP), and `coeffW*` as in route (i). **There is no Dobrushin uniqueness / comparison theorem in the repo** (`rg Dobrushin` finds only the KP file and the named-OPEN item in `WilsonConnCorr`).

**Decidable checks needed.** `R(w)` (or its `(1+a)/(1−a)` bound) at a rational `w`, plus `18·(R−1)/(R+1) < 1`. Both are **cheap**: small truncated sums, about 1–2 GiB. The transfer-matrix side needs `w^{12}` and similar numbers, which are also cheap. The cost lies in the infrastructure, not the checks.

**Back-of-envelope reach (ESTIMATES).**
- (ii-a) SU(2): `R(0.20) = 1.066, α = 0.58`; `R(0.24) = 1.117, α ≈ 0.995`; `R(0.30) = 1.242, α = 1.94`; `R(0.45) = 2.12, α = 6.5`; `R(0.50) = 2.87, α = 8.7`. So the reach is **w ≈ 0.24**. U(1) analogue: **w ≈ 0.028** (at 1/8, `α = 4.5`; at 1/2, `α = 16`). The sanity check passes. Block (Dobrushin–Shlosman) versions might gain a modest factor; reaching 0.45 would need `α` cut about 6.5×, which is not plausible.
- (ii-b) The electric part alone is huge: `w^{12} = 2.4·10⁻⁴` at `w = 1/2`. **The sanity check flags a trap**, because for U(1) the same bound is `w⁴ = 1/16` at `w = 1/2`. Any argument that uses only `K`'s gauge-invariant gap plus a group-blind, volume-uniform bound on `M` would "prove" a U(1) gap at `w = 1/2`, so **it is wrong**. `M` must be controlled by a spatial expansion inside the slab, which again needs small `u₁`. Estimate with slab coordination 12–20 and `c = 4…1`: `w ≲ 0.17–0.31` (U(1): ≲ 0.005–0.03).

**Main risks / obstructions.**
1. Dobrushin's theorem needs conditional laws, couplings and TV distance on `SU(2)^{links}`. The repo handles Haar only through quaternion-polynomial moments, so this is new measure-level infrastructure: high risk, and possibly large constructively.
2. Bridging "decay of correlations in TV/oscillation" to the repo's seed slot (the slab `relativeRate` / `UniformSeedGap`) is a separate, unscoped translation.
3. The transfer-matrix variant (ii-b) is the U(1) trap above. Done correctly, it collapses to a polymer expansion of the magnetic term, which is route (i) in a slab.
4. Its reach (about 0.24) is no better than route (i)'s realistic band.

---

## Recommendation

- **Neither route plausibly reaches 0.45–0.5.** Both scale as `(const)⁻¹ · w³`, and the sanity map (SU(2) at `w` ↔ U(1) at `w³`) puts SU(2) `w = 1/2` at U(1)'s confinement edge. Getting there needs non-abelian structure beyond the Casimir exponent: fusion selection rules pruning surfaces (a three-fold `s = 1` vertex vanishes), or a multiscale/RG step. **Realistic target for a seed: w ≈ 0.25–0.35** (estimate). That leaves a smaller `hcross_OPEN` from about 0.3 up to 0.5145.
- **Build route (i) first, in stages.** It reuses far more of the repo (`coeffW` family, fusion, `SizeWeightedPolymerKP`, the existing guard → `UniformSeedGap` plumbing). Each stage is independently checkable and moves a proved threshold:
  1. Exact character sup `|χ_s| ≤ s+1` in place of `characterCap` (est. 1/55 → about 0.046). About 250–400 lines, 1 commit; a new carrier risk.
  2. Haar-normalized activity `ε(w) ≈ w³` with K still 625 (est. → about 0.09). About 400–700 lines, 2 commits.
  3. Sharper entropy (tree-graph / `D = 24` count, discharging `SizeWeightedPolymerKP`'s OPEN grouping step) (est. → 0.2–0.35). About 600–900 lines, 2–3 commits.
  4. Seed-slot bridge to `UniformSeedGap` plus a decidable instance at the best dyadic/rational `w`. About 200–300 lines, 1 commit.
  - **Total estimate: about 1,450–2,300 lines, 6–7 commits** (each ≤ 400 lines), with stage 3 the riskiest.
- Route (ii-a) is a later cross-check. Its infrastructure (Dobrushin on `SU(2)^{links}` plus the bridge) is estimated at 2,000–3,500 lines over 8–12 commits, for a similar reach of about 0.24.
- Do not pursue (ii-b) in the naive form; it fails the U(1) sanity check.

No route was started. No Lean file was added or changed for this scope.
