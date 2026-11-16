# SCOPE: volume-uniform crossover hypothesis `hcross_unif` (2026-11-16, base b669114f; no implementation)

**Label: scope note only. No Lean was written. The existing `hcross_OPEN` is not edited. Not chart closure.**

## 1. Why
- `hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR3 n` (`Robust3UndershootCrossoverInstance.lean:101`, `Robust3SpacingHeatKernel.lean:79`)
  only bounds the δ **datum**. It reaches the carrier only through `hschur_OPEN`/`hupper_OPEN`, which are stated at the
  user-chosen `width : Nat → Nat` (the literal source width of the all-nome carrier).
- Every final theorem is `∀ width`, but its hypotheses are instantiated per width. So a single small width suffices to
  satisfy the hypotheses, and task2n shows that U(1) does so: "U(1) passes hcross at all six steps with δ_min ≤ 1.2e-4" on
  volumes ≤ 12 sites. Hence, as stated, hcross carries no non-abelian content.
- Its non-abelian content is "no collapse of the gap between w = 0.35 and 0.56" **uniformly in width**. U(1) is expected to fail that at
  step 2 (task2n: estimate, not run).

## 2. Proposed interface (constructive: Φ and D are functions of the width, so no choice is needed)
```lean
-- new file, e.g. YMGap/RG/Robust3CrossUniform.lean
def hcross_unif (delta : Nat → Q')
    (Phi : ∀ (W : Nat → Nat) n, VacuumComplement (ns.nome_pos (n+1)) _ (width := W (n+1)) → VacuumComplement (ns.nome_pos n) _ (width := W n))
    (D   : ∀ (W : Nat → Nat) n, VacuumComplement (ns.nome_pos (n+1)) _ (width := W (n+1)) → RC) : Prop :=
  (∀ n, n < 6 → delta n ≤ etaR3 n) ∧                      -- constants independent of W
  ∀ W : Nat → Nat, ∀ n, n < 6 →
    (∀ y, RCle ‖Phi W n y‖²_C ‖y‖²_F) ∧ SchurDecomposition … (W (n+1)) (W n) (delta n) (Phi W n) (D W n)
```
- The AF steps need the same uniformity: add `hafδ_unif`, the same with `6 ≤ n` and the cap afGap²/10. Equivalently, use one
  `hschur_unif` for all n and keep the cap binders `hcross_OPEN`/`hafδ_OPEN` unchanged on δ.
- Spectral form via `Robust3SchurRankOne`: `f c : Nat → Q'` **independent of W**, with
  `∀ W n, WilsonVacuumSqTwoStepFactor … (W (n+1)) (f n)`, coarse attainment at `W n` with `c n`, and `SchurBudget (f n) (c n) (capDelta n)`.
  For U(1) step 2 this is exactly where it breaks: f_W → 1 as W → ∞ (photon), while the budget at δ = 1/64 needs f ≤ 1/64 + (63/64)c,
  i.e. ρ_F⁴ ≲ 0.016, i.e. m_F(0.56) ≳ 1.035. This matches task2n's "needs m_F(0.56) ≥ 1.035".

## 3. How it plugs in (checked against the current signatures)
- `robust3_physical_floor` (`CrossoverInstance:137`) and `robust3_physical_floor_noMargin` (`Robust3MarginDischarge.lean:99`)
  take `width delta … Phi D hupper hschur` with `width` first. So the uniform corollary is the pointwise application
  `fun W => robust3_physical_floor_noMargin W delta hd0 hd1 hcross hafδ (Phi W) (D W) (hupper W) (hschur W) a ha hsp`
  (`n`-reindexing `0+n` is definitional, as in `Robust3SpacingHeatKernel.lean:99-101`).
- `_HK` variant: `robust3_physical_floor_noMargin_HK` (`SpacingHeatKernel:75`) has the same binder order, and its
  aHK/lo/hi/hpos/hwin/hoff binders are already W-independent. Likewise `robust3_physical_floor_lmax_HK` (`Robust3SchurRankOne.lean:233`)
  with W-indexed `Phi`, `f`, `c` held fixed.
- **Width-uniform conclusion:** the seed `r3_seed (width 0)` (`CrossoverInstance:81`) is already proved for every width
  (strong-coupling, width-independent). The floor constants (timeRate, eDy, afA, r3P) and `latticeMarginOf (relativeRate timeRate delta)`
  depend only on δ. So with δ fixed, the floor `floor·a_n ≤ (P₃ a_0)·latticeMargin_n` holds **for every W with identical constants**.
  This is the honest volume-uniform statement.
- Nothing downstream changes, and the existing theorems stay as they are. The new file only adds the definitions and corollaries.

## 4. Estimate and blockers
- About 70–110 lines: two definitions, two pointwise corollaries (plain and _HK), and an optional spectral corollary reusing
  `schur_of_spectral`. Low risk: no new mathematics, only quantifier order.
- **Blockers (mathematical, not Lean):**
  - `hcross_unif` is not known to be satisfiable. Witnessing it needs width-uniform SU(2) spectral bounds across the
    crossover (0.35 → 0.56 in particular).
  - task2n evidence covers ≤ 12 sites only. The size-stability data (SU(2) ≤ 0.2 % / ≤ 1 % at w ≤ 0.56) is suggestive, not uniform.
  - `hupper` must also hold uniformly for the w-dependent completedInner, which has not been modelled.
- **U(1):** `hcross_unif` is expected to FAIL for U(1) at step 2 (Villain transition w_c ≈ 0.463, literature β_V,c ≈ 0.65;
  free-photon estimate from periodic L ≈ 6, not run). That is precisely what makes it non-abelian content.
- Caveats: numerics are evidence, not proof; build is direct lean against copied oleans, not lake-verified; not chart closure.
