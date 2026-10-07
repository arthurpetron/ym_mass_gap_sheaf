# J04 scope: reflection positivity for the torus SU(2) multi-link measure (2026-10-07 PT)

This doc covers the RP row of `audits/SCOPE-R1-CLUSTER-TO-GAP-2026-10-07.md`. The measure is
`SU2TorusMultiLinkPolyGibbs` (`quaternionHaar n` = `multiLinkHaar n`, weights `Π_p W_p`). It is NOT the BF4 slab law.
RP holds for every β ≥ 0 / w ≥ 0. It is not a strong-coupling statement, but by itself it is not gap evidence.

## Formulation (Osterwalder–Seiler, plane between time slices)

- Θ is a time-reflection plane between slices t = 0 and t = 1. On a torus with even N_t there is a second cut at
  t = N_t/2, and both cuts are crossed.
- Links split three ways: positive-half links Λ₊ (both endpoints at t ≥ 1), negative-half links Λ₋ = ΘΛ₊, and the
  temporal links crossing a cut.
- **Crossing links:** gauge-fix every crossing temporal link to 1 (temporal gauge on one layer at each cut).
  - This is legitimate: the crossing links of the cuts form a forest, so it is a maximal gauge fixing that can be
    absorbed by Haar invariance at the sites of one side.
  - Alternative: treat the crossing links as reflected-half variables via `U ↦ U*`. That needs Haar
    conjugation invariance.
- **Polynomial Θ:** order the links so that blocks 0..a−1 are Λ₊ and block a+i is the reflection of block i.
  - Spatial links reflect to spatial links with the same orientation. With the crossing links fixed to 1,
    Θ is the block translation `shiftPoly a`.
  - Orientation conjugation enters only through the crossing plaquette word, which becomes `U·V*`.
  - Non-crossing plaquettes on the reflected side have words that are Θ-images of positive-side words, up to
    inversion. The weights are class functions that are real and even under `U ↦ U*`, so `W(Θp) = Θ W(p)`.
    This identification (via `characterPolynomial` of conj = itself) is still OPEN in Lean.
- **Target:** `0 ≤ ∫ Θ(F)·F·Π_p W_p` for F a polynomial on Λ₊.

## Mechanism and what is proved

The crossing scalar is `Re(U V*) = Σ_{c<4} u_c v_c`, a sum of Θ-symmetric products. Haar on `a+a` blocks factorizes
(`haar_factor`), so `∫ (F A)·Θ(F A) = (∫ F A)²`.

### `SU2TorusRPCore` (commit A)

- `sh_mul`: `Θ(pq) = Θp·Θq` (literal).
- RPK cone: `kern a L = Σ c·A·ΘA` with c ≥ 0 and A on Λ₊.
  - `rpk_pos`: `RPK a W → 0 ≤ ∫ F·ΘF·W`.
  - Closure: `rpk_one`, `rpk_append`, `rpk_smul`, `rpk_mul`.
- `rp_full`: if `W ≡ W₊·ΘW₊·W_c` with `W_c ∈ RPK`, then `0 ≤ ∫ ΘF·F·W`.
- **No reflection-invariance lemma is needed:** Θ is a block translation, and haar_factor handles it directly.

### `SU2TorusRPWilson` (commit B)

- `cross a b = Σ_c x_{4b+c} x_{4a+4b+c}` is an RPK. `T_K = Σ_k wilsonA β k · χ₁^k` with `χ₁ = 2σ` is an RPK by
  the power-sum closure. The heat kernel and `D^s` are not used.
- `wilson_cross_rp` and `wilson_rp_full` (any product of crossing `T_K`s, with a positive-half W₊).

## Haar lemmas: exist vs missing

| Need | Status |
|---|---|
| half-split factorization `∫_{a+b} p·shift q = ∫p ∫q` | EXISTS (`haar_factor`) |
| commutative / associative Haar-PE algebra | EXISTS (`SU2HaarAlgebra`) |
| `blockSwapInvolution` / block permutation invariance | EXISTS (BF4 files). Needed only to bring the torus link order into the half-split order. |
| Θ-ordering of `links` for the torus (a permutation lemma `quaternionHaar` ∘ block-perm = `quaternionHaar`) | MISSING |
| gauge fixing of crossing links (Haar left-invariance at a site, polynomial form) | MISSING. This is the main new Haar lemma. |
| conj invariance `χ_s(U*) = χ_s(U)` at polynomial level, plus `plaqWord` of a reflected plaquette | MISSING (routine) |
| `D^s` matrix coefficients in real form | MISSING. Needed only for the heat kernel. |

## Heat-kernel plan

- `characterPolynomial x s` (Chebyshev U_s(x)) has alternating-sign coefficients in x. For example,
  `χ₃ = 8x³ − 4x`, so the coefficient of x in `Σ_s c_s χ_s` is `2c₁ − 4c₃ + 6c₅ − …`.
  - The coefficients of the heat-kernel weight in powers of χ₁ are therefore **not termwise nonneg**, and their
    sign is **UNVERIFIED** (correction to the first version of this note).
  - With `c_s ~ w^{s(s+2)}`, lower orders dominate, so they are plausibly ≥ 0 for small w, uniformly in M.
  - Option (0): prove that domination, then reuse the power-sum route with no `D^s`. It needs an explicit
    expansion of `U_s` in powers of x.
- Options:
  - (i) `D^s` route: `χ_s(UV*) = Σ_{ij} D^s_ij(U) conj D^s_ij(V)`. Its real form is a sum of `Re·Re + Im·Im`
    Θ-products, hence an RPK. Each `χ_s(σ)` is an RPK, so the heat kernel is an RPK (coeffW ≥ 0).
  - (ii) Cheaper: show `χ_s(U V*) = Σ` (monomial in u)·(the same monomial in v) with nonnegative weights, via
    symmetric tensor powers of the spin-1/2 representation in quaternion components. This is the same object
    as (i), written polynomially.
- Plan: Wilson first (done at the abstract/crossing level), then the heat kernel via (ii).

## Risks / open

1. **Geometry.** Show that the torus `polyPartition` (with the link list reordered and crossing links gauge-fixed)
   is PE to `W₊·ΘW₊·Π crossTK`, with the crossing plaquette scalar ≡ `cross a b`. This is the remaining bridge from
   `wilson_rp_full` to the actual measure. It needs the three missing Haar lemmas above.
2. **Two cuts on the torus:** both cuts' crossing plaquettes enter `bs`. The gauge fixing must use only one
   layer per cut, and Λ₊ must be the half-torus between the cuts.
3. **Transfer matrix** (next row of the gap scope) is still OPEN. RP gives a positive semi-definite form on
   Λ₊-polynomials; the GNS/transfer step then uses `CompactTransferGNS`.
4. RP is β-uniform, but the gap still needs the strong-coupling clustering, so the window remains STRONG COUPLING ONLY.
