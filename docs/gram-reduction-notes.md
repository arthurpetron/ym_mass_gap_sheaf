# Gram reduction — Piece C of the uniform SU(2) heat-kernel PSD program

**Module:** `YMGap/Continuum/GramReduction.lean` (namespace `YMGap.Continuum.GramRed`).
**Status:** builds green; every theorem is axiom-clean (`[propext]` / `[propext, Quot.sound]`; no `Classical`, no `sorryAx`).

This piece is the **algebraic reduction** that turns Gram positive-semidefiniteness
(PSD) into functional positivity, *uniformly* in the truncation order `N`. It is the
clean bridge that lets Pieces A+B (heat-kernel character positivity + integration)
imply the uniform PSD of the character Gram matrix at every order simultaneously.

It is pure algebra: the Gram quadratic form **is** the moment functional applied to a
square, and PSD ⟸ functional-positivity is the quadratic-form expansion. The remaining
analytic input `E(q²) ≥ 0` is taken as a clean hypothesis (the interface to A+B) and is
**not** proved here.

## The objects

Over a nonnegative moment sequence `m_s = E(χ_{s/2})` (the structure `MomentData`,
carrying `m : Nat → CReal` and `m s ≥ 0`):

- `fusionLow a b = max a b − min a b` — the lowest spin in the SU(2) fusion
  `χ_a χ_b = χ_{|a−b|} + χ_{|a−b|+2} + ⋯ + χ_{a+b}`.
- `gram M a b = Σ_{j=0}^{min a b} m_{|a−b|+2j}` — the Gram entry `G_{ab} = E(χ_a χ_b)`,
  the Clebsch–Gordan sum of moments (the fusion is **baked in** here).
- `gramForm M c N = Σ_{i,j<N} c_i c_j · G_{ij}` — the `N×N` Gram quadratic form, the
  GNS energy of `q = Σ_{i<N} c_i χ_i` (real SU(2): `star = id`).
- `momentSquare M c N = Σ_{i,j<N} c_i c_j · E(χ_i χ_j)` — the moment functional applied
  to the fusion-expanded square `q² = (Σ_i c_i χ_i)²`.

These mirror `WilsonFunctional.fusionLow` / `gramEntry` / `coneExp` exactly; the SU(2)
heat-kernel instance is `wilsonMoments t ht` (`m_s = (s+1)·e^{−t·s(s+2)/4}`).

## Target 1 — the quadratic-form identity `Q_N(c) = E(q²)`

```
gramForm_eq_momentSquare : Equiv (gramForm M c N) (momentSquare M c N)
```

The Gram quadratic form IS the moment functional on a square. It holds
*definitionally* (`equiv_refl`): the fusion expansion `E(χ_i χ_j) = G_{ij}` is already
encoded in `gram`, so both sides are the same double sum. The mathematical content —
that the fused product expectations assemble into the Gram form — is exactly the choice
of `gram` as the Clebsch–Gordan sum of moments.

## Target 2 — the uniform reduction lemma

The single analytic hypothesis (the interface to A+B):

```
MomentSquarePos M  :=  ∀ N c, geRat (momentSquare M c N) 0      -- E(q²) ≥ 0 for all q
```

The reduction:

```
psd_of_momentSquare_nonneg :
    MomentSquarePos M → ∀ N c, geRat (gramForm M c N) 0
```

One hypothesis `E(q²) ≥ 0` ⟹ the `N×N` character Gram is PSD at **every** order `N`
simultaneously. Proof: Target 1 transported through `geRat` (`geRat_of_equiv`).

Per-order forms (`psd_at_order`, `MomentSquarePosAt`, `psd_of_momentSquarePosAt`) isolate
the hypothesis at a single `N` — the shape the concrete SU(2) `form2`/`form3` theorems
plug into. `momentSquarePos_iff_forall_at` records that the per-order facts reassemble
into the full hypothesis.

**Cone corollary (no analytic input):** `gramForm_pos_cone` — when all `c_i ≥ 0` the
Gram form is `≥ 0` unconditionally (every term `(c_μ c_ν ≥ 0)·(G_{μν} ≥ 0) ≥ 0`),
recovering `WilsonFunctional.coneExp_nonneg` abstractly. The genuine analytic content of
`MomentSquarePos` is exactly the off-cone (sign-indefinite) directions.

## SU(2) heat-kernel specialization

The abstract `gram` / `gramForm` / `momentSquare` reduce to
`WilsonFunctional.gramEntry` / `coneExp` *on the nose* (by `equiv_refl`: identical
definitions): `wilson_gram_eq`, `coneExp_eq_gramForm`, `momentSquare_eq_coneExp`. Hence:

```
wilson_psd_of_momentSquare_nonneg :
    MomentSquarePos (wilsonMoments t ht) → ∀ N c, geRat (coneExp t ht c N) 0
wilson_coneExp_nonneg :
    (∀ i, 0 ≤ c i) → geRat (coneExp t ht c N) 0          -- cone, unconditional
```

## Target 3 — `form2_nonneg` / `form3_nonneg` are the `N=2,3` analytic input

`Pivot2.form2_nonneg` and `Pivot3.form3_nonneg` prove `E(q²) ≥ 0` for the SU(2)
heat-kernel at orders `N=2,3` *unconditionally* (completing the square / LDLᵀ
certificates). They are exactly `MomentSquarePos` restricted to one order.

For `N=2` this is discharged **concretely and fully**:

```
coneExp2_eqv_form2 : Equiv (coneExp t ht c 2) (Pivot2.form2 t ht (c 0) (c 1))
coneExp_psd_two    : geRat (coneExp t ht c 2) 0          -- UNCONDITIONAL 2×2 Gram PSD
```

The bridge `coneExp2_eqv_form2` matches the nested-`csum` Gram form to the flat
three-term `form2 = c0²·1 + 2c0c1·m₁ + c1²·(1+m₂)` via: stripping the empty-sum `czero`
leading terms; `⟨χ_0⟩ ≃ 1` (`wce0_eqv_C1`, the `e^0` normalization) and `⟨χ_2⟩ ≃ m₂`
(`wce2_eqv_m2`, an exponent re-encoding `s(s+2)/4 = 2`); merging the symmetric cross
terms `c₀c₁·m₁ + c₁c₀·m₁ ≃ 2c₀c₁·m₁` (`cross_merge`) after a reassociation (`regroup4`).
Then `coneExp_psd_two = geRat_of_equiv coneExp2_eqv_form2 form2_nonneg`. So
`form2_nonneg` IS the `N=2` instance of Target 2, transported to the Gram form — no A+B
input needed at order 2.

For `N=3` the analogous bridge `coneExp t ht c 3 ≃ Pivot3.form3 t ht (c 0) (c 1) (c 2)`
holds by the same scheme (six entries with `m₃`/`m₄` exponent re-encodings and a 9-term
regroup); it is **not** mechanized here. The abstract per-order interface
(`psd_of_momentSquarePosAt`) already consumes `form3_nonneg`-shaped input at `N=3`.

## Does it close?

**Yes, modulo the A+B interface.** The algebraic reduction is complete and axiom-clean:

- Target 1 (`gramForm_eq_momentSquare`) and Target 2 (`psd_of_momentSquare_nonneg`,
  with its Wilson specialization) are fully proved.
- The cone positivity and the concrete `N=2` Gram PSD (`coneExp_psd_two`) are proved
  *unconditionally* (no analytic input).
- The only thing standing between this and the full uniform Gram PSD is the single
  hypothesis below, which Pieces A+B supply.

## The exact interface hypothesis needed from Pieces A+B

```
MomentSquarePos (wilsonMoments t ht)  :=
    ∀ (N : Nat) (c : Nat → Q'),  ExpPos.geRat (momentSquare (wilsonMoments t ht) c N) 0
```

i.e. `E(q²) ≥ 0` for every finite character combination `q = Σ_{i<N} c_i χ_i` (the GNS
positivity of the single-edge heat-kernel functional). Equivalently, via
`momentSquare_eq_coneExp`, `∀ N c, geRat (WilsonFunctional.coneExp t ht c N) 0`.

Pieces A+B establish this (the heat-kernel measure is a genuine positive measure, so its
moment functional `E` is positive on squares). Feeding it to
`wilson_psd_of_momentSquare_nonneg` closes the uniform Gram PSD at all orders. The
`N=2,3` cases of this hypothesis are already discharged unconditionally
(`coneExp_psd_two` here; `Pivot3.form3_nonneg` at order 3).
