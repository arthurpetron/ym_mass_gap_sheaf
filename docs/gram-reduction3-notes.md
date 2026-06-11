# N=3 Gram→functional bridge (`GramReduction3.lean`)

Mechanizes the `N=3` analogue of `GramReduction.lean`'s `coneExp2_eqv_form2` /
`coneExp_psd_two`. Proves **unconditionally** that the SU(2) heat-kernel `3×3`
character Gram quadratic form is positive-semidefinite:

```
coneExp_psd_three : ExpPos.geRat (WilsonFunctional.coneExp t ht c 3) 0
```

via the CReal equivalence

```
coneExp3_eqv_form3 : coneExp t ht c 3 ≃ Pivot3.form3 t ht (c 0) (c 1) (c 2)
```

transported across `Pivot3.form3_nonneg` by `SU3CharFactor.geRat_of_equiv`.
This confirms `form3_nonneg` IS the `N=3` instance of the uniform reduction
(`GramRed.psd_of_momentSquare_nonneg`), fully machine-checked.

## Structure of the bridge

`coneExp t ht c 3` is the nested double `csum`
`Σ_{μ,ν<3} (c μ · c ν)·gramEntry t ht μ ν`. `Pivot3.form3` is the explicit
six-term quadratic form over the manifest Gram entries `G00,…,G22`. The match
is in three steps:

1. **`coneExp3_eqv_cleanTree`** — strip the `czero` row/sum leaders of the
   `csum`s and replace each of the nine `gramEntry μ ν` by its `Pivot3` entry
   `G_{μν}`. The six distinct `gramEntry ≃ G_{ij}` reductions
   (`gramEntry_eqv_G00 … G22`, plus the lower-triangle `G10,G20,G21`) are the
   SU(2) Clebsch–Gordan fusion `χ_iχ_j = Σ χ_{|i−j|..i+j step 2}` made
   definitional: after stripping the empty-sum leader, each is a sum of
   `wilsonCharExp t ht s` terms that match `Pivot3.m_k = (k+1)·a^{k(k+2)}` on the
   nose (the `dim`-factor is identical, the `expNeg` exponents coincide —
   `wce_eqv`). `wce0_eqv_C1` (the `e^0` normalization) handles the unit term.

2. **`cleanTree_eqv_pairedTree`** — a pure nine-leaf commutative-monoid
   rearrangement bringing the three symmetric off-diagonal pairs adjacent. Done
   at the `approx` (rational) level via a small list-based normalizer: model a
   sum as the right fold `sumR` of a `List Q'`, prove `sumR` is
   `Q'.eqv`-invariant under `List.Perm` (`sumR_perm`, by the four `Perm`
   generators), and read both trees off as `sumR` of permutation-related leaf
   lists. Both trees are flattened (`flattenCT`/`flattenPT`, associativity-only
   chains) to `sumR` of index-mapped lists, and the index permutation
   `[0..8] ~ [0,4,8,1,3,2,6,5,7]` bridges them.

3. **`pairedTree_eqv_form3`** — the three symmetric pairs merge to the
   `2 c_i c_j · G_{ij}` terms (`GramRed.cross_merge`); the diagonal terms match
   on the nose. Same association on both sides, so this is a single `add_congr`
   tree.

## Notes / honesty

- `coneExp_psd_three` closes **fully and unconditionally** (no analytic input;
  `Pivot3.form3_nonneg` is itself unconditional via its LDLᵀ/SOS certificate).
- The `cleanTree_eqv_cleanTree` step uses `set_option maxHeartbeats 1600000`
  locally because unifying the unfolded `coneExp … 3` shape with the
  congruence lemmas is whnf-heavy; the proof itself is elementary.
- The `List.Perm` witness in `cleanTree_eqv_pairedTree` is built **explicitly**
  from `List.perm_middle` + `Perm.cons`/`trans`/`refl`, NOT by `decide`:
  `decide` on `List.Perm` invokes the `DecidableEq`-based decision instance,
  which pulls in `Classical.choice`. The hand-built witness keeps the whole
  development off `Classical`.

## Axiom gate

Every theorem in the file depends only on `[propext]` or `[propext, Quot.sound]`.
No `Classical.choice`, no `sorryAx`, no `native_decide`/`ring`/`nlinarith`.
Confirmed by the `#print axioms` block at the end of the file.
```
gramEntry_eqv_G00..G22        [propext, Quot.sound]
ACaux.sumR_perm               [propext]
coneExp3_eqv_cleanTree        [propext, Quot.sound]
cleanTree_eqv_pairedTree      [propext, Quot.sound]
pairedTree_eqv_form3          [propext, Quot.sound]
coneExp3_eqv_form3            [propext, Quot.sound]
coneExp_psd_three             [propext, Quot.sound]
```
