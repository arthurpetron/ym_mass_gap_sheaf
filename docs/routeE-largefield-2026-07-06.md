# Route E — the LARGE-FIELD suppression half of `GapChannelDomination`

**Target.** `HeatKernelSecondCumulant.GapChannelDomination` — the single open physical
input of Route B: the real 4D SU(2) block-spin per-step degradation of the true
dimensionless margin is dominated by the fundamental-channel heat-kernel second cumulant
`δ_model = afDefectSeq afr = pMult·chanCumulant 1 (w_k)`.  The Bałaban/MRS proof splits the
block-spin fluctuation integral `∫ Dξ exp(−S(U·ξ))` into a SMALL-FIELD region (Gaussian +
cumulant → the `s=1` cumulant; higher-rep channel-tail refinement = the parallel agent's
half) and a LARGE-FIELD region (`|ξ| ≥ ε`, rare).  **This deliverable is the LARGE-FIELD
half:** prove the large-field contribution is exponentially suppressed so the small-field
`s=1` cumulant dominates.

**Deliverables.** Lean module `lean/YMGap/Continuum/LargeFieldSuppression.lean` (full
`lake build` green, frontier guard OK, axiom-clean); numerics
`routeE_largefield_numerics.py` (mpmath dps 45); this report.

---

## 1. The physics — correctly oriented (the honest regime + constant)

The SU(2) heat kernel is a class function of the plaquette angle `θ ∈ [0,π]` (= the
fluctuation-field size, `d(1,U)=θ`):

```
K_t(θ) = Σ_{n≥1} n·χ_n(θ)·w^{C₄(s)},   n = s+1 = dim,  C₄(s)=s(s+2)=n²−1,
χ_n(θ) = sin(nθ)/sin(θ),   dμ(θ) = (2/π) sin²θ dθ,   ∫ K_t dμ = 1  (orthogonality).
```

`w` is the heat-kernel weight; small field ↔ `w → 1` (`w = e^{−t}`, `t = −log w`).  The
LARGE-FIELD fraction is the mass of the rare region:

```
F(θ₀,w) = ∫_{θ₀}^{π} K_t dμ = Prob( plaquette angle ≥ θ₀ ).
```

**Orientation (the crux the task flagged).**  Short-time (`w→1`, `t→0`) heat-kernel
Gaussian asymptotics on the group give

```
F(θ₀,w)  ≤  K·exp( − θ₀²/(4t) ),   t = −log w ∼ (1−w) as w→1,
```

so the large field is EXPONENTIALLY small in `1/(1−w)`, and the suppression **improves
monotonically as `w → 1`** (WEAK coupling, deep UV, large `k` along the AF flow).  This is
the honest direction: at STRONG coupling (`w` small) the large field is NOT suppressed;
that regime is covered separately by the already-PROVED fixed-spacing strong-coupling gap.

**Numerical validation** (`routeE_largefield_numerics.py`, mpmath dps 45, `θ₀ = π/2`):

| `w` | `1−w` | `t=−log w` | `F(π/2,w)` | `(−log F)·t` |
|---|---|---|---|---|
| 0.10 | 0.900 | 2.3026 | 4.99·10⁻¹ | 1.600 |
| 0.50 | 0.500 | 0.6931 | 3.94·10⁻¹ | 0.646 |
| 0.80 | 0.200 | 0.2231 | 8.90·10⁻² | 0.540 |
| 0.90 | 0.100 | 0.1054 | 5.46·10⁻³ | 0.549 |
| 0.95 | 0.050 | 0.0513 | 1.56·10⁻⁵ | 0.568 |
| 0.98 | 0.020 | 0.0202 | 2.22·10⁻¹³ | 0.589 |
| 0.99 | 0.010 | 0.0101 | 1.26·10⁻²⁶ | 0.599 |

- Sanity: `∫ K dμ = 1` (character orthogonality — `K` is a probability density). ✓
- `F(π/2,w)` falls monotonically from `0.499` (`w=0.1`) to `1.3·10⁻²⁶` (`w=0.99`):
  **suppression improves as `w→1`.** ✓ (correct orientation)
- `(−log F)·t → 0.60`, converging to the short-time Gaussian constant
  `θ₀²/4 = (π/2)²/4 = 0.6169`.  So `F ≤ K·exp(−c/(1−w))` with `c ≈ θ₀²/4`. ✓
- Slope `d(log F)/d(1/(1−w)) → −0.61 ≈ −θ₀²/4` over `w ∈ [0.8,0.99]`. ✓

**Consequence along AF.**  With `1 − w_k ∼ A/(k+B)`, hence `1/(1−w_k) ∼ (k+B)/A`,

```
F(w_k)  ≤  K·exp( −c·(k+B)/A )  =  K'·r^k,    r = exp(−c/A) ∈ (0,1),
```

i.e. the per-step large-field defect decays **GEOMETRICALLY** in `k`.  A geometric
sequence is summable with the explicit budget `Σ_k K'·r^k ≤ K'/(1−r)` — in DECISIVE
contrast with the LINEAR bond-moving crack, whose harmonic budget `Σ 6p·(1−w_k)` DIVERGES
(`AFRateCalibration.linear_bound_not_summable`).  Geometric decay also beats the `s=1`
cumulant model `≈ 6(1−w_k)² ∼ 1/k²` in the deep UV.  **The large-field half is not an
obstruction: it contributes only a finite, geometrically-summable additive erosion.**

---

## 2. What is PROVED in Lean-core (axiom-clean `propext`/`Quot.sound` only)

Module `YMGap/Continuum/LargeFieldSuppression.lean`:

| Lean declaration | statement | axioms |
|---|---|---|
| `oneSub_le_one` | `1 − x ≤ 1` on `x ≥ 0` | propext |
| **`geomSum_le_recip`** | **`Σ_{k<N} r^k ≤ 1/(1−r)`** on `0≤r<1`, uniform in `N` | propext, Quot.sound |
| `lossSum_geomMajorant` | `Σ_{k<N} K·r^k ≃ K·geomSum r N` | propext |
| **`geomBudget_le`** | **`Σ_{k<N} K·r^k ≤ K/(1−r)`** uniform in `N` | propext, Quot.sound |
| `lossSum_le_termwise` | `f≤g` pointwise ⟹ `lossSum f ≤ lossSum g` | propext |
| **`largeFieldSuppression_summable`** | **`Σ_{k<N} δLF_k ≤ K/(1−r)`** (`Bε` finite) | propext, Quot.sound |
| `largeFieldBudget` | budget `Bε = K/(1−r)` returned as DATA (`Σ'`) | propext, Quot.sound |
| `lossSum_eq_tailSum0` | `lossSum f N = tailSum f 0 N` | (none) |
| `largeField_epsBudget` | `∀ k, tailSum δLF 0 k ≤ K/(1−r)` (the `hBε` slot) | propext, Quot.sound |
| **`largeField_additiveErosion_floor`** | **the honest reduction** (below) | propext, Quot.sound |

- **`geomSum_le_recip` is the analytic heart:** geometric partial sums are bounded by
  `1/(1−r)`, uniformly in `N` — proved from `(1−r)·geomSum = 1 − r^N ≤ 1` via the
  in-tree `oneSub_pow_factor` and `divPos` API.  This is the exact structural fact the
  divergent harmonic linear crack lacks.
- **The budget is COMPUTED as data** (`largeFieldBudget : Σ' R, ∀ N, Σ_{k<N} δLF_k ≤ R`),
  in contrast with `BondMovingStep.BondMovingSummable` for the linear crack, which is
  UNINHABITABLE (its harmonic budget diverges).  The large-field half's summability is
  therefore *positively established*, not merely named.

---

## 3. What of `GapChannelDomination` is reduced — the honest reduction

`GapChannelDomination.domination` requires the real per-step degradation `δ_real_k` of the
true margin to be dominated by the `s=1` model.  The Bałaban split is `δ_real =
δ_small-field + δ_large-field`.  The large-field piece is an ADDITIVE erosion `ε_k` (rare
excursions add to the multiplicative small-field defect `δ_k`).  This deliverable proves:

**the large-field `ε_k` supplies a FINITE, geometrically-summable additive-erosion budget
`Bε = K/(1−r)` and is fully DISCHARGED into the already-proved adequacy engine.**

Concretely (`largeField_additiveErosion_floor`, a guard-safe *conditional* — open binders
on the small-field recursion + anchor-dominance, inhabiting NO frontier bundle): given a
`LargeFieldSuppression` `L`, the small-field multiplicative recursion (the parallel half:
`(1−δ_k)·margin k − δLF_k ≤ margin(k+1)`, `Σδ ≤ Bδ`, `δ_k∈[0,1]`, `margin 0 ≥ 0`), and the
anchor-dominance `K/(1−r) < (1−Bδ)·margin 0`, the PROVED
`AdditiveErosionAdequacy.additiveErosion_uniform_floor` DERIVES the strictly-positive
uniform continuum floor

```
∀ k,  (1−Bδ)·margin 0 − K/(1−r)  ≤  margin k    and    0 < (1−Bδ)·margin 0 − K/(1−r).
```

So the large-field half's footprint on the whole continuum floor is exactly the single
finite constant `Bε = K/(1−r)` (supplied by `largeField_epsBudget`).  It is no longer an
open obstruction.

**What stays open** (the sharpest honest residual): `LargeFieldSuppression` — the
correctly-oriented geometric large-field bound `δLF_k ≤ K·r^k`, `r = exp(−c/A) ∈ (0,1)`,
`c ≈ θ₀²/4` — is NOT inhabited for the real 4D flow.  It IS the large-field half of the
Bałaban/MRS small-field theorem.  Combined with the parallel higher-rep character-tail
(small-field) half, it would discharge `GapChannelDomination`.

**Honesty caveat (Rule 9(6)).**  `lf_geom` bounds a FREE `largeFieldDefect : Nat → Q'`, so
— exactly like every other frontier atom in this program — it is vacuously fakeable in
principle (`largeFieldDefect ≡ 0`).  The residual is genuine only for the physical
large-field mass; the protection is the frontier guard + refusing to land the fake.  The
genuinely NON-vacuous content is the PROVED geometric summability (theorems about the
concrete `qpow`/`geomSum` objects) and the discharge into the proved adequacy engine.

---

## 4. Build / guard / axioms (honesty gate)

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (684 jobs).
```

- `#print axioms` for all 10 load-bearing declarations: `[propext, Quot.sound]`,
  `[propext]`, or empty — NO `Classical.*`, no `sorryAx`, no `native_decide`.
- No banned tokens (`sorry`/`native_decide`/`Classical`/`admit`) anywhere in the module
  except inside prose comments.
- Frontier guard count UNCHANGED at 5: nothing inhabited or weakened.
  `GapChannelDomination`, `SingleStepDefectBound`, `TrueMarginRecursion*` all UNTOUCHED
  and uninhabited.

---

## 5. HONEST VERDICT

**Is the large-field half PROVED / reduced, and in which regime?**

- The **large-field SUPPRESSION is genuine and correctly oriented**: exponentially small,
  `F(θ₀,w) ≤ K·exp(−θ₀²/(4(1−w)))`, improving as `w → 1` (weak coupling, deep UV, large
  `k`).  Validated numerically (const `c ≈ θ₀²/4 = 0.617`).  Along AF this is GEOMETRIC in
  `k`, hence SUMMABLE — this summability is **PROVED in Lean-core** (`geomSum_le_recip`,
  `largeFieldSuppression_summable`, budget returned as data), in decisive contrast with the
  refuted divergent linear crack.
- The large-field half is **fully REDUCED**: it is discharged into the proved
  additive-erosion adequacy engine as the finite geometric budget `Bε = K/(1−r)`
  (`largeField_additiveErosion_floor`).  Its entire footprint on the continuum floor is
  that one finite constant.
- **Regime:** the geometric/exp bound is the deep-UV (large-`k`/weak-coupling) statement;
  the strong-coupling finite regime is covered by the PROVED fixed-spacing gap.  It is
  exp-suppressed ASYMPTOTICALLY along AF (geometric in `k`), not uniformly at fixed
  strong coupling — the honest boundary.

**Does `GapChannelDomination` now close?**  NOT yet, and nothing here claims it.  It
reduces to the sharpest honest residual on this side — `LargeFieldSuppression` (the
geometric large-field constant), UNINHABITED — plus the parallel higher-rep character-tail
(small-field) half.  Together those two would discharge `GapChannelDomination`.  **The 4D
Yang–Mills mass gap remains OPEN; nothing is faked; no free-field or `δ:=0` is used.**  The
genuinely-hard large-field/small-field content is named, correctly oriented, its
summability PROVED, and isolated — not closed.
