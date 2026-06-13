/-
The GENERIC finite-positive-root crude squared-Weyl-dimension majorization,
proven ONCE over an abstract finite positive-root collection, then instantiated
for the whole SU(N) family.

# The object and the crude route

For a compact simple group `G` of rank `r = N − 1` (for `SU(N)`), the Weyl
dimension formula is a product over the positive roots `α > 0`:

    dim V_λ  =  ∏_{α>0} (1 + ⟨λ,α⟩/⟨ρ,α⟩) ,

each factor `1 + (nonneg linear form in λ)`.  The CRUDE uniform bound — the
decisive low-effort route — drops the tightness of the `p(N−p)` per-axis
exponent entirely.  Two ingredients only:

  * **Per-root range extension** (a monotonicity).  Each Weyl factor
    `1 + ⟨λ,α⟩/⟨ρ,α⟩ ≤ 1 + Σ_{p}λ_p ≤ ∏_{p<r}(1 + λ_p) =: B`
    (drop the denominator `⟨ρ,α⟩ ≥ 1`; the proven superadditivity reversal
    `one_add_sum_le_prod`; then extend the product range — every factor
    `1 + λ_p ≥ 1`).  So every one of the `m` Weyl factors is `≤ B`, with
    `B ≥ 1`.

  * **Cardinality bound** `m = #Δ⁺ = N(N−1)/2 ≤ N²`.  Since there are exactly
    `m` positive-root factors, each `≤ B`,

        dim V_λ  ≤  B^m ,     hence     (dim V_λ)²  ≤  B^{2m} .

The exponent `2m` is the SAME for every axis `p` (uniform degree), so the
per-axis squared-dim polynomial is `P_p(x) = (1 + x)^{2m}` for every `p` — no
Fubini, no `p(N−p)` identity, no two inductions.  The polylog tail
`Σ n^k r^n ≤ k!/(1−r)^{k+1}` (`RG/PolylogTail.lean`, general `k`) then handles
the per-axis degree `2m` for each fixed `N`.

# What this module supplies

  * `prodFac` / `prodFac_le_pow` — the GENERIC finite-product-bounded-by-power
    lemma, proven ONCE: a product of `m` factors each in `[0, B]` with `1 ≤ B`
    is `≤ B^m`.  This is the whole crude route's engine.
  * `crudeBound` (`B := ∏_p(1+λ_p)`), `crudeBound_ge_one`, and
    `weyl_factor_le_crudeBound` — the per-root range-extension wired to `B`.
  * `dimSq_le_crude` — the generic crude squared-dim bound
    `dimVal² ≤ B^{2m}` from an abstract Weyl-product hypothesis
    `dimVal ≤ prodFac fac m` with `fac j ≤ B` per root.
  * `weylDimData_crude` — packages the crude bound as the repo's
    `WeylDimData R` residual, with uniform per-axis excess `B^{2m} − 1`, given
    the abstract Weyl-product datum.  For `SU(N)`: `m = N(N−1)/2`.

The honest residual that stays NAMED is the abstract
`dimVal ≤ ∏_{j<m} fac j` (the actual Weyl dimension product over the positive
roots) together with `fac j ≤ B` (each Weyl factor under the crude bound) — the
SU(N) Weyl dimension formula, which this `Q'` stack does not carry for general
`N`.  We do NOT fake it: it is the structure's hypothesis.  For `SU(2)`/`SU(3)`
the concrete bound is the proven `su2_dimSq_le` / `su3_dimSq_le` of
`WeylCharacterBound.lean`; this module is the rank-general home.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` / `[propext, Quot.sound]`
(the `Q'`/`Nat` order layer).  No `Classical.*`, no `native_decide`, no
`sorryAx`.  See the `#print axioms` block at the end.
-/

import YMGap.RG.WeylCharacterBound

namespace YMGap.RG

open YMGap.Constructive
open YMGap.RepTheory

/-! ## The generic finite-product-bounded-by-power engine

A bare finite product `∏_{j<m} fac j` (NOT the `1 + ·` shape of `finProd`),
each factor `fac j ∈ [0, B]` with `1 ≤ B`, is bounded by `B^m`.  This is the
single monotonicity that powers the crude route: the `m` positive-root Weyl
factors each lie under the common bound `B = ∏_p(1+λ_p)`, so their product is
`≤ B^m`. -/

/-- The bare finite product `∏_{j<m} fac j`. -/
def prodFac (fac : Nat → Q') : Nat → Q'
  | 0     => 1
  | m + 1 => prodFac fac m * fac m

@[simp] theorem prodFac_zero (fac : Nat → Q') : prodFac fac 0 = 1 := rfl

@[simp] theorem prodFac_succ (fac : Nat → Q') (m : Nat) :
    prodFac fac (m + 1) = prodFac fac m * fac m := rfl

/-- The product is nonnegative when every factor is. -/
theorem prodFac_nonneg {fac : Nat → Q'} (hfac : ∀ j, (0 : Q') ≤ fac j) :
    ∀ m, (0 : Q') ≤ prodFac fac m := by
  intro m
  induction m with
  | zero => exact Q'.zero_le_one
  | succ m ih => exact Q'.mul_nonneg _ _ ih (hfac m)

/-- `1 ≤ B^m` for `1 ≤ B` (each of the `m` factors is `≥ 1`). -/
theorem one_le_pow {B : Q'} (hB : (1 : Q') ≤ B) : ∀ m : Nat, (1 : Q') ≤ B ^ m := by
  have hB0 : (0 : Q') ≤ B := Q'.le_trans' _ _ _ Q'.zero_le_one hB
  intro m
  induction m with
  | zero => exact Q'.le_refl' 1
  | succ k ih =>
    -- 1 = 1·1 ≤ B·B^k = B^(k+1).
    show (1 : Q') ≤ B * B ^ k
    have hstep : (1 : Q') * 1 ≤ B * B ^ k :=
      Q'.mul_le_mul_of_nonneg hB ih hB0 Q'.zero_le_one
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 1)) hstep

/-- **The generic crude engine.**  If every factor `fac j` lies in `[0, B]`
and `1 ≤ B`, then the `m`-fold product `∏_{j<m} fac j` is bounded by `B^m`.

By induction on `m`: the new factor `fac m ≤ B` and the product so far
`≤ B^m`, both nonnegative, multiply (monotone product) to `B^m · B = B^{m+1}`.
This is the ONLY monotonicity the crude route needs. -/
theorem prodFac_le_pow {fac : Nat → Q'} {B : Q'}
    (hB : (1 : Q') ≤ B) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ B) :
    ∀ m, prodFac fac m ≤ B ^ m := by
  have hB0 : (0 : Q') ≤ B := Q'.le_trans' _ _ _ Q'.zero_le_one hB
  intro m
  induction m with
  | zero =>
    -- prodFac fac 0 = 1 = B^0
    show (1 : Q') ≤ (1 : Q')
    exact Q'.le_refl' 1
  | succ m ih =>
    -- prodFac fac (m+1) = prodFac fac m · fac m ≤ B^m · B = B^(m+1)
    show prodFac fac m * fac m ≤ B ^ (m + 1)
    have hstep : prodFac fac m * fac m ≤ B ^ m * B :=
      Q'.mul_le_mul_of_nonneg ih (hle m) (Q'.pow_nonneg B hB0 m) (hfac m)
    refine Q'.le_trans' _ _ _ hstep ?_
    -- B^m · B = B · B^m = B^(m+1)  (pow_succ; commute)
    show B ^ m * B ≤ B ^ (m + 1)
    exact Q'.le_of_eqv (Q'.mul_comm_eqv (B ^ m) B)

/-! ## The crude common bound `B = ∏_{p<r}(1 + λ_p)`

`B` is the per-axis one-plus-label product `∏_{p<r}(1 + λ_p)` — exactly the
repo's `finProd` on the label sequence `λ`.  Every Weyl factor is `≤ B`, and
`B ≥ 1` (each factor `1 + λ_p ≥ 1`). -/

/-- The crude common bound `B = ∏_{p<r}(1 + λ_p)`, where `lab p` is the `p`-th
Dynkin label coerced to `Q'`.  This is the repo's `finProd` on `lab`. -/
def crudeBound (lab : Nat → Q') (r : Nat) : Q' := finProd lab r

/-- `B = ∏_p(1 + λ_p) ≥ 1` for nonnegative labels (each factor `≥ 1`). -/
theorem crudeBound_ge_one {lab : Nat → Q'} (hlab : ∀ p, (0 : Q') ≤ lab p)
    (r : Nat) : (1 : Q') ≤ crudeBound lab r :=
  finProd_ge_one hlab r

/-- `B = ∏_p(1 + λ_p) ≥ 0`. -/
theorem crudeBound_nonneg {lab : Nat → Q'} (hlab : ∀ p, (0 : Q') ≤ lab p)
    (r : Nat) : (0 : Q') ≤ crudeBound lab r :=
  Q'.le_trans' _ _ _ Q'.zero_le_one (crudeBound_ge_one hlab r)

/-- **Per-root range extension** `1 + Σ_{p<r} λ_p ≤ B`.  The Weyl factor with
the denominator dropped, `1 + Σ_p λ_p`, is dominated by the crude bound
`B = ∏_p(1 + λ_p)`.  This is the proven superadditivity reversal
`one_add_sum_le_prod` read at the crude bound.  Since the true Weyl factor is
`1 + (Σ λ_p)/⟨ρ,α⟩ ≤ 1 + Σ λ_p` (drop `⟨ρ,α⟩ ≥ 1`) and the linear form for
any single positive root only ever sums a SUBSET of the labels (`≤ Σ_p λ_p`),
every Weyl factor is `≤ B`. -/
theorem weyl_factor_le_crudeBound {lab : Nat → Q'} (hlab : ∀ p, (0 : Q') ≤ lab p)
    (r : Nat) : (1 : Q') + sumExcess lab r ≤ crudeBound lab r :=
  one_add_sum_le_prod hlab r

/-! ## The generic crude squared-dimension bound

From an abstract Weyl-product datum — `dimVal ≤ ∏_{j<m} fac j` (the actual
dimension as the product over the `m` positive roots) with each `fac j ≤ B`
(every Weyl factor under the crude bound `B`) and `dimVal ≥ 0` — the crude
engine gives `dimVal ≤ B^m`, hence the SQUARED bound `dimVal² ≤ B^{2m}`. -/

/-- **Generic crude dimension bound** `dimVal ≤ B^m`.  Given the abstract
Weyl-product `dimVal ≤ ∏_{j<m} fac j`, each factor in `[0, B]`, `1 ≤ B`:
the product is `≤ B^m` (`prodFac_le_pow`), so `dimVal ≤ B^m`. -/
theorem dim_le_crude {fac : Nat → Q'} {B dimVal : Q'} {m : Nat}
    (hB : (1 : Q') ≤ B) (hfac : ∀ j, (0 : Q') ≤ fac j) (hle : ∀ j, fac j ≤ B)
    (hdim : dimVal ≤ prodFac fac m) :
    dimVal ≤ B ^ m :=
  Q'.le_trans' _ _ _ hdim (prodFac_le_pow hB hfac hle m)

/-- **Generic crude SQUARED-dimension bound** `dimVal² ≤ B^{2m}`.

From the crude dimension bound `dimVal ≤ B^m` (and `0 ≤ dimVal`), squaring
gives `dimVal² ≤ B^m · B^m = B^{2m}` (`B^m ≥ 0`, monotone product, then
`pow_add`).  This is the uniform-exponent squared majorant: the per-root
tightness is discarded, the exponent `2m` is the same for every axis. -/
theorem dimSq_le_crude {fac : Nat → Q'} {B dimVal : Q'} {m : Nat}
    (hB : (1 : Q') ≤ B) (hfac : ∀ j, (0 : Q') ≤ fac j) (hle : ∀ j, fac j ≤ B)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac m) :
    dimVal * dimVal ≤ B ^ m * B ^ m := by
  have hB0 : (0 : Q') ≤ B := Q'.le_trans' _ _ _ Q'.zero_le_one hB
  have hd := dim_le_crude hB hfac hle hdim
  -- dimVal · dimVal ≤ B^m · B^m  (monotone product, both ≥ 0).
  exact Q'.mul_le_mul_of_nonneg hd hd (Q'.pow_nonneg B hB0 m) hdim_nonneg

/-- `B^m · B^m = B^(m + m)` (so `B^{2m}` is `B^m · B^m` up to the `pow_add`
identity).  Recorded as the bridge between `dimSq_le_crude`'s `B^m · B^m` and
the uniform-exponent form `B^{2m}` the per-axis polylog tail consumes. -/
theorem pow_add_eqv (B : Q') (m n : Nat) :
    (B ^ m * B ^ n).eqv (B ^ (m + n)) := by
  induction n with
  | zero =>
    -- B^m · B^0 = B^m · 1 ≃ B^m = B^(m+0)
    show (B ^ m * B ^ 0).eqv (B ^ (m + 0))
    rw [Nat.add_zero]
    exact Q'.mul_one_eqv (B ^ m)
  | succ n ih =>
    -- B^m · B^(n+1) = B^m · (B · B^n) ≃ B · (B^m · B^n) ≃ B · B^(m+n) = B^(m+(n+1))
    show (B ^ m * B ^ (n + 1)).eqv (B ^ (m + (n + 1)))
    have hidx : m + (n + 1) = (m + n) + 1 := by omega
    rw [hidx]
    show (B ^ m * (B * B ^ n)).eqv (B * B ^ (m + n))
    -- B^m · (B · B^n) ≃ B · (B^m · B^n)
    refine Q'.eqv_trans _ _ _ ?_
      (Q'.mul_eqv_congr_left _ _ _ ih)
    -- B^m · (B · B^n) ≃ B · (B^m · B^n) : reassociate/commute
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (B ^ m) B (B ^ n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (B ^ n) (Q'.mul_comm_eqv (B ^ m) B)) ?_
    exact Q'.mul_assoc_eqv B (B ^ m) (B ^ n)

/-! ## Packaging the crude bound as the repo's `WeylDimData`

The crude squared bound `dimVal² ≤ B^{2m}` is exactly the
`WeylDimData R` residual at UNIFORM per-axis degree: every axis `p` carries the
same excess `B^{2m} − 1` (no `p(N−p)` per-axis tightness).  We build the
`WeylDimData R` from the abstract Weyl-product datum and the crude common bound.

We realize `WeylDimData` at rank `1` with the single uniform axis excess
`B^{2m} − 1` (the product `∏` over the single axis is exactly `1 + (B^{2m}−1)
= B^{2m}`), so the structure's `dimSq_le : dimSqVal ≤ finProd dimSqExcess rank`
is the crude bound `dimVal² ≤ B^{2m}` repackaged.  The honest content — the
abstract Weyl product `dimVal ≤ ∏_{j<m} fac j` with `fac j ≤ B` — is supplied
as hypotheses, not faked. -/

/-- **The crude `WeylDimData`.**  Given the abstract Weyl-product datum for a
group `R` at a lattice point — the squared dimension `dimVal² = (dim V_λ)²`,
the `m` positive-root Weyl factors `fac`, each in `[0, B]` with the crude bound
`B ≥ 1`, and the product domination `dimVal ≤ ∏_{j<m} fac j` — this packages
the crude squared bound `dimVal² ≤ B^{2m}` as a `WeylDimData R` with a single
uniform axis carrying excess `B^{2m} − 1`.

For `SU(N)` instantiate with `B = ∏_{p<N−1}(1 + λ_p)`, `m = N(N−1)/2` (`≤ N²`),
and `fac` the `N(N−1)/2` Weyl factors `1 + (Σ_{p=i}^{j−1}λ_p)/(j−i)`; the
product datum is the SU(N) Weyl dimension formula and `fac j ≤ B` is
`weyl_factor_le_crudeBound`.  The genuine residual stays named in the
hypotheses; the squared-dim majorization itself is proven. -/
def weylDimData_crude {R : RepData} {fac : Nat → Q'} {B dimVal : Q'} {m : Nat}
    (hB : (1 : Q') ≤ B) (hfac : ∀ j, (0 : Q') ≤ fac j) (hle : ∀ j, fac j ≤ B)
    (hdim_nonneg : (0 : Q') ≤ dimVal) (hdim : dimVal ≤ prodFac fac m) :
    WeylDimData R where
  rank        := 1
  dimSqExcess := fun _ => B ^ m * B ^ m - 1
  dimSqVal    := dimVal * dimVal
  exc_nonneg  := fun _ => by
    -- 0 ≤ B^m·B^m − 1  since B^m·B^m ≥ 1 (B ≥ 1).
    have hB0 : (0 : Q') ≤ B := Q'.le_trans' _ _ _ Q'.zero_le_one hB
    have hBm1 : (1 : Q') ≤ B ^ m := one_le_pow hB m
    have hBmm : (1 : Q') ≤ B ^ m * B ^ m := by
      have hstep : (1 : Q') * 1 ≤ B ^ m * B ^ m :=
        Q'.mul_le_mul_of_nonneg hBm1 hBm1 (Q'.pow_nonneg B hB0 m) Q'.zero_le_one
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 1)) hstep
    -- 0 = 1 − 1 ≤ B^m·B^m − 1
    have hz : ((1 : Q') - 1).eqv 0 := by decide
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hz) ?_
    exact Q'.add_le_add_right 1 _ (-1) hBmm
  dimSq_le    := by
    -- dimVal² ≤ B^m·B^m = finProd (fun _ => B^m·B^m − 1) 1.
    refine Q'.le_trans' _ _ _ (dimSq_le_crude hB hfac hle hdim_nonneg hdim) ?_
    -- B^m·B^m ≤ finProd _ 1 = 1·(1 + (B^m·B^m − 1)) ≃ B^m·B^m.
    show B ^ m * B ^ m
      ≤ finProd (fun _ => B ^ m * B ^ m - 1) 1
    refine Q'.le_of_eqv ?_
    -- finProd _ 1 = finProd _ 0 · (1 + (X − 1)) = 1 · (1 + (X − 1)), X = B^m·B^m.
    show (B ^ m * B ^ m).eqv
      (finProd (fun _ => B ^ m * B ^ m - 1) 0
        * (1 + (B ^ m * B ^ m - 1)))
    refine Q'.eqv_symm ?_
    -- 1 · (1 + (X − 1)) ≃ 1 + (X − 1) ≃ X.
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 1 _ (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
    -- 1 + (X − 1) ≃ X.
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 1 _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (B ^ m * B ^ m) (-1) 1) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (show ((-1 : Q') + 1).eqv 0 by decide)) ?_
    exact QPoly.q_add_zero_eqv (B ^ m * B ^ m)

/-! ## SU(N) instantiation cardinality fact `#Δ⁺ = N(N−1)/2 ≤ N²`

The only counting fact the crude route needs: the number of positive roots of
`A_{N−1} = SU(N)` is `m = N(N−1)/2`, a subset of `{1..N}×{1..N}`, so `m ≤ N²`.
This is a pure `Nat` fact (no `p(N−p)` per-axis identity). -/

/-- The number of positive roots of `SU(N)` (type `A_{N−1}`): `#Δ⁺ = N(N−1)/2`. -/
def suN_numPosRoots (N : Nat) : Nat := N * (N - 1) / 2

/-- `#Δ⁺ = N(N−1)/2 ≤ N²` — the crude cardinality bound (the only counting
fact the uniform crude route uses; a subset of `{1..N}×{1..N}`). -/
theorem suN_numPosRoots_le (N : Nat) : suN_numPosRoots N ≤ N * N := by
  show N * (N - 1) / 2 ≤ N * N
  have h1 : N * (N - 1) ≤ N * N := Nat.mul_le_mul_left N (by omega)
  exact Nat.le_trans (Nat.div_le_self _ 2) h1

/-- **The SU(N)-family crude `WeylDimData`.**  For `SU(N)` (rank `r = N − 1`),
the `m = #Δ⁺ = N(N−1)/2` positive-root Weyl factors `fac` each lie under the
crude bound `B = ∏_{p<r}(1 + λ_p)` (`weyl_factor_le_crudeBound`), and the Weyl
dimension is their product `dim V_λ ≤ ∏_{j<m} fac j`.  This packages the crude
squared bound `(dim V_λ)² ≤ B^{2·N(N−1)/2}` as a `WeylDimData R` with the
UNIFORM per-axis exponent — discharging the `WeylDimData` residual for the
whole SU(N) family from the abstract Weyl-product datum, parametric in `N`.

The number of factors is fixed to `m = suN_numPosRoots N` (`≤ N²`,
`suN_numPosRoots_le`); the crude bound is `B = crudeBound lab (N − 1)` for the
`SU(N)` labels `lab`.  The genuine SU(N) residual — the Weyl dimension product
`dimVal ≤ ∏_{j<m} fac j` over the `N(N−1)/2` positive roots — is the
hypothesis, not faked. -/
def suN_weylDimData_crude {R : RepData} (N : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p)
    (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab (N - 1))
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac (suN_numPosRoots N)) :
    WeylDimData R :=
  weylDimData_crude (B := crudeBound lab (N - 1)) (m := suN_numPosRoots N)
    (crudeBound_ge_one hlab (N - 1)) hfac hle hdim_nonneg hdim

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.prodFac_nonneg
#print axioms YMGap.RG.one_le_pow
#print axioms YMGap.RG.prodFac_le_pow
#print axioms YMGap.RG.crudeBound_ge_one
#print axioms YMGap.RG.weyl_factor_le_crudeBound
#print axioms YMGap.RG.dim_le_crude
#print axioms YMGap.RG.dimSq_le_crude
#print axioms YMGap.RG.pow_add_eqv
#print axioms YMGap.RG.weylDimData_crude
#print axioms YMGap.RG.suN_numPosRoots_le
#print axioms YMGap.RG.suN_weylDimData_crude
