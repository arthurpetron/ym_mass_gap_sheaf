/-
# The M-uniform finite-difference modulus for the finite-product truncations
  (Wall-2, Route A, `fdboundC` field: the corrected FLAT product modulus)

## Why the recursive `finiteProductFDDeriv` modulus cannot inhabit `huni`

`ThetaProdDprodClose.UniformProdModulus.huni` demands ONE positive `delStar ε'`
below EVERY per-`M` finite-product modulus
`(FiniteProductFDDeriv.finiteProductFDDeriv C Dk M).δ ε'`.  For the as-built
combinator `C = MulCombinatorClose.mulCombinator`, that recursive modulus is
**monotone-decreasing in `M` with infimum `0`**: each `MulCombinator.mul` step
rescales the tolerance by `mulEta ε = min(1, ½ε/mulK)` with `mulK ≥ 1`, so
unrolling the product head `M` times contracts the innermost factor tolerance
geometrically.  Hence `inf_M (…).δ ε' = 0`, and NO positive `delStar` clears all
`M`: the literal `huni` is unsatisfiable for that `C`.

## The corrected object: a FLAT (non-recursive) M-uniform modulus

The genuine fact is that the *analysis* is M-uniform, not the recursive `δ`.  The
finite-product second finite-difference obeys a single quadratic bound

    |fdRem (∏_{k<M} f_k)(prodDeriv) x h| ≤ B · h²      (|h| ≤ 1, all M),

with `B` assembled from the M-uniform head bound `|P_M| ≤ Θ` and the M-uniform
`Σ`-bounds `sup_M |S_M|`, `sup_M |S_M'|` (geometric tails).  From this ONE datum a
FLAT modulus `δ ε := min(1, ε/B)` — **independent of `M`** — clears the
finite-difference bound for every truncation simultaneously, so `huni` becomes
`le_refl`.

This module builds that flat modulus (`prodFlatModulus`), the re-typed uniform
struct reading a flat family (`UniformProdModulusFlat`), its inhabitant
(`prodUnifModulus`, `huni = le_refl`), and the M-uniform finite-difference bound
`fdboundFlat` — the rational core the CReal `fdboundC` consumes (the lift
`ofQ'FDDerivDataC` is index-wise equal).

## Net residual ledger

The sole named `Type`-level residual is `ProdSecondDiffResidual` — the quadratic
second finite-difference bound `|fdRem …| ≤ B·h²`.  Per the analysis map, this is
the second-difference strengthening of the already-routed
`ThetaDerivDriverClose.DriverProductResidual` plus the one new per-factor estimate
`σ_k'` (a line-for-line mirror of the proved `ThetaDerivDriverClose.sigma_abs_le`).
Everything downstream of that datum — the flat modulus, its positivity, the
uniform bound, and the `huni = le_refl` close — is proved here in full.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  `ProdSecondDiffResidual` is `Type`-level data
(a structure), never `sorry`.
-/

import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.DiffProduct
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.ProdUnifModulusClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv (fdRem FDDerivData)
open YMGap.Continuum.DiffProduct (pre)
open YMGap.Continuum.FiniteProductFDDeriv (prodDeriv)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. `(0 : Q') < 1` (local, avoids importing the order layer). -/

/-- Strict positivity of `1 : Q'`, via numerator positivity. -/
theorem zero_lt_one' : (0 : Q') < (1 : Q') := CReal.pos_of_num_pos (by decide)

/-! ## 1. The sole named residual: the quadratic second finite-difference bound.

The finite-product cleared remainder is second-order in the increment: substituting
the per-factor Taylor data into the Leibniz product gives an `O(h²)` bound with a
prefactor `B` built from the M-uniform head bound `|P_M| ≤ Θ` and the M-uniform
log-derivative `Σ`-bounds.  We package exactly that bound as `Type`-level data
(Rule 8), NOT as a theorem — it is the second-difference strengthening of
`ThetaDerivDriverClose.DriverProductResidual` together with the new `σ_k'`
estimate. -/

/-- **The quadratic second finite-difference residual** (named `Type`-level datum).
For a single M-independent prefactor `B > 0`, every finite-product truncation's
cleared finite-difference remainder is `≤ B·h²` on `|h| ≤ 1`. -/
structure ProdSecondDiffResidual (fk : Nat → Q' → Q') (dk : Nat → Q') (x B : Q') :
    Type where
  /-- The M-independent quadratic prefactor is strictly positive. -/
  hBpos : (0 : Q') < B
  /-- The uniform quadratic second finite-difference bound, on `|h| ≤ 1`, all `M`. -/
  quad : ∀ (M : Nat) (h : Q'), Q'.abs h ≤ (1 : Q') →
    Q'.abs (fdRem (fun t => pre (fun k => fk k t) M) (prodDeriv fk dk x M) x h)
      ≤ B * (h * h)

/-! ## 2. The FLAT M-uniform modulus (fully proved from the residual). -/

/-- **The flat, M-uniform finite-difference derivative datum.**  For each `M`, the
finite product `∏_{k<M} f_k` has finite-difference derivative `prodDeriv fk dk x M`
at `x` with the **M-independent** modulus `δ ε = min(1, ε/B)`.  Uniformity is
manifest: `δ` does not mention `M`.

The bound proof is the standard `O(h²) ⟹ o(h)` step:
`|fdRem| ≤ B·h² ≤ B·(|h|·|h|) = (B·|h|)·|h| ≤ ε·|h|`, using the `≤1` leg for the
residual hypothesis and the `≤ε/B` leg (via `divPos_mul_eqv`) for `B·|h| ≤ ε`. -/
def prodFlatModulus {fk : Nat → Q' → Q'} {dk : Nat → Q'} {x B : Q'}
    (H : ProdSecondDiffResidual fk dk x B) (M : Nat) :
    FDDerivData (fun t => pre (fun k => fk k t) M) (prodDeriv fk dk x M) x where
  δ ε := Q'.min' 1 (Q'.divPos ε B H.hBpos)
  δ_pos ε hε := TsumDeriv.Q'.lt_min' zero_lt_one' (Q'.divPos_pos ε B H.hBpos hε)
  bound := by
    intro ε hε h hpos hle
    -- Split the two legs of the min modulus.
    have hle1 : Q'.abs h ≤ (1 : Q') :=
      Q'.le_trans' _ _ _ hle (Q'.min_le_left' 1 (Q'.divPos ε B H.hBpos))
    have hleD : Q'.abs h ≤ Q'.divPos ε B H.hBpos :=
      Q'.le_trans' _ _ _ hle (Q'.min_le_right' 1 (Q'.divPos ε B H.hBpos))
    -- The residual gives the quadratic bound.
    have hres := H.quad M h hle1
    -- The `≤ ε/B` leg gives `B·|h| ≤ ε`.
    have hBh : B * Q'.abs h ≤ ε := by
      have hstep : Q'.abs h * B ≤ (Q'.divPos ε B H.hBpos) * B :=
        Q'.mul_le_mul_of_nonneg_right _ _ B hleD (Q'.le_of_lt H.hBpos)
      have hdiv : (Q'.divPos ε B H.hBpos * B) ≈ ε := Q'.divPos_mul_eqv ε B H.hBpos
      have hAbsB : Q'.abs h * B ≤ ε := Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hdiv)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv B (Q'.abs h))) hAbsB
    -- `h·h ≤ |h|·|h|`.
    have hhh : h * h ≤ Q'.abs h * Q'.abs h :=
      Q'.le_trans' _ _ _ (Q'.le_abs_self (h * h)) (TsumDeriv.Q'.abs_mul_le h h)
    -- `B·(h·h) ≤ B·(|h|·|h|)`.
    have hb1 : B * (h * h) ≤ B * (Q'.abs h * Q'.abs h) :=
      Q'.mul_le_mul_of_nonneg_left _ _ B hhh (Q'.le_of_lt H.hBpos)
    -- `B·(|h|·|h|) ≈ (B·|h|)·|h|`.
    have hassoc : (B * (Q'.abs h * Q'.abs h)) ≈ ((B * Q'.abs h) * Q'.abs h) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv B (Q'.abs h) (Q'.abs h))
    -- `(B·|h|)·|h| ≤ ε·|h|`.
    have hb2 : (B * Q'.abs h) * Q'.abs h ≤ ε * Q'.abs h :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hBh (Q'.abs_nonneg h)
    -- Chain: `|fdRem| ≤ B·h² ≤ B·(|h|·|h|) = (B·|h|)·|h| ≤ ε·|h|`.
    refine Q'.le_trans' _ _ _ hres ?_
    refine Q'.le_trans' _ _ _ hb1 ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) hb2

/-! ## 3. The re-typed uniform struct reading a flat family, and its inhabitant. -/

/-- **The corrected uniform-in-`M` modulus struct.**  Identical shape to
`ThetaProdDprodClose.UniformProdModulus`, but `huni` reads a FLAT family
`Dprodfam M` (each a `FDDerivData` at `x`) instead of the recursive
`finiteProductFDDeriv C Dk M` whose `δ` provably tends to `0`. -/
structure UniformProdModulusFlat {x : Q'}
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dprodfam : ∀ M, FDDerivData (fun t => pre (fun k => fk k t) M)
                       (prodDeriv fk dk x M) x) : Type where
  /-- The common finite-difference modulus (family equicontinuity at `x`). -/
  delStar : Q' → Q'
  /-- `delStar` is positive for positive tolerance. -/
  delStar_pos : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < delStar ε
  /-- The stage past which the common modulus is valid. -/
  mStar : Q' → Nat
  /-- Past `mStar ε'`, `delStar ε'` is below the per-`M` flat modulus. -/
  huni : ∀ ε' : Q', ∀ M : Nat, mStar ε' ≤ M →
    delStar ε' ≤ (Dprodfam M).δ ε'

/-- **The inhabitant.**  For the flat family `prodFlatModulus H`, `delStar` IS the
per-`M` modulus (definitionally M-independent), so `mStar ≡ 0` and `huni` is
`le_refl`.  This closes the corrected uniform-modulus obligation from the single
residual `H`. -/
def prodUnifModulus {fk : Nat → Q' → Q'} {dk : Nat → Q'} {x B : Q'}
    (H : ProdSecondDiffResidual fk dk x B) :
    UniformProdModulusFlat fk dk (prodFlatModulus H) where
  delStar ε := Q'.min' 1 (Q'.divPos ε B H.hBpos)
  delStar_pos ε hε := TsumDeriv.Q'.lt_min' zero_lt_one' (Q'.divPos_pos ε B H.hBpos hε)
  mStar _ := 0
  huni _ _ _ := Q'.le_refl' _

/-! ## 4. The M-uniform finite-difference bound (the `fdboundC` rational core). -/

/-- **`fdboundFlat` — the M-uniform finite-difference bound.**  Past `mStar ε'`, the
single modulus `delStar ε'` yields the cleared finite-difference bound for EVERY
finite-product truncation, exactly the shape `ThetaProdDprodClose.prodC1Inputs`
feeds into `fdboundC` (there through the CReal lift `ofQ'FDDerivDataC`, which is
index-wise equal to this rational bound).  Proof: `Q'.le_trans'` through `huni`
into the per-`M` flat modulus, then `(prodFlatModulus H M).bound`. -/
theorem fdboundFlat {fk : Nat → Q' → Q'} {dk : Nat → Q'} {x B : Q'}
    (H : ProdSecondDiffResidual fk dk x B)
    (U : UniformProdModulusFlat fk dk (prodFlatModulus H))
    (ε' : Q') (hε' : (0 : Q') < ε') (M : Nat) (hM : U.mStar ε' ≤ M)
    (h : Q') (hpos : (0 : Q') < Q'.abs h) (hle : Q'.abs h ≤ U.delStar ε') :
    Q'.abs (fdRem (fun t => pre (fun k => fk k t) M) (prodDeriv fk dk x M) x h)
      ≤ ε' * Q'.abs h :=
  (prodFlatModulus H M).bound ε' hε' h hpos
    (Q'.le_trans' (Q'.abs h) (U.delStar ε') ((prodFlatModulus H M).δ ε')
      hle (U.huni ε' M hM))

end YMGap.Continuum.ProdUnifModulusClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ProdUnifModulusClose.zero_lt_one'
#print axioms YMGap.Continuum.ProdUnifModulusClose.prodFlatModulus
#print axioms YMGap.Continuum.ProdUnifModulusClose.prodUnifModulus
#print axioms YMGap.Continuum.ProdUnifModulusClose.fdboundFlat
