/-
# `DeMoivreNode 5` fully inhabited at `√(3/4)`, and the uniform-in-`M` branch reduction

This module completes the order-5 de Moivre rotation node and reduces the general-`M`
located-branch obligation to ONE elementary residual, reusing the machine-checked
Pythagorean identity `Cheb.pythForm_all`.

## Track A — `DeMoivreNode 5` fully inhabited (no Pell, no located sign)

The largest `U₅`-node is `cos(π/6) = √(3/4)`, a node with `x² ≈ 3/4`.  The order-6
`Tcr`/`Ucr` ladder collapses through `x² = 3/4` exactly as `deMoivre3`'s does through
`x² = 1/2`.  The `√(3/4)` radicand is RATIONAL, so `CReal.sqrtFrom` suffices — no
`csqrt` (moving CReal radicand) is needed for this node.

  * **`s34`/`s34sq`** — the located `√(3/4)` node and its defining identity
    `s34·s34 ≈ 3/4`.
  * **`Tcr{2..6}_of_34` / `Ucr{2..5}_of_34`** — the `3/4`-square node ladder (each a
    one-step recurrence collapse), the `3/4`-analogues of
    `ChebLocatedRoots.Tcr{2,3,4}_of_half` / `Ucr{2,3}_of_half`.
  * **`deMoivre5 : DeMoivreNode 5`** — FULLY INHABITED: `root = U₅(√¾) ≈ 0`
    (`Ucr5_of_34`), `half = T₆(√¾) ≈ −1` (`Tcr6_of_34`).  No Pell, no located sign
    needed at `M = 5`.

## Track B — the uniform-in-`M` reduction

For general `M` the surd ladder has no rational closed form, so `DeMoivreHalf` is
assembled from the Pythagorean identity plus a located branch sign:

  * **`tcr_pell`** — lift of the machine-checked `Cheb.pythForm_all` to `CReal`:
    `T_{M+1}(x)² + (1−x²)·U_M(x)² ≈ 1`, for ALL `x`, ALL `M` (no bound on `x`).
  * **`tcr_sq_one_of_root`** — under `U_M(x) ≈ 0`, the off-part collapses and
    `T_{M+1}(x)² ≈ 1` (branch-free).
  * **`LocatedBranchCollapse`** — the SOLE remaining elementary residual: the
    located branch-sign collapse `a² ≈ 1 ∧ a ≤ 0 ⟹ a ≈ −1`.
  * **`deMoivreHalf_of_root_sign`** — given the branch collapse, a `U_M`-root datum
    and a co-located sign `T_{M+1}(x) ≤ 0` discharge `DeMoivreHalf M x`.  So the entire
    uniform residual is `LocatedBranchCollapse` + two per-`M` located bracket inputs.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`, no
`native_decide`, no custom axiom.  `decide` only on closed `Q'`/`Nat`.  All node data are
`Type`-level; the residual `LocatedBranchCollapse` / `DeMoivreHalf` are `Prop`s, never
`sorry`.
-/

import YMGap.Continuum.ChebRotationPair

namespace YMGap.Continuum.ChebLocatedNodesGen

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebLocatedRoots (Ucr Tcr cmul_x_zero cmul_neg cneg_ofQ')

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The two rational constants `3/4` and `3/2` -/

/-- `3/4 : Q'` (the square of the node `cos(π/6) = √(3/4)`). -/
abbrev q34 : Q' := Q'.mkPos 3 4 (by decide)

/-- `3/2 : Q'` (the value `2·(3/4)`). -/
abbrev q32 : Q' := Q'.mkPos 3 2 (by decide)

/-! ## 1. The located `√(3/4)` node and its square -/

/-- The constructive real `√(3/4)` (`a = 3/4`, `L = 1/2`, `L·L = 1/4 ≤ 3/4`). -/
def s34 : CReal :=
  CReal.sqrtFrom q34 HalfPow.half (by decide) (by decide) (by decide)

/-- `s34 · s34 ≈ 3/4`. -/
theorem s34sq : CReal.Equiv (CReal.mul s34 s34) (CReal.ofQ' q34) :=
  CReal.sqrtFrom_sq_equiv q34 HalfPow.half (by decide) (by decide) (by decide)

/-! ## 2. Small `CReal` scalar helpers -/

/-- `ofQ' 2 · ofQ' (3/4) ≈ ofQ' (3/2)`. -/
theorem two_34 :
    CReal.Equiv (CReal.mul (CReal.ofQ' 2) (CReal.ofQ' q34)) (CReal.ofQ' q32) :=
  CReal.Equiv.trans (CReal.Equiv.symm (CRealContinuumAlg.cofQ'_mul 2 q34))
    (ChebDiscreteOrtho.ofQ'_eqv (by decide : ((2 : Q') * q34) ≈ q32))

/-- `(2y)·y ≈ 3/2` for a `3/4`-square node `y`: `2·(y·y) ≈ 2·(3/4) = 3/2`. -/
theorem mul34_three_halves (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) y) (CReal.ofQ' q32) :=
  CReal.Equiv.trans (CRealAlg.cmul_assoc (CReal.ofQ' 2) y y)
    (CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right hy) two_34)

/-- Scalar-through-node: `(2y)·(ofQ' c) ≈ (ofQ' (2·c))·y`. -/
theorem two_y_scaled (y : CReal) (c : Q') :
    CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (CReal.ofQ' c))
      (CReal.mul (CReal.ofQ' (2 * c)) y) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (((2 : Q') * y.approx n) * c) ≈ ((2 * c) * y.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv 2 (y.approx n) c) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left 2 (y.approx n * c) (c * y.approx n)
      (Q'.mul_comm_eqv (y.approx n) c)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv 2 c (y.approx n))

/-- `(ofQ' (-1))·y ≈ neg y`. -/
theorem cmul_negone_left (y : CReal) :
    CReal.Equiv (CReal.mul (CReal.ofQ' (-(1 : Q'))) y) (CReal.neg y) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((-(1 : Q')) * y.approx n) ≈ (-(y.approx n))
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (y.approx n)) ?_
  exact Q'.neg_eqv_congr (1 * y.approx n) (y.approx n) (Q'.one_mul_eqv (y.approx n))

/-- `(2y)·(2y) ≈ 3` for a `3/4`-square node `y`: `4·(y·y) ≈ 4·(3/4) = 3`. -/
theorem two_y_sq (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (CReal.mul (CReal.ofQ' 2) y))
      (CReal.ofQ' 3) := by
  refine CReal.Equiv.trans (CRealAlg.cmul_assoc (CReal.ofQ' 2) y (CReal.mul (CReal.ofQ' 2) y)) ?_
  have hy2 : CReal.Equiv (CReal.mul y (CReal.mul (CReal.ofQ' 2) y)) (CReal.ofQ' q32) :=
    CReal.Equiv.trans (CRealAlg.cmul_comm y (CReal.mul (CReal.ofQ' 2) y))
      (mul34_three_halves y hy)
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right hy2) ?_
  refine CReal.Equiv.trans (CReal.Equiv.symm (CRealContinuumAlg.cofQ'_mul 2 q32)) ?_
  exact ChebDiscreteOrtho.ofQ'_eqv (by decide : ((2 : Q') * q32) ≈ (3 : Q'))

/-! ## 3. The `3/4`-square first-kind (`T`) node ladder -/

/-- `Tcr y 2 ≈ 1/2`: `2x²−1 ≈ 2·(3/4)−1 = 1/2`. -/
theorem Tcr2_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Tcr y 2) (CReal.ofQ' HalfPow.half) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) y) (CReal.neg CReal.cone))
    (CReal.ofQ' HalfPow.half)
  refine CReal.Equiv.trans (Pivot2.add_congr (mul34_three_halves y hy) (Pivot2.equiv_refl _)) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (q32 + (-(1 : Q'))) ≈ HalfPow.half
  decide

/-- `Tcr y 3 ≈ 0`: `2x·T₂ − T₁ ≈ 2x·(1/2) − x = x − x = 0`. -/
theorem Tcr3_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Tcr y 3) (CReal.ofQ' 0) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 2)) (CReal.neg y)) (CReal.ofQ' 0)
  have hL : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 2)) y := by
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Tcr2_of_34 y hy)) ?_
    refine CReal.Equiv.trans (two_y_scaled y HalfPow.half) ?_
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_left
        (ChebDiscreteOrtho.ofQ'_eqv (by decide : ((2 : Q') * HalfPow.half) ≈ (1 : Q')))) ?_
    exact CRealAlg.cone_mul y
  refine CReal.Equiv.trans (Pivot2.add_congr hL (Pivot2.equiv_refl _)) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (y.approx n + (-(y.approx n))) ≈ (0 : Q')
  exact Q'.add_neg_self_eqv _

/-- `Tcr y 4 ≈ −1/2`: `2x·T₃ − T₂ ≈ 0 − 1/2 = −1/2`. -/
theorem Tcr4_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Tcr y 4) (CReal.ofQ' (-(HalfPow.half))) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 3)) (CReal.neg (Tcr y 2)))
    (CReal.ofQ' (-(HalfPow.half)))
  have hA : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 3)) (CReal.ofQ' 0) :=
    CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Tcr3_of_34 y hy)) (cmul_x_zero _)
  have hB : CReal.Equiv (CReal.neg (Tcr y 2)) (CReal.ofQ' (-(HalfPow.half))) :=
    CReal.Equiv.trans (Pivot2.neg_congr (Tcr2_of_34 y hy)) (cneg_ofQ' HalfPow.half)
  refine CReal.Equiv.trans (Pivot2.add_congr hA hB) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((0 : Q') + (-(HalfPow.half))) ≈ (-(HalfPow.half))
  decide

/-- `Tcr y 5 ≈ −y`: `2x·T₄ − T₃ ≈ 2x·(−1/2) − 0 = −x`. -/
theorem Tcr5_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Tcr y 5) (CReal.neg y) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 4)) (CReal.neg (Tcr y 3)))
    (CReal.neg y)
  have hA : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 4)) (CReal.neg y) := by
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Tcr4_of_34 y hy)) ?_
    refine CReal.Equiv.trans (two_y_scaled y (-(HalfPow.half))) ?_
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_left
        (ChebDiscreteOrtho.ofQ'_eqv (by decide : ((2 : Q') * (-(HalfPow.half))) ≈ (-(1 : Q'))))) ?_
    exact cmul_negone_left y
  have hB : CReal.Equiv (CReal.neg (Tcr y 3)) (CReal.ofQ' 0) :=
    CReal.Equiv.trans (Pivot2.neg_congr (Tcr3_of_34 y hy))
      (CReal.Equiv.trans (cneg_ofQ' 0)
        (ChebDiscreteOrtho.ofQ'_eqv (by decide : (-(0 : Q')) ≈ (0 : Q'))))
  refine CReal.Equiv.trans (Pivot2.add_congr hA hB) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((-(y.approx n)) + (0 : Q')) ≈ (-(y.approx n))
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- `Tcr y 6 ≈ −1`: `2x·T₅ − T₄ ≈ 2x·(−x) − (−1/2) = −3/2 + 1/2 = −1`. -/
theorem Tcr6_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Tcr y 6) (CReal.ofQ' (-(1 : Q'))) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 5)) (CReal.neg (Tcr y 4)))
    (CReal.ofQ' (-(1 : Q')))
  have hA : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 5))
      (CReal.ofQ' (-(q32))) := by
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Tcr5_of_34 y hy)) ?_
    refine CReal.Equiv.trans (cmul_neg (CReal.mul (CReal.ofQ' 2) y) y) ?_
    refine CReal.Equiv.trans (Pivot2.neg_congr (mul34_three_halves y hy)) ?_
    exact cneg_ofQ' q32
  have hB : CReal.Equiv (CReal.neg (Tcr y 4)) (CReal.ofQ' HalfPow.half) := by
    refine CReal.Equiv.trans (Pivot2.neg_congr (Tcr4_of_34 y hy)) ?_
    refine CReal.Equiv.trans (cneg_ofQ' (-(HalfPow.half))) ?_
    exact ChebDiscreteOrtho.ofQ'_eqv (by decide : (-(-(HalfPow.half))) ≈ HalfPow.half)
  refine CReal.Equiv.trans (Pivot2.add_congr hA hB) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((-(q32)) + HalfPow.half) ≈ (-(1 : Q'))
  decide

/-! ## 4. The `3/4`-square second-kind (`U`) node ladder -/

/-- `Ucr y 2 ≈ 2`: `4x²−1 ≈ 4·(3/4)−1 = 3−1 = 2`. -/
theorem Ucr2_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Ucr y 2) (CReal.ofQ' 2) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (CReal.mul (CReal.ofQ' 2) y))
      (CReal.neg CReal.cone)) (CReal.ofQ' 2)
  refine CReal.Equiv.trans (Pivot2.add_congr (two_y_sq y hy) (Pivot2.equiv_refl _)) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((3 : Q') + (-(1 : Q'))) ≈ (2 : Q')
  decide

/-- `Ucr y 3 ≈ 2y`: `2x·U₂ − U₁ ≈ 2x·2 − 2x = 4x − 2x = 2x`. -/
theorem Ucr3_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Ucr y 3) (CReal.mul (CReal.ofQ' 2) y) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Ucr y 2))
      (CReal.neg (CReal.mul (CReal.ofQ' 2) y))) (CReal.mul (CReal.ofQ' 2) y)
  have hL : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Ucr y 2))
      (CReal.mul (CReal.ofQ' 4) y) := by
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Ucr2_of_34 y hy)) ?_
    refine CReal.Equiv.trans (two_y_scaled y 2) ?_
    exact CRealContinuumAlg.cmul_congr_left
      (ChebDiscreteOrtho.ofQ'_eqv (by decide : ((2 : Q') * 2) ≈ (4 : Q')))
  refine CReal.Equiv.trans (Pivot2.add_congr hL (Pivot2.equiv_refl _)) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((4 : Q') * y.approx n + (-((2 : Q') * y.approx n))) ≈ ((2 : Q') * y.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.sub_mul_eqv 4 2 (y.approx n))) ?_
  exact Q'.mul_eqv_congr_right (4 + -2) 2 (y.approx n) (by decide)

/-- `Ucr y 4 ≈ 1`: `2x·U₃ − U₂ ≈ 2x·2x − 2 = 3 − 2 = 1`. -/
theorem Ucr4_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Ucr y 4) (CReal.ofQ' 1) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Ucr y 3)) (CReal.neg (Ucr y 2)))
    (CReal.ofQ' 1)
  have hL : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Ucr y 3)) (CReal.ofQ' 3) :=
    CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Ucr3_of_34 y hy)) (two_y_sq y hy)
  have hR : CReal.Equiv (CReal.neg (Ucr y 2)) (CReal.ofQ' (-(2 : Q'))) :=
    CReal.Equiv.trans (Pivot2.neg_congr (Ucr2_of_34 y hy)) (cneg_ofQ' 2)
  refine CReal.Equiv.trans (Pivot2.add_congr hL hR) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((3 : Q') + (-(2 : Q'))) ≈ (1 : Q')
  decide

/-- `Ucr y 5 ≈ 0`: `2x·U₄ − U₃ ≈ 2x·1 − 2x = 0`. -/
theorem Ucr5_of_34 (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' q34)) :
    CReal.Equiv (Ucr y 5) (CReal.ofQ' 0) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Ucr y 4)) (CReal.neg (Ucr y 3)))
    (CReal.ofQ' 0)
  have hL : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Ucr y 4))
      (CReal.mul (CReal.ofQ' 2) y) :=
    CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Ucr4_of_34 y hy))
      (CRealAlg.cmul_cone (CReal.mul (CReal.ofQ' 2) y))
  have hR : CReal.Equiv (CReal.neg (Ucr y 3)) (CReal.neg (CReal.mul (CReal.ofQ' 2) y)) :=
    Pivot2.neg_congr (Ucr3_of_34 y hy)
  refine CReal.Equiv.trans (Pivot2.add_congr hL hR) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((2 : Q') * y.approx n + (-((2 : Q') * y.approx n))) ≈ (0 : Q')
  exact Q'.add_neg_self_eqv _

/-! ## 5. `DeMoivreNode 5` fully inhabited at `√(3/4) = cos π/6` -/

/-- **`DeMoivreNode 5`, FULLY INHABITED** at `x = √(3/4)` (`cos π/6`).  `root` is
`U₅(√¾) ≈ 0` (`Ucr5_of_34`), `half` is `T₆(√¾) ≈ −1` (`Tcr6_of_34`).  No Pell identity,
no `csqrt`, no located branch-sign is needed — the surd ladder discharges `half`
outright. -/
def deMoivre5 : ChebRotationPair.DeMoivreNode 5 where
  x := s34
  root := Ucr5_of_34 s34 s34sq
  half := Tcr6_of_34 s34 s34sq

/-- The residual `DeMoivreHalf 5 √(3/4)` is discharged (the branch sign at order 5). -/
theorem deMoivreHalf5 : ChebRotationPair.DeMoivreHalf 5 s34 :=
  deMoivre5.half

/-- The half-period `s`-coordinate at the order-5 node vanishes (free from `root`). -/
theorem deMoivre5_half_period_s (yv : CReal) :
    CReal.Equiv (CReal.mul (Ucr s34 5) yv) (CReal.ofQ' 0) :=
  ChebRotationPair.half_period_s 5 s34 yv deMoivre5.root

/-! ## 6. The uniform-in-`M` reduction (Track B) -/

/-- **The `CReal` Pythagorean identity, uniform in `M`, for ALL `x`** (no bound on `x`):
`T_{M+1}(x)² + (1−x²)·U_M(x)² ≈ 1`.  Lifted approx-wise from the machine-checked
`Cheb.pythForm_all`. -/
theorem tcr_pell (x : CReal) (M : Nat) :
    CReal.Equiv
      (CReal.add (CReal.mul (Tcr x (M + 1)) (Tcr x (M + 1)))
        (CReal.mul (CReal.add CReal.cone (CReal.neg (CReal.mul x x)))
          (CReal.mul (Ucr x M) (Ucr x M))))
      CReal.cone := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((Tcr x (M + 1)).approx n * (Tcr x (M + 1)).approx n
        + ((CReal.cone.approx n + (-(x.approx n * x.approx n)))
            * ((Ucr x M).approx n * (Ucr x M).approx n)))
      ≈ CReal.cone.approx n
  rw [ChebLocatedRoots.Tcr_approx x n (M + 1), ChebLocatedRoots.Ucr_approx x n M]
  exact Cheb.pythForm_all M (x.approx n)

/-- **Branch-free square collapse**: under `U_M(x) ≈ 0`, the off-part vanishes and
`T_{M+1}(x)² ≈ 1`. -/
theorem tcr_sq_one_of_root (x : CReal) (M : Nat)
    (root : CReal.Equiv (Ucr x M) (CReal.ofQ' 0)) :
    CReal.Equiv (CReal.mul (Tcr x (M + 1)) (Tcr x (M + 1))) CReal.cone := by
  have hpell := tcr_pell x M
  have hUU : CReal.Equiv (CReal.mul (Ucr x M) (Ucr x M)) (CReal.ofQ' 0) :=
    CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right root) (cmul_x_zero (Ucr x M))
  have hoff : CReal.Equiv
      (CReal.mul (CReal.add CReal.cone (CReal.neg (CReal.mul x x)))
        (CReal.mul (Ucr x M) (Ucr x M))) (CReal.ofQ' 0) :=
    CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right hUU)
      (cmul_x_zero (CReal.add CReal.cone (CReal.neg (CReal.mul x x))))
  have hstep : CReal.Equiv
      (CReal.add (CReal.mul (Tcr x (M + 1)) (Tcr x (M + 1))) (CReal.ofQ' 0)) CReal.cone :=
    CReal.Equiv.trans (Pivot2.add_congr (Pivot2.equiv_refl _) (CReal.Equiv.symm hoff)) hpell
  have hzr : CReal.Equiv
      (CReal.add (CReal.mul (Tcr x (M + 1)) (Tcr x (M + 1))) (CReal.ofQ' 0))
      (CReal.mul (Tcr x (M + 1)) (Tcr x (M + 1))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.add_zero' _))
  exact CReal.Equiv.trans (CReal.Equiv.symm hzr) hstep

/-- **The sole remaining elementary residual for the uniform-in-`M` chain**: the located
branch-sign collapse `a² ≈ 1 ∧ a ≤ 0 ⟹ a ≈ −1`.  A single reusable `CReal` sign lemma;
its two per-`M` located bracket inputs (`root` and the co-located `sign`) live behind the
general-`M` rational-π-enclosure wall. -/
def LocatedBranchCollapse : Prop :=
  ∀ (a : CReal), CReal.Equiv (CReal.mul a a) CReal.cone → a ≤ CReal.czero →
    CReal.Equiv a (CReal.ofQ' (-(1 : Q')))

/-- **The uniform-in-`M` assembly of `DeMoivreHalf`.**  Given the located branch collapse,
a `U_M`-root datum (`root`) and a co-located branch sign (`sign : T_{M+1}(x) ≤ 0`) discharge
`DeMoivreHalf M x`.  The entire uniform residual is `LocatedBranchCollapse` plus the two
per-`M` located bracket inputs. -/
theorem deMoivreHalf_of_root_sign (hbc : LocatedBranchCollapse)
    (x : CReal) (M : Nat)
    (root : CReal.Equiv (Ucr x M) (CReal.ofQ' 0))
    (sign : Tcr x (M + 1) ≤ CReal.czero) :
    ChebRotationPair.DeMoivreHalf M x :=
  hbc (Tcr x (M + 1)) (tcr_sq_one_of_root x M root) sign

/-- **`M = 5` cross-check via the uniform chain.**  Independently of the surd `deMoivreHalf5`,
`T₆(√¾)² ≈ 1` from `tcr_sq_one_of_root` fed by the located root `U₅(√¾) ≈ 0`. -/
theorem tcr5_sq_one_of_root : CReal.Equiv (CReal.mul (Tcr s34 6) (Tcr s34 6)) CReal.cone :=
  tcr_sq_one_of_root s34 5 (Ucr5_of_34 s34 s34sq)

end YMGap.Continuum.ChebLocatedNodesGen

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebLocatedNodesGen.s34sq
#print axioms YMGap.Continuum.ChebLocatedNodesGen.Tcr6_of_34
#print axioms YMGap.Continuum.ChebLocatedNodesGen.Ucr5_of_34
#print axioms YMGap.Continuum.ChebLocatedNodesGen.deMoivre5
#print axioms YMGap.Continuum.ChebLocatedNodesGen.deMoivreHalf5
#print axioms YMGap.Continuum.ChebLocatedNodesGen.deMoivre5_half_period_s
#print axioms YMGap.Continuum.ChebLocatedNodesGen.tcr_pell
#print axioms YMGap.Continuum.ChebLocatedNodesGen.tcr_sq_one_of_root
#print axioms YMGap.Continuum.ChebLocatedNodesGen.deMoivreHalf_of_root_sign
#print axioms YMGap.Continuum.ChebLocatedNodesGen.tcr5_sq_one_of_root
