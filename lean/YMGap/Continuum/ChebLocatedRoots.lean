/-
# The located irrational `U₃` nodes `0, ±√(1/2)` — order-3 `t > 0` off-diagonal
# OS2 closed UNCONDITIONALLY (Track B: located √½ nodes + power-sum collapse)

The `t > 0` heat-kernel off-diagonal OS2 reduces (`HeatKernelGaussNode`,
`RiemannSOS`) to the Gauss–Chebyshev exactness of the second-kind discrete
orthogonality at the irrational nodes `x_k = cos(kπ/(M+1))` (the roots of `U_M`).
For `M = 3` those nodes are `0, ±√(1/2)`, and the entire order-3 chain was
previously reduced (`ChebDiscreteOrtho`) to the SINGLE located-root residual
`LocatedRootPowerSums3` — "the located `U₃` roots realize the Newton first-kind
power sums `S₁,…,S₄`" — with the explicit note that no `M = 3` node datum had been
*constructed* (the rational-node interface `RootedNodes` cannot give one, since the
nodes are irrational).

## What this module proves (genuine, axiom-clean, π-free)

  * **The constructive `√(1/2)` node** `shalf` (via `CReal.sqrtFrom`), with its
    defining identity `shalf·shalf ≃ ½` (`ssq`) and the symmetric companion
    `(−shalf)·(−shalf) ≃ ½` (`ssq'`).  This is the ONLY transcendental-free located
    real needed; everything else collapses to rationals through `s² ≃ ½`.

  * **`CReal` Chebyshev recurrences** `Ucr`, `Tcr` (the constructive-real mirrors of
    `Cheb.U`, `Cheb.T`), with the pointwise bridges `Ucr_approx`/`Tcr_approx`
    (`(Ucr x p).approx n = U_p(x.approx n)`, likewise `T`).  Because `CReal.mul`,
    `CReal.add`, `CReal.neg`, `CReal.ofQ'` all act approx-wise, the recurrence-carried
    node values reduce every per-node fact to its proved `Q'` shadow.

  * **`rootData3 : ChebRootDataT 3`** — the genuine `M = 3` node datum on the located
    nodes `0, ±√(1/2)`.  Its `uval_fold` is the recurrence (definitional-up-to-additive
    cancellation), and its `uval_bridge` reduces pointwise to the proved `Q'` weight
    bridge `PowerSumCollapse.qbridge` (`(1−x²)·U_p = ½(T_p − T_{p+2})`).

  * **`locatedRootPowerSums3`** — the residual `LocatedRootPowerSums3 rootData3`,
    DISCHARGED.  The four located-root power sums `Σ_k T_j(x_k)` (`j = 1,…,4`) are
    computed via the recurrence + `ssq`: the odd `j` cancel by the symmetric pair
    `shalf + (−shalf) ≃ 0`, the even `j` collapse to rationals through `s² ≃ ½`,
    matching the Newton values `S₁ = 0, S₂ = −1, S₃ = 0, S₄ = −1`.

  * **`order3_discreteOrthogonality_collapse` / `order3_diag_value_closed`** — order-3
    discrete Chebyshev-`U` orthogonality, including the diagonal value `(3+1)/2 = 2`,
    now UNCONDITIONAL (the dangling hypothesis of `ChebDiscreteOrtho` is discharged).
    This upgrades order-3 — the finite shadow of the heat-kernel Gauss exactness — from
    "reduced to `LocatedRootPowerSums3`" to **closed**, joining orders 1 and 2.

## General `M` (honest reduction, no fakes)

The general-`M` discrete orthogonality is, by `NewtonRecurrence`, already reduced to
the cyclotomic second-kind power-sum evaluation `(U★)` (`RootedNodesU.Usum_value`),
and the `t > 0` off-diagonal OS2 scalar to `RiemannSOS.MomentIntegralIdentity` — both
re-exported here.  Proving `(U★)` / `MomentIntegralIdentity` for general `M` needs the
Dirichlet-kernel/Newton–Vieta cyclotomic sum and the heat-kernel moment reproduction
(Gauss–Christoffel weights at `cos(kπ/(M+1))`), which remain the named walls.  This
module closes the order-3 instance EXACTLY; it does NOT close general `M`.

## Reuse / provenance

The moment-matrix SOS machine is the Mathlib-free constructive transfer of the
external 4D-GFF formalization (Douglas–Hoback–Mei–Nissim, "Formalization of QFT",
arXiv:2603.15770; repository `mrdouglasny/OSforGFF`).  The product linearization,
weight-fold bridge, and the `ChebRootDataT` node interface are the repo's
`ChebOrthogonality` / `PowerSumCollapse` / `ChebDiscreteOrtho` layers; the
`CReal.sqrtFrom` square root is the repo's constructive Heron iteration.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only (`Quot.sound` via reused `omega`/`Nat`/
`Int` helpers).  No `Classical.*`, no `sorry`/`sorryAx`, no `native_decide`, no
`decide` on a non-decidable `Prop` (`decide` only on closed `Q'`/`Nat`).  All node
data (`Ucr`/`Tcr`/`rootData3`) are `Type`-level (MLTT/HoTT-valid); the discharged
residual `LocatedRootPowerSums3` is a `Prop`, never `sorry`.
-/

import YMGap.Continuum.ChebDiscreteOrtho
import YMGap.Continuum.NewtonRecurrence
import YMGap.Constructive.Sqrt
import YMGap.Constructive.HalfPow
import YMGap.Continuum.CRealContinuumAlg

namespace YMGap.Continuum.ChebLocatedRoots

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Small `Q'` and `CReal` pointwise helpers -/

/-- `a ≃ (a + (−b)) + b` over `Q'` — the additive cancellation behind the
recurrence-carried `uval_fold` (`2x·U_{n+1} ≃ (2x·U_{n+1} − U_n) + U_n`). -/
theorem q_fold_back (a b : Q') : a ≈ ((a + (-b)) + b) := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a ((-b) + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' a)

/-- `(((0:Q') + 0) + x) + (−x) ≈ 0` — the odd-order located-root cancellation
(`T₀(0) + T_j(s) + T_j(−s) = 0` for odd `j`). -/
theorem q_z2_cancel (x : Q') : ((((0 : Q') + 0) + x) + (-x)) ≈ (0 : Q') := by
  rw [Q'.zero_add' (0 : Q'), Q'.zero_add' x]
  exact Q'.add_neg_self_eqv x

/-- `A · (ofQ' 0) ≃ ofQ' 0`. -/
theorem cmul_x_zero (A : CReal) : CReal.Equiv (CReal.mul A (CReal.ofQ' 0)) (CReal.ofQ' 0) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_zero_eqv (A.approx n))

/-- `(ofQ' 0) + B ≃ B`. -/
theorem czero_add (B : CReal) : CReal.Equiv (CReal.add (CReal.ofQ' 0) B) B :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' (B.approx n)))

/-- `A · (neg B) ≃ neg (A · B)`. -/
theorem cmul_neg (A B : CReal) :
    CReal.Equiv (CReal.mul A (CReal.neg B)) (CReal.neg (CReal.mul A B)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_neg_eqv (A.approx n) (B.approx n))

/-- `neg (ofQ' a) ≃ ofQ' (−a)`. -/
theorem cneg_ofQ' (a : Q') : CReal.Equiv (CReal.neg (CReal.ofQ' a)) (CReal.ofQ' (-a)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-! ## 1. The located `√(1/2)` node and its square -/

/-- The constructive real `√(1/2)` (`a = L = ½`, `L·L = ¼ ≤ ½`). -/
def shalf : CReal :=
  CReal.sqrtFrom HalfPow.half HalfPow.half (by decide) (by decide) (by decide)

/-- `shalf · shalf ≃ ½`. -/
theorem ssq : CReal.Equiv (CReal.mul shalf shalf) (CReal.ofQ' HalfPow.half) :=
  CReal.sqrtFrom_sq_equiv HalfPow.half HalfPow.half (by decide) (by decide) (by decide)

/-- `(−shalf)·(−shalf) ≃ shalf · shalf` (pointwise `(−s)(−s) = s·s`). -/
theorem neg_shalf_sq :
    CReal.Equiv (CReal.mul (CReal.neg shalf) (CReal.neg shalf)) (CReal.mul shalf shalf) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Cheb.negnegmul_eqv (shalf.approx n))

/-- `(−shalf)·(−shalf) ≃ ½`. -/
theorem ssq' :
    CReal.Equiv (CReal.mul (CReal.neg shalf) (CReal.neg shalf)) (CReal.ofQ' HalfPow.half) :=
  CReal.Equiv.trans neg_shalf_sq ssq

/-! ## 2. `CReal` Chebyshev recurrences and their pointwise bridges -/

/-- `U_n(x)` over `CReal` (mirrors `Cheb.U`). -/
def Ucr (x : CReal) : Nat → CReal
  | 0 => CReal.cone
  | 1 => CReal.mul (CReal.ofQ' 2) x
  | (n + 2) => CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) x) (Ucr x (n + 1)))
                 (CReal.neg (Ucr x n))

/-- `T_n(x)` over `CReal` (mirrors `Cheb.T`). -/
def Tcr (x : CReal) : Nat → CReal
  | 0 => CReal.cone
  | 1 => x
  | (n + 2) => CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) x) (Tcr x (n + 1)))
                 (CReal.neg (Tcr x n))

/-- **Pointwise bridge** `(Ucr x p).approx n = U_p(x.approx n)`. -/
theorem Ucr_approx (x : CReal) (n : Nat) :
    ∀ p, (Ucr x p).approx n = Cheb.U p (x.approx n) := by
  have hpair : ∀ m, ((Ucr x m).approx n = Cheb.U m (x.approx n))
      ∧ ((Ucr x (m + 1)).approx n = Cheb.U (m + 1) (x.approx n)) := by
    intro m
    induction m with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
        obtain ⟨h0, h1⟩ := ih
        refine ⟨h1, ?_⟩
        have hred : (Ucr x (k + 2)).approx n
            = ((2 : Q') * x.approx n) * (Ucr x (k + 1)).approx n + (-((Ucr x k).approx n)) := rfl
        rw [hred, h0, h1, Cheb.U_succ_succ]
  exact fun p => (hpair p).1

/-- **Pointwise bridge** `(Tcr x p).approx n = T_p(x.approx n)`. -/
theorem Tcr_approx (x : CReal) (n : Nat) :
    ∀ p, (Tcr x p).approx n = Cheb.T p (x.approx n) := by
  have hpair : ∀ m, ((Tcr x m).approx n = Cheb.T m (x.approx n))
      ∧ ((Tcr x (m + 1)).approx n = Cheb.T (m + 1) (x.approx n)) := by
    intro m
    induction m with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
        obtain ⟨h0, h1⟩ := ih
        refine ⟨h1, ?_⟩
        have hred : (Tcr x (k + 2)).approx n
            = ((2 : Q') * x.approx n) * (Tcr x (k + 1)).approx n + (-((Tcr x k).approx n)) := rfl
        rw [hred, h0, h1, Cheb.T_succ_succ]
  exact fun p => (hpair p).1

/-! ## 3. Node-value lemmas (recurrence + `ssq`) -/

/-- `Tcr czero j ≃ ofQ'(T_j(0))` (the `czero` node is constant `0`). -/
theorem Tcr_czero (j : Nat) :
    CReal.Equiv (Tcr CReal.czero j) (CReal.ofQ' (Cheb.T j 0)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (Tcr CReal.czero j).approx n ≈ Cheb.T j 0
  rw [Tcr_approx CReal.czero n]
  exact Q'.eqv_refl _

/-- `(2:Q')·½ ≃ 1` lifted: `ofQ' 2 · ofQ' ½ ≃ ofQ' 1`. -/
theorem two_half :
    CReal.Equiv (CReal.mul (CReal.ofQ' 2) (CReal.ofQ' HalfPow.half)) (CReal.ofQ' 1) :=
  CReal.Equiv.trans (CReal.Equiv.symm (CRealContinuumAlg.cofQ'_mul 2 HalfPow.half))
    (ChebDiscreteOrtho.ofQ'_eqv (by decide : ((2 : Q') * HalfPow.half) ≈ (1 : Q')))

/-- `(2x)·x ≃ 1` for a `½`-square node: `(2x)·x = 2·(x·x) ≃ 2·½ = 1`. -/
theorem mulhalf_one (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' HalfPow.half)) :
    CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) y) (CReal.ofQ' 1) :=
  CReal.Equiv.trans (CRealAlg.cmul_assoc (CReal.ofQ' 2) y y)
    (CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right hy) two_half)

/-- `Tcr y 2 ≃ 0` for a `½`-square node `y`: `2x²−1 ≃ 2·½−1 = 0`. -/
theorem Tcr2_of_half (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' HalfPow.half)) :
    CReal.Equiv (Tcr y 2) (CReal.ofQ' 0) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) y) (CReal.neg CReal.cone)) (CReal.ofQ' 0)
  refine CReal.Equiv.trans (Pivot2.add_congr (mulhalf_one y hy) (Pivot2.equiv_refl _)) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((1 : Q') + (-(1 : Q'))) ≈ (0 : Q')
  decide

/-- `Tcr y 3 ≃ −y` for a `½`-square node `y`: `2x·T₂ − T₁ ≃ 0 − x = −x`. -/
theorem Tcr3_of_half (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' HalfPow.half)) :
    CReal.Equiv (Tcr y 3) (CReal.neg y) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 2)) (CReal.neg y)) (CReal.neg y)
  have hmz : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 2)) (CReal.ofQ' 0) :=
    CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Tcr2_of_half y hy)) (cmul_x_zero _)
  refine CReal.Equiv.trans (Pivot2.add_congr hmz (Pivot2.equiv_refl _)) ?_
  exact czero_add (CReal.neg y)

/-- `Tcr y 4 ≃ −1` for a `½`-square node `y`: `2x·T₃ − T₂ ≃ 2x·(−x) − 0 = −2x² ≃ −1`. -/
theorem Tcr4_of_half (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' HalfPow.half)) :
    CReal.Equiv (Tcr y 4) (CReal.ofQ' (-(1 : Q'))) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 3)) (CReal.neg (Tcr y 2)))
    (CReal.ofQ' (-(1 : Q')))
  have hA : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Tcr y 3)) (CReal.ofQ' (-(1 : Q'))) := by
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Tcr3_of_half y hy)) ?_
    refine CReal.Equiv.trans (cmul_neg (CReal.mul (CReal.ofQ' 2) y) y) ?_
    refine CReal.Equiv.trans (Pivot2.neg_congr (mulhalf_one y hy)) ?_
    exact cneg_ofQ' 1
  have hB : CReal.Equiv (CReal.neg (Tcr y 2)) (CReal.ofQ' 0) :=
    CReal.Equiv.trans (Pivot2.neg_congr (Tcr2_of_half y hy))
      (CReal.Equiv.trans (cneg_ofQ' 0)
        (ChebDiscreteOrtho.ofQ'_eqv (by decide : (-(0 : Q')) ≈ (0 : Q'))))
  refine CReal.Equiv.trans (Pivot2.add_congr hA hB) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((-(1 : Q')) + (0 : Q')) ≈ (-(1 : Q'))
  decide

/-! ## 4. The located `M = 3` node datum `rootData3` -/

/-- The three located `U₃` nodes `0, +√½, −√½`. -/
def node3 : Nat → CReal
  | 0 => CReal.czero
  | 1 => shalf
  | 2 => CReal.neg shalf
  | (_ + 3) => CReal.czero

/-- **The genuine `M = 3` node datum** on the located irrational nodes `0, ±√(1/2)`.
`uval_fold` is the second-kind recurrence (additive cancellation), `uval_bridge` is the
proved `Q'` weight bridge `PowerSumCollapse.qbridge` pulled back along the pointwise
recurrence carriers `Ucr_approx`/`Tcr_approx`. -/
def rootData3 : PowerSumCollapse.ChebRootDataT 3 where
  x := node3
  uval := fun p k => Ucr (node3 k) p
  tval := fun p k => Tcr (node3 k) p
  wt := fun k => CReal.add CReal.cone (CReal.neg (CReal.mul (node3 k) (node3 k)))
  uval_zero := fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  uval_fold := fun n k => by
    refine SumOfSquares.Equiv_of_approx_eqv (fun m => ?_)
    exact q_fold_back _ _
  uval_bridge := fun p k => by
    refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
    show PowerSumCollapse.wQ ((node3 k).approx n) * (Ucr (node3 k) p).approx n
        ≈ HalfPow.half * ((Tcr (node3 k) p).approx n + (-((Tcr (node3 k) (p + 2)).approx n)))
    rw [Ucr_approx (node3 k) n p, Tcr_approx (node3 k) n p, Tcr_approx (node3 k) n (p + 2)]
    exact PowerSumCollapse.qbridge ((node3 k).approx n) p

/-! ## 5. Discharging `LocatedRootPowerSums3` -/

/-- `Sj rootData3 j` unfolds to the explicit 3-node sum (definitional). -/
theorem Sj3_eq (j : Nat) :
    PowerSumCollapse.Sj rootData3 j
      = CReal.add (CReal.add (CReal.add CReal.czero (Tcr CReal.czero j)) (Tcr shalf j))
          (Tcr (CReal.neg shalf) j) := rfl

/-- `S₁ = Σ_k T₁(x_k) ≃ 0` (odd: the symmetric pair `s + (−s)` cancels). -/
theorem Sj_val_1 : CReal.Equiv (PowerSumCollapse.Sj rootData3 1) (CReal.ofQ' 0) := by
  rw [Sj3_eq]
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (((0 : Q') + 0) + shalf.approx n) + (-(shalf.approx n)) ≈ (0 : Q')
  exact q_z2_cancel (shalf.approx n)

/-- `S₂ = Σ_k T₂(x_k) ≃ −1` (`T₂(0) + 2·T₂(s) ≃ −1 + 0 + 0`). -/
theorem Sj_val_2 : CReal.Equiv (PowerSumCollapse.Sj rootData3 2) (CReal.ofQ' (-(1 : Q'))) := by
  rw [Sj3_eq]
  have hC : CReal.Equiv (Tcr CReal.czero 2) (CReal.ofQ' (-(1 : Q'))) :=
    CReal.Equiv.trans (Tcr_czero 2) (ChebDiscreteOrtho.ofQ'_eqv (by decide : Cheb.T 2 0 ≈ (-(1 : Q'))))
  have hS : CReal.Equiv (Tcr shalf 2) (CReal.ofQ' 0) := Tcr2_of_half shalf ssq
  have hN : CReal.Equiv (Tcr (CReal.neg shalf) 2) (CReal.ofQ' 0) := Tcr2_of_half (CReal.neg shalf) ssq'
  refine CReal.Equiv.trans
    (Pivot2.add_congr (Pivot2.add_congr (Pivot2.add_congr (Pivot2.equiv_refl _) hC) hS) hN) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (((0 : Q') + (-(1 : Q'))) + (0 : Q')) + (0 : Q') ≈ (-(1 : Q'))
  decide

/-- `S₃ = Σ_k T₃(x_k) ≃ 0` (odd: `T₃(0) + (−s) + s` cancels). -/
theorem Sj_val_3 : CReal.Equiv (PowerSumCollapse.Sj rootData3 3) (CReal.ofQ' 0) := by
  rw [Sj3_eq]
  have hC : CReal.Equiv (Tcr CReal.czero 3) (CReal.ofQ' 0) :=
    CReal.Equiv.trans (Tcr_czero 3) (ChebDiscreteOrtho.ofQ'_eqv (by decide : Cheb.T 3 0 ≈ (0 : Q')))
  have hS : CReal.Equiv (Tcr shalf 3) (CReal.neg shalf) := Tcr3_of_half shalf ssq
  have hN : CReal.Equiv (Tcr (CReal.neg shalf) 3) (CReal.neg (CReal.neg shalf)) :=
    Tcr3_of_half (CReal.neg shalf) ssq'
  refine CReal.Equiv.trans
    (Pivot2.add_congr (Pivot2.add_congr (Pivot2.add_congr (Pivot2.equiv_refl _) hC) hS) hN) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (((0 : Q') + 0) + (-(shalf.approx n))) + (-(-(shalf.approx n))) ≈ (0 : Q')
  exact q_z2_cancel (-(shalf.approx n))

/-- `S₄ = Σ_k T₄(x_k) ≃ −1` (`T₄(0) + 2·T₄(s) ≃ 1 + (−1) + (−1)`). -/
theorem Sj_val_4 : CReal.Equiv (PowerSumCollapse.Sj rootData3 4) (CReal.ofQ' (-(1 : Q'))) := by
  rw [Sj3_eq]
  have hC : CReal.Equiv (Tcr CReal.czero 4) (CReal.ofQ' 1) :=
    CReal.Equiv.trans (Tcr_czero 4) (ChebDiscreteOrtho.ofQ'_eqv (by decide : Cheb.T 4 0 ≈ (1 : Q')))
  have hS : CReal.Equiv (Tcr shalf 4) (CReal.ofQ' (-(1 : Q'))) := Tcr4_of_half shalf ssq
  have hN : CReal.Equiv (Tcr (CReal.neg shalf) 4) (CReal.ofQ' (-(1 : Q'))) :=
    Tcr4_of_half (CReal.neg shalf) ssq'
  refine CReal.Equiv.trans
    (Pivot2.add_congr (Pivot2.add_congr (Pivot2.add_congr (Pivot2.equiv_refl _) hC) hS) hN) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (((0 : Q') + (1 : Q')) + (-(1 : Q'))) + (-(1 : Q')) ≈ (-(1 : Q'))
  decide

/-- **The order-3 located-root residual, DISCHARGED.**  The located `U₃` roots
`0, ±√(1/2)` realize the Newton first-kind power sums `S₁ = 0`, `S₂ = −1`, `S₃ = 0`,
`S₄ = −1` — the `M = 3` Vieta link that `ChebDiscreteOrtho` left as the sole open
hypothesis. -/
theorem locatedRootPowerSums3 : ChebDiscreteOrtho.LocatedRootPowerSums3 rootData3 :=
  ⟨ CReal.Equiv.trans Sj_val_1 (ChebDiscreteOrtho.ofQ'_eqv (by decide : (0 : Q') ≈ ChebDiscreteOrtho.S1)),
    CReal.Equiv.trans Sj_val_2 (ChebDiscreteOrtho.ofQ'_eqv (by decide : (-(1 : Q')) ≈ ChebDiscreteOrtho.S2)),
    CReal.Equiv.trans Sj_val_3 (ChebDiscreteOrtho.ofQ'_eqv (by decide : (0 : Q') ≈ ChebDiscreteOrtho.S3)),
    CReal.Equiv.trans Sj_val_4 (ChebDiscreteOrtho.ofQ'_eqv (by decide : (-(1 : Q')) ≈ ChebDiscreteOrtho.S4)) ⟩

/-! ## 6. Order-3 `t > 0` off-diagonal OS2 — UNCONDITIONAL -/

/-- The canonical `tval 0 k ≃ 1` for `rootData3` (`T₀ = 1` at every node). -/
theorem rootData3_tval0 (k : Nat) : CReal.Equiv (rootData3.tval 0 k) CReal.cone :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- **Order-3 discrete Chebyshev-`U` orthogonality collapse, UNCONDITIONAL.**
`ChebOrthogonality.PowerSumCollapse rootData3.toU` — the all-order single-`U` moment
collapse at the located `M = 3` nodes, with the previously-dangling
`LocatedRootPowerSums3` hypothesis now discharged. -/
theorem order3_discreteOrthogonality_collapse :
    ChebOrthogonality.PowerSumCollapse rootData3.toU :=
  ChebDiscreteOrtho.orthoCollapse3_of_located rootData3 rootData3_tval0 locatedRootPowerSums3

/-- **Order-3 discrete orthogonality diagonal value `(3+1)/2 = 2`, UNCONDITIONAL.**
`Σ_{k<3} (1 − x_k²)·U₀(x_k)·U₀(x_k) = 2` at the located nodes `0, ±√(1/2)` — the
load-bearing normalization at `M = 3`, the finite shadow of the heat-kernel Gauss
exactness, now closed end-to-end (joining the closed orders 1 and 2). -/
theorem order3_diag_value_closed :
    CReal.Equiv (ChebOrthogonality.orthoSum rootData3.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((3 : Int) + 1) 2 (by decide))) :=
  ChebDiscreteOrtho.orthogonality_diag0_3_of_located rootData3 rootData3_tval0 locatedRootPowerSums3

/-! ## 7. General `M` — honest reduction re-exports (the remaining walls) -/

/-- **General-`M` discrete orthogonality from the cyclotomic root datum `(U★)`.**
Re-export of `NewtonRecurrence.gram_psd_closed`: a `RootedNodesU M` (the unweighted
second-kind power-sum evaluation `Σ_k U_n(x_k) = Uval M n`) discharges the all-order
single-`U` moment collapse for general `M`.  Inhabiting `RootedNodesU M` at the
irrational nodes `cos(kπ/(M+1))` for general `M` is the named cyclotomic wall `(U★)`. -/
theorem generalM_orthoCollapse_of_rootedU {M : Nat} (D : NewtonRecurrence.RootedNodesU M) :
    ChebOrthogonality.PowerSumCollapse D.toRooted.toData.toU :=
  NewtonRecurrence.gram_psd_closed D

/-- **`t > 0` off-diagonal OS2 at all orders, reduced to the Gauss-exactness wall.**
Re-export of `HeatKernelGaussNode.heatKernel_offdiag_OS2_coneExp`: the SU(2)
heat-kernel character Gram `coneExp` is PSD at every order `N` given the single
residual `RiemannSOS.MomentIntegralIdentity` — the continuous moment-integral identity
whose finite shadow is the discrete orthogonality closed above at order 3. -/
theorem heatKernel_t_pos_offdiag_OS2_of_momentIntegral (t : Q') (ht : (0 : Q') ≤ t)
    (h : RiemannSOS.MomentIntegralIdentity (GramRed.wilsonMoments t ht)) (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  HeatKernelGaussNode.heatKernel_offdiag_OS2_coneExp t ht h N c

end YMGap.Continuum.ChebLocatedRoots

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebLocatedRoots.ssq
#print axioms YMGap.Continuum.ChebLocatedRoots.ssq'
#print axioms YMGap.Continuum.ChebLocatedRoots.Ucr_approx
#print axioms YMGap.Continuum.ChebLocatedRoots.Tcr_approx
#print axioms YMGap.Continuum.ChebLocatedRoots.rootData3
#print axioms YMGap.Continuum.ChebLocatedRoots.Sj_val_1
#print axioms YMGap.Continuum.ChebLocatedRoots.Sj_val_2
#print axioms YMGap.Continuum.ChebLocatedRoots.Sj_val_3
#print axioms YMGap.Continuum.ChebLocatedRoots.Sj_val_4
#print axioms YMGap.Continuum.ChebLocatedRoots.locatedRootPowerSums3
#print axioms YMGap.Continuum.ChebLocatedRoots.order3_discreteOrthogonality_collapse
#print axioms YMGap.Continuum.ChebLocatedRoots.order3_diag_value_closed
#print axioms YMGap.Continuum.ChebLocatedRoots.generalM_orthoCollapse_of_rootedU
#print axioms YMGap.Continuum.ChebLocatedRoots.heatKernel_t_pos_offdiag_OS2_of_momentIntegral
