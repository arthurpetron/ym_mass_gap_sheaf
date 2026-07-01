/-
# The de Moivre rotation node `DeMoivreNode M` — the correct uniform-in-`M` primitive
# root datum, replacing the uninhabitable scalar `UnitRootPair`

`ChebUniformOrtho.UnitRootPair M` carries a SINGLE scalar `z : Q'` with `z^{M+1} ≈ −1`
and `z^{2(M+1)} ≈ 1`.  For the geometry it is meant to encode — the primitive rotation
`e^{iπ/(M+1)}` — a single scalar cannot work: this module proves the clean uniform no-go

  * **`no_unitRootPair_odd`** — for every odd `M = 2t+1` the interface `UnitRootPair M`
    is UNINHABITABLE.  If `z^{M+1} ≈ −1` with `M+1 = 2s` even, then
    `z^{2s} ≈ (z^s)·(z^s) ≥ 0`, forcing `0 ≤ −1`, absurd.  (For even `M` the only scalar
    witness is the degenerate `z = −1`, i.e. the node `(z+w)/2 = −1`, NOT a genuine
    `U_M`-node.)  So `UnitRootPair` is the wrong interface: the primitive root is genuinely
    two-dimensional and does not live as a scalar in `Q'`.

The correct object is the **de Moivre rotation node** over `CReal`: the rotation by
`θ = π/(M+1)`, represented radical-free through the first-kind Chebyshev trace
`c_k = T_k(cos θ)` and the second-kind `s`-coordinate `s_k = U_{k−1}(cos θ)·sin θ`.  We
package the primitive-root content as

  * **`DeMoivreNode M`** — `Type`-level (MLTT/HoTT-valid): a located node `x = cos θ` with
    the two conditions that survive uniformly,
      - `root : U_M(x) ≈ 0`   (`x` is a `U_M`-node — the half-period `s`-coordinate is 0),
      - `half : T_{M+1}(x) ≈ −1`   (the located BRANCH sign — the sole residual).

## What this module proves (genuine, axiom-clean, π-free)

  * **`half_period_s`** — uniform in `M`: the half-period `s`-coordinate `U_M(x)·y ≈ 0`
    is FREE from `root` (for ANY `y`, the reflection `R^{M+1} = −I` has zero off-part).

  * **`Ucr2_of_half` / `Ucr3_of_half`** — the second-kind node ladder at a `½`-square node,
    the `U`-companions of `ChebLocatedRoots.Tcr{2,3,4}_of_half`.

  * **`deMoivre3`** — the datum `DeMoivreNode 3` FULLY INHABITED at the located node
    `x = √½` (`cos π/4`): `root` from `Ucr3_of_half` (`U_3(√½) = 4√½·(2·½−1) = 0`), `half`
    from `ChebLocatedRoots.Tcr4_of_half` (`T_4(√½) ≈ −1`).  This shows `DeMoivreNode` is
    genuinely inhabitable and its residual `half` is dischargeable (order 3), unlike the
    scalar `UnitRootPair`.

## The sole uniform residual

  * **`DeMoivreHalf M x`** — the named located-branch obligation `T_{M+1}(x) ≈ −1`.  This is
    the ONLY gap in the uniform-in-`M` realization: `root` (`U_M(x) ≈ 0`) is a located
    bisection fact, the half-period `s`-part is free from it, and the roots-of-unity
    `order` condition follows from `half` via `T_{2n} = 2T_n²−1`.  Everything collapses to
    this one `CReal` sign equivalence, strictly smaller and cleaner than the per-`M` surd
    ladders of orders 3/4.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`, no
`native_decide`, no custom axiom.  `decide` only on closed `Q'`/`Nat`.  All node data are
`Type`-level; the residual `DeMoivreHalf` is a `Prop`, never `sorry`.
-/

import YMGap.Continuum.ChebLocatedRoots
import YMGap.Continuum.ChebUniformOrtho

namespace YMGap.Continuum.ChebRotationPair

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebLocatedRoots (Ucr Tcr shalf ssq)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The scalar `UnitRootPair` is uninhabitable for odd `M` -/

/-- **The clean uniform no-go.**  For every odd `M = 2t+1`, `ChebUniformOrtho.UnitRootPair M`
is UNINHABITABLE.  With `M+1 = 2s` even, the half-period relation `z^{2s} ≈ −1` collides with
`z^{2s} ≈ (z^s)·(z^s) ≥ 0`, forcing the absurd `0 ≤ −1`.  This proves the scalar interface is
wrong: no rational scalar realizes the primitive rotation `e^{iπ/(M+1)}` for odd `M`. -/
theorem no_unitRootPair_odd (t : Nat) (P : ChebUniformOrtho.UnitRootPair (2 * t + 1)) : False := by
  -- `M + 1 = 2*(t+1)`
  have hidx : (2 * t + 1) + 1 = 2 * (t + 1) := by omega
  have hhalf : P.z ^ (2 * (t + 1)) ≈ (-(1 : Q')) := by
    have h := P.half
    rw [hidx] at h
    exact h
  -- `z^{2(t+1)} ≈ (z^{t+1})·(z^{t+1})`
  have hsum : P.z ^ (t + 1) * P.z ^ (t + 1) ≈ P.z ^ (2 * (t + 1)) := by
    have hz := OffDiagShift.zpow_add P.z (t + 1) (t + 1)
    have he : (t + 1) + (t + 1) = 2 * (t + 1) := by omega
    rw [he] at hz
    exact hz
  have hnn : (0 : Q') ≤ P.z ^ (t + 1) * P.z ^ (t + 1) :=
    SumOfSquares.q_mul_self_nonneg _
  have hle : P.z ^ (t + 1) * P.z ^ (t + 1) ≤ (-(1 : Q')) :=
    Q'.le_of_eqv (Q'.eqv_trans _ _ _ hsum hhalf)
  have hbad : (0 : Q') ≤ (-(1 : Q')) := Q'.le_trans' _ _ _ hnn hle
  exact absurd hbad (by decide)

/-! ## 2. The de Moivre rotation node and its sole residual -/

/-- **The de Moivre rotation node** (`Type`-level, MLTT/HoTT-valid), uniform in `M`.
`x = cos(π/(M+1))` is a located `U_M`-node (`root`), and the half-period reflection sign is
`T_{M+1}(x) ≈ −1` (`half`).  This is the correct `CReal` primitive-root datum: `root` is a
located bisection fact, and every other primitive-root condition reduces to `half`. -/
structure DeMoivreNode (M : Nat) where
  /-- The located node `x = cos(π/(M+1))`, the largest root of `U_M`. -/
  x : CReal
  /-- `U_M(x) ≈ 0` — `x` is a `U_M`-node; this alone gives the half-period `s`-coordinate `= 0`. -/
  root : CReal.Equiv (Ucr x M) (CReal.ofQ' 0)
  /-- `T_{M+1}(x) ≈ −1` — the located branch sign (the sole residual). -/
  half : CReal.Equiv (Tcr x (M + 1)) (CReal.ofQ' (-(1 : Q')))

/-- **The sole uniform residual** `T_{M+1}(x) ≈ −1` (the located branch-sign obligation). -/
def DeMoivreHalf (M : Nat) (x : CReal) : Prop :=
  CReal.Equiv (Tcr x (M + 1)) (CReal.ofQ' (-(1 : Q')))

/-- **Half-period `s`-coordinate is FREE from `root`** (uniform in `M`, any `y`).  The
reflection `R^{M+1} = −I` has zero off-diagonal part: `s_{M+1} = U_M(x)·y ≈ 0` follows from
`U_M(x) ≈ 0` with no branch information. -/
theorem half_period_s (M : Nat) (x y : CReal)
    (root : CReal.Equiv (Ucr x M) (CReal.ofQ' 0)) :
    CReal.Equiv (CReal.mul (Ucr x M) y) (CReal.ofQ' 0) := by
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_left root) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((0 : Q') * y.approx n) ≈ (0 : Q')
  exact Q'.zero_mul_eqv (y.approx n)

/-! ## 3. The second-kind node ladder at a `½`-square node -/

/-- `Ucr y 2 ≃ 1` for a `½`-square node `y`: `U_2(x) = 4x²−1 ≃ 4·½−1 = 1`. -/
theorem Ucr2_of_half (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' HalfPow.half)) :
    CReal.Equiv (Ucr y 2) (CReal.ofQ' 1) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (CReal.mul (CReal.ofQ' 2) y))
      (CReal.neg CReal.cone)) (CReal.ofQ' 1)
  -- `(2y)·(2y) ≃ 2`
  have haa : CReal.Equiv
      (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (CReal.mul (CReal.ofQ' 2) y)) (CReal.ofQ' 2) := by
    refine CReal.Equiv.trans (CRealAlg.cmul_assoc (CReal.ofQ' 2) y (CReal.mul (CReal.ofQ' 2) y)) ?_
    have hy2 : CReal.Equiv (CReal.mul y (CReal.mul (CReal.ofQ' 2) y)) (CReal.ofQ' 1) :=
      CReal.Equiv.trans (CRealAlg.cmul_comm y (CReal.mul (CReal.ofQ' 2) y))
        (ChebLocatedRoots.mulhalf_one y hy)
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right hy2) ?_
    refine CReal.Equiv.trans (CReal.Equiv.symm (CRealContinuumAlg.cofQ'_mul 2 1)) ?_
    exact ChebDiscreteOrtho.ofQ'_eqv (by decide : ((2 : Q') * 1) ≈ (2 : Q'))
  refine CReal.Equiv.trans (Pivot2.add_congr haa (Pivot2.equiv_refl _)) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((2 : Q') + (-(1 : Q'))) ≈ (1 : Q')
  decide

/-- `Ucr y 3 ≃ 0` for a `½`-square node `y`: `U_3(x) = 2x·U_2 − U_1 ≃ 2x·1 − 2x = 0`. -/
theorem Ucr3_of_half (y : CReal)
    (hy : CReal.Equiv (CReal.mul y y) (CReal.ofQ' HalfPow.half)) :
    CReal.Equiv (Ucr y 3) (CReal.ofQ' 0) := by
  show CReal.Equiv
    (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Ucr y 2)) (CReal.neg (Ucr y 1)))
    (CReal.ofQ' 0)
  have hL : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) y) (Ucr y 2))
      (CReal.mul (CReal.ofQ' 2) y) :=
    CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Ucr2_of_half y hy))
      (CRealAlg.cmul_cone _)
  refine CReal.Equiv.trans (Pivot2.add_congr hL (Pivot2.equiv_refl _)) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((CReal.mul (CReal.ofQ' 2) y).approx n + (-((CReal.mul (CReal.ofQ' 2) y).approx n))) ≈ (0 : Q')
  exact Q'.add_neg_self_eqv _

/-! ## 4. `DeMoivreNode 3` fully inhabited at the located node `√½ = cos π/4` -/

/-- **`DeMoivreNode 3`, FULLY INHABITED** at `x = √½` (`cos π/4`).  `root` is
`U_3(√½) ≈ 0` (`Ucr3_of_half`), `half` is `T_4(√½) ≈ −1` (`ChebLocatedRoots.Tcr4_of_half`).
The residual `half` is discharged: the scalar `UnitRootPair 3` is uninhabitable
(`no_unitRootPair_odd 1`), yet the rotation node exists and closes. -/
def deMoivre3 : DeMoivreNode 3 where
  x := shalf
  root := Ucr3_of_half shalf ssq
  half := ChebLocatedRoots.Tcr4_of_half shalf ssq

/-- The residual `DeMoivreHalf 3 √½` is discharged (the branch sign at order 3). -/
theorem deMoivreHalf3 : DeMoivreHalf 3 shalf :=
  deMoivre3.half

/-- The half-period `s`-coordinate at the order-3 node vanishes (free from `root`). -/
theorem deMoivre3_half_period_s (y : CReal) :
    CReal.Equiv (CReal.mul (Ucr shalf 3) y) (CReal.ofQ' 0) :=
  half_period_s 3 shalf y deMoivre3.root

end YMGap.Continuum.ChebRotationPair

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebRotationPair.no_unitRootPair_odd
#print axioms YMGap.Continuum.ChebRotationPair.half_period_s
#print axioms YMGap.Continuum.ChebRotationPair.Ucr2_of_half
#print axioms YMGap.Continuum.ChebRotationPair.Ucr3_of_half
#print axioms YMGap.Continuum.ChebRotationPair.deMoivre3
#print axioms YMGap.Continuum.ChebRotationPair.deMoivreHalf3
#print axioms YMGap.Continuum.ChebRotationPair.deMoivre3_half_period_s
