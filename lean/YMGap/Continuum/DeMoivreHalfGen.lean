/-
# Closing the located branch collapse (Lead 1) and the uniform-in-`M` de Moivre half

This module discharges the sole *elementary* residual of the uniform-in-`M` de Moivre
chain — `ChebLocatedNodesGen.LocatedBranchCollapse` — as a genuine theorem, and uses it to
make `DeMoivreHalf M x` uniform in `M` modulo only the per-`M` located bracket datum
(the standing rational-π-enclosure wall).

## What is proved here (Lead 1, fully elementary)

  * **`Q'.half_factor_squeeze`** — the one new `Q'` sign-squeeze:
    `½ ≤ c`, `c·w ≈ s`, `|s| ≤ tol` ⟹ `|w| ≤ tol + tol`.  Two-sided case split on the
    sign of `w`; no `abs_mul`, no division.
  * **`locatedBranchCollapse`** — `LocatedBranchCollapse` PROVED:
    `a² ≈ 1 ∧ a ≤ 0 ⟹ a ≈ −1`.  Routes through `Equiv_of_sub_eqv_zero`,
    `eqv_zero_of_abs_le_all_pos`, `leRat_of_eventually`, the factorization
    `1 + −a² ≈ (1 + −a)(1 + a)` (`ChebRoot.sq_diff_eqv`), and the squeeze above.
  * **`deMoivreHalf_uniform`** — `deMoivreHalf_of_root_sign` with its
    `LocatedBranchCollapse` hypothesis discharged: for ALL `M` and `x`, a `U_M`-root
    (`root`) plus a co-located branch sign (`sign : T_{M+1}(x) ≤ 0`) give `DeMoivreHalf M x`.

## What remains (Lead 2, the honest residual — NOT closed here)

The general-`M` located bracket datum is packaged as the `Type`-level residual
`LocatedNodeData M` (a node `x` with the `U_M`-root and the branch sign).  Inhabiting it for
general `M` is exactly the rational enclosure of `cos(π/(M+1))` — the standing π wall; it is
free only at the surd-collapse orders.  `deMoivreNode_of_located` shows this residual is now
the *whole* gap: it yields a fully inhabited `DeMoivreNode M` (with the branch collapse
proved), hence general-`M` off-diagonal OS2 Gram positivity downstream.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`, no
`native_decide`, no custom axiom.  `decide` only on closed `Q'` facts.  `LocatedNodeData`
is `Type`-level; `LocatedBranchCollapse`/`DeMoivreHalf` are `Prop`s, never `sorry`.
-/

import YMGap.Continuum.ChebLocatedNodesGen
import YMGap.Continuum.ChebRoot
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealLe
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.DeMoivreHalfGen

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebLocatedRoots (Ucr Tcr)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The `Q'` sign-squeeze (the one new elementary lemma) -/

/-- **The half-factor squeeze.**  If `½ ≤ c`, `c·w ≈ s`, and `|s| ≤ tol`, then
`|w| ≤ tol + tol`.  Proof by a two-sided case split on the sign of `w`, each branch a single
`mul_le_mul_of_nonneg_right` monotonicity step against `½ ≤ c` followed by `Q'.abs_le`.  No
`abs_mul` (deliberately absent), no division. -/
theorem Q'.half_factor_squeeze {c w s tol : Q'}
    (hc : HalfPow.half ≤ c) (heq : (c * w) ≈ s)
    (habs : Q'.abs s ≤ tol) : Q'.abs w ≤ tol + tol := by
  have htol0 : (0 : Q') ≤ tol :=
    Q'.le_trans' 0 (Q'.abs s) tol (Q'.abs_nonneg s) habs
  have hs_le : s ≤ tol := Q'.le_trans' s (Q'.abs s) tol (Q'.le_abs_self s) habs
  have hs_ge : -tol ≤ s := by
    have h1 : -s ≤ tol := Q'.le_trans' (-s) (Q'.abs s) tol (Q'.neg_le_abs s) habs
    have h2 : -tol ≤ -(-s) := Q'.neg_le_neg h1
    exact Q'.le_trans' (-tol) (-(-s)) s h2 (Q'.le_of_eqv (Q'.neg_neg_eqv s))
  have hcw_le : c * w ≤ tol := Q'.le_trans' (c * w) s tol (Q'.le_of_eqv heq) hs_le
  have hcw_ge : -tol ≤ c * w := Q'.le_trans' (-tol) s (c * w) hs_ge (Q'.ge_of_eqv heq)
  have htoltol0 : (0 : Q') ≤ tol + tol := Q'.zero_le_add tol tol htol0 htol0
  by_cases hw : (0 : Q') ≤ w
  · -- `w ≥ 0`: `½·w ≤ c·w ≤ tol`, double to `w ≤ tol + tol`.
    have hmul : HalfPow.half * w ≤ c * w :=
      Q'.mul_le_mul_of_nonneg_right HalfPow.half c w hc hw
    have hhalf : HalfPow.half * w ≤ tol := Q'.le_trans' _ _ _ hmul hcw_le
    have hsum : HalfPow.half * w + HalfPow.half * w ≤ tol + tol :=
      Q'.add_le_add hhalf hhalf
    have hw_le : w ≤ tol + tol :=
      Q'.le_trans' w (HalfPow.half * w + HalfPow.half * w) (tol + tol)
        (Q'.ge_of_eqv (ExpNeg.two_halves w)) hsum
    have hw_ge : -(tol + tol) ≤ w := by
      have h0 : -(tol + tol) ≤ -(0 : Q') := Q'.neg_le_neg htoltol0
      exact Q'.le_trans' (-(tol + tol)) 0 w h0 hw
    exact Q'.abs_le hw_ge hw_le
  · -- `w < 0`: `½·(−w) ≤ c·(−w) = −(c·w) ≤ tol`, double to `−w ≤ tol + tol`.
    have hnw : (0 : Q') ≤ -w := Q'.neg_nonneg_of_not_nonneg hw
    have hmul : HalfPow.half * (-w) ≤ c * (-w) :=
      Q'.mul_le_mul_of_nonneg_right HalfPow.half c (-w) hc hnw
    have hcnw_le : c * (-w) ≤ tol := by
      have e : (c * (-w)) ≈ (-(c * w)) := Q'.mul_neg_eqv c w
      have hneg : -(c * w) ≤ tol := by
        have hn := Q'.neg_le_neg hcw_ge   -- -(c*w) ≤ -(-tol)
        exact Q'.le_trans' (-(c * w)) (-(-tol)) tol hn (Q'.le_of_eqv (Q'.neg_neg_eqv tol))
      exact Q'.le_trans' (c * (-w)) (-(c * w)) tol (Q'.le_of_eqv e) hneg
    have hhalf : HalfPow.half * (-w) ≤ tol := Q'.le_trans' _ _ _ hmul hcnw_le
    have hsum : HalfPow.half * (-w) + HalfPow.half * (-w) ≤ tol + tol :=
      Q'.add_le_add hhalf hhalf
    have hnw_le : -w ≤ tol + tol :=
      Q'.le_trans' (-w) (HalfPow.half * (-w) + HalfPow.half * (-w)) (tol + tol)
        (Q'.ge_of_eqv (ExpNeg.two_halves (-w))) hsum
    have hw_ge : -(tol + tol) ≤ w := by
      have h1 : -(tol + tol) ≤ -(-w) := Q'.neg_le_neg hnw_le
      exact Q'.le_trans' (-(tol + tol)) (-(-w)) w h1 (Q'.le_of_eqv (Q'.neg_neg_eqv w))
    have hw_le : w ≤ tol + tol :=
      Q'.le_trans' w 0 (tol + tol) (Q'.nonpos_of_not_nonneg hw) htoltol0
    exact Q'.abs_le hw_ge hw_le

/-! ## 2. `LocatedBranchCollapse` proved -/

/-- **The located branch collapse, PROVED.**  `a² ≈ 1` and `a ≤ 0` force `a ≈ −1`.

Top-level: `Equiv_of_sub_eqv_zero` reduces `Equiv a (ofQ' (−1))` to
`Equiv (a + −(ofQ' −1)) 0`, discharged by `eqv_zero_of_abs_le_all_pos` via the eventual
pointwise bound `|aₙ + 1| ≤ ε`.  Pointwise: with `c = 1 + −aₙ` (`≥ ½` from `a ≤ 0`),
`w = aₙ + 1`, `s = 1 + −aₙ²` (`|s| ≤ tol` from `a² ≈ 1`), the factorization
`(1 + −aₙ)(1 + aₙ) ≈ 1 + −aₙ²` and `Q'.half_factor_squeeze` give `|aₙ + 1| ≤ tol + tol`. -/
theorem locatedBranchCollapse : ChebLocatedNodesGen.LocatedBranchCollapse := by
  intro a hsq ha
  refine CReal.Equiv_of_sub_eqv_zero ?_
  refine CReal.eqv_zero_of_abs_le_all_pos ?_
  intro ε hε
  refine CReal.leRat_of_eventually ?_
  let tol : Q' := HalfPow.half * ε
  have htol_pos : (0 : Q') < tol := ExpNeg.half_mul_pos ε hε
  obtain ⟨N₁, hN₁⟩ := hsq tol htol_pos
  refine ⟨max 1 N₁, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnN₁ : N₁ ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  let an : Q' := a.approx n
  -- Sign bound: `aₙ ≤ ½`, hence `½ ≤ 1 + −aₙ`.
  have han_half : an ≤ HalfPow.half := by
    have h2 : CReal.czero.approx n + Q'.invSucc n ≤ HalfPow.half := by
      show (0 : Q') + Q'.invSucc n ≤ HalfPow.half
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_of_eq' (Q'.zero_add' (Q'.invSucc n)))) ?_
      refine Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn1) ?_
      decide
    exact Q'.le_trans' an (CReal.czero.approx n + Q'.invSucc n) HalfPow.half (ha n) h2
  have hc : HalfPow.half ≤ 1 + -an :=
    Q'.le_trans' HalfPow.half (1 + -HalfPow.half) (1 + -an)
      (by decide)
      (Q'.add_le_add_left 1 (-HalfPow.half) (-an) (Q'.neg_le_neg han_half))
  -- Square bounds from `a² ≈ 1` at tolerance `tol`.
  have hb1 : an * an ≤ 1 + tol := (hN₁ n hnN₁).1
  have hb2 : (1 : Q') ≤ an * an + tol := (hN₁ n hnN₁).2
  -- `s := 1 + −aₙ²`; `|s| ≤ tol`.
  have hs_le : (1 + -(an * an)) ≤ tol := by
    refine Q'.le_trans' (1 + -(an * an)) ((an * an + tol) + -(an * an)) tol
      (Q'.add_le_add_right 1 (an * an + tol) (-(an * an)) hb2) ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (an * an + tol) (tol + an * an) (-(an * an))
        (Q'.add_comm_eqv (an * an) tol)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv tol (an * an) (-(an * an))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left tol (an * an + -(an * an)) 0 (Q'.add_neg_self_eqv (an * an))) ?_
    exact Q'.eqv_of_eq' (Q'.add_zero' tol)
  have hs_ge : -tol ≤ (1 + -(an * an)) := by
    have e_neg : (1 + -(1 + tol)) ≈ (-tol) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 1 (-(1 + tol)) ((-1) + -tol) (Q'.neg_add_eqv 1 tol)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) (-tol))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (1 + -1) 0 (-tol) (Q'.add_neg_self_eqv 1)) ?_
      exact Q'.eqv_of_eq' (Q'.zero_add' (-tol))
    refine Q'.le_trans' (-tol) (1 + -(1 + tol)) (1 + -(an * an)) (Q'.ge_of_eqv e_neg) ?_
    exact Q'.add_le_add_left 1 (-(1 + tol)) (-(an * an)) (Q'.neg_le_neg hb1)
  have habs : Q'.abs (1 + -(an * an)) ≤ tol := Q'.abs_le hs_ge hs_le
  -- Factorization `(1 + −aₙ)·(aₙ + 1) ≈ 1 + −aₙ²`, with `w = aₙ + −(−1)`.
  have hfac : ((1 + -an) * (1 + an)) ≈ (1 + -(an * an)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ChebRoot.sq_diff_eqv 1 an)) ?_
    exact Q'.add_eqv_congr_right (1 * 1) 1 (-(an * an)) (Q'.one_mul_eqv 1)
  have hconv : (an + -(-(1 : Q'))) ≈ (1 + an) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left an (-(-(1 : Q'))) 1 (Q'.neg_neg_eqv 1)) ?_
    exact Q'.add_comm_eqv an 1
  have heq : ((1 + -an) * (an + -(-(1 : Q')))) ≈ (1 + -(an * an)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (1 + -an) (an + -(-(1 : Q'))) (1 + an) hconv) hfac
  -- Squeeze: `|aₙ + −(−1)| ≤ tol + tol ≤ ε`.
  have hbound : Q'.abs (an + -(-(1 : Q'))) ≤ tol + tol :=
    Q'.half_factor_squeeze hc heq habs
  show Q'.abs (an + -(-(1 : Q'))) ≤ ε
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (ExpNeg.two_halves ε))

/-! ## 3. Uniform-in-`M` `DeMoivreHalf` and the honest per-`M` residual -/

/-- **`DeMoivreHalf` uniform in `M`.**  `deMoivreHalf_of_root_sign` with its
`LocatedBranchCollapse` hypothesis discharged: for ALL `M` and `x`, a `U_M`-root datum and a
co-located branch sign `T_{M+1}(x) ≤ 0` give `DeMoivreHalf M x`.  No per-`M` assumption on
the branch collapse remains — only the two located bracket inputs. -/
theorem deMoivreHalf_uniform (x : CReal) (M : Nat)
    (root : CReal.Equiv (Ucr x M) (CReal.ofQ' 0))
    (sign : Tcr x (M + 1) ≤ CReal.czero) :
    ChebRotationPair.DeMoivreHalf M x :=
  ChebLocatedNodesGen.deMoivreHalf_of_root_sign locatedBranchCollapse x M root sign

/-- **The honest per-`M` residual** (`Type`-level, MLTT/HoTT-valid): a located node `x` with
the `U_M`-root fact and the co-located branch sign.  Inhabiting `LocatedNodeData M` for
general `M` is exactly the rational enclosure of `cos(π/(M+1))` — the standing π wall (free
only at the surd-collapse orders).  This is now the WHOLE residual: the branch collapse is
proved. -/
structure LocatedNodeData (M : Nat) where
  /-- The candidate node `x = cos(π/(M+1))`. -/
  x : CReal
  /-- `U_M(x) ≈ 0` — `x` is the located `U_M`-node. -/
  root : CReal.Equiv (Ucr x M) (CReal.ofQ' 0)
  /-- `T_{M+1}(x) ≤ 0` — the co-located branch sign. -/
  sign : Tcr x (M + 1) ≤ CReal.czero

/-- **From the per-`M` located datum to a fully inhabited `DeMoivreNode M`.**  With
`locatedBranchCollapse` proved, the sole remaining input is `LocatedNodeData M`; it yields
the full de Moivre node (root + branch sign `T_{M+1}(x) ≈ −1`), hence general-`M`
off-diagonal OS2 Gram positivity downstream. -/
def deMoivreNode_of_located (M : Nat) (d : LocatedNodeData M) :
    ChebRotationPair.DeMoivreNode M where
  x := d.x
  root := d.root
  half := deMoivreHalf_uniform d.x M d.root d.sign

end YMGap.Continuum.DeMoivreHalfGen

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DeMoivreHalfGen.Q'.half_factor_squeeze
#print axioms YMGap.Continuum.DeMoivreHalfGen.locatedBranchCollapse
#print axioms YMGap.Continuum.DeMoivreHalfGen.deMoivreHalf_uniform
#print axioms YMGap.Continuum.DeMoivreHalfGen.deMoivreNode_of_located
