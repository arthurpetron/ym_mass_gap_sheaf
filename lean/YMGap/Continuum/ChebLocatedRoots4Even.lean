/-
# Discharging `EvenLocatedPowerSums4` — the located `√5`-quadrature at the `U₄` nodes
# `±(√5±1)/4`, closing order-4 discrete Chebyshev-`U` orthogonality UNCONDITIONALLY

The order-4 file `ChebLocatedRoots4` reduced the whole `M = 4` located-root chain to
the SINGLE named residual `EvenLocatedPowerSums4` — the even first-kind power sums
`S₂ = S₄ = S₆ = S₈ ≃ −1` at the constructed irrational nodes `n1 = (√5+1)/4`,
`n2 = (√5−1)/4` — with the explicit note that, unlike `M = 3` (rational node squares
`s² = ½`), the `U₄` node squares `(3 ± √5)/8` are irrational, so realizing the residual
needs genuine `√5`-located bookkeeping.  This module DISCHARGES that residual.

## What this module proves (genuine, axiom-clean, π-free)

  * **The `ℚ(√5)` normal form `lin p q ≃ p + q·√5`** with its arithmetic:
    `lin_add`, `lin_neg`, `lin_smul`, `lin_congr`, `lin_to_ofQ` are POINTWISE (they
    reduce, at each approximation index, to a `Q'` identity in the free variable
    `√5.approx n`, i.e. they hold for EVERY rational and never touch `sqrt5_sq`), and
    the SINGLE nonlinear multiplication `lin_mul`
    `(p+q√5)(p'+q'√5) ≃ (pp'+5qq') + (pq'+qp')√5` is the ONLY consumer of
    `sqrt5_sq : √5·√5 ≃ 5`.  This is the exact factoring anticipated by the residual:
    three `√5`-atoms (`n1·n1`, `n1·n2`, `n2·n2`), reused across a `√5`-LINEAR ladder.

  * **The `Tcr` value ladder** `Tcr n1 j`, `Tcr n2 j` (`j = 2,…,8`) as explicit
    `lin`-values (the located shadow of `T_j(cos π/5)`, `T_j(cos 2π/5)`), each a small
    step lemma driven by the one recurrence-collapse `tcr_rec_lin` — no monolith.

  * **`Tcr_neg_even`** — the even reflection parity `T_{2m}(−t) ≈ T_{2m}(t)` pulled
    back to the located reals (the even companion of `ChebLocatedRoots4.Tcr_neg_odd`).

  * **`Sj_even_2/4/6/8`** — the four even conjuncts, each folding the two reflected
    nodes onto the base pair and collapsing the ladder to the single `√5`-FREE identity
    `2(n2 − n1) ≃ −1`, matching the rational Newton certificate
    `ChebGeneralOrtho.order4_powerSum_collapse` (`S₂=S₄=S₆=S₈ ≃ −1`).

  * **`evenLocatedPowerSums4 : EvenLocatedPowerSums4`** — the residual, DISCHARGED,
    hence `ChebGeneralOrtho.LocatedRootPowerSums4 rootData4` UNCONDITIONAL and the
    order-4 discrete orthogonality collapse / diagonal value `5/2` UNCONDITIONAL on the
    CONSTRUCTED located datum — the `M = 4` analogue of the `M = 3` closure
    `ChebLocatedRoots.locatedRootPowerSums3`.

## Honesty / scope (AGENTS.md Rule 6)

This closes the order-4 DISCRETE (finite Gauss) shadow only.  The distinct continuous
`t > 0` heat-kernel residual `RiemannSOS.MomentIntegralIdentity` (the `R`-modulated
Christoffel measure) remains the named wall, as re-exported by `ChebLocatedRoots4`; it
is NOT touched here.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`; `decide` only on closed `Q'`/`Nat`.  The `lin` normal form and all
node data are `Type`-level (MLTT/HoTT-valid).
-/

import YMGap.Continuum.ChebLocatedRoots4

namespace YMGap.Continuum.ChebLocatedRoots4Even

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebLocatedRoots4
open YMGap.Continuum.ChebLocatedRoots (Tcr Tcr_approx)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Rational coefficients for the ladder (`±1/4`, and `0,1,−1` reused inline) -/

/-- `−1/4` (the recurring node-coordinate). -/
def qm : Q' := Q'.mkPos (-1) 4 (by decide)

/-! ## 1. The `ℚ(√5)` normal form `lin p q ≃ p + q·√5` and its algebra

`CReal.mul`/`add`/`neg`/`ofQ'` all act approx-wise, so every `lin` law EXCEPT the
multiplication reduces at each index to a `Q'` identity in the free variable
`√5.approx n` — none of them touches `sqrt5_sq`. -/

/-- The located `ℚ(√5)` element `p + q·√5`. -/
@[reducible] def lin (p q : Q') : CReal :=
  CReal.add (CReal.ofQ' p) (CReal.mul (CReal.ofQ' q) sqrt5)

/-- Pointwise right-distributivity `(A+B)·C ≃ A·C + B·C`. -/
theorem cadd_mul (A B C : CReal) :
    CReal.Equiv (CReal.mul (CReal.add A B) C) (CReal.add (CReal.mul A C) (CReal.mul B C)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_mul_eqv (A.approx n) (B.approx n) (C.approx n))

/-- Pointwise left-distributivity `A·(B+C) ≃ A·B + A·C`. -/
theorem cmul_add (A B C : CReal) :
    CReal.Equiv (CReal.mul A (CReal.add B C)) (CReal.add (CReal.mul A B) (CReal.mul A C)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_add_eqv (A.approx n) (B.approx n) (C.approx n))

/-- Pointwise commutativity `A + B ≃ B + A`. -/
theorem cadd_comm (A B : CReal) :
    CReal.Equiv (CReal.add A B) (CReal.add B A) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_comm_eqv (A.approx n) (B.approx n))

/-- **`lin` addition** `lin p q + lin p' q' ≃ lin (p+p') (q+q')`. -/
theorem lin_add (p q p' q' : Q') :
    CReal.Equiv (CReal.add (lin p q) (lin p' q')) (lin (p + p') (q + q')) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((p + q * sqrt5.approx n) + (p' + q' * sqrt5.approx n))
      ≈ ((p + p') + (q + q') * sqrt5.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.add_swap_inner p (q * sqrt5.approx n) p' (q' * sqrt5.approx n)) ?_
  refine Q'.add_eqv_congr_left (p + p') (q * sqrt5.approx n + q' * sqrt5.approx n)
    ((q + q') * sqrt5.approx n) ?_
  exact Q'.eqv_symm (Q'.add_mul_eqv q q' (sqrt5.approx n))

/-- **`lin` negation** `−(lin p q) ≃ lin (−p) (−q)`. -/
theorem lin_neg (p q : Q') :
    CReal.Equiv (CReal.neg (lin p q)) (lin (-p) (-q)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (-(p + q * sqrt5.approx n)) ≈ ((-p) + (-q) * sqrt5.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv p (q * sqrt5.approx n)) ?_
  refine Q'.add_eqv_congr_left (-p) (-(q * sqrt5.approx n)) ((-q) * sqrt5.approx n) ?_
  exact Q'.eqv_symm (Q'.neg_mul_eqv q (sqrt5.approx n))

/-- **`lin` scalar multiplication** `ofQ' c · lin p q ≃ lin (c·p) (c·q)`. -/
theorem lin_smul (c p q : Q') :
    CReal.Equiv (CReal.mul (CReal.ofQ' c) (lin p q)) (lin (c * p) (c * q)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (c * (p + q * sqrt5.approx n)) ≈ ((c * p) + (c * q) * sqrt5.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c p (q * sqrt5.approx n)) ?_
  refine Q'.add_eqv_congr_left (c * p) (c * (q * sqrt5.approx n)) ((c * q) * sqrt5.approx n) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv c q (sqrt5.approx n))

/-- **`lin` coefficient congruence** `p ≈ p' → q ≈ q' → lin p q ≃ lin p' q'`. -/
theorem lin_congr (p q p' q' : Q') (hp : p ≈ p') (hq : q ≈ q') :
    CReal.Equiv (lin p q) (lin p' q') := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (p + q * sqrt5.approx n) ≈ (p' + q' * sqrt5.approx n)
  exact Q'.add_eqv_congr' hp (Q'.mul_eqv_congr_right q q' (sqrt5.approx n) hq)

/-- **Collapse of a `√5`-free `lin`** `q ≈ 0 → p ≈ c → lin p q ≃ ofQ' c`. -/
theorem lin_to_ofQ (c p q : Q') (hp : p ≈ c) (hq : q ≈ 0) :
    CReal.Equiv (lin p q) (CReal.ofQ' c) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (p + q * sqrt5.approx n) ≈ c
  have hqs : (q * sqrt5.approx n) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right q 0 (sqrt5.approx n) hq)
      (Q'.zero_mul_eqv (sqrt5.approx n))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left p (q * sqrt5.approx n) 0 hqs) ?_
  rw [Q'.add_zero' p]
  exact hp

/-- `czero + lin p q ≃ lin p q`. -/
theorem czero_add_lin (p q : Q') :
    CReal.Equiv (CReal.add CReal.czero (lin p q)) (lin p q) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' ((lin p q).approx n)))

/-! ## 2. The three `√5`-atom sub-products (the ONLY `sqrt5_sq` sites)

`ofQ_mul_Qs` and `Qs_mul_ofQ` are pure rearrangements; `Qs_mul_Qs` is where
`√5·√5 ≃ 5` collapses the single quadratic radical.  Together they give `lin_mul`. -/

/-- `ofQ' a · (ofQ' b · √5) ≃ ofQ'(a·b) · √5`. -/
theorem ofQ_mul_Qs (a b : Q') :
    CReal.Equiv (CReal.mul (CReal.ofQ' a) (CReal.mul (CReal.ofQ' b) sqrt5))
      (CReal.mul (CReal.ofQ' (a * b)) sqrt5) := by
  refine CReal.Equiv.trans (CReal.Equiv.symm (CRealAlg.cmul_assoc (CReal.ofQ' a) (CReal.ofQ' b) sqrt5)) ?_
  exact CRealContinuumAlg.cmul_congr_left (CReal.Equiv.symm (CRealAlg.ofQ'_mul a b))

/-- `(ofQ' a · √5) · ofQ' b ≃ ofQ'(a·b) · √5`. -/
theorem Qs_mul_ofQ (a b : Q') :
    CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' a) sqrt5) (CReal.ofQ' b))
      (CReal.mul (CReal.ofQ' (a * b)) sqrt5) := by
  refine CReal.Equiv.trans (CRealAlg.cmul_assoc (CReal.ofQ' a) sqrt5 (CReal.ofQ' b)) ?_
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (CRealAlg.cmul_comm sqrt5 (CReal.ofQ' b))) ?_
  refine CReal.Equiv.trans (CReal.Equiv.symm (CRealAlg.cmul_assoc (CReal.ofQ' a) (CReal.ofQ' b) sqrt5)) ?_
  exact CRealContinuumAlg.cmul_congr_left (CReal.Equiv.symm (CRealAlg.ofQ'_mul a b))

/-- `(ofQ' a · √5) · (ofQ' b · √5) ≃ ofQ'(a·(b·5))` — the single `sqrt5_sq` collapse. -/
theorem Qs_mul_Qs (a b : Q') :
    CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' a) sqrt5) (CReal.mul (CReal.ofQ' b) sqrt5))
      (CReal.ofQ' (a * (b * 5))) := by
  have inner : CReal.Equiv (CReal.mul sqrt5 (CReal.mul (CReal.ofQ' b) sqrt5))
      (CReal.mul (CReal.ofQ' b) (CReal.mul sqrt5 sqrt5)) := by
    refine CReal.Equiv.trans (CReal.Equiv.symm (CRealAlg.cmul_assoc sqrt5 (CReal.ofQ' b) sqrt5)) ?_
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_left (CRealAlg.cmul_comm sqrt5 (CReal.ofQ' b))) ?_
    exact CRealAlg.cmul_assoc (CReal.ofQ' b) sqrt5 sqrt5
  refine CReal.Equiv.trans (CRealAlg.cmul_assoc (CReal.ofQ' a) sqrt5 (CReal.mul (CReal.ofQ' b) sqrt5)) ?_
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right inner) ?_
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (CRealContinuumAlg.cmul_congr_right sqrt5_sq)) ?_
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (CReal.Equiv.symm (CRealAlg.ofQ'_mul b 5))) ?_
  exact CReal.Equiv.symm (CRealAlg.ofQ'_mul a (b * 5))

/-- **`lin` multiplication** `(p+q√5)(p'+q'√5) ≃ (pp' + q(q'·5)) + (pq' + qp')√5`.
The sole consumer of `sqrt5_sq` (via `Qs_mul_Qs`). -/
theorem lin_mul (p q p' q' : Q') :
    CReal.Equiv (CReal.mul (lin p q) (lin p' q'))
      (lin ((p * p') + (q * (q' * 5))) ((p * q') + (q * p'))) := by
  -- expand the product of the two binomials
  refine CReal.Equiv.trans
    (cadd_mul (CReal.ofQ' p) (CReal.mul (CReal.ofQ' q) sqrt5) (lin p' q')) ?_
  refine CReal.Equiv.trans (Pivot2.add_congr
    (cmul_add (CReal.ofQ' p) (CReal.ofQ' p') (CReal.mul (CReal.ofQ' q') sqrt5))
    (cmul_add (CReal.mul (CReal.ofQ' q) sqrt5) (CReal.ofQ' p')
      (CReal.mul (CReal.ofQ' q') sqrt5))) ?_
  -- collapse the four sub-products via the √5-atoms
  refine CReal.Equiv.trans (Pivot2.add_congr
    (Pivot2.add_congr (CReal.Equiv.symm (CRealAlg.ofQ'_mul p p')) (ofQ_mul_Qs p q'))
    (Pivot2.add_congr (Qs_mul_ofQ q p') (Qs_mul_Qs q q'))) ?_
  -- commute the imaginary/real halves of the second group into `lin` order, then add
  refine CReal.Equiv.trans (Pivot2.add_congr (Pivot2.equiv_refl _)
    (cadd_comm (CReal.mul (CReal.ofQ' (q * p')) sqrt5) (CReal.ofQ' (q * (q' * 5))))) ?_
  exact lin_add (p * p') (p * q') (q * (q' * 5)) (q * p')

/-! ## 3. The located nodes and the constant `1` as `lin` values -/

/-- `cone ≃ lin 1 0`. -/
theorem cone_lin : CReal.Equiv CReal.cone (lin (1 : Q') (0 : Q')) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (1 : Q') ≈ ((1 : Q') + (0 : Q') * sqrt5.approx n)
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') ((0 : Q') * sqrt5.approx n) 0 (Q'.zero_mul_eqv (sqrt5.approx n))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (1 : Q'))

/-- `n1 = (√5+1)/4 ≃ lin (1/4) (1/4)`. -/
theorem n1_lin : CReal.Equiv n1 (lin quarter quarter) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (quarter * (sqrt5.approx n + 1)) ≈ (quarter + quarter * sqrt5.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv quarter (sqrt5.approx n) 1) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (quarter * sqrt5.approx n) (quarter * 1) quarter (Q'.mul_one_eqv quarter)) ?_
  exact Q'.add_comm_eqv (quarter * sqrt5.approx n) quarter

/-- `n2 = (√5−1)/4 ≃ lin (−1/4) (1/4)`. -/
theorem n2_lin : CReal.Equiv n2 (lin qm quarter) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (quarter * (sqrt5.approx n + (-(1 : Q')))) ≈ (qm + quarter * sqrt5.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv quarter (sqrt5.approx n) (-(1 : Q'))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (quarter * sqrt5.approx n) (quarter * (-(1 : Q'))) qm (by decide)) ?_
  exact Q'.add_comm_eqv (quarter * sqrt5.approx n) qm

/-! ## 4. The recurrence-collapse and the `Tcr` value ladder

`tcr_rec_lin` performs ONE recurrence step `2·node·prev − prevprev` on `lin` values
(the single `lin_mul` × `lin_smul` × `lin_add` composition); every ladder lemma is that
step plus a closed `decide` coefficient normalization. -/

/-- **One `Tcr` recurrence step over the `lin` normal form.** -/
theorem tcr_rec_lin (node prev prevprev : CReal) (pn qn p1 q1 p2 q2 : Q')
    (hn : CReal.Equiv node (lin pn qn))
    (h1 : CReal.Equiv prev (lin p1 q1))
    (h2 : CReal.Equiv prevprev (lin p2 q2)) :
    CReal.Equiv
      (CReal.add (CReal.mul (CReal.mul (CReal.ofQ' 2) node) prev) (CReal.neg prevprev))
      (lin (((2 : Q') * ((pn * p1) + (qn * (q1 * 5)))) + (-p2))
        (((2 : Q') * ((pn * q1) + (qn * p1))) + (-q2))) := by
  have hprod : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' 2) node) prev)
      (lin ((2 : Q') * ((pn * p1) + (qn * (q1 * 5)))) ((2 : Q') * ((pn * q1) + (qn * p1)))) := by
    refine CReal.Equiv.trans (CRealAlg.cmul_assoc (CReal.ofQ' 2) node prev) ?_
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_right
        (CReal.Equiv.trans (Pivot2.mul_congr hn h1) (lin_mul pn qn p1 q1))) ?_
    exact lin_smul 2 ((pn * p1) + (qn * (q1 * 5))) ((pn * q1) + (qn * p1))
  have hneg : CReal.Equiv (CReal.neg prevprev) (lin (-p2) (-q2)) :=
    CReal.Equiv.trans (Pivot2.neg_congr h2) (lin_neg p2 q2)
  refine CReal.Equiv.trans (Pivot2.add_congr hprod hneg) ?_
  exact lin_add ((2 : Q') * ((pn * p1) + (qn * (q1 * 5)))) ((2 : Q') * ((pn * q1) + (qn * p1)))
    (-p2) (-q2)

/-- Ladder, node `n1`: `Tcr n1 2 ≃ n2 = lin (−1/4) (1/4)`. -/
theorem L1_2 : CReal.Equiv (Tcr n1 2) (lin qm quarter) :=
  CReal.Equiv.trans
    (tcr_rec_lin n1 n1 CReal.cone quarter quarter quarter quarter (1 : Q') (0 : Q') n1_lin n1_lin cone_lin)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n1 3 ≃ −n2 = lin (1/4) (−1/4)`. -/
theorem L1_3 : CReal.Equiv (Tcr n1 3) (lin quarter qm) :=
  CReal.Equiv.trans
    (tcr_rec_lin n1 (Tcr n1 2) (Tcr n1 1) quarter quarter qm quarter quarter quarter n1_lin L1_2 n1_lin)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n1 4 ≃ −n1 = lin (−1/4) (−1/4)`. -/
theorem L1_4 : CReal.Equiv (Tcr n1 4) (lin qm qm) :=
  CReal.Equiv.trans
    (tcr_rec_lin n1 (Tcr n1 3) (Tcr n1 2) quarter quarter quarter qm qm quarter n1_lin L1_3 L1_2)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n1 5 ≃ −1 = lin (−1) 0`. -/
theorem L1_5 : CReal.Equiv (Tcr n1 5) (lin (-(1 : Q')) (0 : Q')) :=
  CReal.Equiv.trans
    (tcr_rec_lin n1 (Tcr n1 4) (Tcr n1 3) quarter quarter qm qm quarter qm n1_lin L1_4 L1_3)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n1 6 ≃ −n1 = lin (−1/4) (−1/4)`. -/
theorem L1_6 : CReal.Equiv (Tcr n1 6) (lin qm qm) :=
  CReal.Equiv.trans
    (tcr_rec_lin n1 (Tcr n1 5) (Tcr n1 4) quarter quarter (-(1 : Q')) (0 : Q') qm qm n1_lin L1_5 L1_4)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n1 7 ≃ −n2 = lin (1/4) (−1/4)`. -/
theorem L1_7 : CReal.Equiv (Tcr n1 7) (lin quarter qm) :=
  CReal.Equiv.trans
    (tcr_rec_lin n1 (Tcr n1 6) (Tcr n1 5) quarter quarter qm qm (-(1 : Q')) (0 : Q') n1_lin L1_6 L1_5)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n1 8 ≃ n2 = lin (−1/4) (1/4)`. -/
theorem L1_8 : CReal.Equiv (Tcr n1 8) (lin qm quarter) :=
  CReal.Equiv.trans
    (tcr_rec_lin n1 (Tcr n1 7) (Tcr n1 6) quarter quarter quarter qm qm qm n1_lin L1_7 L1_6)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- Ladder, node `n2`: `Tcr n2 2 ≃ −n1 = lin (−1/4) (−1/4)`. -/
theorem L2_2 : CReal.Equiv (Tcr n2 2) (lin qm qm) :=
  CReal.Equiv.trans
    (tcr_rec_lin n2 n2 CReal.cone qm quarter qm quarter (1 : Q') (0 : Q') n2_lin n2_lin cone_lin)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n2 3 ≃ −n1 = lin (−1/4) (−1/4)`. -/
theorem L2_3 : CReal.Equiv (Tcr n2 3) (lin qm qm) :=
  CReal.Equiv.trans
    (tcr_rec_lin n2 (Tcr n2 2) (Tcr n2 1) qm quarter qm qm qm quarter n2_lin L2_2 n2_lin)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n2 4 ≃ n2 = lin (−1/4) (1/4)`. -/
theorem L2_4 : CReal.Equiv (Tcr n2 4) (lin qm quarter) :=
  CReal.Equiv.trans
    (tcr_rec_lin n2 (Tcr n2 3) (Tcr n2 2) qm quarter qm qm qm qm n2_lin L2_3 L2_2)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n2 5 ≃ 1 = lin 1 0`. -/
theorem L2_5 : CReal.Equiv (Tcr n2 5) (lin (1 : Q') (0 : Q')) :=
  CReal.Equiv.trans
    (tcr_rec_lin n2 (Tcr n2 4) (Tcr n2 3) qm quarter qm quarter qm qm n2_lin L2_4 L2_3)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n2 6 ≃ n2 = lin (−1/4) (1/4)`. -/
theorem L2_6 : CReal.Equiv (Tcr n2 6) (lin qm quarter) :=
  CReal.Equiv.trans
    (tcr_rec_lin n2 (Tcr n2 5) (Tcr n2 4) qm quarter (1 : Q') (0 : Q') qm quarter n2_lin L2_5 L2_4)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n2 7 ≃ −n1 = lin (−1/4) (−1/4)`. -/
theorem L2_7 : CReal.Equiv (Tcr n2 7) (lin qm qm) :=
  CReal.Equiv.trans
    (tcr_rec_lin n2 (Tcr n2 6) (Tcr n2 5) qm quarter qm quarter (1 : Q') (0 : Q') n2_lin L2_6 L2_5)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-- `Tcr n2 8 ≃ −n1 = lin (−1/4) (−1/4)`. -/
theorem L2_8 : CReal.Equiv (Tcr n2 8) (lin qm qm) :=
  CReal.Equiv.trans
    (tcr_rec_lin n2 (Tcr n2 7) (Tcr n2 6) qm quarter qm qm qm quarter n2_lin L2_7 L2_6)
    (lin_congr _ _ _ _ (by decide) (by decide))

/-! ## 5. Even reflection parity and the even power-sum assembly -/

/-- **Even reflection parity on the located reals** `Tcr (−y) (2m) ≃ Tcr y (2m)` — the
even companion of `ChebLocatedRoots4.Tcr_neg_odd`, via `(T_reflect · m).1`. -/
theorem Tcr_neg_even (y : CReal) (m : Nat) :
    CReal.Equiv (Tcr (CReal.neg y) (2 * m)) (Tcr y (2 * m)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (Tcr (CReal.neg y) (2 * m)).approx n ≈ (Tcr y (2 * m)).approx n
  rw [Tcr_approx (CReal.neg y) n (2 * m), Tcr_approx y n (2 * m)]
  exact (T_reflect (y.approx n) m).1

/-- **The folded even power sum** `S_{2m} ≃ 2·Tcr n1 (2m) + 2·Tcr n2 (2m)` in `lin`
form: the two reflected nodes `−n2, −n1` fold onto `n2, n1` by `Tcr_neg_even`. -/
theorem Sj_even_lin (m : Nat) (p1 q1 p2 q2 : Q')
    (h1 : CReal.Equiv (Tcr n1 (2 * m)) (lin p1 q1))
    (h2 : CReal.Equiv (Tcr n2 (2 * m)) (lin p2 q2)) :
    CReal.Equiv (PowerSumCollapse.Sj rootData4 (2 * m))
      (lin (((p1 + p2) + p2) + p1) (((q1 + q2) + q2) + q1)) := by
  rw [Sj4_eq (2 * m)]
  have hn2 : CReal.Equiv (Tcr (CReal.neg n2) (2 * m)) (lin p2 q2) :=
    CReal.Equiv.trans (Tcr_neg_even n2 m) h2
  have hn1 : CReal.Equiv (Tcr (CReal.neg n1) (2 * m)) (lin p1 q1) :=
    CReal.Equiv.trans (Tcr_neg_even n1 m) h1
  refine CReal.Equiv.trans (Pivot2.add_congr (Pivot2.add_congr (Pivot2.add_congr
    (Pivot2.add_congr (Pivot2.equiv_refl CReal.czero) h1) h2) hn2) hn1) ?_
  refine CReal.Equiv.trans (Pivot2.add_congr (Pivot2.add_congr (Pivot2.add_congr
    (czero_add_lin p1 q1) (Pivot2.equiv_refl _)) (Pivot2.equiv_refl _)) (Pivot2.equiv_refl _)) ?_
  refine CReal.Equiv.trans (Pivot2.add_congr (Pivot2.add_congr
    (lin_add p1 q1 p2 q2) (Pivot2.equiv_refl _)) (Pivot2.equiv_refl _)) ?_
  refine CReal.Equiv.trans (Pivot2.add_congr (lin_add (p1 + p2) (q1 + q2) p2 q2)
    (Pivot2.equiv_refl _)) ?_
  exact lin_add ((p1 + p2) + p2) ((q1 + q2) + q2) p1 q1

/-- `S₂ ≃ −1`. -/
theorem Sj_even_2 : CReal.Equiv (PowerSumCollapse.Sj rootData4 2) (CReal.ofQ' (-(1 : Q'))) :=
  CReal.Equiv.trans (Sj_even_lin 1 qm quarter qm qm L1_2 L2_2)
    (lin_to_ofQ (-(1 : Q')) _ _ (by decide) (by decide))

/-- `S₄ ≃ −1`. -/
theorem Sj_even_4 : CReal.Equiv (PowerSumCollapse.Sj rootData4 4) (CReal.ofQ' (-(1 : Q'))) :=
  CReal.Equiv.trans (Sj_even_lin 2 qm qm qm quarter L1_4 L2_4)
    (lin_to_ofQ (-(1 : Q')) _ _ (by decide) (by decide))

/-- `S₆ ≃ −1`. -/
theorem Sj_even_6 : CReal.Equiv (PowerSumCollapse.Sj rootData4 6) (CReal.ofQ' (-(1 : Q'))) :=
  CReal.Equiv.trans (Sj_even_lin 3 qm qm qm quarter L1_6 L2_6)
    (lin_to_ofQ (-(1 : Q')) _ _ (by decide) (by decide))

/-- `S₈ ≃ −1`. -/
theorem Sj_even_8 : CReal.Equiv (PowerSumCollapse.Sj rootData4 8) (CReal.ofQ' (-(1 : Q'))) :=
  CReal.Equiv.trans (Sj_even_lin 4 qm quarter qm qm L1_8 L2_8)
    (lin_to_ofQ (-(1 : Q')) _ _ (by decide) (by decide))

/-! ## 6. The residual DISCHARGED, and the order-4 collapse made UNCONDITIONAL -/

/-- **`EvenLocatedPowerSums4`, DISCHARGED.**  The located `U₄` roots `±(√5±1)/4` realize
the even Newton first-kind power sums `S₂ = S₄ = S₆ = S₈ ≃ −1`, matching the rational
certificate `ChebGeneralOrtho.order4_powerSum_collapse`. -/
theorem evenLocatedPowerSums4 : EvenLocatedPowerSums4 :=
  ⟨Sj_even_2, Sj_even_4, Sj_even_6, Sj_even_8⟩

/-- **The full order-4 located residual, UNCONDITIONAL.**
`ChebGeneralOrtho.LocatedRootPowerSums4 rootData4` (odd half by parity, even half above). -/
theorem locatedRootPowerSums4 : ChebGeneralOrtho.LocatedRootPowerSums4 rootData4 :=
  locatedRootPowerSums4_of_even evenLocatedPowerSums4

/-- **Order-4 discrete Chebyshev-`U` orthogonality collapse, UNCONDITIONAL** on the
CONSTRUCTED located datum `rootData4` (the `M = 4` analogue of the closed `M = 3`
instance `ChebLocatedRoots.order3_discreteOrthogonality_collapse`). -/
theorem order4_orthoCollapse_locatedNodes :
    ChebOrthogonality.PowerSumCollapse rootData4.toU :=
  order4_orthoCollapse_of_locatedNodes evenLocatedPowerSums4

/-- **Order-4 discrete orthogonality diagonal value `(4+1)/2 = 5/2`, UNCONDITIONAL** at
the located nodes `±(√5±1)/4`. -/
theorem order4_diag_value_locatedNodes :
    CReal.Equiv (ChebOrthogonality.orthoSum rootData4.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((4 : Int) + 1) 2 (by decide))) :=
  order4_diag_value_of_locatedNodes evenLocatedPowerSums4

end YMGap.Continuum.ChebLocatedRoots4Even

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebLocatedRoots4Even.lin_mul
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.L1_8
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.L2_8
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.Tcr_neg_even
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.Sj_even_2
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.Sj_even_8
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.evenLocatedPowerSums4
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.locatedRootPowerSums4
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.order4_orthoCollapse_locatedNodes
#print axioms YMGap.Continuum.ChebLocatedRoots4Even.order4_diag_value_locatedNodes
