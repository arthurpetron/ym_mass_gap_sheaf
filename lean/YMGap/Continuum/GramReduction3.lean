/-
The **N=3 bridge** of Piece C (the Gram→functional reduction).

Companion to `GramReduction.lean`'s `coneExp2_eqv_form2` / `coneExp_psd_two`:
here we mechanize the N=3 analogue, proving UNCONDITIONALLY that the SU(2)
heat-kernel `3×3` character Gram quadratic form is nonnegative.

The Gram form `WilsonFunctional.coneExp t ht c 3` is a nested double `csum`
over the fusion-built Gram entries `gramEntry t ht i j` (`i,j < 3`).  The
LDLᵀ-certified `Pivot3.form3 t ht (c 0) (c 1) (c 2)` is the explicit six-term
quadratic form over the manifest Gram entries `G00,…,G22`.  We prove the two
are `CReal.Equiv` and transport `Pivot3.form3_nonneg` across the bridge.

The match is:

  * each of the six needed Gram entries `gramEntry t ht i j` (`i ≤ j`) reduces,
    after stripping the empty-sum `czero` leading term(s), to the corresponding
    `Pivot3` Gram entry `G_{ij}` (`gramEntry_eqv_G**` below) — this is the
    SU(2) Clebsch–Gordan fusion `χ_iχ_j = Σ χ_{|i−j|..i+j step 2}` made
    definitional, plus `wilsonCharExp t ht s ≃ (s+1)·a^{C₂}` matching
    `Pivot3.m_k = (k+1)·a^{k(k+2)}`;
  * the 3×3 `coneExp` double sum (9 terms) is regrouped to the 6 `form3`
    terms via the Gram symmetry `gramEntry i j = gramEntry j i` and the
    symmetric-cross-term merge `c_i c_j·m + c_j c_i·m ≃ 2 c_i c_j·m`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.GramReduction
import YMGap.Continuum.Pivot3Defs
import YMGap.Continuum.Pivot3

namespace YMGap.Continuum.GramRed3

open YMGap.Constructive
open YMGap.Continuum.Pivot2 (equiv_trans add_congr mul_congr_right)
open YMGap.Continuum.GramRed (equiv_refl czero_add_eqv cross_merge equiv_ofQ'_of_bounds)

/-! ## The six Gram entries `gramEntry t ht i j ≃ G_{ij}`

Each `gramEntry t ht a b = Σ_{j=0}^{min a b} wce_{|a−b|+2j}` (a `csum` with
`min a b + 1` terms, leading `czero`).  We reduce each of the six needed
entries to its `Pivot3` counterpart.  The building block is that the heat-kernel
moment `wilsonCharExp t ht s` matches the `Pivot3` moment encoding. -/

/-- The heat-kernel moment `wilsonCharExp t ht s = (s+1)·e^{−t·s(s+2)/4}` IS the
`Pivot3` moment encoding `(s+1)·a^{s(s+2)}` (`smul (dim s) (apow (4·C₂(s)))`):
the `dim`-factor is identical and the `expNeg` exponents coincide. -/
theorem wce_eqv (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) :
    CReal.Equiv (WilsonFunctional.wilsonCharExp t ht s)
      (Pivot3.smul (RepTheory.SU2.dimension s)
        (Pivot3.apow t ht (RepTheory.SU2.fourTimesCasimir s))) :=
  equiv_refl _

/-- `gramEntry t ht 0 0 = wce_0 ≃ G00 = 1` (strip the empty sum, normalize). -/
theorem gramEntry_eqv_G00 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 0 0) Pivot3.G00 :=
  equiv_trans (czero_add_eqv _) (GramRed.wce0_eqv_C1 t ht)

/-- `gramEntry t ht 0 1 = wce_1 ≃ G01 = m₁`. -/
theorem gramEntry_eqv_G01 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 0 1) (Pivot3.G01 t ht) :=
  equiv_trans (czero_add_eqv _) (equiv_refl _)

/-- `gramEntry t ht 0 2 = wce_2 ≃ G02 = m₂`. -/
theorem gramEntry_eqv_G02 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 0 2) (Pivot3.G02 t ht) :=
  equiv_trans (czero_add_eqv _) (equiv_refl _)

/-- `gramEntry t ht 1 1 = (wce_0)+(wce_2) ≃ G11 = 1 + m₂`. -/
theorem gramEntry_eqv_G11 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 1 1) (Pivot3.G11 t ht) :=
  add_congr (equiv_trans (czero_add_eqv _) (GramRed.wce0_eqv_C1 t ht)) (equiv_refl _)

/-- `gramEntry t ht 1 2 = (wce_1)+(wce_3) ≃ G12 = m₁ + m₃`. -/
theorem gramEntry_eqv_G12 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 1 2) (Pivot3.G12 t ht) :=
  add_congr (equiv_trans (czero_add_eqv _) (equiv_refl _)) (equiv_refl _)

/-- `gramEntry t ht 2 2 = ((wce_0)+(wce_2))+(wce_4) ≃ G22 = (1 + m₂) + m₄`. -/
theorem gramEntry_eqv_G22 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 2 2) (Pivot3.G22 t ht) :=
  add_congr
    (add_congr (equiv_trans (czero_add_eqv _) (GramRed.wce0_eqv_C1 t ht)) (equiv_refl _))
    (equiv_refl _)

/-! The symmetric (lower-triangle) Gram entries reduce to the same `Pivot3`
entry as their transpose, since `gramEntry a b` depends only on `{a,b}`. -/

/-- `gramEntry t ht 1 0 = wce_1 ≃ G01 = m₁`. -/
theorem gramEntry_eqv_G10 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 1 0) (Pivot3.G01 t ht) :=
  equiv_trans (czero_add_eqv _) (equiv_refl _)

/-- `gramEntry t ht 2 0 = wce_2 ≃ G02 = m₂`. -/
theorem gramEntry_eqv_G20 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 2 0) (Pivot3.G02 t ht) :=
  equiv_trans (czero_add_eqv _) (equiv_refl _)

/-- `gramEntry t ht 2 1 = (wce_1)+(wce_3) ≃ G12 = m₁ + m₃`. -/
theorem gramEntry_eqv_G21 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.gramEntry t ht 2 1) (Pivot3.G12 t ht) :=
  add_congr (equiv_trans (czero_add_eqv _) (equiv_refl _)) (equiv_refl _)

/-! ## The 3×3 `coneExp` double sum, with Gram entries reduced to `G_{ij}`

`coneExp t ht c 3` is `((0 + R0) + R1) + R2` with
`Rμ = ((0 + Tμ0) + Tμ1) + Tμ2` and `Tμν = (cμ·cν)·gramEntry μ ν`.  We rewrite
it, stripping the three `czero` row-leaders and replacing each `gramEntry μ ν`
by its `Pivot3` entry `G_{μν}`, to the clean nine-term tree below. -/

/-- The clean nine-term tree (same association as `coneExp … 3`, with `czero`
row-leaders stripped and `gramEntry → G`). -/
private def cleanTree (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') : CReal :=
  CReal.add
    (CReal.add
      (CReal.add
        (CReal.add (CReal.mul (CReal.ofQ' (c 0 * c 0)) Pivot3.G00)
                   (CReal.mul (CReal.ofQ' (c 0 * c 1)) (Pivot3.G01 t ht)))
        (CReal.mul (CReal.ofQ' (c 0 * c 2)) (Pivot3.G02 t ht)))
      (CReal.add
        (CReal.add (CReal.mul (CReal.ofQ' (c 1 * c 0)) (Pivot3.G01 t ht))
                   (CReal.mul (CReal.ofQ' (c 1 * c 1)) (Pivot3.G11 t ht)))
        (CReal.mul (CReal.ofQ' (c 1 * c 2)) (Pivot3.G12 t ht))))
    (CReal.add
      (CReal.add (CReal.mul (CReal.ofQ' (c 2 * c 0)) (Pivot3.G02 t ht))
                 (CReal.mul (CReal.ofQ' (c 2 * c 1)) (Pivot3.G12 t ht)))
      (CReal.mul (CReal.ofQ' (c 2 * c 2)) (Pivot3.G22 t ht)))

set_option maxHeartbeats 1600000 in
/-- **Step 1:** `coneExp t ht c 3 ≃ cleanTree` — strip the `czero` row-leaders
and replace each `gramEntry μ ν` by `G_{μν}`. -/
theorem coneExp3_eqv_cleanTree (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    CReal.Equiv (WilsonFunctional.coneExp t ht c 3) (cleanTree t ht c) := by
  refine equiv_trans (add_congr (add_congr (czero_add_eqv _) (equiv_refl _)) (equiv_refl _)) ?_
  refine add_congr (add_congr ?row0 ?row1) ?row2
  case row0 =>
    refine add_congr (add_congr
      (equiv_trans (czero_add_eqv _) (mul_congr_right (gramEntry_eqv_G00 t ht)))
      (mul_congr_right (gramEntry_eqv_G01 t ht)))
      (mul_congr_right (gramEntry_eqv_G02 t ht))
  case row1 =>
    refine add_congr (add_congr
      (equiv_trans (czero_add_eqv _) (mul_congr_right (gramEntry_eqv_G10 t ht)))
      (mul_congr_right (gramEntry_eqv_G11 t ht)))
      (mul_congr_right (gramEntry_eqv_G12 t ht))
  case row2 =>
    refine add_congr (add_congr
      (equiv_trans (czero_add_eqv _) (mul_congr_right (gramEntry_eqv_G20 t ht)))
      (mul_congr_right (gramEntry_eqv_G21 t ht)))
      (mul_congr_right (gramEntry_eqv_G22 t ht))

/-! ## A list-based rational commutative-monoid normalizer

The nine-leaf regroup is, at the `approx` level, a pure `Q'` commutative-monoid
rearrangement.  We model a sum as the right fold `sumR` of a `List Q'`, prove
`sumR` is `Q'.eqv`-invariant under `List.Perm` (by the four `Perm` generators),
and read both trees off as `sumR` of permutation-related leaf lists.  This
makes the otherwise gigantic AC reordering a single `decide`-checked `Perm`. -/

namespace ACaux

open YMGap.Constructive

/-- Right-fold sum of a list of rationals (`Σ`, right-associated, with `0` seed). -/
def sumR (l : List Q') : Q' := l.foldr (· + ·) 0

@[simp] theorem sumR_nil : sumR [] = 0 := rfl
@[simp] theorem sumR_cons (a : Q') (l : List Q') : sumR (a :: l) = a + sumR l := rfl

/-- `sumR` is `Q'.eqv`-invariant under adjacent transposition of the first two
elements: `a + (b + R) ≃ b + (a + R)`. -/
private theorem sumR_swap (a b : Q') (l : List Q') :
    (sumR (b :: a :: l)).eqv (sumR (a :: b :: l)) := by
  show (b + (a + sumR l)).eqv (a + (b + sumR l))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv b a (sumR l))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (b + a) (a + b) (sumR l) (Q'.add_comm_eqv b a)) ?_
  exact Q'.add_assoc_eqv a b (sumR l)

/-- **`sumR` respects `List.Perm`:** permuting the summands preserves the
right-fold up to `Q'.eqv`.  Proved by the four `Perm` generators. -/
theorem sumR_perm {l₁ l₂ : List Q'} (h : l₁.Perm l₂) : (sumR l₁).eqv (sumR l₂) := by
  induction h with
  | nil => exact Q'.eqv_refl 0
  | cons a _ ih =>
      exact Q'.add_eqv_congr_left a _ _ ih
  | swap a b l => exact sumR_swap a b l
  | trans _ _ ih₁ ih₂ => exact Q'.eqv_trans _ _ _ ih₁ ih₂

/-- Two index-lists that are `List.Perm` give `Q'.eqv`-equal `sumR (map f ·)`. -/
theorem sumR_map_perm (f : Nat → Q') {i₁ i₂ : List Nat} (h : i₁.Perm i₂) :
    (sumR (i₁.map f)).eqv (sumR (i₂.map f)) :=
  sumR_perm (h.map f)

private theorem tr3 (a b c : Q') (h1 : a.eqv b) (h2 : b.eqv c) : a.eqv c :=
  Q'.eqv_trans a b c h1 h2
private theorem as3 (a b c : Q') : ((a + b) + c).eqv (a + (b + c)) := Q'.add_assoc_eqv a b c
private theorem cgl (a b c : Q') (h : b.eqv c) : (a + b).eqv (a + c) :=
  Q'.add_eqv_congr_left a b c h

/-- **Flatten the `cleanTree` leaf-shape** to `sumR [x0..x8]` (associativity
only, plus the trailing `+0`). -/
theorem flattenCT (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Q') :
    ((((x0 + x1) + x2) + ((x3 + x4) + x5)) + ((x6 + x7) + x8)).eqv
      (sumR [x0, x1, x2, x3, x4, x5, x6, x7, x8]) := by
  show ((((x0 + x1) + x2) + ((x3 + x4) + x5)) + ((x6 + x7) + x8)).eqv
    (x0 + (x1 + (x2 + (x3 + (x4 + (x5 + (x6 + (x7 + (x8 + 0)))))))))
  refine tr3 _ _ _ (as3 ((x0 + x1) + x2) ((x3 + x4) + x5) ((x6 + x7) + x8)) ?_
  refine tr3 _ _ _ (as3 (x0 + x1) x2 (((x3 + x4) + x5) + ((x6 + x7) + x8))) ?_
  refine tr3 _ _ _ (as3 x0 x1 (x2 + (((x3 + x4) + x5) + ((x6 + x7) + x8)))) ?_
  refine cgl x0 _ _ (cgl x1 _ _ ?_)
  -- x2 + (((x3+x4)+x5) + ((x6+x7)+x8))
  refine cgl x2 _ _ ?_
  refine tr3 _ _ _ (as3 (x3 + x4) x5 ((x6 + x7) + x8)) ?_
  refine tr3 _ _ _ (as3 x3 x4 (x5 + ((x6 + x7) + x8))) ?_
  refine cgl x3 _ _ (cgl x4 _ _ ?_)
  refine cgl x5 _ _ ?_
  refine tr3 _ _ _ (as3 x6 x7 x8) ?_
  exact cgl x6 _ _ (cgl x7 _ _ (Q'.eqv_symm (QPoly.q_add_zero_eqv x8)))

/-- **Flatten the `pairedTree` leaf-shape** to `sumR [y0..y8]`. -/
theorem flattenPT (y0 y1 y2 y3 y4 y5 y6 y7 y8 : Q') :
    (((y0 + y1) + (y2 + (y3 + y4))) + ((y5 + y6) + (y7 + y8))).eqv
      (sumR [y0, y1, y2, y3, y4, y5, y6, y7, y8]) := by
  show (((y0 + y1) + (y2 + (y3 + y4))) + ((y5 + y6) + (y7 + y8))).eqv
    (y0 + (y1 + (y2 + (y3 + (y4 + (y5 + (y6 + (y7 + (y8 + 0)))))))))
  refine tr3 _ _ _ (as3 (y0 + y1) (y2 + (y3 + y4)) ((y5 + y6) + (y7 + y8))) ?_
  refine tr3 _ _ _ (as3 y0 y1 ((y2 + (y3 + y4)) + ((y5 + y6) + (y7 + y8)))) ?_
  refine cgl y0 _ _ (cgl y1 _ _ ?_)
  -- (y2+(y3+y4)) + ((y5+y6)+(y7+y8))
  refine tr3 _ _ _ (as3 y2 (y3 + y4) ((y5 + y6) + (y7 + y8))) ?_
  refine cgl y2 _ _ ?_
  refine tr3 _ _ _ (as3 y3 y4 ((y5 + y6) + (y7 + y8))) ?_
  refine cgl y3 _ _ (cgl y4 _ _ ?_)
  refine tr3 _ _ _ (as3 y5 y6 (y7 + y8)) ?_
  exact cgl y5 _ _ (cgl y6 _ _ (cgl y7 _ _ (Q'.eqv_symm (QPoly.q_add_zero_eqv y8))))

end ACaux

/-! ## CReal `add` commutativity / associativity as `Equiv` (pointwise)

The substrate has no `add`-comm/assoc `Equiv` lemmas; we build the few needed
for the nine-leaf regroup, each proved at the `approx` level by the matching
`Q'` lemma (as `regroup4` is in `GramReduction.lean`). -/

/-- `A + B ≃ B + A`. -/
theorem cadd_comm (A B : CReal) : CReal.Equiv (CReal.add A B) (CReal.add B A) := by
  apply SumOfSquares.Equiv_of_approx_eqv; intro n
  exact Q'.add_comm_eqv (A.approx n) (B.approx n)

/-- `(A + B) + C ≃ A + (B + C)`. -/
theorem cadd_assoc (A B C : CReal) :
    CReal.Equiv (CReal.add (CReal.add A B) C) (CReal.add A (CReal.add B C)) := by
  apply SumOfSquares.Equiv_of_approx_eqv; intro n
  exact Q'.add_assoc_eqv (A.approx n) (B.approx n) (C.approx n)

/-- `A + (B + C) ≃ (A + B) + C`. -/
theorem cadd_assoc' (A B C : CReal) :
    CReal.Equiv (CReal.add A (CReal.add B C)) (CReal.add (CReal.add A B) C) :=
  CReal.Equiv.symm (cadd_assoc A B C)

/-! ## Step 2 — `cleanTree ≃ form3` (the 9→6 regroup with symmetric merges)

We regroup the nine `coneExp` leaves into the six `form3` terms, merging the
three symmetric pairs `T_{ij} + T_{ji} ≃ 2 c_i c_j · G_{ij}` (`cross_merge`).

We first move `cleanTree` (the `coneExp` association) into the *paired* tree
`((T00 + T11) + (T22 + (T01+T10))) + ((T02+T20) + (T12+T21))`, then apply the
three merges and land on `form3`. -/

/-- The paired tree: diagonals collected, the three symmetric off-diagonal
pairs adjacent, in exactly the `form3` association. -/
private def pairedTree (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') : CReal :=
  CReal.add
    (CReal.add
      (CReal.add (CReal.mul (CReal.ofQ' (c 0 * c 0)) Pivot3.G00)
                 (CReal.mul (CReal.ofQ' (c 1 * c 1)) (Pivot3.G11 t ht)))
      (CReal.add (CReal.mul (CReal.ofQ' (c 2 * c 2)) (Pivot3.G22 t ht))
                 (CReal.add (CReal.mul (CReal.ofQ' (c 0 * c 1)) (Pivot3.G01 t ht))
                            (CReal.mul (CReal.ofQ' (c 1 * c 0)) (Pivot3.G01 t ht)))))
    (CReal.add
      (CReal.add (CReal.mul (CReal.ofQ' (c 0 * c 2)) (Pivot3.G02 t ht))
                 (CReal.mul (CReal.ofQ' (c 2 * c 0)) (Pivot3.G02 t ht)))
      (CReal.add (CReal.mul (CReal.ofQ' (c 1 * c 2)) (Pivot3.G12 t ht))
                 (CReal.mul (CReal.ofQ' (c 2 * c 1)) (Pivot3.G12 t ht))))

/-- **Step 2a:** `cleanTree ≃ pairedTree` — a pure nine-leaf rearrangement
(commutativity/associativity of `add`), no merges yet.  Proved at the `approx`
level by the `Q'` commutative-monoid laws. -/
theorem cleanTree_eqv_pairedTree (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    CReal.Equiv (cleanTree t ht c) (pairedTree t ht c) := by
  apply SumOfSquares.Equiv_of_approx_eqv; intro n
  -- the nine leaf approx-values, in `cleanTree` left-to-right order
  let a := (c 0 * c 0) * (Pivot3.G00).approx n
  let p := (c 0 * c 1) * (Pivot3.G01 t ht).approx n
  let q := (c 0 * c 2) * (Pivot3.G02 t ht).approx n
  let p' := (c 1 * c 0) * (Pivot3.G01 t ht).approx n
  let b := (c 1 * c 1) * (Pivot3.G11 t ht).approx n
  let r := (c 1 * c 2) * (Pivot3.G12 t ht).approx n
  let q' := (c 2 * c 0) * (Pivot3.G02 t ht).approx n
  let r' := (c 2 * c 1) * (Pivot3.G12 t ht).approx n
  let d := (c 2 * c 2) * (Pivot3.G22 t ht).approx n
  show ((((a + p) + q) + ((p' + b) + r)) + ((q' + r') + d)).eqv
      (((a + b) + (d + (p + p'))) + ((q + q') + (r + r')))
  -- index the nine atoms in `cleanTree` left-to-right order
  let f : Nat → Q' := fun i => [a, p, q, p', b, r, q', r', d].getD i 0
  -- flatten both trees to `sumR` of (index-mapped) lists
  have hCT : ((((a + p) + q) + ((p' + b) + r)) + ((q' + r') + d)).eqv
      (ACaux.sumR (([0,1,2,3,4,5,6,7,8] : List Nat).map f)) :=
    ACaux.flattenCT a p q p' b r q' r' d
  have hPT : (((a + b) + (d + (p + p'))) + ((q + q') + (r + r'))).eqv
      (ACaux.sumR (([0,4,8,1,3,2,6,5,7] : List Nat).map f)) :=
    ACaux.flattenPT a b d p p' q q' r r'
  -- the two index-lists are permutations ⇒ the `sumR`s are `Q'.eqv`.
  -- Explicit `List.Perm` witness (avoiding `decide`, which pulls in `Classical`):
  -- repeatedly bring the next target head to the front via `perm_middle`.
  have hperm : (([0,1,2,3,4,5,6,7,8] : List Nat)).Perm [0,4,8,1,3,2,6,5,7] := by
    refine List.Perm.cons 0 ?_
    refine List.Perm.trans (List.perm_middle (l₁ := [1,2,3]) (a := 4) (l₂ := [5,6,7,8])) ?_
    refine List.Perm.cons 4 ?_
    refine List.Perm.trans (List.perm_middle (l₁ := [1,2,3,5,6,7]) (a := 8) (l₂ := [])) ?_
    refine List.Perm.cons 8 ?_
    refine List.Perm.cons 1 ?_
    refine List.Perm.trans (List.perm_middle (l₁ := [2]) (a := 3) (l₂ := [5,6,7])) ?_
    refine List.Perm.cons 3 ?_
    refine List.Perm.cons 2 ?_
    refine List.Perm.trans (List.perm_middle (l₁ := [5]) (a := 6) (l₂ := [7])) ?_
    refine List.Perm.cons 6 ?_
    exact List.Perm.refl _
  exact Q'.eqv_trans _ _ _ hCT
    (Q'.eqv_trans _ _ _ (ACaux.sumR_map_perm f hperm) (Q'.eqv_symm hPT))

/-- **Step 2b:** `pairedTree ≃ form3` — the three symmetric off-diagonal pairs
merge to the `2 c_i c_j` terms (`cross_merge`); the diagonal terms match
on the nose.  Same association on both sides. -/
theorem pairedTree_eqv_form3 (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    CReal.Equiv (pairedTree t ht c) (Pivot3.form3 t ht (c 0) (c 1) (c 2)) :=
  add_congr
    (add_congr
      (add_congr (equiv_refl _) (equiv_refl _))
      (add_congr (equiv_refl _) (cross_merge (c 0) (c 1) (Pivot3.G01 t ht))))
    (add_congr (cross_merge (c 0) (c 2) (Pivot3.G02 t ht))
               (cross_merge (c 1) (c 2) (Pivot3.G12 t ht)))

/-! ## The N=3 bridge and the unconditional 3×3 Gram PSD -/

/-- **The N=3 bridge:** the SU(2) heat-kernel `3×3` Gram quadratic form
`coneExp t ht c 3` (a nested double `csum` over fusion-built Gram entries) equals
`Pivot3.form3 t ht (c 0) (c 1) (c 2)` (the explicit six-term LDLᵀ-certified
quadratic form).  The abstract Gram form and `form3` are the same observable
energy — the `N=3` analogue of `GramRed.coneExp2_eqv_form2`. -/
theorem coneExp3_eqv_form3 (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    CReal.Equiv (WilsonFunctional.coneExp t ht c 3)
      (Pivot3.form3 t ht (c 0) (c 1) (c 2)) :=
  equiv_trans (coneExp3_eqv_cleanTree t ht c)
    (equiv_trans (cleanTree_eqv_pairedTree t ht c) (pairedTree_eqv_form3 t ht c))

/-- **SU(2) heat-kernel `3×3` Gram PSD, UNCONDITIONALLY.**  `coneExp t ht c 3 ≥ 0`
for every `c` — the `N=3` Gram positive-semidefiniteness, with NO analytic input:
it is `Pivot3.form3_nonneg` transported across the bridge `coneExp3_eqv_form3`.
This is the concrete witness that `form3_nonneg` IS the `N=3` instance of the
uniform reduction (`GramRed.psd_of_momentSquare_nonneg`), fully machine-checked. -/
theorem coneExp_psd_three (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c 3) 0 :=
  SU3CharFactor.geRat_of_equiv (coneExp3_eqv_form3 t ht c)
    (Pivot3.form3_nonneg t ht (c 0) (c 1) (c 2))

end YMGap.Continuum.GramRed3

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GramRed3.gramEntry_eqv_G00
#print axioms YMGap.Continuum.GramRed3.gramEntry_eqv_G01
#print axioms YMGap.Continuum.GramRed3.gramEntry_eqv_G02
#print axioms YMGap.Continuum.GramRed3.gramEntry_eqv_G11
#print axioms YMGap.Continuum.GramRed3.gramEntry_eqv_G12
#print axioms YMGap.Continuum.GramRed3.gramEntry_eqv_G22
#print axioms YMGap.Continuum.GramRed3.ACaux.sumR_perm
#print axioms YMGap.Continuum.GramRed3.coneExp3_eqv_cleanTree
#print axioms YMGap.Continuum.GramRed3.cleanTree_eqv_pairedTree
#print axioms YMGap.Continuum.GramRed3.pairedTree_eqv_form3
#print axioms YMGap.Continuum.GramRed3.coneExp3_eqv_form3
#print axioms YMGap.Continuum.GramRed3.coneExp_psd_three
