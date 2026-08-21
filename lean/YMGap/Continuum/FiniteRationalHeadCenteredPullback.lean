/-
# Canonical pullback matrices for positive-head centered coordinates

This module represents the explicit positive-head centering lift by a finite
rational coordinate matrix.  Combining that linearization with the generic
`A^T M A` theorem constructs the two reduced canonical penalized matrices and
all exact quadratic-identification fields of
`FiniteCenteredTwoSidedRestriction`.

Thus a strictly positive head weight now generates the entire centered
restriction.  Only factorization/nonnegativity of the displayed reduced
matrices remains for the finite LDL producer.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRationalHeadCenteredCoordinates
import YMGap.Continuum.FiniteRationalMatrixPullback

namespace YMGap.Continuum.FiniteRationalHeadCenteredPullback

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalHeadCenteredCoordinates
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalMatrixPullback
open YMGap.Continuum.FiniteRationalPenalizedMatrix
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem eqv_of_le_of_le_local
    {a b : Q'} (hab : a ≤ b) (hba : b ≤ a) : a ≈ b :=
  Int.le_antisymm hab hba

private theorem eqv_divPos_of_mul_local
    {a numerator denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hmul : a * denominator ≈ numerator) :
    a ≈ Q'.divPos numerator denominator hdenominator := by
  apply eqv_of_le_of_le_local
  · exact Q'.le_divPos_of_mul_le numerator denominator hdenominator
      (Q'.le_of_eqv hmul)
  · exact Q'.divPos_le_of_le_mul numerator denominator hdenominator
      (Q'.ge_of_eqv hmul)

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem rangeNodupLocal (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

private theorem listQSum_ite_single
    {A : Type} [DecidableEq A] (selected : A) (value : A → Q') :
    ∀ items : List A,
      items.Nodup → selected ∈ items →
      listQSum
          (fun item => if selected = item then value item else 0)
          items ≈
        value selected
  | [], _hnodup, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum]
        have htailZero :
            listQSum
                (fun item => if selected = item then value item else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _item => (0 : Q')) tail) _ ?_ ?_
          · apply listQSum_congr_on
            intro item hitem
            rw [if_neg]
            exact Q'.eqv_refl 0
            intro heq
            exact hparts.1 (heq ▸ hitem)
          · exact listQSum_zero tail
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : selected ≠ head := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hne]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left _ _ _
            (listQSum_ite_single selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem range_succ_shift_local (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        List.range (Nat.succ n + 1) =
            List.range (n + 1) ++ [n + 1] := by
          simpa only [Nat.succ_eq_add_one] using
            (List.range_succ (n := n + 1))
        _ = (0 :: (List.range n).map Nat.succ) ++ [n + 1] :=
          congrArg (fun items => items ++ [n + 1]) ih
        _ = 0 :: (List.range (n + 1)).map Nat.succ := by
          simp only [List.range_succ, List.map_append, List.map,
            List.cons_append, Nat.succ_eq_add_one]

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

/-! ## 1. The coordinate matrix of the centering lift -/

/-- Coordinate matrix for the positive-head centered lift.  The head row
contains the negative tail weights divided by the head weight; the remaining
rows form the identity. -/
def finiteHeadCenteredTransform
    (weight : Nat → Q') (hhead : (0 : Q') < weight 0) :
    Nat → Nat → Q'
  | 0, k => Q'.divPos (-(weight (k + 1))) (weight 0) hhead
  | i + 1, k => if i = k then 1 else 0

/-- The head row of the coordinate matrix evaluates to the division formula
used by the explicit centered lift. -/
theorem finiteHeadCenteredLinearApply_zero
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (coefficient : Nat → Q') :
    finiteLinearApply n
        (finiteHeadCenteredTransform weight hhead) coefficient 0 ≈
      finiteHeadCenteredLift n weight hhead coefficient 0 := by
  apply eqv_divPos_of_mul_local hhead
  refine Q'.eqv_trans _
    (listQSum
      (fun k =>
        (coefficient k *
          Q'.divPos (-(weight (k + 1))) (weight 0) hhead) *
            weight 0)
      (List.range n)) _ ?_ ?_
  · unfold finiteLinearApply finiteHeadCenteredTransform
    exact Q'.eqv_symm
      (listQSum_mul_right
        (fun k => coefficient k *
          Q'.divPos (-(weight (k + 1))) (weight 0) hhead)
        (weight 0) (List.range n))
  · refine Q'.eqv_trans _
      (listQSum
        (fun k => -(coefficient k * weight (k + 1)))
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro k _hk
      refine Q'.eqv_trans _
        (coefficient k *
          (Q'.divPos (-(weight (k + 1))) (weight 0) hhead *
            weight 0)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _
        (coefficient k * (-(weight (k + 1)))) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.divPos_mul_eqv (-(weight (k + 1))) (weight 0) hhead)) ?_
      exact Q'.mul_neg_eqv _ _
    · exact listQSum_neg_local
        (fun k => coefficient k * weight (k + 1))
        (List.range n)

/-- Every in-range non-head row of the coordinate matrix evaluates to its
literal retained tail coefficient. -/
theorem finiteHeadCenteredLinearApply_succ
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (coefficient : Nat → Q') (i : Nat) (hi : i < n) :
    finiteLinearApply n
        (finiteHeadCenteredTransform weight hhead) coefficient (i + 1) ≈
      coefficient i := by
  unfold finiteLinearApply finiteHeadCenteredTransform
  refine Q'.eqv_trans _
    (listQSum
      (fun k => if i = k then coefficient k else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro k _hk
    by_cases hik : i = k
    · change coefficient k * (if i = k then 1 else 0) ≈
        (if i = k then coefficient k else 0)
      rw [if_pos hik, if_pos hik]
      exact Q'.mul_one_eqv _
    · change coefficient k * (if i = k then 1 else 0) ≈
        (if i = k then coefficient k else 0)
      rw [if_neg hik, if_neg hik]
      exact Q'.mul_zero_eqv _
  · exact listQSum_ite_single i coefficient (List.range n)
      (rangeNodupLocal n) (List.mem_range.mpr hi)

/-- On every full in-range index, finite application of the coordinate matrix
equals the already verified explicit centered lift. -/
theorem finiteHeadCenteredLinearApply_eqv_lift
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (coefficient : Nat → Q') :
    ∀ i, i < n + 1 →
      finiteLinearApply n
          (finiteHeadCenteredTransform weight hhead) coefficient i ≈
        finiteHeadCenteredLift n weight hhead coefficient i := by
  intro i hi
  cases i with
  | zero =>
      exact finiteHeadCenteredLinearApply_zero
        n weight hhead coefficient
  | succ i =>
      have hitail : i < n := by omega
      exact finiteHeadCenteredLinearApply_succ
        n weight hhead coefficient i hitail

/-! ## 2. Sparse column and diagonal formulas -/

/-- Summing against one column of the head-centering transform reads only
the head and the selected tail entry.  This sparse formula prevents exact
certificate checks from expanding a mostly-zero `(n+1)`-term sum. -/
theorem finiteHeadCenteredColumnSum
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (value : Nat → Q') (k : Nat) (hk : k < n) :
    listQSum
        (fun i => value i * finiteHeadCenteredTransform weight hhead i k)
        (List.range (n + 1)) ≈
      value 0 * Q'.divPos (-(weight (k + 1))) (weight 0) hhead +
        value (k + 1) := by
  rw [range_succ_shift_local]
  simp only [listQSum, listQSum_map_local,
    finiteHeadCenteredTransform]
  let tailValue : Nat → Q' := fun i => value (i + 1)
  have htail :
      listQSum
          (fun i => value (i + 1) * (if i = k then 1 else 0))
          (List.range n) ≈
        value (k + 1) := by
    refine Q'.eqv_trans _
      (listQSum
        (fun i => if k = i then tailValue i else 0)
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro i _hi
      by_cases hik : i = k
      · rw [if_pos hik, if_pos hik.symm]
        exact Q'.mul_one_eqv _
      · rw [if_neg hik, if_neg]
        · exact Q'.mul_zero_eqv _
        · exact fun hki => hik hki.symm
    · exact listQSum_ite_single k tailValue (List.range n)
        (rangeNodupLocal n) (List.mem_range.mpr hk)
  exact Q'.add_eqv_congr_left _ _ _ htail

/-- A diagonal entry of `A^T M A` for the head-centering transform depends
on only the four full-matrix entries at the head and selected tail indices. -/
theorem finiteHeadCenteredMatrix_diagonal
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (matrix : Nat → Nat → Q') (k : Nat) (hk : k < n) :
    finiteMatrixPullback (n + 1) matrix
        (finiteHeadCenteredTransform weight hhead) k k ≈
      let a := Q'.divPos (-(weight (k + 1))) (weight 0) hhead
      (matrix 0 0 * a + matrix 0 (k + 1)) * a +
        (matrix (k + 1) 0 * a + matrix (k + 1) (k + 1)) := by
  let transform := finiteHeadCenteredTransform weight hhead
  let a := Q'.divPos (-(weight (k + 1))) (weight 0) hhead
  have hinner : ∀ i,
      listQSum
          (fun j => matrix i j * (transform i k * transform j k))
          (List.range (n + 1)) ≈
        (matrix i 0 * transform i k) * a +
          matrix i (k + 1) * transform i k := by
    intro i
    refine Q'.eqv_trans _
      (listQSum
        (fun j => (matrix i j * transform i k) * transform j k)
        (List.range (n + 1))) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    · simpa only [transform, a] using
        (finiteHeadCenteredColumnSum n weight hhead
          (fun j => matrix i j * transform i k) k hk)
  refine Q'.eqv_trans _
    (listQSum
      (fun i =>
        (matrix i 0 * transform i k) * a +
          matrix i (k + 1) * transform i k)
      (List.range (n + 1))) _ ?_ ?_
  · unfold finiteMatrixPullback
    apply listQSum_congr_on
    intro i _hi
    exact hinner i
  · refine Q'.eqv_trans _
      (listQSum
        (fun i =>
          (matrix i 0 * a + matrix i (k + 1)) * transform i k)
        (List.range (n + 1))) _ ?_ ?_
    · apply listQSum_congr_on
      intro i _hi
      have hswap :
          (matrix i 0 * transform i k) * a ≈
            (matrix i 0 * a) * transform i k := by
        refine Q'.eqv_trans _
          (matrix i 0 * (transform i k * a)) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _
          (matrix i 0 * (a * transform i k)) _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_comm_eqv _ _)) ?_
        exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      exact Q'.eqv_trans _
        ((matrix i 0 * a) * transform i k +
          matrix i (k + 1) * transform i k) _
        (Q'.add_eqv_congr' hswap (Q'.eqv_refl _))
        (Q'.eqv_symm
          (Q'.add_mul_eqv
            (matrix i 0 * a) (matrix i (k + 1)) (transform i k)))
    · simpa only [transform, a] using
        (finiteHeadCenteredColumnSum n weight hhead
          (fun i => matrix i 0 * a + matrix i (k + 1)) k hk)

/-! ## 3. Generated reduced penalized matrices -/

/-- Canonical reduced upper-edge matrix obtained by pulling back
`qD-K+dd^T` along the positive-head centering transform. -/
def finiteHeadCenteredUpperMatrix
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q')
    (hhead : (0 : Q') < weight 0) : Nat → Nat → Q' :=
  finiteMatrixPullback (n + 1)
    (finiteUpperPenalizedMatrix q weight kernel)
    (finiteHeadCenteredTransform weight hhead)

/-- Canonical reduced lower-edge matrix obtained by pulling back
`qD+K+dd^T` along the positive-head centering transform. -/
def finiteHeadCenteredLowerMatrix
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q')
    (hhead : (0 : Q') < weight 0) : Nat → Nat → Q' :=
  finiteMatrixPullback (n + 1)
    (finiteLowerPenalizedMatrix q weight kernel)
    (finiteHeadCenteredTransform weight hhead)

/-- Exact quadratic identification for the generated reduced upper matrix. -/
theorem finiteHeadCenteredUpperMatrix_identify
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (finiteHeadCenteredUpperMatrix n q weight kernel hhead)
        coefficient ≈
      finitePenalizedReversibleQuadratic
        (n + 1) q weight kernel
        (finiteHeadCenteredLift n weight hhead coefficient) := by
  refine Q'.eqv_trans _
    (finiteMatrixQuadratic (n + 1)
      (finiteUpperPenalizedMatrix q weight kernel)
      (finiteLinearApply n
        (finiteHeadCenteredTransform weight hhead) coefficient)) _
    (finiteMatrixQuadratic_pullback
      (n + 1) n (finiteUpperPenalizedMatrix q weight kernel)
      (finiteHeadCenteredTransform weight hhead) coefficient) ?_
  refine Q'.eqv_trans _
    (finiteMatrixQuadratic (n + 1)
      (finiteUpperPenalizedMatrix q weight kernel)
      (finiteHeadCenteredLift n weight hhead coefficient)) _ ?_ ?_
  · exact finiteMatrixQuadratic_coefficient_congr
      (finiteHeadCenteredLinearApply_eqv_lift
        n weight hhead coefficient)
  · exact finiteUpperPenalizedMatrix_identify
      (n + 1) q weight kernel
      (finiteHeadCenteredLift n weight hhead coefficient)

/-- Exact quadratic identification for the generated reduced lower matrix. -/
theorem finiteHeadCenteredLowerMatrix_identify
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (finiteHeadCenteredLowerMatrix n q weight kernel hhead)
        coefficient ≈
      finiteLowerPenalizedReversibleQuadratic
        (n + 1) q weight kernel
        (finiteHeadCenteredLift n weight hhead coefficient) := by
  refine Q'.eqv_trans _
    (finiteMatrixQuadratic (n + 1)
      (finiteLowerPenalizedMatrix q weight kernel)
      (finiteLinearApply n
        (finiteHeadCenteredTransform weight hhead) coefficient)) _
    (finiteMatrixQuadratic_pullback
      (n + 1) n (finiteLowerPenalizedMatrix q weight kernel)
      (finiteHeadCenteredTransform weight hhead) coefficient) ?_
  refine Q'.eqv_trans _
    (finiteMatrixQuadratic (n + 1)
      (finiteLowerPenalizedMatrix q weight kernel)
      (finiteHeadCenteredLift n weight hhead coefficient)) _ ?_ ?_
  · exact finiteMatrixQuadratic_coefficient_congr
      (finiteHeadCenteredLinearApply_eqv_lift
        n weight hhead coefficient)
  · exact finiteLowerPenalizedMatrix_identify
      (n + 1) q weight kernel
      (finiteHeadCenteredLift n weight hhead coefficient)

/-- A positive head weight canonically generates the entire centered
two-sided restriction, including both reduced matrices and their identities. -/
def finiteCanonicalHeadCenteredRestriction
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q')
    (hhead : (0 : Q') < weight 0) :
    FiniteCenteredTwoSidedRestriction (n + 1) q weight kernel :=
  finiteHeadCenteredTwoSidedRestriction
    n q weight kernel hhead
    (finiteHeadCenteredUpperMatrix n q weight kernel hhead)
    (finiteHeadCenteredLowerMatrix n q weight kernel hhead)
    (finiteHeadCenteredUpperMatrix_identify n q weight kernel hhead)
    (finiteHeadCenteredLowerMatrix_identify n q weight kernel hhead)

end YMGap.Continuum.FiniteRationalHeadCenteredPullback

#print axioms
  YMGap.Continuum.FiniteRationalHeadCenteredPullback.finiteHeadCenteredLinearApply_eqv_lift
#print axioms
  YMGap.Continuum.FiniteRationalHeadCenteredPullback.finiteHeadCenteredUpperMatrix_identify
#print axioms
  YMGap.Continuum.FiniteRationalHeadCenteredPullback.finiteHeadCenteredLowerMatrix_identify
#print axioms
  YMGap.Continuum.FiniteRationalHeadCenteredPullback.finiteCanonicalHeadCenteredRestriction
