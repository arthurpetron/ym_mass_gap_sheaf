/-
# Canonical finite matrices for two-sided reversible contraction

This module gives literal matrix entries for the two rank-one-penalized forms

  q D - K + d d^T,     q D + K + d d^T,

and proves that their complete finite matrix quadratics are exactly the scalar
penalized quadratics used by the reversible contraction theorem.  An external
program may therefore produce LDL factors for these displayed entries; it is
not trusted to identify a different matrix with the physical form.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.FiniteRationalPenalizedMatrix

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

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

/-- The weighted diagonal entry `q D`. -/
def finiteScaledDiagonalMatrix
    (q : Q') (weight : Nat → Q') (row column : Nat) : Q' :=
  if row = column then q * weight row else 0

/-- Rank-one stationary matrix `d d^T`. -/
def finiteWeightRankOneMatrix
    (weight : Nat → Q') (row column : Nat) : Q' :=
  weight row * weight column

/-- Canonical upper-edge matrix `q D - K + d d^T`. -/
def finiteUpperPenalizedMatrix
    (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') (row column : Nat) : Q' :=
  (finiteScaledDiagonalMatrix q weight row column +
      -(kernel row column)) +
    finiteWeightRankOneMatrix weight row column

/-- Canonical lower-edge matrix `q D + K + d d^T`. -/
def finiteLowerPenalizedMatrix
    (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') (row column : Nat) : Q' :=
  (finiteScaledDiagonalMatrix q weight row column +
      kernel row column) +
    finiteWeightRankOneMatrix weight row column

/-- Matrix quadratic respects entrywise addition. -/
theorem finiteMatrixQuadratic_add
    (n : Nat) (left right : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (fun i j => left i j + right i j) coefficient ≈
      finiteMatrixQuadratic n left coefficient +
        finiteMatrixQuadratic n right coefficient := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun i =>
        listQSum
            (fun j =>
              (coefficient i * coefficient j) * left i j)
            (List.range n) +
          listQSum
            (fun j =>
              (coefficient i * coefficient j) * right i j)
            (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _hi
    refine Q'.eqv_trans _
      (listQSum
        (fun j =>
          (coefficient i * coefficient j) * left i j +
            (coefficient i * coefficient j) * right i j)
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      exact Q'.mul_add_eqv _ _ _
    · exact listQSum_add _ _ (List.range n)
  · exact listQSum_add _ _ (List.range n)

/-- Matrix quadratic respects entrywise negation. -/
theorem finiteMatrixQuadratic_neg
    (n : Nat) (matrix : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (fun i j => -(matrix i j)) coefficient ≈
      -(finiteMatrixQuadratic n matrix coefficient) := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun i =>
        -(listQSum
          (fun j =>
            (coefficient i * coefficient j) * matrix i j)
          (List.range n)))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _hi
    refine Q'.eqv_trans _
      (listQSum
        (fun j =>
          -((coefficient i * coefficient j) * matrix i j))
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      exact Q'.mul_neg_eqv _ _
    · exact listQSum_neg_local _ (List.range n)
  · exact listQSum_neg_local _ (List.range n)

/-- The quadratic of the literal scaled diagonal is `q` times the weighted
diagonal quadratic. -/
theorem finiteMatrixQuadratic_scaledDiagonal
    (n : Nat) (q : Q') (weight coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (finiteScaledDiagonalMatrix q weight) coefficient ≈
      q * finiteDiagonalQuadratic n weight coefficient := by
  unfold finiteMatrixQuadratic finiteScaledDiagonalMatrix
    finiteDiagonalQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun i =>
        q * ((coefficient i * coefficient i) * weight i))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i hi
    refine Q'.eqv_trans _
      ((coefficient i * coefficient i) * (q * weight i)) _ ?_ ?_
    · refine Q'.eqv_trans _
        (listQSum
          (fun j =>
            if i = j then
              (coefficient i * coefficient j) * (q * weight i)
            else 0)
          (List.range n)) _ ?_ ?_
      · apply listQSum_congr_on
        intro j _hj
        by_cases hij : i = j
        · subst j
          rw [if_pos (Eq.refl i)]
          rw [if_pos (Eq.refl i)]
          exact Q'.eqv_refl _
        · simp only [if_neg hij]
          exact Q'.mul_zero_eqv _
      · exact listQSum_ite_single i
          (fun j =>
            (coefficient i * coefficient j) * (q * weight i))
          (List.range n) (rangeNodupLocal n) hi
    · refine Q'.eqv_trans _ ((q * weight i) *
          (coefficient i * coefficient i)) _
        (Q'.mul_comm_eqv _ _) ?_
      refine Q'.eqv_trans _
        (q * (weight i * (coefficient i * coefficient i))) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      exact Q'.mul_eqv_congr_left q _ _
        (Q'.mul_comm_eqv _ _)
  · exact listQSum_mul_left q _ (List.range n)

/-- The quadratic of `d d^T` is the square of the weighted mean. -/
theorem finiteMatrixQuadratic_weightRankOne
    (n : Nat) (weight coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (finiteWeightRankOneMatrix weight) coefficient ≈
      finiteWeightedMean n weight coefficient *
        finiteWeightedMean n weight coefficient := by
  unfold finiteMatrixQuadratic finiteWeightRankOneMatrix finiteWeightedMean
  refine Q'.eqv_trans _
    (listQSum
      (fun i => listQSum
        (fun j =>
          (coefficient i * weight i) *
            (coefficient j * weight j))
        (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _hi
    apply listQSum_congr_on
    intro j _hj
    exact q_mul4_swap
      (coefficient i) (coefficient j) (weight i) (weight j)
  · exact listQSum_product
      (fun i => coefficient i * weight i)
      (fun j => coefficient j * weight j)
      (List.range n) (List.range n)

/-- The canonical upper-edge matrix quadratic is exactly the upper penalized
reversible quadratic. -/
theorem finiteUpperPenalizedMatrix_identify
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (finiteUpperPenalizedMatrix q weight kernel) coefficient ≈
      finitePenalizedReversibleQuadratic
        n q weight kernel coefficient := by
  unfold finiteUpperPenalizedMatrix
    finitePenalizedReversibleQuadratic
  refine Q'.eqv_trans _
    (finiteMatrixQuadratic n
        (fun i j =>
          finiteScaledDiagonalMatrix q weight i j + -(kernel i j))
        coefficient +
      finiteMatrixQuadratic n
        (finiteWeightRankOneMatrix weight) coefficient) _
    (finiteMatrixQuadratic_add n _ _ coefficient) ?_
  apply Q'.add_eqv_congr'
  · refine Q'.eqv_trans _
      (finiteMatrixQuadratic n
          (finiteScaledDiagonalMatrix q weight) coefficient +
        finiteMatrixQuadratic n
          (fun i j => -(kernel i j)) coefficient) _
      (finiteMatrixQuadratic_add n _ _ coefficient) ?_
    exact Q'.add_eqv_congr'
      (finiteMatrixQuadratic_scaledDiagonal n q weight coefficient)
      (finiteMatrixQuadratic_neg n kernel coefficient)
  · exact finiteMatrixQuadratic_weightRankOne n weight coefficient

/-- The canonical lower-edge matrix quadratic is exactly the lower penalized
reversible quadratic. -/
theorem finiteLowerPenalizedMatrix_identify
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q') (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (finiteLowerPenalizedMatrix q weight kernel) coefficient ≈
      finiteLowerPenalizedReversibleQuadratic
        n q weight kernel coefficient := by
  unfold finiteLowerPenalizedMatrix
    finiteLowerPenalizedReversibleQuadratic
  refine Q'.eqv_trans _
    (finiteMatrixQuadratic n
        (fun i j =>
          finiteScaledDiagonalMatrix q weight i j + kernel i j)
        coefficient +
      finiteMatrixQuadratic n
        (finiteWeightRankOneMatrix weight) coefficient) _
    (finiteMatrixQuadratic_add n _ _ coefficient) ?_
  apply Q'.add_eqv_congr'
  · refine Q'.eqv_trans _
      (finiteMatrixQuadratic n
          (finiteScaledDiagonalMatrix q weight) coefficient +
        finiteMatrixQuadratic n kernel coefficient) _
      (finiteMatrixQuadratic_add n _ _ coefficient) ?_
    exact Q'.add_eqv_congr'
      (finiteMatrixQuadratic_scaledDiagonal n q weight coefficient)
      (Q'.eqv_refl _)
  · exact finiteMatrixQuadratic_weightRankOne n weight coefficient

end YMGap.Continuum.FiniteRationalPenalizedMatrix

#print axioms
  YMGap.Continuum.FiniteRationalPenalizedMatrix.finiteMatrixQuadratic_scaledDiagonal
#print axioms
  YMGap.Continuum.FiniteRationalPenalizedMatrix.finiteMatrixQuadratic_weightRankOne
#print axioms
  YMGap.Continuum.FiniteRationalPenalizedMatrix.finiteUpperPenalizedMatrix_identify
#print axioms
  YMGap.Continuum.FiniteRationalPenalizedMatrix.finiteLowerPenalizedMatrix_identify
