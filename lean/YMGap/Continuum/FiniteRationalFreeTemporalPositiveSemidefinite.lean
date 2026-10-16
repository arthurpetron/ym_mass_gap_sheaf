/-
# Constructive positivity of the finite free temporal path

The free-endpoint temporal tridiagonal precision is the Gram matrix of the
literal forward-difference rows.  This module proves that entry identity by a
finite sparse-sum calculation and derives nonnegativity of its complete
rational quadratic form from the checked weighted-Gram theorem.

No Fourier modes, eigenvalues, determinant argument, Gaussian law, continuum
limit, or mass-gap statement is used or proved here.
-/

import YMGap.Continuum.FiniteRationalFreeHistoryQuadratic

namespace YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

local infix:50 " ≈ " => Q'.eqv

/-- Oriented incidence of one temporal bond with its two endpoint slices. -/
def freeTemporalDifference (bond time : Nat) : Q' :=
  if time = bond then -1 else if time = bond + 1 then 1 else 0

private theorem sum_indicator_present
    (bound selected : Nat) (value : Q') (hselected : selected < bound) :
    listQSum (fun index => if selected = index then value else 0)
        (List.range bound) ≈ value :=
  listQSum_ite_single selected (fun _index => value)
    (List.range bound) (rangeNodupLocal bound)
    (List.mem_range.mpr hselected)

private theorem sum_indicator_absent
    (bound selected : Nat) (value : Q') (hselected : bound ≤ selected) :
    listQSum (fun index => if selected = index then value else 0)
        (List.range bound) ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum (fun _index => (0 : Q')) (List.range bound)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index hindex
    have hne : selected ≠ index := by
      intro heq
      have hindexLt := List.mem_range.mp hindex
      omega
    rw [if_neg hne]
    exact Q'.eqv_refl _
  · exact listQSum_zero (List.range bound)

private theorem freeTemporalDifference_diagonal_sum
    (timeBonds time : Nat) (htime : time < timeBonds + 1) :
    listQSum
        (fun bond =>
          freeTemporalDifference bond time * freeTemporalDifference bond time)
        (List.range timeBonds) ≈
      freeTemporalDegree timeBonds time := by
  by_cases hzero : timeBonds = 0
  · subst timeBonds
    have htimeZero : time = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ htime)
    subst time
    unfold freeTemporalDegree
    rw [if_pos rfl]
    exact Q'.eqv_refl _
  · have hpositive : 0 < timeBonds := Nat.pos_of_ne_zero hzero
    unfold freeTemporalDegree
    rw [if_neg hzero]
    by_cases htimeZero : time = 0
    · subst time
      rw [if_pos (Or.inl rfl)]
      refine Q'.eqv_trans _
        (listQSum (fun bond => if 0 = bond then (1 : Q') else 0)
          (List.range timeBonds)) _ ?_ ?_
      · apply listQSum_congr_on
        intro bond _hbond
        unfold freeTemporalDifference
        by_cases hbond : 0 = bond
        · subst bond
          rw [if_pos rfl, if_pos rfl]
          decide
        · have hsucc : 0 ≠ bond + 1 := Nat.zero_ne_add_one bond
          rw [if_neg hbond, if_neg hsucc, if_neg hbond]
          exact Q'.zero_mul_eqv _
      · exact sum_indicator_present timeBonds 0 1 hpositive
    · by_cases htimeLast : time = timeBonds
      · subst time
        rw [if_pos (Or.inr rfl)]
        let selected := timeBonds - 1
        have hselected : selected < timeBonds := by
          exact Nat.sub_one_lt hzero
        refine Q'.eqv_trans _
          (listQSum
            (fun bond => if selected = bond then (1 : Q') else 0)
            (List.range timeBonds)) _ ?_ ?_
        · apply listQSum_congr_on
          intro bond hbond
          have hbondLt : bond < timeBonds := List.mem_range.mp hbond
          unfold freeTemporalDifference selected
          have hnotSelf : timeBonds ≠ bond :=
            (Nat.ne_of_lt hbondLt).symm
          rw [if_neg hnotSelf]
          by_cases hpred : timeBonds - 1 = bond
          · have hsucc : timeBonds = bond + 1 :=
              (Nat.sub_eq_iff_eq_add
                (Nat.succ_le_iff.mpr hpositive)).mp hpred
            rw [if_pos hsucc, if_pos hpred]
            exact Q'.one_mul_eqv _
          · have hsucc : timeBonds ≠ bond + 1 := by
              intro h
              exact hpred ((Nat.sub_eq_iff_eq_add
                (Nat.succ_le_iff.mpr hpositive)).mpr h)
            rw [if_neg hsucc, if_neg hpred]
            exact Q'.zero_mul_eqv _
        · exact sum_indicator_present timeBonds selected 1 hselected
      · have htimePositive : 0 < time := Nat.pos_of_ne_zero htimeZero
        have htimeLe : time ≤ timeBonds := Nat.le_of_lt_succ htime
        have htimeIn : time < timeBonds :=
          Nat.lt_of_le_of_ne htimeLe htimeLast
        rw [if_neg (not_or_intro htimeZero htimeLast)]
        let previous := time - 1
        have hprevious : previous < timeBonds := by
          unfold previous
          exact Nat.sub_lt_of_lt htimeIn
        refine Q'.eqv_trans _
          (listQSum
            (fun bond =>
              (if time = bond then (1 : Q') else 0) +
                (if previous = bond then (1 : Q') else 0))
            (List.range timeBonds)) _ ?_ ?_
        · apply listQSum_congr_on
          intro bond hbond
          have hbondLt : bond < timeBonds := List.mem_range.mp hbond
          unfold freeTemporalDifference previous
          by_cases hself : time = bond
          · subst bond
            have hnotPrevious : time - 1 ≠ time :=
              Nat.ne_of_lt (Nat.sub_one_lt htimeZero)
            rw [if_pos rfl, if_pos rfl, if_neg hnotPrevious]
            decide
          · rw [if_neg hself, if_neg hself]
            by_cases hpred : time - 1 = bond
            · have hsucc : time = bond + 1 :=
                (Nat.sub_eq_iff_eq_add
                  (Nat.succ_le_iff.mpr htimePositive)).mp hpred
              rw [if_pos hsucc, if_pos hpred]
              decide
            · have hsucc : time ≠ bond + 1 := by
                intro h
                exact hpred ((Nat.sub_eq_iff_eq_add
                  (Nat.succ_le_iff.mpr htimePositive)).mpr h)
              rw [if_neg hsucc, if_neg hpred]
              decide
        · refine Q'.eqv_trans _
            (listQSum (fun bond => if time = bond then (1 : Q') else 0)
                (List.range timeBonds) +
              listQSum (fun bond => if previous = bond then (1 : Q') else 0)
                (List.range timeBonds)) _
            (listQSum_add _ _ _) ?_
          exact Q'.eqv_trans _ (1 + 1) _
            (Q'.add_eqv_congr'
              (sum_indicator_present timeBonds time 1 htimeIn)
              (sum_indicator_present timeBonds previous 1 hprevious))
            (by decide)

private theorem freeTemporalDifference_forward_sum
    (timeBonds left : Nat) (hright : left + 1 < timeBonds + 1) :
    listQSum
        (fun bond =>
          freeTemporalDifference bond left *
            freeTemporalDifference bond (left + 1))
        (List.range timeBonds) ≈ -1 := by
  have hleft : left < timeBonds := by omega
  refine Q'.eqv_trans _
    (listQSum (fun bond => if left = bond then (-1 : Q') else 0)
      (List.range timeBonds)) _ ?_ ?_
  · apply listQSum_congr_on
    intro bond hbond
    have hbondLt : bond < timeBonds := List.mem_range.mp hbond
    unfold freeTemporalDifference
    by_cases hselected : left = bond
    · subst bond
      rw [if_pos rfl, if_pos rfl, if_neg (by omega), if_pos rfl]
      exact Q'.neg_mul_eqv 1 1
    · rw [if_neg hselected]
      by_cases hleftSucc : left = bond + 1
      · rw [if_pos hleftSucc]
        have hrightSelf : left + 1 ≠ bond := by omega
        have hrightSucc : left + 1 ≠ bond + 1 := by omega
        rw [if_neg hrightSelf, if_neg hrightSucc, if_neg hselected]
        exact Q'.mul_zero_eqv _
      · rw [if_neg hleftSucc]
        rw [if_neg hselected]
        exact Q'.zero_mul_eqv _
  · exact sum_indicator_present timeBonds left (-1) hleft

private theorem freeTemporalDifference_separated_sum
    (timeBonds left right : Nat)
    (hne : left ≠ right) (hforward : left + 1 ≠ right)
    (hbackward : right + 1 ≠ left) :
    listQSum
        (fun bond =>
          freeTemporalDifference bond left * freeTemporalDifference bond right)
        (List.range timeBonds) ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum (fun _bond => (0 : Q')) (List.range timeBonds)) _ ?_ ?_
  · apply listQSum_congr_on
    intro bond _hbond
    unfold freeTemporalDifference
    by_cases hleftSelf : left = bond
    · subst bond
      rw [if_pos rfl]
      have hrightSelf : right ≠ left := fun h => hne h.symm
      have hrightSucc : right ≠ left + 1 := fun h => hforward h.symm
      rw [if_neg hrightSelf, if_neg hrightSucc]
      exact Q'.mul_zero_eqv _
    · rw [if_neg hleftSelf]
      by_cases hleftSucc : left = bond + 1
      · rw [if_pos hleftSucc]
        have hrightSelf : right ≠ bond := by omega
        have hrightSucc : right ≠ bond + 1 := by omega
        rw [if_neg hrightSelf, if_neg hrightSucc]
        exact Q'.mul_zero_eqv _
      · rw [if_neg hleftSucc]
        exact Q'.zero_mul_eqv _
  · exact listQSum_zero (List.range timeBonds)

/-- Exact path-incidence Gram entry for the free temporal precision. -/
theorem freeTemporalDifference_gram
    (timeBonds left right : Nat)
    (hleft : left < timeBonds + 1) (hright : right < timeBonds + 1) :
    weightedGram (List.range timeBonds) (fun _bond => (1 : Q'))
        (fun time bond => freeTemporalDifference bond time) left right ≈
      freeTemporalPrecision timeBonds left right := by
  refine Q'.eqv_trans _
    (listQSum
      (fun bond =>
        freeTemporalDifference bond left * freeTemporalDifference bond right)
      (List.range timeBonds)) _ ?_ ?_
  · unfold weightedGram
    apply listQSum_congr
    intro bond
    exact Q'.one_mul_eqv _
  · unfold freeTemporalPrecision
    by_cases heq : left = right
    · subst right
      rw [if_pos rfl]
      exact freeTemporalDifference_diagonal_sum timeBonds left hleft
    · rw [if_neg heq]
      by_cases hforward : left + 1 = right
      · rw [if_pos (Or.inl hforward)]
        subst right
        exact freeTemporalDifference_forward_sum timeBonds left hright
      · by_cases hbackward : right + 1 = left
        · rw [if_pos (Or.inr hbackward)]
          subst left
          refine Q'.eqv_trans _ _ _
            (listQSum_congr
              (fun bond => Q'.mul_comm_eqv
                (freeTemporalDifference bond (right + 1))
                (freeTemporalDifference bond right))
              (List.range timeBonds))
            (freeTemporalDifference_forward_sum timeBonds right hleft)
        · rw [if_neg (not_or_intro hforward hbackward)]
          exact freeTemporalDifference_separated_sum
            timeBonds left right heq hforward hbackward

private theorem freeTemporalQuadratic_eq_weightedGram
    (timeBonds : Nat) (coefficient : Nat → Q') :
    finiteMatrixQuadratic (timeBonds + 1)
        (freeTemporalPrecision timeBonds) coefficient ≈
      weightedGramQuadratic
        (List.range (timeBonds + 1)) (List.range timeBonds)
        (fun _bond => (1 : Q'))
        (fun time bond => freeTemporalDifference bond time)
        coefficient := by
  unfold finiteMatrixQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm
      (freeTemporalDifference_gram timeBonds left right
        (List.mem_range.mp hleft) (List.mem_range.mp hright)))

/-- The complete finite free temporal path quadratic is nonnegative. -/
theorem freeTemporalQuadratic_nonnegative
    (timeBonds : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteMatrixQuadratic (timeBonds + 1)
      (freeTemporalPrecision timeBonds) coefficient := by
  exact Q'.le_trans' _ _ _
    (weightedGramQuadratic_nonnegative
      (List.range (timeBonds + 1)) (List.range timeBonds)
      (fun _bond => (1 : Q'))
      (fun time bond => freeTemporalDifference bond time)
      coefficient (fun _bond _hbond => Q'.zero_le_one))
    (Q'.ge_of_eqv
      (freeTemporalQuadratic_eq_weightedGram timeBonds coefficient))

end YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite

#print axioms YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite.freeTemporalDifference_gram
#print axioms YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite.freeTemporalQuadratic_nonnegative
