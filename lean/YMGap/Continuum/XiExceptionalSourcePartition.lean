/-
# Exact partition of the occurrence-pair source

The full product enumeration splits into inadmissible zero-weight pairs and
admissible pairs.  The admissible list then splits exactly into the already
bounded exceptional list and its nonexceptional complement.  All identities
retain occurrence multiplicities.
-/

import YMGap.Continuum.XiExceptionalFullSourceBound
import YMGap.Continuum.XiExceptionalFiberwiseInjection

namespace YMGap.Continuum.XiExceptionalSourcePartition

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def admissibleSourceCodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (MaskPair Gamma.length) :=
  (maskPairs Gamma.length).filter (sourceAdmissible Gamma qP b1 b2)

def nonexceptionalSourceCodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (MaskPair Gamma.length) :=
  (maskPairs Gamma.length).filter (fun pair =>
    sourceAdmissible Gamma qP b1 b2 pair &&
      !(exceptionalSourceCode Gamma b1 b2 pair))

theorem occurrencePairWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (pair : MaskPair Gamma.length) :
    (0 : Q') ≤ occurrencePairWeight w qP b1 b2 Gamma label pair := by
  unfold occurrencePairWeight
  exact Q'.mul_nonneg _ _
    (admissibleFamilyWeight_nonnegative hw _ label _)
    (admissibleFamilyWeight_nonnegative hw _ label _)

theorem occurrencePairWeight_zero_of_not_admissible
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (pair : MaskPair Gamma.length)
    (hbad : sourceAdmissible Gamma qP b1 b2 pair = false) :
    occurrencePairWeight w qP b1 b2 Gamma label pair ≈ 0 := by
  unfold sourceAdmissible at hbad
  unfold occurrencePairWeight admissibleFamilyWeight
  rw [← all_and, ← all_and]
  cases hLq : (leftFamily Gamma pair).all qP <;>
    cases hLb : (leftFamily Gamma pair).all (fun X => !(b1 X)) <;>
    cases hLc : familyCompatibleB (leftFamily Gamma pair) <;>
    cases hRq : (rightFamily Gamma pair).all qP <;>
    cases hRb : (rightFamily Gamma pair).all (fun X => !(b2 X)) <;>
    cases hRc : familyCompatibleB (rightFamily Gamma pair) <;>
    simp_all
  all_goals
    first
    | exact Q'.zero_mul_eqv _
    | exact Q'.mul_zero_eqv _

private theorem filter_filter_and (xs : List alpha) (p q : alpha → Bool) :
    (xs.filter p).filter q = xs.filter (fun x => p x && q x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;>
        simp only [List.filter_cons, hp, hq, Bool.false_eq_true,
          Bool.false_and, Bool.true_and, ↓reduceIte, ih]

private theorem qListSum_zero_of_pointwise (weight : alpha → Q') :
    ∀ xs : List alpha, (∀ x, x ∈ xs → weight x ≈ 0) →
      qListSum weight xs ≈ 0
  | [], _ => Q'.eqv_refl _
  | x :: xs, h => by
      simp only [qListSum_cons]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (h x List.mem_cons_self)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
      exact qListSum_zero_of_pointwise weight xs
        (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem admissible_filter_exceptional
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    (admissibleSourceCodes Gamma qP b1 b2).filter
        (exceptionalSourceCode Gamma b1 b2) =
      exceptionalSourceCodes Gamma qP b1 b2 := by
  unfold admissibleSourceCodes exceptionalSourceCodes
  exact filter_filter_and (maskPairs Gamma.length)
    (sourceAdmissible Gamma qP b1 b2)
    (exceptionalSourceCode Gamma b1 b2)

theorem admissible_filter_nonexceptional
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    (admissibleSourceCodes Gamma qP b1 b2).filter
        (fun pair => !(exceptionalSourceCode Gamma b1 b2 pair)) =
      nonexceptionalSourceCodes Gamma qP b1 b2 := by
  unfold admissibleSourceCodes nonexceptionalSourceCodes
  exact filter_filter_and (maskPairs Gamma.length)
    (sourceAdmissible Gamma qP b1 b2)
    (fun pair => !(exceptionalSourceCode Gamma b1 b2 pair))

theorem full_source_sum_eqv_admissible
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (maskPairs Gamma.length) ≈
      qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (admissibleSourceCodes Gamma qP b1 b2) := by
  have hpart := qListSum_filter_partition
    (occurrencePairWeight w qP b1 b2 Gamma label)
    (sourceAdmissible Gamma qP b1 b2) (maskPairs Gamma.length)
  have hzero : qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
      ((maskPairs Gamma.length).filter
        (fun pair => !(sourceAdmissible Gamma qP b1 b2 pair))) ≈ 0 := by
    apply qListSum_zero_of_pointwise
    intro pair hpair
    have hp := (List.mem_filter.mp hpair).2
    have hbad : sourceAdmissible Gamma qP b1 b2 pair = false := by
      cases h : sourceAdmissible Gamma qP b1 b2 pair
      · rfl
      · rw [h] at hp
        cases hp
    exact occurrencePairWeight_zero_of_not_admissible
      w qP b1 b2 Gamma label pair hbad
  unfold admissibleSourceCodes
  refine Q'.eqv_trans _ _ _ hpart ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hzero) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

theorem admissible_source_partition
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (admissibleSourceCodes Gamma qP b1 b2) ≈
      qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
          (exceptionalSourceCodes Gamma qP b1 b2) +
        qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
          (nonexceptionalSourceCodes Gamma qP b1 b2) := by
  have hpart := qListSum_filter_partition
    (occurrencePairWeight w qP b1 b2 Gamma label)
    (exceptionalSourceCode Gamma b1 b2)
    (admissibleSourceCodes Gamma qP b1 b2)
  rw [admissible_filter_exceptional,
    admissible_filter_nonexceptional] at hpart
  exact hpart

theorem restriction_product_eqv_exceptional_add_nonexceptional
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep) :
    XiR w (fun X => qP X && !(b1 X)) Gamma label *
        XiR w (fun X => qP X && !(b2 X)) Gamma label ≈
      qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
          (exceptionalSourceCodes Gamma qP b1 b2) +
        qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
          (nonexceptionalSourceCodes Gamma qP b1 b2) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (occurrencePairWeight_sum_eqv_restriction_product
        w qP b1 b2 Gamma label)) ?_
  exact Q'.eqv_trans _ _ _
    (full_source_sum_eqv_admissible w qP b1 b2 Gamma label)
    (admissible_source_partition w qP b1 b2 Gamma label)

#print axioms occurrencePairWeight_zero_of_not_admissible
#print axioms full_source_sum_eqv_admissible
#print axioms admissible_source_partition
#print axioms restriction_product_eqv_exceptional_add_nonexceptional

end YMGap.Continuum.XiExceptionalSourcePartition
