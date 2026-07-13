/-
# Exact weights of the exceptional occurrence source

The finite source consists of pairs of occurrence masks.  This file proves
that its zero-extended pair weight sums exactly to the product of the two
restricted partition functions, including all duplicate ambient
occurrences.  On an admissible exceptional source member the zero-extended
weight is exactly the original product of family activities.
-/

import YMGap.Continuum.XiExceptionalPathEncoder

namespace YMGap.Continuum.XiExceptionalSourceWeight

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def occurrencePairWeight
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (pair : MaskPair Gamma.length) : Q' :=
  admissibleFamilyWeight w (fun X => qP X && !(b1 X)) label
      (leftFamily Gamma pair) *
    admissibleFamilyWeight w (fun X => qP X && !(b2 X)) label
      (rightFamily Gamma pair)

theorem occurrencePairWeight_sum_eqv_restriction_product
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (maskPairs Gamma.length) ≈
      XiR w (fun X => qP X && !(b1 X)) Gamma label *
        XiR w (fun X => qP X && !(b2 X)) Gamma label := by
  unfold maskPairs
  refine Q'.eqv_trans _ _ _
    (qListSum_flatMap (occurrencePairWeight w qP b1 b2 Gamma label)
      (fun left => (bitVectors Gamma.length).map
        (fun right => (left, right)))
      (bitVectors Gamma.length)) ?_
  have hinner : ∀ left, left ∈ bitVectors Gamma.length →
      qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
          ((bitVectors Gamma.length).map (fun right => (left, right))) ≈
        admissibleFamilyWeight w (fun X => qP X && !(b1 X)) label
            (selectByBits Gamma left) *
          XiR w (fun X => qP X && !(b2 X)) Gamma label := by
    intro left _
    rw [qListSum_map]
    unfold occurrencePairWeight leftFamily rightFamily
    refine Q'.eqv_trans _ _ _
      (qListSum_const_mul
        (admissibleFamilyWeight w (fun X => qP X && !(b1 X)) label
          (selectByBits Gamma left))
        (fun right => admissibleFamilyWeight w
          (fun X => qP X && !(b2 X)) label (selectByBits Gamma right))
        (bitVectors Gamma.length)) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (admissibleFamilyWeight_bitVectors_eqv_XiR w
        (fun X => qP X && !(b2 X)) Gamma label)
  refine Q'.eqv_trans _ _ _
    (qListSum_eqv_congr
      (fun left => qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        ((bitVectors Gamma.length).map (fun right => (left, right))))
      (fun left =>
        admissibleFamilyWeight w (fun X => qP X && !(b1 X)) label
            (selectByBits Gamma left) *
          XiR w (fun X => qP X && !(b2 X)) Gamma label)
      (bitVectors Gamma.length) hinner) ?_
  refine Q'.eqv_trans _ _ _
    (qListSum_mul_const
      (fun left => admissibleFamilyWeight w
        (fun X => qP X && !(b1 X)) label (selectByBits Gamma left))
      (XiR w (fun X => qP X && !(b2 X)) Gamma label)
      (bitVectors Gamma.length)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (admissibleFamilyWeight_bitVectors_eqv_XiR w
      (fun X => qP X && !(b1 X)) Gamma label)

theorem occurrencePairWeight_eq_source_activity
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (pair : MaskPair Gamma.length)
    (hadmiss : sourceAdmissible Gamma qP b1 b2 pair = true) :
    occurrencePairWeight w qP b1 b2 Gamma label pair =
      familyActivity w (leftFamily Gamma pair) label *
        familyActivity w (rightFamily Gamma pair) label := by
  unfold sourceAdmissible at hadmiss
  have hsides := (Bool.and_eq_true _ _).mp hadmiss
  have hleft := (Bool.and_eq_true _ _).mp hsides.1
  have hleftPred := (Bool.and_eq_true _ _).mp hleft.1
  have hright := (Bool.and_eq_true _ _).mp hsides.2
  have hrightPred := (Bool.and_eq_true _ _).mp hright.1
  have hleftAll : (leftFamily Gamma pair).all
      (fun X => qP X && !(b1 X)) = true := by
    rw [← all_and]
    exact (Bool.and_eq_true _ _).mpr hleftPred
  have hrightAll : (rightFamily Gamma pair).all
      (fun X => qP X && !(b2 X)) = true := by
    rw [← all_and]
    exact (Bool.and_eq_true _ _).mpr hrightPred
  unfold occurrencePairWeight admissibleFamilyWeight
  rw [hleftAll, hleft.2, hrightAll, hright.2]
  rfl

theorem occurrencePairWeight_eq_source_activity_of_mem
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (pair : MaskPair Gamma.length)
    (hmem : pair ∈ exceptionalSourceCodes Gamma qP b1 b2) :
    occurrencePairWeight w qP b1 b2 Gamma label pair =
      familyActivity w (leftFamily Gamma pair) label *
        familyActivity w (rightFamily Gamma pair) label :=
  occurrencePairWeight_eq_source_activity w qP b1 b2 Gamma label pair
    (exceptionalSourceFactsOfMem Gamma qP b1 b2 pair hmem).source_admissible

#print axioms occurrencePairWeight_sum_eqv_restriction_product
#print axioms occurrencePairWeight_eq_source_activity
#print axioms occurrencePairWeight_eq_source_activity_of_mem

end YMGap.Continuum.XiExceptionalSourceWeight
