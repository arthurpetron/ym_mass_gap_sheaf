/-
An exact obstruction to obtaining a multi-coordinate positive-time sector from
the repository's actual three-slice non-unit reference weight.

The two raw observables below are distinct cyclic translates of a one-slice
character tensor.  Thus they are the two basis candidates forced on the first
nontrivial character-tensor span.  For every carrier module which genuinely
makes `halfReferenceWeight 3` into a Wilson GNS datum, however, their exact
two-by-two Gram matrix is the all-ones matrix.  Its determinant is zero and
cyclic translation identifies the two modes in the GNS quotient.

This banks the obstruction without replacing the Wilson weight by an Ising or
auxiliary finite-state model: the current pure-product `ReferenceWeight`
substrate has only the total-character state coordinate.  A strict transfer
eigenvalue therefore cannot be obtained by merely taking the linear span of
cyclic character-tensor representatives.  The file also checks the candidate
`lambda = 1/2`: scalar multiplication separates the unit-norm mode, while the
actual cyclic translate remains its identical quotient class.
-/

import YMGap.Continuum.MultiSliceWilsonPositiveTimePilot

namespace YMGap.Continuum.CharacterTensorSpanPositiveTimePilot

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.E2ProductFunctional
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.MultiSliceWilsonPositiveTimePilot
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The hypotheses of any honest Wilson module on the actual non-unit
three-slice reference weight.  This is a bundle of laws, not an existence
assumption: every result below is a universal no-go for such a module. -/
structure CompatibleThreeSliceCarrier : Type where
  M : WilsonGNSData.CarrierModule (prodAlg (fun _ => realEdge) 3)
  elin_congr : ∀ {a b}, M.veq a b →
    ((halfReferenceWeight 3).E_Λ a) ≈ ((halfReferenceWeight 3).E_Λ b)
  elin_add : ∀ a b,
    ((halfReferenceWeight 3).E_Λ (M.add a b)) ≈
      ((halfReferenceWeight 3).E_Λ a + (halfReferenceWeight 3).E_Λ b)
  elin_smul : ∀ (s : Q') a,
    ((halfReferenceWeight 3).E_Λ (M.smul s a)) ≈
      (s * (halfReferenceWeight 3).E_Λ a)
  hconj : ∀ a b,
    ((halfReferenceWeight 3).E_Λ
      ((prodAlg (fun _ => realEdge) 3).mul
        ((prodAlg (fun _ => realEdge) 3).star a) b)) ≈
    ((halfReferenceWeight 3).E_Λ
      ((prodAlg (fun _ => realEdge) 3).mul
        ((prodAlg (fun _ => realEdge) 3).star b) a))

abbrev CompatibleThreeSliceCarrier.wilson (C : CompatibleThreeSliceCarrier) :
    WilsonGNSData (prodAlg (fun _ => realEdge) 3) :=
  WilsonGNSData.ofReferenceWeight (halfReferenceWeight 3) C.M
    C.elin_congr C.elin_add C.elin_smul C.hconj

abbrev CompatibleThreeSliceCarrier.gns (C : CompatibleThreeSliceCarrier) :
    GNSData := C.wilson.toGNSData

/-! ## Two distinct character-tensor representatives -/

/-- Character insertion on slice zero. -/
def sliceZeroCharacter : Nat → Q' := fun i => if i = 0 then -1 else 1

/-- Its genuine one-step cyclic translate. -/
def translatedCharacter : Nat → Q' := rotate3 sliceZeroCharacter

theorem character_tensors_raw_distinct :
    translatedCharacter ≠ sliceZeroCharacter := by
  intro h
  have h0 := congrFun h 0
  exact (by decide : ¬ ((1 : Q') = (-1 : Q'))) h0

/-- Both distinct representatives have the same total character, the only
state coordinate exposed by `halfReferenceWeight 3`. -/
theorem sliceZeroCharacter_total :
    threeSliceTotal sliceZeroCharacter ≈ -1 := by decide

theorem translatedCharacter_total :
    threeSliceTotal translatedCharacter ≈ -1 := by decide

/-! ## Exact actual Wilson Gram matrix -/

theorem character_tensor_gram_00 (C : CompatibleThreeSliceCarrier) :
    C.gns.B sliceZeroCharacter sliceZeroCharacter ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (compatible_threeSlice_Wilson_form_rankOne C.M C.elin_congr C.elin_add
      C.elin_smul C.hconj sliceZeroCharacter sliceZeroCharacter) ?_
  decide

theorem character_tensor_gram_01 (C : CompatibleThreeSliceCarrier) :
    C.gns.B sliceZeroCharacter translatedCharacter ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (compatible_threeSlice_Wilson_form_rankOne C.M C.elin_congr C.elin_add
      C.elin_smul C.hconj sliceZeroCharacter translatedCharacter) ?_
  decide

theorem character_tensor_gram_10 (C : CompatibleThreeSliceCarrier) :
    C.gns.B translatedCharacter sliceZeroCharacter ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (compatible_threeSlice_Wilson_form_rankOne C.M C.elin_congr C.elin_add
      C.elin_smul C.hconj translatedCharacter sliceZeroCharacter) ?_
  decide

theorem character_tensor_gram_11 (C : CompatibleThreeSliceCarrier) :
    C.gns.B translatedCharacter translatedCharacter ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (compatible_threeSlice_Wilson_form_rankOne C.M C.elin_congr C.elin_add
      C.elin_smul C.hconj translatedCharacter translatedCharacter) ?_
  decide

private theorem mul_eqv_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- The exact determinant of the proposed two-coordinate state Gram matrix is
zero.  This is the machine-checked rank-one obstruction. -/
theorem character_tensor_gram_determinant_zero
    (C : CompatibleThreeSliceCarrier) :
    C.gns.B sliceZeroCharacter sliceZeroCharacter *
        C.gns.B translatedCharacter translatedCharacter +
      -(C.gns.B sliceZeroCharacter translatedCharacter *
        C.gns.B translatedCharacter sliceZeroCharacter) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (mul_eqv_congr (character_tensor_gram_00 C)
        (character_tensor_gram_11 C))
      (Q'.neg_eqv_congr _ _
        (mul_eqv_congr (character_tensor_gram_01 C)
          (character_tensor_gram_10 C)))) ?_
  decide

/-! ## Quotient collapse and the failed strict eigenvalue -/

/-- Cyclic time identifies the two distinct raw character tensors in every
honest Wilson GNS quotient on the actual three-slice weight. -/
theorem translated_character_same_physical_class
    (C : CompatibleThreeSliceCarrier) :
    C.gns.qmk translatedCharacter = C.gns.qmk sliceZeroCharacter := by
  apply Quotient.sound
  exact compatible_threeSlice_rotation_radical C.M C.elin_congr C.elin_add
    C.elin_smul C.hconj sliceZeroCharacter

/-- The exact half-scaled character has squared distance `1/4` from the
unit-norm character mode. -/
theorem half_scaled_character_distance_quarter
    (C : CompatibleThreeSliceCarrier) :
    C.gns.B
      (C.gns.sub (C.gns.smul half sliceZeroCharacter) sliceZeroCharacter)
      (C.gns.sub (C.gns.smul half sliceZeroCharacter) sliceZeroCharacter) ≈
        Q'.mkPos 1 4 (by decide) := by
  let D := C.gns
  have hnorm : D.B sliceZeroCharacter sliceZeroCharacter ≈ 1 :=
    character_tensor_gram_00 C
  have haa : D.B (D.smul half sliceZeroCharacter)
      (D.smul half sliceZeroCharacter) ≈
        Q'.mkPos 1 4 (by decide) := by
    refine Q'.eqv_trans _ _ _
      (D.B_smul_left half sliceZeroCharacter
        (D.smul half sliceZeroCharacter)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _
        (D.B_smul_right half sliceZeroCharacter sliceZeroCharacter)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _
        (Q'.mul_eqv_congr_left half _ _ hnorm)) ?_
    decide
  have hab : D.B (D.smul half sliceZeroCharacter) sliceZeroCharacter ≈
      half := by
    refine Q'.eqv_trans _ _ _
      (D.B_smul_left half sliceZeroCharacter sliceZeroCharacter) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half _ _ hnorm) (by decide)
  refine Q'.eqv_trans _ _ _
    (D.B_sub_diag_expand (D.smul half sliceZeroCharacter)
      sliceZeroCharacter) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' haa (Q'.neg_eqv_congr _ _ hab))
      (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hab) hnorm)) ?_
  decide

/-- Hence multiplication by the strict candidate `1/2` genuinely separates
the nonzero character mode in the actual GNS quotient. -/
theorem half_scaled_character_separates
    (C : CompatibleThreeSliceCarrier) :
    C.gns.qmk (C.gns.smul half sliceZeroCharacter) ≠
      C.gns.qmk sliceZeroCharacter := by
  intro h
  have hr : C.gns.rad (C.gns.smul half sliceZeroCharacter)
      sliceZeroCharacter := Quotient.exact h
  have hzero : C.gns.B
      (C.gns.sub (C.gns.smul half sliceZeroCharacter) sliceZeroCharacter)
      (C.gns.sub (C.gns.smul half sliceZeroCharacter) sliceZeroCharacter) ≈ 0 := hr
  have hquarter : Q'.mkPos 1 4 (by decide) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (half_scaled_character_distance_quarter C)) hzero
  exact (by decide : ¬ (Q'.mkPos 1 4 (by decide) ≈ (0 : Q'))) hquarter

theorem half_strict_window : (0 : Q') < half ∧ half < (1 : Q') := by decide

/-- The actual cyclic character translate therefore cannot satisfy the strict
`lambda = 1/2` eigen-equation.  Time is quotient-trivial on this raw
two-character span, while half-scaling is not. -/
theorem no_half_eigen_on_character_tensor_span
    (C : CompatibleThreeSliceCarrier) :
    C.gns.qmk translatedCharacter ≠
      C.gns.qmk (C.gns.smul half sliceZeroCharacter) := by
  intro h
  apply half_scaled_character_separates C
  exact h.symm.trans (translated_character_same_physical_class C)

end YMGap.Continuum.CharacterTensorSpanPositiveTimePilot

#print axioms YMGap.Continuum.CharacterTensorSpanPositiveTimePilot.character_tensors_raw_distinct
#print axioms YMGap.Continuum.CharacterTensorSpanPositiveTimePilot.character_tensor_gram_determinant_zero
#print axioms YMGap.Continuum.CharacterTensorSpanPositiveTimePilot.translated_character_same_physical_class
#print axioms YMGap.Continuum.CharacterTensorSpanPositiveTimePilot.half_scaled_character_separates
#print axioms YMGap.Continuum.CharacterTensorSpanPositiveTimePilot.no_half_eigen_on_character_tensor_span
