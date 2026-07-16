/-
# Exact cutoff-one conditional law of the corrected reflection slab

The corrected slab is the ambient corner ensemble conditioned on the event
that no occupied canonical polymer reaches an omitted top face.  The image
and cutoff-one component theorems prove the two unnormalised descriptions.
Here we identify their denominators, prove strict positivity, and record the
exact equality of the resulting physical and canonical conditional laws.

This file is algebraic.  It does not estimate the difference between this
conditioned law and the unconditioned ambient law; that is the boundary
switching problem treated next.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientComplement
import YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The supported ambient partition is a masked event numerator -/

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) : ∀ xs : List A,
    listQSum (fun item => if event item then weight item else 0) xs ≈
      listQSum weight (xs.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head with
      | false =>
          simp only [hevent, Bool.false_eq_true, if_false,
            List.filter_cons, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum weight (tail.filter event)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (listQSum_mask_eq_filter_local weight event tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [hevent, if_true, List.filter_cons, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_mask_eq_filter_local weight event tail)

/-- At cutoff one, the ambient partition restricted to corrected-slab
support is exactly the physical support-event numerator. -/
theorem ambientSlabSupportedPhysicalPartition_eqv_eventNumerator
    (extent : Nat) :
    ambientSlabSupportedPhysicalPartition
        anchorCoupling 1 extent ≈
      parametricKEventNumerator anchorCoupling 1 (extent + 1)
        (ambientSlabSupportedB extent) := by
  unfold ambientSlabSupportedPhysicalPartition
    ambientSlabSupportedLabellings
    parametricKEventNumerator parametricKEventTerm
  exact Q'.eqv_symm
    (listQSum_mask_eq_filter_local
      (parametricKPhysicalTerm anchorCoupling 1 (extent + 1))
      (ambientSlabSupportedB extent)
      (boundedEdgeLabellings 1
        (List.range (plaquetteEdgeCount (extent + 1)))))

/-- The literal corrected-slab partition is the cutoff-one physical
support-event numerator in the ambient corner box. -/
theorem slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
    (extent : Nat) :
    slabParametricKPhysicalPartition anchorCoupling 1 extent ≈
      parametricKEventNumerator anchorCoupling 1 (extent + 1)
        (ambientSlabSupportedB extent) := by
  exact Q'.eqv_trans _
    (ambientSlabSupportedPhysicalPartition anchorCoupling 1 extent) _
    (slabParametricKPhysicalPartition_eq_ambientSupported
      anchorCoupling 1 extent)
    (ambientSlabSupportedPhysicalPartition_eqv_eventNumerator extent)

/-- The same denominator after the exact cutoff-one component reindexing. -/
theorem slabParametricKPhysicalPartition_eqv_canonicalSupportNumerator
    (extent : Nat) :
    slabParametricKPhysicalPartition anchorCoupling 1 extent ≈
      anchorEventNumerator (extent + 1)
        (canonicalFamilySlabSupportedB extent) := by
  exact Q'.eqv_trans _
    (parametricKEventNumerator anchorCoupling 1 (extent + 1)
      (ambientSlabSupportedB extent)) _
    (slabParametricKPhysicalPartition_eqv_physicalSupportNumerator extent)
    (anchorPhysicalSlabSupportNumerator_eqv_canonical extent)

/-! ## 2. Strict positivity of both conditional denominators -/

theorem physicalSlabSupportNumerator_pos (extent : Nat) :
    (0 : Q') <
      parametricKEventNumerator anchorCoupling 1 (extent + 1)
        (ambientSlabSupportedB extent) := by
  exact Q'.pos_of_lt_of_le
    (slabParametricKPhysicalPartition_pos (by decide) 1 extent)
    (Q'.le_of_eqv
      (slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
        extent))

theorem canonicalSlabSupportNumerator_pos (extent : Nat) :
    (0 : Q') <
      anchorEventNumerator (extent + 1)
        (canonicalFamilySlabSupportedB extent) := by
  exact Q'.pos_of_lt_of_le
    (slabParametricKPhysicalPartition_pos (by decide) 1 extent)
    (Q'.le_of_eqv
      (slabParametricKPhysicalPartition_eqv_canonicalSupportNumerator
        extent))

/-! ## 3. Exact physical/canonical conditional-law equality -/

/-- The cutoff-one ambient physical law conditioned on corrected-slab
support, evaluated on a lifted canonical-family event. -/
def anchorPhysicalGivenSlabProbability
    (extent : Nat) (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (parametricKEventNumerator anchorCoupling 1 (extent + 1)
      (fun physical => ambientSlabSupportedB extent physical &&
        cutoffOneLiftedFamilyEvent (extent + 1) event physical))
    (parametricKEventNumerator anchorCoupling 1 (extent + 1)
      (ambientSlabSupportedB extent))
    (physicalSlabSupportNumerator_pos extent)

/-- The canonical compatible-polymer law conditioned on every occupied
polymer lying in the corrected slab. -/
def anchorCanonicalGivenSlabProbability
    (extent : Nat) (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (anchorEventNumerator (extent + 1)
      (canonicalSlabRestrictedEvent extent event))
    (anchorEventNumerator (extent + 1)
      (canonicalFamilySlabSupportedB extent))
    (canonicalSlabSupportNumerator_pos extent)

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (haEq : a ≈ a') (hbEq : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hbEq))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) haEq))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hbEq)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm haEq)))

/-- Exact cutoff-one identification of the physical and canonical
conditioned probability laws. -/
theorem anchorPhysicalGivenSlabProbability_eqv_canonical
    (extent : Nat) (event : List (List Nat) → Bool) :
    anchorPhysicalGivenSlabProbability extent event ≈
      anchorCanonicalGivenSlabProbability extent event := by
  unfold anchorPhysicalGivenSlabProbability
    anchorCanonicalGivenSlabProbability
  exact divPos_eqv_congr_local
    (physicalSlabSupportNumerator_pos extent)
    (canonicalSlabSupportNumerator_pos extent)
    (anchorPhysicalSlabRestrictedNumerator_eqv_canonical extent event)
    (anchorPhysicalSlabSupportNumerator_eqv_canonical extent)

/-! ## 4. Normalization checks -/

theorem anchorPhysicalGivenSlabProbability_true (extent : Nat) :
    anchorPhysicalGivenSlabProbability extent (fun _ => true) ≈ 1 := by
  unfold anchorPhysicalGivenSlabProbability
  have hevent :
      (fun physical => ambientSlabSupportedB extent physical &&
        cutoffOneLiftedFamilyEvent (extent + 1) (fun _ => true) physical) =
      ambientSlabSupportedB extent := by
    funext physical
    unfold cutoffOneLiftedFamilyEvent
    simp only [Bool.and_true]
  rw [hevent]
  unfold Q'.divPos
  exact Q'.mul_recipPos_eqv _ (physicalSlabSupportNumerator_pos extent)

theorem anchorCanonicalGivenSlabProbability_true (extent : Nat) :
    anchorCanonicalGivenSlabProbability extent (fun _ => true) ≈ 1 := by
  exact Q'.eqv_trans _
    (anchorPhysicalGivenSlabProbability extent (fun _ => true)) _
    (Q'.eqv_symm
      (anchorPhysicalGivenSlabProbability_eqv_canonical
        extent (fun _ => true)))
    (anchorPhysicalGivenSlabProbability_true extent)

#print axioms ambientSlabSupportedPhysicalPartition_eqv_eventNumerator
#print axioms slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
#print axioms slabParametricKPhysicalPartition_eqv_canonicalSupportNumerator
#print axioms physicalSlabSupportNumerator_pos
#print axioms canonicalSlabSupportNumerator_pos
#print axioms anchorPhysicalGivenSlabProbability_eqv_canonical
#print axioms anchorPhysicalGivenSlabProbability_true
#print axioms anchorCanonicalGivenSlabProbability_true

end YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalLaw
