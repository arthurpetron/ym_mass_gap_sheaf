/-
# Physical-event disintegration of the expanded corrected-slab law

The literal expanded source carrier pairs each corrected-slab physical
labelling with every accepted fine-intertwiner witness above it.  The fiber
sum over those witnesses is already known to be exactly the production
physical summand.  This module proves the event-level consequence: every
Boolean event depending only on the physical labelling has exactly the same
unnormalized mass and normalized probability before and after the auxiliary
intertwiner coordinate is forgotten.

As a first application, the face-positive covariance controlled by the
paired-support peeling argument is identified with the ordinary Boolean
covariance of two face-spin events in the genuine corrected-slab physical
law.  No support-gas or Osterwalder--Schrader identification is asserted here.

Constructive contract: finite rational Fubini and Boolean filtering only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableBooleanCovariance

namespace YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedBooleanCovariance
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem divPos_numerator_eqv_local {p p' q : Q'}
    (hq : (0 : Q') < q) (hp : p ≈ p') :
    Q'.divPos p q hq ≈ Q'.divPos p' q hq := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ hp

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) : ∀ source : List A,
    listQSum (fun item => if event item then weight item else 0) source ≈
      listQSum weight (source.filter event)
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

/-! ## 1. Exact event-level disintegration -/

private theorem slabExpandedFineSourceBlock_masked_weight
    (D : SlabPhysicalData) (event : SlabLabelling → Bool)
    (physical : SlabLabelling) :
    listQSum
        (fun source =>
          if event source.1 then
            slabExpandedFineSourceWeight D source
          else 0)
        (slabExpandedFineSourceBlock D physical) ≈
      if event physical then D.physicalTerm physical else 0 := by
  unfold slabExpandedFineSourceBlock
  rw [listQSum_map]
  cases hevent : event physical with
  | false =>
      simp only [hevent, Bool.false_eq_true, if_false]
      exact listQSum_zero _
  | true =>
      simp only [hevent, if_true]
      exact retainedFineIntertwinerPhysicalFiberWeight_total D physical

/-- Forgetting the accepted intertwiner witness preserves the exact
unnormalized mass of every event depending only on the physical labelling. -/
theorem slabExpandedPhysicalEventMass_eqv
    (D : SlabPhysicalData) (event : SlabLabelling → Bool) :
    finiteWeightedEventMass
        (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        (fun source => event source.1) ≈
      finiteWeightedEventMass
        D.physicalLabellings D.physicalTerm event := by
  have hflat :
      listQSum
          (fun source =>
            if event source.1 then
              slabExpandedFineSourceWeight D source
            else 0)
          (slabExpandedFineSources D) ≈
        listQSum
          (fun physical =>
            listQSum
              (fun source =>
                if event source.1 then
                  slabExpandedFineSourceWeight D source
                else 0)
              (slabExpandedFineSourceBlock D physical))
          D.physicalLabellings := by
    unfold slabExpandedFineSources
    exact listQSum_flatMap _ _ _
  have hblocks :
      listQSum
          (fun physical =>
            listQSum
              (fun source =>
                if event source.1 then
                  slabExpandedFineSourceWeight D source
                else 0)
              (slabExpandedFineSourceBlock D physical))
          D.physicalLabellings ≈
        listQSum
          (fun physical =>
            if event physical then D.physicalTerm physical else 0)
          D.physicalLabellings := by
    apply listQSum_congr
    intro physical
    exact slabExpandedFineSourceBlock_masked_weight D event physical
  unfold finiteWeightedEventMass
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_mask_eq_filter_local
        (slabExpandedFineSourceWeight D)
        (fun source => event source.1)
        (slabExpandedFineSources D)))
    (Q'.eqv_trans _ _ _ hflat
      (Q'.eqv_trans _ _ _ hblocks
        (listQSum_mask_eq_filter_local
          D.physicalTerm event D.physicalLabellings)))

/-- The corresponding normalized event probabilities are identical. -/
theorem slabExpandedPhysicalEventProbability_eqv
    (D : SlabPhysicalData) (event : SlabLabelling → Bool) :
    finiteWeightedEventProbability
        (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        (fun source => event source.1) ≈
      finiteWeightedEventProbability
        D.physicalLabellings D.physicalTerm
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)
        event := by
  unfold finiteWeightedEventProbability
  exact divPos_numerator_eqv_local
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (slabExpandedPhysicalEventMass_eqv D event)

/-! ## 2. The covariance on the genuine physical slab law -/

def slabPhysicalFacePositiveB
    (faceId : Nat) (physical : SlabLabelling) : Bool :=
  decide (0 < physical faceId)

def slabPhysicalFaceBooleanCovariance
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  finiteWeightedBooleanCovariance
    D.physicalLabellings D.physicalTerm
    D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (slabPhysicalFacePositiveB rootFaceId)
    (slabPhysicalFacePositiveB targetFaceId)

/-- The paired-support covariance is already a covariance on the production
physical corrected-slab law; the fine-intertwiner witness coordinate has
been completely summed out. -/
theorem slabObservableFaceBooleanCovariance_eqv_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId ≈
      slabPhysicalFaceBooleanCovariance D rootFaceId targetFaceId := by
  have hjoint := slabExpandedPhysicalEventProbability_eqv D
    (fun physical =>
      slabPhysicalFacePositiveB rootFaceId physical &&
        slabPhysicalFacePositiveB targetFaceId physical)
  have hroot := slabExpandedPhysicalEventProbability_eqv D
    (slabPhysicalFacePositiveB rootFaceId)
  have htarget := slabExpandedPhysicalEventProbability_eqv D
    (slabPhysicalFacePositiveB targetFaceId)
  unfold slabObservableFaceBooleanCovariance
    slabPhysicalFaceBooleanCovariance
    finiteWeightedBooleanCovariance
    slabObservableRawFacePositiveB
    slabPhysicalFacePositiveB at *
  exact sub_eqv_both_local hjoint
    (mul_eqv_both_local hroot htarget)

/-- **Strict covariance on the genuine physical slab law.**  At the fixed
production coupling and lattice separation at least two, the face-spin
covariance is bounded by the cutoff- and slab-size-independent rational
`4096/5625 < 1`. -/
theorem slabPhysicalFaceBooleanCovariance_le_twoStepRate
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (hseparated : 2 ≤
      linfDist
        (slabPlaquetteAt (centralExtent half) rootFaceId)
        (slabPlaquetteAt (centralExtent half) targetFaceId)) :
    slabPhysicalFaceBooleanCovariance
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId ≤
      slabObservablePairedSupportTwoStepRate := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (slabObservableFaceBooleanCovariance_eqv_physical
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId)))
    (slabObservableFaceBooleanCovariance_le_twoStepRate
      cutoff half rootFaceId targetFaceId htarget hseparated)

#print axioms slabExpandedPhysicalEventMass_eqv
#print axioms slabExpandedPhysicalEventProbability_eqv
#print axioms slabPhysicalFacePositiveB
#print axioms slabPhysicalFaceBooleanCovariance
#print axioms slabObservableFaceBooleanCovariance_eqv_physical
#print axioms slabPhysicalFaceBooleanCovariance_le_twoStepRate

end YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
