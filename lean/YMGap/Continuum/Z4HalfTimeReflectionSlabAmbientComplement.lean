/-
# Exact ambient complement decomposition for the corrected slab

The corrected-slab ensemble is the ambient corner-box ensemble conditioned on
vanishing excitation outside the slab.  This file records the complementary
finite list and splits both the full partition and every pulled-back observable
sum exactly into supported and complement pieces.

There is no estimate in this module.  The top-boundary carrier tail controls
the complement only after a connected-component switching argument.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal complementary list and its two sums -/

def ambientSlabComplementLabellings (K extent : Nat) :
    List EdgeLabelling :=
  (boundedEdgeLabellings K
    (List.range (plaquetteEdgeCount (extent + 1)))).filter
      (fun target => !(ambientSlabSupportedB extent target))

def ambientSlabComplementPhysicalPartition
    (w : Q') (K extent : Nat) : Q' :=
  listQSum
    (parametricKPhysicalTerm w K (extent + 1))
    (ambientSlabComplementLabellings K extent)

def ambientFullPulledBackWeightedSum
    (w : Q') (K extent : Nat)
    (observable : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun target =>
      observable (ambientToSlabPhysical extent target) *
        parametricKPhysicalTerm w K (extent + 1) target)
    (boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount (extent + 1))))

def ambientSlabComplementWeightedSum
    (w : Q') (K extent : Nat)
    (observable : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun target =>
      observable (ambientToSlabPhysical extent target) *
        parametricKPhysicalTerm w K (extent + 1) target)
    (ambientSlabComplementLabellings K extent)

/-! ## 2. Exact full = supported + complement identities -/

theorem parametricKPhysicalPartition_eq_supported_add_complement
    (w : Q') (K extent : Nat) :
    parametricKPhysicalPartition w K (extent + 1) ≈
      ambientSlabSupportedPhysicalPartition w K extent +
        ambientSlabComplementPhysicalPartition w K extent := by
  unfold parametricKPhysicalPartition
    ambientSlabSupportedPhysicalPartition
    ambientSlabSupportedLabellings
    ambientSlabComplementPhysicalPartition
    ambientSlabComplementLabellings
  exact listQSum_filter_partition
    (parametricKPhysicalTerm w K (extent + 1))
    (ambientSlabSupportedB extent)
    (boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount (extent + 1))))

theorem slabPartition_add_complement_eq_ambientFull
    (w : Q') (K extent : Nat) :
    slabParametricKPhysicalPartition w K extent +
        ambientSlabComplementPhysicalPartition w K extent ≈
      parametricKPhysicalPartition w K (extent + 1) := by
  refine Q'.eqv_trans _
    (ambientSlabSupportedPhysicalPartition w K extent +
      ambientSlabComplementPhysicalPartition w K extent) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (slabParametricKPhysicalPartition_eq_ambientSupported
        w K extent)
  · exact Q'.eqv_symm
      (parametricKPhysicalPartition_eq_supported_add_complement
        w K extent)

theorem ambientFullPulledBackWeightedSum_eq_supported_add_complement
    (w : Q') (K extent : Nat)
    (observable : EdgeLabelling -> Q') :
    ambientFullPulledBackWeightedSum w K extent observable ≈
      ambientSlabSupportedWeightedSum w K extent observable +
        ambientSlabComplementWeightedSum w K extent observable := by
  unfold ambientFullPulledBackWeightedSum
    ambientSlabSupportedWeightedSum
    ambientSlabSupportedLabellings
    ambientSlabComplementWeightedSum
    ambientSlabComplementLabellings
  exact listQSum_filter_partition
    (fun target =>
      observable (ambientToSlabPhysical extent target) *
        parametricKPhysicalTerm w K (extent + 1) target)
    (ambientSlabSupportedB extent)
    (boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount (extent + 1))))

theorem slabWeighted_add_complement_eq_ambientFull
    (w : Q') (K extent : Nat)
    (observable : EdgeLabelling -> Q') :
    slabWeightedPhysicalSum w K extent observable +
        ambientSlabComplementWeightedSum w K extent observable ≈
      ambientFullPulledBackWeightedSum w K extent observable := by
  refine Q'.eqv_trans _
    (ambientSlabSupportedWeightedSum w K extent observable +
      ambientSlabComplementWeightedSum w K extent observable) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (slabWeightedPhysicalSum_eq_ambientSupported
        w K extent observable)
  · exact Q'.eqv_symm
      (ambientFullPulledBackWeightedSum_eq_supported_add_complement
        w K extent observable)

/-! ## 3. Positivity of the omitted partition mass -/

private theorem listQSum_nonnegative_local {A : Type}
    (weight : A -> Q') (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ items : List A, (0 : Q') ≤ listQSum weight items
  | [] => Q'.le_refl' 0
  | head :: tail => Q'.zero_le_add _ _
      (hweight head) (listQSum_nonnegative_local weight hweight tail)

theorem ambientSlabComplementPhysicalPartition_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K extent : Nat) :
    (0 : Q') ≤
      ambientSlabComplementPhysicalPartition w K extent := by
  unfold ambientSlabComplementPhysicalPartition
  exact listQSum_nonnegative_local _
    (parametricKPhysicalTerm_nonnegative hw K (extent + 1)) _

#print axioms parametricKPhysicalPartition_eq_supported_add_complement
#print axioms slabPartition_add_complement_eq_ambientFull
#print axioms ambientFullPulledBackWeightedSum_eq_supported_add_complement
#print axioms slabWeighted_add_complement_eq_ambientFull
#print axioms ambientSlabComplementPhysicalPartition_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientComplement
