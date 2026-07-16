/-
# Arbitrary-cutoff normalized slab stability algebra

The marked slab switch is now weighted by the exact finite-cutoff,
coupling-parametric spin-summed support activity.  This file identifies its
four cells with the literal compatible-gas numerators and divides the cross
difference by the two actual positive partition functions.  The remaining
right side is the connected carrier residue treated by the uniform tail.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
import YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingSwitchSummation
import YMGap.Continuum.Z4CanonicalOccurrenceStability
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingSwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The four literal finite-cutoff cell masses -/

def couplingSlabSupportedCylinderEventNumerator
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (slabSupportedCylinderEventFamilyList extent roots predicate)

def couplingSlabSupportedCylinderComplementNumerator
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (slabSupportedCylinderComplementFamilyList extent roots predicate)

def couplingSlabBoundaryCylinderEventNumerator
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (slabBoundaryCylinderEventFamilyList extent roots predicate)

def couplingSlabBoundaryCylinderComplementNumerator
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (slabBoundaryCylinderComplementFamilyList extent roots predicate)

def couplingSlabBoundaryNumerator
    (coupling : Q') (cutoff extent : Nat) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (canonicalSlabBoundaryFamilies extent)

private theorem filters_commute {A : Type}
    (first second : A → Bool) (source : List A) :
    (source.filter first).filter second =
      (source.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

private theorem filter_and_eq_filter_filter {A : Type}
    (first second : A → Bool) (source : List A) :
    source.filter (fun item => first item && second item) =
      (source.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

private theorem mul_eqv_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 2. Exact identification with compatible-gas numerators -/

theorem couplingSlabSupportedCylinderEventNumerator_eqv_restricted
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    couplingSlabSupportedCylinderEventNumerator
        coupling cutoff extent roots predicate ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
        (canonicalSlabRestrictedEvent extent
          (slabMarkedCylinderEvent roots predicate)) := by
  unfold couplingSlabSupportedCylinderEventNumerator
    couplingParametricKCompatibleSupportEventNumerator
    slabSupportedCylinderEventFamilyList
    canonicalSlabSupportedFamilies canonicalSlabRestrictedEvent
  rw [filter_and_eq_filter_filter]
  exact Q'.eqv_refl _

theorem couplingCylinderEventNumerator_eqv_supported_add_boundary
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
        (slabMarkedCylinderEvent roots predicate) ≈
      couplingSlabSupportedCylinderEventNumerator
          coupling cutoff extent roots predicate +
        couplingSlabBoundaryCylinderEventNumerator
          coupling cutoff extent roots predicate := by
  let weight := couplingParametricKSupportFamilyActivity
    coupling cutoff (extent + 1)
  let ambient := canonicalCompatibleAmbientFamilies (extent + 1)
  let support := canonicalFamilySlabSupportedB extent
  let event := slabMarkedCylinderEvent roots predicate
  have hsplit := listQSum_filter_partition weight support
    (ambient.filter event)
  rw [filters_commute event support ambient,
    filters_commute event (fun family => !(support family)) ambient]
    at hsplit
  simpa [couplingParametricKCompatibleSupportEventNumerator,
    couplingSlabSupportedCylinderEventNumerator,
    couplingSlabBoundaryCylinderEventNumerator,
    slabSupportedCylinderEventFamilyList,
    slabBoundaryCylinderEventFamilyList,
    canonicalSlabSupportedFamilies, canonicalSlabBoundaryFamilies,
    weight, ambient, support, event] using hsplit

theorem couplingSlabSupportNumerator_eqv_cylinder_cells
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
        (canonicalFamilySlabSupportedB extent) ≈
      couplingSlabSupportedCylinderEventNumerator
          coupling cutoff extent roots predicate +
        couplingSlabSupportedCylinderComplementNumerator
          coupling cutoff extent roots predicate := by
  unfold couplingParametricKCompatibleSupportEventNumerator
    couplingSlabSupportedCylinderEventNumerator
    couplingSlabSupportedCylinderComplementNumerator
    slabSupportedCylinderEventFamilyList
    slabSupportedCylinderComplementFamilyList
    canonicalSlabSupportedFamilies
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (slabMarkedCylinderEvent roots predicate)
    ((canonicalCompatibleAmbientFamilies (extent + 1)).filter
      (canonicalFamilySlabSupportedB extent))

theorem couplingSlabBoundaryNumerator_eqv_cylinder_cells
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    couplingSlabBoundaryNumerator coupling cutoff extent ≈
      couplingSlabBoundaryCylinderEventNumerator
          coupling cutoff extent roots predicate +
        couplingSlabBoundaryCylinderComplementNumerator
          coupling cutoff extent roots predicate := by
  unfold couplingSlabBoundaryNumerator
    couplingSlabBoundaryCylinderEventNumerator
    couplingSlabBoundaryCylinderComplementNumerator
    slabBoundaryCylinderEventFamilyList
    slabBoundaryCylinderComplementFamilyList
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (slabMarkedCylinderEvent roots predicate)
    (canonicalSlabBoundaryFamilies extent)

theorem couplingCompatiblePartition_eqv_slabSupport_add_boundary
    (coupling : Q') (cutoff extent : Nat) :
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (extent + 1) ≈
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent) +
        couplingSlabBoundaryNumerator coupling cutoff extent := by
  unfold couplingParametricKCompatibleSupportGasPartition
    couplingParametricKCompatibleSupportEventNumerator
    couplingSlabBoundaryNumerator canonicalSlabBoundaryFamilies
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (extent + 1))
    (canonicalFamilySlabSupportedB extent)
    (canonicalCompatibleAmbientFamilies (extent + 1))

/-! ## 3. Four-cell cross cancellation -/

private def slabCrossL : RingNormaliser.PolyExpr :=
  let SE := RingNormaliser.PolyExpr.var 0
  let SC := RingNormaliser.PolyExpr.var 1
  let BE := RingNormaliser.PolyExpr.var 2
  let BC := RingNormaliser.PolyExpr.var 3
  .add (.mul (.add SE BE) (.add SE SC))
    (.neg (.mul SE (.add (.add SE SC) (.add BE BC))))

private def slabCrossR : RingNormaliser.PolyExpr :=
  let SE := RingNormaliser.PolyExpr.var 0
  let SC := RingNormaliser.PolyExpr.var 1
  let BE := RingNormaliser.PolyExpr.var 2
  let BC := RingNormaliser.PolyExpr.var 3
  .add (.mul BE SC) (.neg (.mul BC SE))

private theorem slabCross_normal :
    RingNormaliser.normalize slabCrossL =
      RingNormaliser.normalize slabCrossR := by decide

private theorem slab_cross_algebra (SE SC BE BC : Q') :
    (SE + BE) * (SE + SC) +
        -(SE * ((SE + SC) + (BE + BC))) ≈
      BE * SC + -(BC * SE) := by
  simpa [slabCrossL, slabCrossR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      slabCrossL slabCrossR slabCross_normal
      (fun | 0 => SE | 1 => SC | 2 => BE | _ => BC))

theorem couplingSlabCylinderCrossDifference_eqv_cells
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (slabMarkedCylinderEvent roots predicate) *
        couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent) -
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalSlabRestrictedEvent extent
            (slabMarkedCylinderEvent roots predicate)) *
        couplingParametricKCompatibleSupportGasPartition
          coupling cutoff (extent + 1) ≈
      couplingSlabBoundaryCylinderEventNumerator
            coupling cutoff extent roots predicate *
          couplingSlabSupportedCylinderComplementNumerator
            coupling cutoff extent roots predicate -
        couplingSlabBoundaryCylinderComplementNumerator
            coupling cutoff extent roots predicate *
          couplingSlabSupportedCylinderEventNumerator
            coupling cutoff extent roots predicate := by
  let SE := couplingSlabSupportedCylinderEventNumerator
    coupling cutoff extent roots predicate
  let SC := couplingSlabSupportedCylinderComplementNumerator
    coupling cutoff extent roots predicate
  let BE := couplingSlabBoundaryCylinderEventNumerator
    coupling cutoff extent roots predicate
  let BC := couplingSlabBoundaryCylinderComplementNumerator
    coupling cutoff extent roots predicate
  have hfull : couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff (extent + 1)
      (slabMarkedCylinderEvent roots predicate) ≈ SE + BE :=
    couplingCylinderEventNumerator_eqv_supported_add_boundary
      coupling cutoff extent roots predicate
  have hsupport : couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff (extent + 1)
      (canonicalFamilySlabSupportedB extent) ≈ SE + SC :=
    couplingSlabSupportNumerator_eqv_cylinder_cells
      coupling cutoff extent roots predicate
  have hrestricted : couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff (extent + 1)
      (canonicalSlabRestrictedEvent extent
        (slabMarkedCylinderEvent roots predicate)) ≈ SE :=
    Q'.eqv_symm
      (couplingSlabSupportedCylinderEventNumerator_eqv_restricted
        coupling cutoff extent roots predicate)
  have hboundary : couplingSlabBoundaryNumerator
      coupling cutoff extent ≈ BE + BC :=
    couplingSlabBoundaryNumerator_eqv_cylinder_cells
      coupling cutoff extent roots predicate
  have hpartition : couplingParametricKCompatibleSupportGasPartition
      coupling cutoff (extent + 1) ≈
      (SE + SC) + (BE + BC) := by
    refine Q'.eqv_trans _
      (couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent) +
        couplingSlabBoundaryNumerator coupling cutoff extent) _
      (couplingCompatiblePartition_eqv_slabSupport_add_boundary
        coupling cutoff extent) ?_
    exact Q'.add_eqv_congr' hsupport hboundary
  refine Q'.eqv_trans _
    ((SE + BE) * (SE + SC) -
      SE * ((SE + SC) + (BE + BC))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (mul_eqv_congr_local hfull hsupport)
      (Q'.neg_eqv_congr _ _
        (mul_eqv_congr_local hrestricted hpartition))
  · change
      ((SE + BE) * (SE + SC) +
          -(SE * ((SE + SC) + (BE + BC)))) ≈
        BE * SC + -(BC * SE)
    exact slab_cross_algebra SE SC BE BC

theorem couplingSlabCylinderCrossDifference_le_connectedResidue
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (slabMarkedCylinderEvent roots predicate) *
        couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent) -
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalSlabRestrictedEvent extent
            (slabMarkedCylinderEvent roots predicate)) *
        couplingParametricKCompatibleSupportGasPartition
          coupling cutoff (extent + 1) ≤
      couplingSpinSummedSlabConnectedCylinderResidue
        coupling cutoff extent roots predicate := by
  have hcell :=
    couplingSpinSummedSlabBoundaryEvent_supportedComplement_le
      hcoupling cutoff extent roots predicate
  have hsub :
      couplingSlabBoundaryCylinderEventNumerator
            coupling cutoff extent roots predicate *
          couplingSlabSupportedCylinderComplementNumerator
            coupling cutoff extent roots predicate -
        couplingSlabBoundaryCylinderComplementNumerator
            coupling cutoff extent roots predicate *
          couplingSlabSupportedCylinderEventNumerator
            coupling cutoff extent roots predicate ≤
      couplingSpinSummedSlabConnectedCylinderResidue
        coupling cutoff extent roots predicate := by
    exact Q'.sub_le_of_le_add hcell
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSlabCylinderCrossDifference_eqv_cells
        coupling cutoff extent roots predicate)) hsub

/-! ## 4. Positive normalization -/

theorem couplingSlabFullSupportPartitionProduct_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) :
    (0 : Q') <
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent) *
        couplingParametricKCompatibleSupportGasPartition
          coupling cutoff (extent + 1) :=
  Q'.mul_pos
    (couplingParametricKCompatibleSlabSupportNumerator_pos
      hcoupling cutoff extent)
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff (extent + 1))

def couplingNormalizedSlabConnectedCylinderResidue
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  Q'.divPos
    (couplingSpinSummedSlabConnectedCylinderResidue
      coupling cutoff extent roots predicate)
    (couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
        (canonicalFamilySlabSupportedB extent) *
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (extent + 1))
    (couplingSlabFullSupportPartitionProduct_pos
      hcoupling cutoff extent)

private theorem divPos_sub_le_of_cross
    {targetNumerator targetPartition sourceNumerator sourcePartition
      epsilon : Q'}
    (htarget : (0 : Q') < targetPartition)
    (hsource : (0 : Q') < sourcePartition)
    (hcross :
      targetNumerator * sourcePartition -
          sourceNumerator * targetPartition ≤
        epsilon * (sourcePartition * targetPartition)) :
    Q'.divPos targetNumerator targetPartition htarget -
        Q'.divPos sourceNumerator sourcePartition hsource ≤
      epsilon := by
  have hadd :
      targetNumerator * sourcePartition ≤
        sourceNumerator * targetPartition +
          epsilon * (sourcePartition * targetPartition) :=
    le_add_of_sub_le_local hcross
  have hreorder :
      (sourceNumerator * targetPartition +
          epsilon * (sourcePartition * targetPartition)).eqv
        ((sourceNumerator + epsilon * sourcePartition) *
          targetPartition) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (sourceNumerator * targetPartition)
        (epsilon * (sourcePartition * targetPartition))
        ((epsilon * sourcePartition) * targetPartition)
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv epsilon sourcePartition targetPartition))) ?_
    exact Q'.eqv_symm
      (Q'.add_mul_eqv sourceNumerator
        (epsilon * sourcePartition) targetPartition)
  have hratio := divPos_le_divPos_of_cross_local
    targetNumerator targetPartition
    (sourceNumerator + epsilon * sourcePartition) sourcePartition
    htarget hsource
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreorder))
  have hcollapse := divPos_add_scaled_eqv
    sourceNumerator epsilon sourcePartition hsource
  have hprob :
      Q'.divPos targetNumerator targetPartition htarget ≤
        Q'.divPos sourceNumerator sourcePartition hsource + epsilon :=
    Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hcollapse)
  exact Q'.sub_le_of_le_add hprob

/-- Exact arbitrary-cutoff normalized comparison.  Its right side is the
literal connected two-replica residue divided by the two positive partition
functions. -/
theorem couplingAmbientProbability_sub_givenSlab_le_normalizedResidue
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (extent + 1)
          (slabMarkedCylinderEvent roots predicate) -
        couplingParametricKCompatibleGivenSlabProbability
          coupling hcoupling cutoff extent
          (slabMarkedCylinderEvent roots predicate) ≤
      couplingNormalizedSlabConnectedCylinderResidue
        coupling hcoupling cutoff extent roots predicate := by
  let S := couplingParametricKCompatibleSupportEventNumerator
    coupling cutoff (extent + 1)
    (canonicalFamilySlabSupportedB extent)
  let Z := couplingParametricKCompatibleSupportGasPartition
    coupling cutoff (extent + 1)
  let R := couplingSpinSummedSlabConnectedCylinderResidue
    coupling cutoff extent roots predicate
  let epsilon := couplingNormalizedSlabConnectedCylinderResidue
    coupling hcoupling cutoff extent roots predicate
  have hcross := couplingSlabCylinderCrossDifference_le_connectedResidue
    hcoupling cutoff extent roots predicate
  have hscale : epsilon * (S * Z) ≈ R := by
    unfold epsilon couplingNormalizedSlabConnectedCylinderResidue S Z R
    exact Q'.divPos_mul_eqv _ _
      (couplingSlabFullSupportPartitionProduct_pos
        hcoupling cutoff extent)
  have hcrossScaled :
      couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff (extent + 1)
            (slabMarkedCylinderEvent roots predicate) * S -
        couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff (extent + 1)
            (canonicalSlabRestrictedEvent extent
              (slabMarkedCylinderEvent roots predicate)) * Z ≤
      epsilon * (S * Z) :=
    Q'.le_trans' _ _ _ hcross (Q'.ge_of_eqv hscale)
  unfold couplingParametricKCompatibleSupportEventProbability
    couplingParametricKCompatibleGivenSlabProbability
  exact divPos_sub_le_of_cross
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff (extent + 1))
    (couplingParametricKCompatibleSlabSupportNumerator_pos
      hcoupling cutoff extent)
    hcrossScaled

#print axioms couplingSlabSupportedCylinderEventNumerator_eqv_restricted
#print axioms couplingCylinderEventNumerator_eqv_supported_add_boundary
#print axioms couplingSlabSupportNumerator_eqv_cylinder_cells
#print axioms couplingCompatiblePartition_eqv_slabSupport_add_boundary
#print axioms couplingSlabCylinderCrossDifference_eqv_cells
#print axioms couplingSlabCylinderCrossDifference_le_connectedResidue
#print axioms couplingSlabFullSupportPartitionProduct_pos
#print axioms couplingAmbientProbability_sub_givenSlab_le_normalizedResidue

end YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityAlgebra
