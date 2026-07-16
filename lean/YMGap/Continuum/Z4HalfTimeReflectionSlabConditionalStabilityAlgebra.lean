/-
# Normalized slab-versus-ambient stability algebra

The finite marked switch leaves a connected two-replica residue.  This file
identifies the four cell sums with the actual canonical numerators and divides
the cross-difference by the positive full and slab-supported partitions.  The
result is already a normalized probability estimate; the next module bounds
its literal connected residue geometrically.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
import YMGap.Continuum.Z4CanonicalOccurrenceStability
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalStabilityAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalLaw
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 1. Short names for the four cell masses and connected residue -/

def slabSupportedCylinderEventNumerator
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (slabSupportedCylinderEventFamilyList extent roots predicate)

def slabSupportedCylinderComplementNumerator
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (slabSupportedCylinderComplementFamilyList extent roots predicate)

def slabBoundaryCylinderEventNumerator
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (slabBoundaryCylinderEventFamilyList extent roots predicate)

def slabBoundaryCylinderComplementNumerator
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (slabBoundaryCylinderComplementFamilyList extent roots predicate)

def slabConnectedCylinderResidue
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  listQSum slabCylinderSourcePairWeight
    (connectedSlabCylinderSourcePairs
      (extent := extent) (roots := roots) (predicate := predicate))

private theorem filters_commute {A : Type}
    (first second : A → Bool) (xs : List A) :
    (xs.filter first).filter second =
      (xs.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

private theorem filter_and_eq_filter_filter {A : Type}
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

private theorem mul_eqv_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' := by
  exact Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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

/-! ## 2. Exact identification with the actual canonical numerators -/

theorem slabSupportedCylinderEventNumerator_eqv_restricted
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    slabSupportedCylinderEventNumerator extent roots predicate ≈
      anchorEventNumerator (extent + 1)
        (canonicalSlabRestrictedEvent extent
          (slabMarkedCylinderEvent roots predicate)) := by
  unfold slabSupportedCylinderEventNumerator
    slabSupportedCylinderEventFamilyList
    canonicalSlabSupportedFamilies anchorEventNumerator
    canonicalSlabRestrictedEvent
  rw [filter_and_eq_filter_filter]
  exact Q'.eqv_refl _

theorem anchorCylinderEventNumerator_eqv_supported_add_boundary
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    anchorEventNumerator (extent + 1)
        (slabMarkedCylinderEvent roots predicate) ≈
      slabSupportedCylinderEventNumerator extent roots predicate +
        slabBoundaryCylinderEventNumerator extent roots predicate := by
  let weight :=
    canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
  let ambient := canonicalCompatibleAmbientFamilies (extent + 1)
  let support := canonicalFamilySlabSupportedB extent
  let event := slabMarkedCylinderEvent roots predicate
  have hsplit := listQSum_filter_partition weight support
    (ambient.filter event)
  rw [filters_commute event support ambient,
    filters_commute event (fun family => !(support family)) ambient]
    at hsplit
  simpa [anchorEventNumerator, slabSupportedCylinderEventNumerator,
    slabBoundaryCylinderEventNumerator,
    slabSupportedCylinderEventFamilyList,
    slabBoundaryCylinderEventFamilyList,
    canonicalSlabSupportedFamilies, canonicalSlabBoundaryFamilies,
    weight, ambient, support, event] using hsplit

theorem canonicalSlabSupportNumerator_eqv_cylinder_cells
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    anchorEventNumerator (extent + 1)
        (canonicalFamilySlabSupportedB extent) ≈
      slabSupportedCylinderEventNumerator extent roots predicate +
        slabSupportedCylinderComplementNumerator
          extent roots predicate := by
  unfold anchorEventNumerator slabSupportedCylinderEventNumerator
    slabSupportedCylinderComplementNumerator
    slabSupportedCylinderEventFamilyList
    slabSupportedCylinderComplementFamilyList
    canonicalSlabSupportedFamilies
  exact listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (slabMarkedCylinderEvent roots predicate)
    ((canonicalCompatibleAmbientFamilies (extent + 1)).filter
      (canonicalFamilySlabSupportedB extent))

theorem canonicalSlabBoundaryNumerator_eqv_cylinder_cells
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    canonicalSlabBoundaryNumerator extent ≈
      slabBoundaryCylinderEventNumerator extent roots predicate +
        slabBoundaryCylinderComplementNumerator
          extent roots predicate := by
  unfold canonicalSlabBoundaryNumerator
    slabBoundaryCylinderEventNumerator
    slabBoundaryCylinderComplementNumerator
    slabBoundaryCylinderEventFamilyList
    slabBoundaryCylinderComplementFamilyList
  exact listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (slabMarkedCylinderEvent roots predicate)
    (canonicalSlabBoundaryFamilies extent)

/-! ## 3. The actual cross-difference is the four-cell cross-difference -/

theorem anchorSlabCylinderCrossDifference_eqv_cells
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    anchorEventNumerator (extent + 1)
          (slabMarkedCylinderEvent roots predicate) *
        anchorEventNumerator (extent + 1)
          (canonicalFamilySlabSupportedB extent) -
      anchorEventNumerator (extent + 1)
          (canonicalSlabRestrictedEvent extent
            (slabMarkedCylinderEvent roots predicate)) *
        anchorCanonicalPartition (extent + 1) ≈
      slabBoundaryCylinderEventNumerator extent roots predicate *
          slabSupportedCylinderComplementNumerator extent roots predicate -
        slabBoundaryCylinderComplementNumerator extent roots predicate *
          slabSupportedCylinderEventNumerator extent roots predicate := by
  let SE := slabSupportedCylinderEventNumerator extent roots predicate
  let SC := slabSupportedCylinderComplementNumerator extent roots predicate
  let BE := slabBoundaryCylinderEventNumerator extent roots predicate
  let BC := slabBoundaryCylinderComplementNumerator extent roots predicate
  have hfull : anchorEventNumerator (extent + 1)
      (slabMarkedCylinderEvent roots predicate) ≈ SE + BE :=
    anchorCylinderEventNumerator_eqv_supported_add_boundary
      extent roots predicate
  have hsupport : anchorEventNumerator (extent + 1)
      (canonicalFamilySlabSupportedB extent) ≈ SE + SC :=
    canonicalSlabSupportNumerator_eqv_cylinder_cells
      extent roots predicate
  have hrestricted : anchorEventNumerator (extent + 1)
      (canonicalSlabRestrictedEvent extent
        (slabMarkedCylinderEvent roots predicate)) ≈ SE :=
    Q'.eqv_symm
      (slabSupportedCylinderEventNumerator_eqv_restricted
        extent roots predicate)
  have hboundary : canonicalSlabBoundaryNumerator extent ≈ BE + BC :=
    canonicalSlabBoundaryNumerator_eqv_cylinder_cells
      extent roots predicate
  have hpartition : anchorCanonicalPartition (extent + 1) ≈
      (SE + SC) + (BE + BC) := by
    refine Q'.eqv_trans _
      (anchorEventNumerator (extent + 1)
          (canonicalFamilySlabSupportedB extent) +
        canonicalSlabBoundaryNumerator extent) _
      (anchorCanonicalPartition_eqv_slabSupport_add_boundary extent) ?_
    exact Q'.add_eqv_congr' hsupport hboundary
  refine Q'.eqv_trans _
    ((SE + BE) * (SE + SC) - SE * ((SE + SC) + (BE + BC))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (mul_eqv_congr_local hfull hsupport)
      (Q'.neg_eqv_congr _ _
        (mul_eqv_congr_local hrestricted hpartition))
  · change
      ((SE + BE) * (SE + SC) +
          -(SE * ((SE + SC) + (BE + BC)))) ≈
        BE * SC + -(BC * SE)
    exact slab_cross_algebra SE SC BE BC

theorem anchorSlabCylinderCrossDifference_le_connectedResidue
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    anchorEventNumerator (extent + 1)
          (slabMarkedCylinderEvent roots predicate) *
        anchorEventNumerator (extent + 1)
          (canonicalFamilySlabSupportedB extent) -
      anchorEventNumerator (extent + 1)
          (canonicalSlabRestrictedEvent extent
            (slabMarkedCylinderEvent roots predicate)) *
        anchorCanonicalPartition (extent + 1) ≤
      slabConnectedCylinderResidue extent roots predicate := by
  have hcell := slabBoundaryEvent_supportedComplement_le
    extent roots predicate
  have hsub :
      slabBoundaryCylinderEventNumerator extent roots predicate *
          slabSupportedCylinderComplementNumerator extent roots predicate -
        slabBoundaryCylinderComplementNumerator extent roots predicate *
          slabSupportedCylinderEventNumerator extent roots predicate ≤
      slabConnectedCylinderResidue extent roots predicate := by
    exact Q'.sub_le_of_le_add hcell
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (anchorSlabCylinderCrossDifference_eqv_cells
        extent roots predicate)) hsub

/-! ## 4. Positive normalization of the literal residue -/

theorem slabFullSupportPartitionProduct_pos (extent : Nat) :
    (0 : Q') <
      anchorEventNumerator (extent + 1)
          (canonicalFamilySlabSupportedB extent) *
        anchorCanonicalPartition (extent + 1) :=
  Q'.mul_pos (canonicalSlabSupportNumerator_pos extent)
    (anchorCanonicalPartition_pos (extent + 1))

def normalizedSlabConnectedCylinderResidue
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : Q' :=
  Q'.divPos (slabConnectedCylinderResidue extent roots predicate)
    (anchorEventNumerator (extent + 1)
        (canonicalFamilySlabSupportedB extent) *
      anchorCanonicalPartition (extent + 1))
    (slabFullSupportPartitionProduct_pos extent)

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

/-- Normalized, exact same-volume comparison.  No unproved limit or boundary
estimate occurs: the right side is the literal connected-pair residue divided
by the two actual positive partition functions. -/
theorem anchorAmbientProbability_sub_givenSlab_le_normalizedResidue
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    anchorEventProbability (extent + 1)
          (slabMarkedCylinderEvent roots predicate) -
        anchorCanonicalGivenSlabProbability extent
          (slabMarkedCylinderEvent roots predicate) ≤
      normalizedSlabConnectedCylinderResidue
        extent roots predicate := by
  let S := anchorEventNumerator (extent + 1)
    (canonicalFamilySlabSupportedB extent)
  let Z := anchorCanonicalPartition (extent + 1)
  let R := slabConnectedCylinderResidue extent roots predicate
  let epsilon := normalizedSlabConnectedCylinderResidue
    extent roots predicate
  have hcross := anchorSlabCylinderCrossDifference_le_connectedResidue
    extent roots predicate
  have hscale : epsilon * (S * Z) ≈ R := by
    unfold epsilon normalizedSlabConnectedCylinderResidue S Z R
    exact Q'.divPos_mul_eqv _ _
      (slabFullSupportPartitionProduct_pos extent)
  have hcrossScaled :
      anchorEventNumerator (extent + 1)
            (slabMarkedCylinderEvent roots predicate) * S -
        anchorEventNumerator (extent + 1)
            (canonicalSlabRestrictedEvent extent
              (slabMarkedCylinderEvent roots predicate)) * Z ≤
      epsilon * (S * Z) :=
    Q'.le_trans' _ _ _ hcross (Q'.ge_of_eqv hscale)
  unfold anchorEventProbability anchorCanonicalGivenSlabProbability
  exact divPos_sub_le_of_cross
    (anchorCanonicalPartition_pos (extent + 1))
    (canonicalSlabSupportNumerator_pos extent)
    hcrossScaled

#print axioms slabSupportedCylinderEventNumerator_eqv_restricted
#print axioms anchorCylinderEventNumerator_eqv_supported_add_boundary
#print axioms canonicalSlabSupportNumerator_eqv_cylinder_cells
#print axioms anchorSlabCylinderCrossDifference_eqv_cells
#print axioms anchorSlabCylinderCrossDifference_le_connectedResidue
#print axioms slabFullSupportPartitionProduct_pos
#print axioms anchorAmbientProbability_sub_givenSlab_le_normalizedResidue

end YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalStabilityAlgebra
