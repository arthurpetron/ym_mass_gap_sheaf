/-
# Distance decay of the SAME original signed connected numerator

Every retained common-root core is a literal animal connecting the two
probe roots. Its size is at least distance+1-M_left-M_right. Feeding this
PROVED geometric floor into the original partition-relative tail estimate
gives a coefficient proportional to s(w)^(distance+1-M_left-M_right), with
s(w)<1 under the explicit small-nome guard. No distance or counting premise
remains. The bound holds for every cutoff and every physical ambient list.

This is a finite original-numerator theorem with its SAME partition square.
Normalized cutoff/thermodynamic transport and actual reflected time-support
instances remain to be supplied before claiming operator time decay or gap.
Coupling and spacing-uniform continuum control are not claimed.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget
import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor

namespace YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabTwoProbeAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor (rootedAnimal_linf_size_floor)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

def minimumCoreSize {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right) : Nat :=
  linfDist P.animal.root Q.animal.root+1-totalProbeSize P Q

theorem connecting_core_size_floor {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (ids : List Nat) (ha : ids ∈ connectingAnchors extent left right ambient) :
    minimumCoreSize P Q ≤ ids.length := by
  let animal := augmentedAnimal P Q extent ids ((selected_sublist (connecting_selected ha)).nodup hn)
    (fun id hi => hphys id (selected_mem (connecting_selected ha) id hi)) (connecting_keep ha) (connecting_fixed ha)
  have h := rootedAnimal_linf_size_floor animal Q.animal.root (right_support_mem P Q extent ids _ Q.animal.root_mem)
  have bound := Nat.le_trans h (augmented_size_le P Q extent ids)
  change linfDist P.animal.root Q.animal.root+1 ≤ totalProbeSize P Q+ids.length at bound
  unfold minimumCoreSize
  omega

def distanceBudget {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (w : Q') (hd : heatRemainderBound w < 1) (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c d : Q') : Q' := twoProbeBudget P Q w hd hs c d (minimumCoreSize P Q)

theorem connectedNumerator_distance_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K extent : Nat) (p q : RatPoly) (c d : Q')
    (Ip : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Iq : Interval (boundaryCompleteSlabLinks extent).length q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (connectedNumerator w K extent ambient p q) ≤ distanceBudget P Q w hd hs c d * partitionSquare w K extent ambient :=
  connectedNumerator_tail_bound hw0 hw1 hsmall hd hs K extent p q c d Ip Iq left right P Q hl hr
    ambient (minimumCoreSize P Q) hn hphys (connecting_core_size_floor P Q extent ambient hn hphys)

/-- Full ORIGINAL interacting slab, every representation cutoff and extent. -/
theorem full_connectedNumerator_distance_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K extent : Nat) (p q : RatPoly) (c d : Q')
    (Ip : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Iq : Interval (boundaryCompleteSlabLinks extent).length q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) :
    Q'.abs (connectedNumerator w K extent (slabPhysicalFaceEdges extent) p q) ≤
      distanceBudget P Q w hd hs c d * partitionSquare w K extent (slabPhysicalFaceEdges extent) :=
  connectedNumerator_distance_bound hw0 hw1 hsmall hd hs K extent p q c d Ip Iq left right P Q hl hr
    (slabPhysicalFaceEdges extent) (CayleyParentInj.range_nodup _) (fun _ hi => hi)

end YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay

#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay.minimumCoreSize
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay.connecting_core_size_floor
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay.distanceBudget
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay.connectedNumerator_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay.full_connectedNumerator_distance_bound
