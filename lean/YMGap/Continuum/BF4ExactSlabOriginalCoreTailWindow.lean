/-
# Split the actual other-core remainder by its selected-support size

The short and large lists partition the EXISTING other-core list. All
original coefficients and their individual detached partition squares
are retained. The large subfamily has the explicit geometric budget at
every cutoff and margin. No sign is asserted for the short subfamily.
-/

import YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit
import YMGap.Continuum.BF4ExactSlabResummedSubfamilyBound

namespace YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit
open YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget
open YMGap.Continuum.BF4ExactSlabResummedSubfamilyBound
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabCancellationTailBudget
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def coreTerm (w : Q') (K margin : Nat) (ids : List Nat) : Q' :=
  connectedCoefficient w K (responseExtent margin)
    (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids *
    partitionSquare w K (responseExtent margin) (detachedIds (responseExtent margin)
      (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)) ids
      (slabPhysicalFaceEdges (responseExtent margin)))

def otherCores (margin : Nat) : List (List Nat) :=
  (largeConnectingAnchors (responseExtent margin) (edgesOf (sliceFace margin 0))
    (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)) 12).filter
      (fun ids => !(decide (ids = tubeIds margin)))

def shortOtherCores (threshold margin : Nat) : List (List Nat) :=
  (otherCores margin).filter (fun ids => decide (ids.length < threshold))

def largeOtherCores (threshold margin : Nat) : List (List Nat) :=
  (otherCores margin).filter (fun ids => !(decide (ids.length < threshold)))

def shortOtherRemainder (w : Q') (K threshold margin : Nat) : Q' :=
  listQSum (coreTerm w K margin) (shortOtherCores threshold margin)

def largeOtherRemainder (w : Q') (K threshold margin : Nat) : Q' :=
  listQSum (coreTerm w K margin) (largeOtherCores threshold margin)

private theorem sum_split {A : Type} (f : A → Q') (keep : A → Bool) (xs : List A) :
    listQSum f xs ≈ listQSum f (xs.filter keep) + listQSum f (xs.filter (fun x => !(keep x))) :=
  Q'.eqv_trans _ _ _ (listQSum_perm f (List.filter_append_perm keep xs).symm) (sum_append _ _ _)

/-- Exact partition of the prior signed remainder, preserving all multiplicities. -/
theorem otherCoreRemainder_split (w : Q') (K threshold margin : Nat) :
    otherCoreRemainder w K margin ≈
      shortOtherRemainder w K threshold margin + largeOtherRemainder w K threshold margin :=
  sum_split (coreTerm w K margin) (fun ids => decide (ids.length < threshold)) (otherCores margin)

theorem largeOtherCores_sublist (threshold margin : Nat) :
    (largeOtherCores threshold margin).Sublist
      (connectingAnchors (responseExtent margin) (edgesOf (sliceFace margin 0))
        (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin))) :=
  List.filter_sublist.trans (List.filter_sublist.trans List.filter_sublist)

theorem largeOtherCores_size {threshold margin : Nat} {ids : List Nat}
    (hi : ids ∈ largeOtherCores threshold margin) : threshold ≤ ids.length := by
  have hfalse : decide (ids.length < threshold) = false := by
    simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hi).2
  have hnot : ¬ ids.length < threshold := of_decide_eq_false hfalse
  omega

theorem shortOtherCores_window {threshold margin : Nat} {ids : List Nat}
    (hi : ids ∈ shortOtherCores threshold margin) :
    12 ≤ ids.length ∧ ids.length < threshold ∧ ids ≠ tubeIds margin := by
  have hother := (List.mem_filter.mp hi).1
  have hlarge := (List.mem_filter.mp hother).1
  have hfalse : decide (ids = tubeIds margin) = false := by
    simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hother).2
  exact ⟨of_decide_eq_true (List.mem_filter.mp hlarge).2,
    of_decide_eq_true (List.mem_filter.mp hi).2,
    of_decide_eq_false hfalse⟩

def tailCoefficient (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (threshold : Nat) : Q' :=
  (((2 : Q')*2+2*2)*probePrefactor w hd 8)*tailBudget 1562500 625 threshold (adjustedCoreRate w hd) hs

/-- The actual large other-core sum, not the entire numerator. -/
theorem largeOtherRemainder_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (K threshold margin : Nat) :
    Q'.abs (largeOtherRemainder w K threshold margin) ≤
      tailCoefficient w hd hs threshold * partitionSquare w K (responseExtent margin)
        (slabPhysicalFaceEdges (responseExtent margin)) := by
  have hc : countPrefactor (singletonCarrier (sliceFace margin 0))
      (singletonCarrier (sliceFace margin 3)) = 1562500 := by
    change 2^2*625^2=1562500
    decide
  have h := resummed_subfamily_tail hw0 hw1 hsmall hd hs K (responseExtent margin)
    (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) 2 2
    (lowerInterval margin) (upperInterval margin) _ _
    (singletonCarrier (sliceFace margin 0)) (singletonCarrier (sliceFace margin 3))
    (lower_link_local margin) (upper_link_local margin) _ threshold (CayleyParentInj.range_nodup _)
    (fun _ hi => hi) (largeOtherCores threshold margin) (largeOtherCores_sublist threshold margin)
    (fun _ hi => largeOtherCores_size hi)
  unfold twoProbeBudget at h
  rw [hc] at h
  exact h

end YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow

#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.coreTerm
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.otherCores
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.shortOtherCores
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.largeOtherCores
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.shortOtherRemainder
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.largeOtherRemainder
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.otherCoreRemainder_split
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.largeOtherCores_sublist
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.largeOtherCores_size
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.shortOtherCores_window
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.tailCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow.largeOtherRemainder_bound
