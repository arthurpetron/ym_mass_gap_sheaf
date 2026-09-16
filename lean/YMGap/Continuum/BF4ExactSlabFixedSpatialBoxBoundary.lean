/-
# Fixed-support spatial boundary comparison for the original chart action

A fixed connected box carrier covers the supplied polynomial's actual
links. Its size and link count remain unchanged when the chart grows or
its temporal boundaries recede. The aligned mask separation forces each
active original core to pay the spatial margin, less the fixed carrier
size. The existing signed determinant estimate then cancels both original
partitions, without a volume-dependent reciprocal penalty.

Interval and syntactic locality certificates are explicit inputs here;
the actual reflected-probe compiler supplies them downstream. No spatial
limit, general-nome estimate, OS norm bound or continuum gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction
import YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
import YMGap.Continuum.BF4ExactSlabUniformCoreBudget
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion (activeAnchors)
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.BF4ExactSlabActiveCoreCount (countPrefactor)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

def carrierSize (n : Nat) : Nat := (n*n*n*n)*6

/-- Counts only the fixed support box, never the ambient chart. -/
def boxAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (n : Nat) : Q' :=
  (probePrefactor w hd ((n*n*n*n)*24) *
    Q'.ofNat (2^carrierSize n * 625^carrierSize n)) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs)

theorem shifted_budget_factor (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (n space time depth : Nat) (hn : 0<n) :
    Q'.eqv (summedBoundaryBudget (shiftedBoxProbe n space time hn) w hd hs depth)
      (boxAmplitude w hd hs n * (entropyRate 625 (adjustedCoreRate w hd))^depth) := by
  unfold summedBoundaryBudget countPrefactor
  rw [shiftedBoxLinks_length, shiftedBoxProbe_size]
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
    (fun i => if i = 0 then probePrefactor w hd ((n*n*n*n)*24)
      else if i = 1 then Q'.ofNat (2^carrierSize n * 625^carrierSize n)
      else if i = 2 then (entropyRate 625 (adjustedCoreRate w hd))^depth
      else Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs))

private theorem origin_spatial {base : Nat} (hb : 0<base) : originFace ∈ spatialFaces base := by
  apply (spatialFaces_mem_iff base originFace).mpr
  exact ⟨hb, hb, hb, rfl, by decide⟩

theorem active_core_size_floor (base r d H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n)
    {anchor : List Nat}
    (ha : anchor ∈ activeAnchors (chartExtent base (r+d) H t)
      ((boxLinks n).map (shiftLink (r+d+1) timeOrigin)) (keep base r d H t)
      (chartIds base (r+d) H t)) : r+1-carrierSize n ≤ anchor.length := by
  have h := active_core_linf_floor (distance := r+1)
    (shiftedBoxProbe n (r+d+1) timeOrigin hn)
    (chartIds_nodup base (r+d) H t) (fun _ hi => chartIds_physical hi) ha (by
      intro id hi ho
      exact omitted_separation base r d H t timeOrigin (origin_spatial hb) hi
        ((keep_eq_false base r d H t id).mp ho))
  rw [shiftedBoxProbe_size] at h
  unfold carrierSize
  omega

theorem determinant_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K base r d H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (chartExtent base (r+d) H t)).length p c)
    (hl : LinkLocal (chartExtent base (r+d) H t)
      ((boxLinks n).map (shiftLink (r+d+1) timeOrigin)) p) :
    Q'.abs (mixedNumerator w K (chartExtent base (r+d) H t) (keep base r d H t) p
      (chartIds base (r+d) H t)) ≤
      (((c+c)*boxAmplitude w hd hs n) *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize n)) *
        mixedPartition w K (chartExtent base (r+d) H t) (keep base r d H t)
          (chartIds base (r+d) H t) := by
  have h := mixedNumerator_tail_bound hw0 hw1 hsmall hd hs K (chartExtent base (r+d) H t)
    (keep base r d H t) p c P _ (shiftedBoxProbe n (r+d+1) timeOrigin hn) hl
    (chartIds base (r+d) H t) (r+1-carrierSize n) (chartIds_nodup base (r+d) H t)
    (fun _ hi => chartIds_physical hi)
    (fun _ ha => active_core_size_floor base r d H t timeOrigin n hb hn ha)
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (c+c) _ _ (shifted_budget_factor w hd hs n _ _ _ hn))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

/-- Normalized bound retaining the given actual interval/locality data. -/
theorem finiteValue_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (base r d H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (chartExtent base (r+d) H t)).length p c)
    (hl : LinkLocal (chartExtent base (r+d) H t)
      ((boxLinks n).map (shiftLink (r+d+1) timeOrigin)) p) (stage : Nat) :
    Q'.abs (finiteValue w hw0 hw1 (chartExtent base (r+d) H t)
      (chartIds base (r+d) H t) (fun _ hi => chartIds_physical hi) p stage +
      -(finiteValue w hw0 hw1 (chartExtent base (r+d) H t) (insideIds base r d H t)
        (insideIds_physical base r d H t) p stage)) ≤
      ((c+c)*boxAmplitude w hd hs n) *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize n) := by
  apply finite_comparison_bound w hw0 hw1 (chartExtent base (r+d) H t)
    (chartIds base (r+d) H t) (fun _ hi => chartIds_physical hi)
    (insideIds base r d H t) (insideIds_physical base r d H t) p _ stage
  exact determinant_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs
    (headCutoff w+stage) base r d H t timeOrigin n hb hn p c P hl

end YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary.carrierSize
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary.boxAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary.shifted_budget_factor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary.active_core_size_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary.determinant_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary.finiteValue_bound
