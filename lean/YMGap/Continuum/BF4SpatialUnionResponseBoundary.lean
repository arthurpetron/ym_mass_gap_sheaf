/-
# Quantitative comparison with the actual embedded old response action

The full old response slab and the current selected chain are different
actions. The proved omitted-face distance, with the current fixed box
carrier of side seven, gives a growing active-core floor. The existing
signed determinant theorem then bounds their normalized finite expectation
difference at every heat cutoff headCutoff(w)+stage.

The rate and amplitude retain their actual nome dependence. Only the
fixed support size 6*7^4 is paid, not the ambient volume. This supplies
the analytic comparison needed by the three actual response moments;
no positive union-response or continuum conclusion is asserted here.
-/

import YMGap.Continuum.BF4SpatialUnionResponseGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl

namespace YMGap.Continuum.BF4SpatialUnionResponseBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (carrierSize boxAmplitude shifted_budget_factor)
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion (activeAnchors)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4SpatialUnionResponseGeometry

def depth (s : Nat) : Nat := s+1-carrierSize 7

theorem carrier_root (s : Nat) : (chartCarrier 1 (s+1) 3 (s+1)).animal.root = root s := by
  rw [chartCarrier_root, root_eq]
  have hspace : s+1+1 = s+2 := by omega
  have htime : paddedWidth 1 (s+1)+1+(s+1) = 3*s+7 := by unfold paddedWidth; omega
  simp only [shiftFace, shiftVertex, originFace, Nat.zero_add, hspace, htime]

theorem core_floor (s : Nat) {anchor : List Nat}
    (ha : anchor ∈ activeAnchors (targetExtent s) (chartLinks 1 (s+1) 3 (s+1))
      (keep s) (ambientIds s)) : depth s ≤ anchor.length := by
  have h := active_core_floor s (chartCarrier 1 (s+1) 3 (s+1)) (carrier_root s) ha
  rw [chartCarrier_size] at h
  change s+2 ≤ carrierSize 7+anchor.length at h
  unfold depth
  omega

theorem budget_factor (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (s : Nat) :
    Q'.eqv (summedBoundaryBudget (chartCarrier 1 (s+1) 3 (s+1)) w hd hs (depth s))
      (boxAmplitude w hd hs 7 * (entropyRate 625 (adjustedCoreRate w hd))^(depth s)) :=
  shifted_budget_factor w hd hs (boxSize 1 3) ((s+1)+1)
    (paddedWidth 1 (s+1)+1+(s+1)) (depth s) (boxSize_pos 1 3)

theorem filtered_physical (s id : Nat) (hi : id ∈ (ambientIds s).filter (keep s)) :
    id ∈ slabPhysicalFaceEdges (targetExtent s) := ambientIds_physical s (List.mem_filter.mp hi).1

/-- A proved determinant estimate for these two particular original actions. -/
theorem determinant_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (K s : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (targetExtent s)).length p c)
    (hl : LinkLocal (targetExtent s) (chartLinks 1 (s+1) 3 (s+1)) p) :
    Q'.abs (mixedNumerator w K (targetExtent s) (keep s) p (ambientIds s)) ≤
      (((c+c)*boxAmplitude w hd hs 7) *
        (entropyRate 625 (adjustedCoreRate w hd))^(depth s)) *
        mixedPartition w K (targetExtent s) (keep s) (ambientIds s) := by
  have h := mixedNumerator_tail_bound hw0 hw1 hsmall hd hs K (targetExtent s)
    (keep s) p c P _ (chartCarrier 1 (s+1) 3 (s+1)) hl (ambientIds s) (depth s)
    (ambientIds_nodup s) (fun _ hi => ambientIds_physical s hi) (fun _ ha => core_floor s ha)
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (c+c) _ _ (budget_factor w hd hs s))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

/-- Both actual partitions cancel before taking any regulator limit. -/
theorem finiteValue_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s : Nat) (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks (targetExtent s)).length p c)
    (hl : LinkLocal (targetExtent s) (chartLinks 1 (s+1) 3 (s+1)) p) (stage : Nat) :
    Q'.abs (finiteValue w hw0 hw1 (targetExtent s) (ambientIds s)
      (fun _ hi => ambientIds_physical s hi) p stage +
      -(finiteValue w hw0 hw1 (targetExtent s) ((ambientIds s).filter (keep s))
        (filtered_physical s) p stage)) ≤
      ((c+c)*boxAmplitude w hd hs 7) *
        (entropyRate 625 (adjustedCoreRate w hd))^(depth s) := by
  apply finite_comparison_bound w hw0 hw1 (targetExtent s) (ambientIds s)
    (fun _ hi => ambientIds_physical s hi) ((ambientIds s).filter (keep s))
    (filtered_physical s) p _ stage
  exact determinant_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs
    (headCutoff w+stage) s p c P hl

end YMGap.Continuum.BF4SpatialUnionResponseBoundary

#print axioms YMGap.Continuum.BF4SpatialUnionResponseBoundary.depth
#print axioms YMGap.Continuum.BF4SpatialUnionResponseBoundary.carrier_root
#print axioms YMGap.Continuum.BF4SpatialUnionResponseBoundary.core_floor
#print axioms YMGap.Continuum.BF4SpatialUnionResponseBoundary.budget_factor
#print axioms YMGap.Continuum.BF4SpatialUnionResponseBoundary.filtered_physical
#print axioms YMGap.Continuum.BF4SpatialUnionResponseBoundary.determinant_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResponseBoundary.finiteValue_bound
