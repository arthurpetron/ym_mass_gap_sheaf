/-
# Generic original-action comparison under spatial-base inclusion

The actual larger-base chart is compared with its translated smaller-base
selection using the literal keep mask and insideIds. Every omitted face,
including every orientation, is separated from the shifted support-box
root. The existing signed mixed-numerator tail estimate retains the two
original partitions, which cancel in the normalized comparison.

This exposes the polynomial-level argument used privately by BaseCoherence,
without a PhysicalSpan premise or any change to that module. The supplied
polynomial has its actual interval and LinkLocal certificates. Support size
n and interval cap c, not the larger ambient base or heat stage, determine
the amplitude. The original small-nome guards remain unchanged. A Wilson
observable pin and actual limit comparison are separate consumers; no finite
full-action identity, OS norm estimate or continuum claim follows here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseAlignedBoxes
import YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBaseBoundaryComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion (activeAnchors)
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseAlignedBoxes
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
  (chartExtent chartIds chartIds_physical chartIds_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary
  (carrierSize boxAmplitude shifted_budget_factor)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem origin_spatial {base : Nat} (hb : 0<base) : originFace ∈ spatialFaces base := by
  apply (spatialFaces_mem_iff base originFace).mpr
  exact ⟨hb, hb, hb, rfl, by decide⟩

private theorem active_core_size_floor {base larger : Nat} (h : base ≤ larger)
    (r H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n) {anchor : List Nat}
    (ha : anchor ∈ activeAnchors (chartExtent larger r H t)
      ((boxLinks n).map (shiftLink (r+1) timeOrigin)) (keep h r H t)
      (chartIds larger r H t)) : r+1-carrierSize n ≤ anchor.length := by
  have hf := active_core_linf_floor (distance := r+1)
    (shiftedBoxProbe n (r+1) timeOrigin hn)
    (chartIds_nodup larger r H t) (fun _ hi => chartIds_physical hi) ha (by
      intro id hi ho
      exact omitted_separation h r H t timeOrigin (origin_spatial hb) hi
        ((keep_eq_false h r H t id).mp ho))
  rw [shiftedBoxProbe_size] at hf
  unfold carrierSize
  omega

private theorem determinant_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base larger : Nat} (h : base ≤ larger)
    (K r H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n) (p : RatPoly) (c : Q')
    (P : Interval (blocks (chartExtent larger r H t)) p c)
    (hl : LinkLocal (chartExtent larger r H t)
      ((boxLinks n).map (shiftLink (r+1) timeOrigin)) p) :
    Q'.abs (mixedNumerator w K (chartExtent larger r H t) (keep h r H t) p
      (chartIds larger r H t)) ≤
      (((c+c)*boxAmplitude w hd hs n) *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize n)) *
        mixedPartition w K (chartExtent larger r H t) (keep h r H t)
          (chartIds larger r H t) := by
  have hbnd := mixedNumerator_tail_bound hw0 hw1 hsmall hd hs K (chartExtent larger r H t)
    (keep h r H t) p c P _ (shiftedBoxProbe n (r+1) timeOrigin hn) hl
    (chartIds larger r H t) (r+1-carrierSize n) (chartIds_nodup larger r H t)
    (fun _ hi => chartIds_physical hi)
    (fun _ ha => active_core_size_floor h r H t timeOrigin n hb hn ha)
  exact Q'.le_trans' _ _ _ hbnd
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (c+c) _ _ (shifted_budget_factor w hd hs n _ _ _ hn))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

/-- The SAME larger-chart polynomial and cutoff occur in both normalized
expectations. The amplitude is independent of larger base, stage and time
parameters; support size and interval cap remain explicit supplied data. -/
theorem finiteValue_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base larger : Nat} (h : base ≤ larger)
    (r H t timeOrigin n : Nat) (hb : 0<base) (hn : 0<n) (p : RatPoly) (c : Q')
    (P : Interval (blocks (chartExtent larger r H t)) p c)
    (hl : LinkLocal (chartExtent larger r H t)
      ((boxLinks n).map (shiftLink (r+1) timeOrigin)) p) (stage : Nat) :
    Q'.abs (finiteValue w hw0 hw1 (chartExtent larger r H t)
      (chartIds larger r H t) (fun _ hi => chartIds_physical hi) p stage +
      -(finiteValue w hw0 hw1 (chartExtent larger r H t) (insideIds h r H t)
        (insideIds_physical h r H t) p stage)) ≤
      ((c+c)*boxAmplitude w hd hs n) *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize n) := by
  apply finite_comparison_bound w hw0 hw1 (chartExtent larger r H t)
    (chartIds larger r H t) (fun _ hi => chartIds_physical hi)
    (insideIds h r H t) (insideIds_physical h r H t) p _ stage
  exact determinant_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs h
    (headCutoff w+stage) r H t timeOrigin n hb hn p c P hl

end YMGap.Continuum.BF4ExactSlabFixedSpatialBaseBoundaryComparison

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBaseBoundaryComparison.finiteValue_bound
