/-
# Complete the paid high-spin path through the finite core

The high-spin exterior path stops at a physical labelling which need not carry
an accepted trivalent assignment.  It therefore cannot itself be summed as a
physical target.  The residual component word repairs this exactly: it lowers
the intermediate core field to the already constructed accepted complete-
component target.

At every `0 < w < 1`, an arbitrary positive face peel costs at most the
deliberately coarse factor `2`.  Combining that residual path with the sharp
high-spin payment proves the honest two-rate comparison

```text
source weight
  <= anchorFaceCoefficient ^ paidLength
       * 2 ^ residualLength
       * accepted complete-target weight.
```

The factor `2` is not claimed contractive.  Its purpose is to expose exactly
the low-spin price that the later entropy-balanced split must absorb.

Constructive contract: finite path induction, exact `Nat` subtraction, and
`Q'` order algebra only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentCoreCompletionWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Every ordinary face peel costs at most two -/

/-- At threshold zero, the exact exterior successor rate is at most two on
the full subunit coupling interval. -/
theorem exteriorFaceCoefficient_zero_le_two
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) :
    exteriorFaceCoefficient w 0 <= Q'.ofNat 2 := by
  unfold exteriorFaceCoefficient
  have hpow : qpow w 3 <= (1 : Q') := qpow_le_one hw0 hw1 3
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hpow
    (zero_le_ofNat 2)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat 2)))

/-- A legal ordinary peel path telescopes at the universal coarse rate `2`.
Unlike the high-spin payment, this is not a contraction. -/
theorem slabFacePeelPath_faceFactor_le_two
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {cutoff extent : Nat} {source target : EdgeLabelling}
    {faces : List Nat}
    (path : SlabFacePeelPath cutoff extent source faces target) :
    slabParametricKPhysicalFaceFactor w cutoff extent source <=
      (Q'.ofNat 2) ^ faces.length *
        slabParametricKPhysicalFaceFactor w cutoff extent target := by
  induction path with
  | nil physical =>
      simp only [List.length_nil, Q'.pow_zero]
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.one_mul_eqv
            (slabParametricKPhysicalFaceFactor
              w cutoff extent physical)))
  | @cons physical target faces faceId hface hpositive hbounded tail ih =>
      have hone := slabPhysicalFaceFactor_exterior_lower_one_le_of_rate
        hw0 hw1 cutoff extent 0 physical faceId hface hpositive hbounded
        (exteriorFaceCoefficient_zero_le_two hw0 hw1)
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ ih
        (zero_le_ofNat 2)
      have hchain := Q'.le_trans' _ _ _ hone hscaled
      simp only [List.length_cons, Q'.pow_succ]
      exact Q'.le_trans' _ _ _ hchain
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv (Q'.ofNat 2)
              ((Q'.ofNat 2) ^ faces.length)
              (slabParametricKPhysicalFaceFactor
                w cutoff extent target))))

/-- Unit Haar counting lifts the coarse residual telescope to arbitrary
source and target assignment witnesses. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_peelPath_le_two
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (cutoff half : Nat)
    {sourcePhysical targetPhysical : EdgeLabelling} {faces : List Nat}
    (sourceWitness targetWitness : SlabFusionWitnessAssignment)
    (path : SlabFacePeelPath cutoff (centralExtent half)
      sourcePhysical faces targetPhysical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight
        D sourcePhysical sourceWitness <=
      (Q'.ofNat 2) ^ faces.length *
        retainedFineIntertwinerPhysicalFiberWeight
          D targetPhysical targetWitness := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
        { coupling := w
          coupling_nonnegative := hw0
          cutoff := cutoff
          half := half }
        sourcePhysical sourceWitness))
    (Q'.le_trans' _ _ _
      (slabFacePeelPath_faceFactor_le_two hw0 hw1 path)
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left ((Q'.ofNat 2) ^ faces.length) _ _
          (Q'.eqv_symm
            (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
              { coupling := w
                coupling_nonnegative := hw0
                cutoff := cutoff
                half := half }
              targetPhysical targetWitness)))))

/-! ## 2. The residual word is a legal path to the accepted target -/

/-- The residual drop fits in the intermediate core field coordinatewise. -/
theorem coreResidualDropCount_le_corePhysical
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat)
    (hdrop : forall faceId, faceId ∈ slabPhysicalFaceEdges extent ->
      drop faceId <= physical faceId)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    coreResidualDropCount physical threshold drop faceId <=
      highSpinCorePhysical extent physical threshold drop faceId := by
  unfold highSpinCorePhysical highSpinExteriorDropFaces lowerSlabFacesByList
  rw [slabFaceDropList_count_of_mem extent
    (exteriorDropCount physical threshold drop) hface]
  have hexterior := exteriorDropCount_le_drop
    physical threshold drop faceId
  have hcapacity := hdrop faceId hface
  unfold coreResidualDropCount
  omega

/-- The intermediate core field remains bounded whenever the source is. -/
theorem highSpinCorePhysical_bounded
    (cutoff extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat)
    (hbounded : SlabFaceLabellingBounded cutoff extent physical) :
    SlabFaceLabellingBounded cutoff extent
      (highSpinCorePhysical extent physical threshold drop) := by
  intro faceId hface
  unfold highSpinCorePhysical highSpinExteriorDropFaces lowerSlabFacesByList
  rw [slabFaceDropList_count_of_mem extent
    (exteriorDropCount physical threshold drop) hface]
  exact Nat.le_trans (Nat.sub_le _ _) (hbounded faceId hface)

/-- The finite-core residual of an actual rooted component is a legal
ordinary peel path from the nonphysical intermediate field to the already
accepted complete-component physical target. -/
def SlabFusionWitnessFaceStrandSeed.coreResidualPath
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat)
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    SlabFacePeelPath K extent
      (SlabFusionWitnessFaceStrandSeed.corePhysical seed threshold)
      (SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed threshold)
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) := by
  let path := slabFacePeelPath_of_drop K extent
    (SlabFusionWitnessFaceStrandSeed.corePhysical seed threshold)
    (coreResidualDropCount physical threshold
      (slabFaceStrandSelectionCount seed.selected))
    (fun faceId hface =>
      coreResidualDropCount_le_corePhysical extent physical threshold
        (slabFaceStrandSelectionCount seed.selected)
        (fun id _ => slabFaceStrandSelectionCount_le seed.selected id)
        faceId hface)
    (highSpinCorePhysical_bounded K extent physical threshold
      (slabFaceStrandSelectionCount seed.selected) hbounded)
  change SlabFacePeelPath K extent
    (SlabFusionWitnessFaceStrandSeed.corePhysical seed threshold)
    (SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed threshold)
    (lowerSlabFacesByList
      (SlabFusionWitnessFaceStrandSeed.corePhysical seed threshold)
      (SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed threshold)) at path
  rw [SlabFusionWitnessFaceStrandSeed.lower_corePhysical_residual_eq_lowerPhysical
    seed threshold] at path
  exact path

/-! ## 3. Sharp exterior payment followed by honest core completion -/

private theorem two_rate_chain
    {source core target exteriorRate residualRate : Q'}
    (hexteriorRate : (0 : Q') <= exteriorRate)
    (hexterior : source <= exteriorRate * core)
    (hresidual : core <= residualRate * target) :
    source <= (exteriorRate * residualRate) * target := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hresidual hexteriorRate
  exact Q'.le_trans' _ _ _ hexterior
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv exteriorRate residualRate target))))

/-- Every rooted component has a two-rate comparison to its actual accepted
complete-removal target.  The sharp exterior factor is contractive; the
explicit residual factor `2^r` records the entire low-spin cost. -/
theorem expandedFiberWeight_coreCompleted_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))}
    (seed : SlabFusionWitnessFaceStrandSeed
      cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))
        assignment hassignment)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := Q'.le_of_lt hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight D physical assignment <=
      (anchorFaceCoefficient ^
          (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces seed
            (anchorPaidExteriorThreshold w)).length *
        (Q'.ofNat 2) ^
          (SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed
            (anchorPaidExteriorThreshold w)).length) *
        retainedFineIntertwinerPhysicalFiberWeight D
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
          (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) := by
  dsimp only
  have hexterior :=
    SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_coreSplit_le
      hw0 hw1 cutoff half seed
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) hbounded
  dsimp only at hexterior
  have hresidual :=
    retainedFineIntertwinerPhysicalFiberWeight_peelPath_le_two
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) cutoff half
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
      (SlabFusionWitnessFaceStrandSeed.coreResidualPath
        seed (anchorPaidExteriorThreshold w) hbounded)
  dsimp only at hresidual
  have hanchorNonnegative :
      (0 : Q') <= anchorFaceCoefficient ^
        (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces seed
          (anchorPaidExteriorThreshold w)).length :=
    Q'.pow_nonneg anchorFaceCoefficient (by decide) _
  exact two_rate_chain hanchorNonnegative hexterior hresidual

#print axioms exteriorFaceCoefficient_zero_le_two
#print axioms slabFacePeelPath_faceFactor_le_two
#print axioms retainedFineIntertwinerPhysicalFiberWeight_peelPath_le_two
#print axioms coreResidualDropCount_le_corePhysical
#print axioms highSpinCorePhysical_bounded
#print axioms SlabFusionWitnessFaceStrandSeed.coreResidualPath
#print axioms expandedFiberWeight_coreCompleted_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentCoreCompletionWeight
