/-
# Retained all-label Choi contraction and complete-order domination

The four-preimage coarse packet can erase transverse fine flux.  The corrected
conditional kernel therefore has to contract the physical observable while the
complete fine link-intertwiner assignment is still retained.

This module performs that contraction on the literal production carrier
`slabFineFusionWitnesses`.  For every positive physical row it constructs:

* the exact conditional expectation over the normalized Haar fiber;
* a source/target Choi entry as a weighted Gram on that same carrier;
* finite quadratic-form positivity, including arbitrary matrix amplification;
* a lower/upper Loewner sandwich whenever the complete interior spatial weight
  has a pointwise scalar window.

The domination is potential-independent after the pointwise window is supplied:
the normalized Haar weight is common to the reference and physical contractions,
so no carrier-cardinality factor is introduced.

The pinned collar counterexample is instantiated explicitly.  Thus the row on
which the old four-preimage carrier is empty has a normalized retained kernel
and a completely positive all-label contraction.

Honest scope: `spatialWeight` and `amplitude` are explicit arguments.  A later
module must identify them with the grouped BF4 Feynman--Kac/Choi observable and
prove a spacing-uniform pointwise window.  No such physical identification or
uniform estimate is assumed here.

## Axiom gate

Finite list algebra and exact `Q'` order only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
import YMGap.Continuum.BF4RetainedGramReferenceOrder

namespace YMGap.Continuum.BF4SU2FineIntertwinerChoiCPOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4RetainedGramReferenceOrder
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.BF4SU2OuterRawRowMassCounterexample
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact conditional expectation on the retained Haar fiber -/

private theorem listQSum_mono_on {A : Type}
    (lower upper : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → lower item ≤ upper item) →
        listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, horder =>
      Q'.add_le_add
        (horder head List.mem_cons_self)
        (listQSum_mono_on lower upper tail
          (fun item hitem =>
            horder item (List.mem_cons_of_mem head hitem)))

/-- Conditional expectation of an all-label observable before the fine
intertwiner assignment is forgotten. -/
def retainedFineIntertwinerConditionalExpectation
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (observable : SlabFusionWitnessAssignment → Q') : Q' :=
  listQSum
    (fun witness =>
      retainedFineIntertwinerConditionalKernel source witness *
        observable witness)
    (slabFineFusionWitnesses D source.fineState)

/-- Conditional integration preserves the nonnegative cone. -/
theorem retainedFineIntertwinerConditionalExpectation_nonnegative
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (observable : SlabFusionWitnessAssignment → Q')
    (hobservable :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        (0 : Q') ≤ observable witness) :
    (0 : Q') ≤
      retainedFineIntertwinerConditionalExpectation
        source observable := by
  unfold retainedFineIntertwinerConditionalExpectation
  apply listQSum_nonnegative_on
  intro witness hwitness
  exact Q'.mul_nonneg _ _
    (retainedFineIntertwinerConditionalKernel_nonnegative
      source witness)
    (hobservable witness hwitness)

/-- Conditional integration is order preserving on the complete retained
carrier. -/
theorem retainedFineIntertwinerConditionalExpectation_mono
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (lower upper : SlabFusionWitnessAssignment → Q')
    (horder :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        lower witness ≤ upper witness) :
    retainedFineIntertwinerConditionalExpectation source lower ≤
      retainedFineIntertwinerConditionalExpectation source upper := by
  unfold retainedFineIntertwinerConditionalExpectation
  apply listQSum_mono_on
  intro witness hwitness
  exact Q'.mul_le_mul_of_nonneg_left
    (lower witness) (upper witness)
    (retainedFineIntertwinerConditionalKernel source witness)
    (horder witness hwitness)
    (retainedFineIntertwinerConditionalKernel_nonnegative
      source witness)

/-- Exact preservation of the constant observable. -/
theorem retainedFineIntertwinerConditionalExpectation_one
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D) :
    retainedFineIntertwinerConditionalExpectation
        source (fun _ => 1) ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun witness =>
        Q'.mul_one_eqv
          (retainedFineIntertwinerConditionalKernel source witness))
      (slabFineFusionWitnesses D source.fineState))
    (retainedFineIntertwinerConditionalKernel_row_normalized source)

/-! ## 2. Physical spatial weights on the same retained carrier -/

/-- The normalized Haar-fiber weight multiplied by the complete interior
spatial observable. -/
def retainedFineIntertwinerSpatialWeight
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (spatialWeight : SlabFusionWitnessAssignment → Q')
    (witness : SlabFusionWitnessAssignment) : Q' :=
  retainedFineIntertwinerConditionalKernel source witness *
    spatialWeight witness

theorem retainedFineIntertwinerSpatialWeight_nonnegative
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (spatialWeight : SlabFusionWitnessAssignment → Q')
    (hspatial :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        (0 : Q') ≤ spatialWeight witness)
    (witness : SlabFusionWitnessAssignment)
    (hwitness :
      witness ∈
        slabFineFusionWitnesses D source.fineState) :
    (0 : Q') ≤
      retainedFineIntertwinerSpatialWeight
        source spatialWeight witness := by
  unfold retainedFineIntertwinerSpatialWeight
  exact Q'.mul_nonneg _ _
    (retainedFineIntertwinerConditionalKernel_nonnegative
      source witness)
    (hspatial witness hwitness)

/-- A pointwise spatial window becomes a nonnegative reference window between
the physical retained weight and the normalized Haar-fiber weight. -/
def retainedFineIntertwinerReferenceWindow
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (spatialWeight : SlabFusionWitnessAssignment → Q')
    (lower upper : Q')
    (lower_nonnegative : (0 : Q') ≤ lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (lower_bound :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        lower ≤ spatialWeight witness)
    (upper_bound :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        spatialWeight witness ≤ upper) :
    NonnegativeGramReferenceWindow
      (slabFineFusionWitnesses D source.fineState)
      (retainedFineIntertwinerConditionalKernel source)
      (retainedFineIntertwinerSpatialWeight
        source spatialWeight) where
  lower := lower
  upper := upper
  lower_nonnegative := lower_nonnegative
  upper_nonnegative := upper_nonnegative
  reference_nonnegative := by
    intro witness _
    exact
      retainedFineIntertwinerConditionalKernel_nonnegative
        source witness
  lower_bound := by
    intro witness hwitness
    have hmul :=
      Q'.mul_le_mul_of_nonneg_left
        lower (spatialWeight witness)
        (retainedFineIntertwinerConditionalKernel source witness)
        (lower_bound witness hwitness)
        (retainedFineIntertwinerConditionalKernel_nonnegative
          source witness)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv lower
          (retainedFineIntertwinerConditionalKernel source witness)))
      hmul
  upper_bound := by
    intro witness hwitness
    have hmul :=
      Q'.mul_le_mul_of_nonneg_left
        (spatialWeight witness) upper
        (retainedFineIntertwinerConditionalKernel source witness)
        (upper_bound witness hwitness)
        (retainedFineIntertwinerConditionalKernel_nonnegative
          source witness)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (retainedFineIntertwinerConditionalKernel source witness)
          upper))

/-! ## 3. All-label source/target Choi contraction -/

/-- The retained source/target Choi entry.  The channel is the literal global
fine-intertwiner assignment, the channel weight is the normalized Haar fiber
times the complete spatial weight, and `amplitude` contains the source/target
half-amplitudes. -/
def retainedFineIntertwinerChoiEntry
    {D : SlabPhysicalData} {Boundary : Type}
    (source : RetainedFineIntertwinerSource D)
    (spatialWeight : SlabFusionWitnessAssignment → Q')
    (amplitude :
      Boundary → SlabFusionWitnessAssignment → Q')
    (left right : Boundary) : Q' :=
  weightedGram
    (slabFineFusionWitnesses D source.fineState)
    (retainedFineIntertwinerSpatialWeight
      source spatialWeight)
    amplitude left right

/-- The complete finite quadratic form of the retained Choi contraction. -/
def retainedFineIntertwinerChoiQuadratic
    {D : SlabPhysicalData} {Boundary : Type}
    (source : RetainedFineIntertwinerSource D)
    (boundaries : List Boundary)
    (spatialWeight : SlabFusionWitnessAssignment → Q')
    (amplitude :
      Boundary → SlabFusionWitnessAssignment → Q')
    (coefficient : Boundary → Q') : Q' :=
  weightedGramQuadratic
    boundaries
    (slabFineFusionWitnesses D source.fineState)
    (retainedFineIntertwinerSpatialWeight
      source spatialWeight)
    amplitude coefficient

/-- The retained all-label Choi contraction is completely positive at every
finite carrier level. -/
theorem retainedFineIntertwinerChoiQuadratic_nonnegative
    {D : SlabPhysicalData} {Boundary : Type}
    (source : RetainedFineIntertwinerSource D)
    (boundaries : List Boundary)
    (spatialWeight : SlabFusionWitnessAssignment → Q')
    (amplitude :
      Boundary → SlabFusionWitnessAssignment → Q')
    (coefficient : Boundary → Q')
    (hspatial :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        (0 : Q') ≤ spatialWeight witness) :
    (0 : Q') ≤
      retainedFineIntertwinerChoiQuadratic
        source boundaries spatialWeight
        amplitude coefficient := by
  unfold retainedFineIntertwinerChoiQuadratic
  exact weightedGramQuadratic_nonnegative
    boundaries
    (slabFineFusionWitnesses D source.fineState)
    (retainedFineIntertwinerSpatialWeight
      source spatialWeight)
    amplitude coefficient
    (retainedFineIntertwinerSpatialWeight_nonnegative
      source spatialWeight hspatial)

/-- **Complete-order domination.**  Pointwise lower/upper bounds on the
complete spatial weight pass through the retained Choi contraction to every
finite quadratic form. -/
theorem retainedFineIntertwinerChoiQuadratic_cp_order
    {D : SlabPhysicalData} {Boundary : Type}
    (source : RetainedFineIntertwinerSource D)
    (boundaries : List Boundary)
    (spatialWeight : SlabFusionWitnessAssignment → Q')
    (amplitude :
      Boundary → SlabFusionWitnessAssignment → Q')
    (coefficient : Boundary → Q')
    (lower upper : Q')
    (lower_nonnegative : (0 : Q') ≤ lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (lower_bound :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        lower ≤ spatialWeight witness)
    (upper_bound :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        spatialWeight witness ≤ upper) :
    lower *
        weightedGramQuadratic
          boundaries
          (slabFineFusionWitnesses D source.fineState)
          (retainedFineIntertwinerConditionalKernel source)
          amplitude coefficient ≤
      retainedFineIntertwinerChoiQuadratic
        source boundaries spatialWeight amplitude coefficient ∧
    retainedFineIntertwinerChoiQuadratic
          source boundaries spatialWeight amplitude coefficient ≤
      upper *
        weightedGramQuadratic
          boundaries
          (slabFineFusionWitnesses D source.fineState)
          (retainedFineIntertwinerConditionalKernel source)
          amplitude coefficient := by
  exact
    (retainedFineIntertwinerReferenceWindow
      source spatialWeight lower upper
      lower_nonnegative upper_nonnegative
      lower_bound upper_bound).quadratic_sandwich
        boundaries
        (slabFineFusionWitnesses D source.fineState)
        (retainedFineIntertwinerConditionalKernel source)
        (retainedFineIntertwinerSpatialWeight
          source spatialWeight)
        amplitude coefficient

/-- The same Loewner sandwich survives an arbitrary finite matrix
amplification. -/
theorem retainedFineIntertwinerChoiQuadratic_cp_order_amplified
    {D : SlabPhysicalData}
    {MatrixIndex Boundary : Type}
    (source : RetainedFineIntertwinerSource D)
    (amplifiedBoundaries : List (MatrixIndex × Boundary))
    (spatialWeight : SlabFusionWitnessAssignment → Q')
    (amplitude :
      (MatrixIndex × Boundary) →
        SlabFusionWitnessAssignment → Q')
    (coefficient : (MatrixIndex × Boundary) → Q')
    (lower upper : Q')
    (lower_nonnegative : (0 : Q') ≤ lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (lower_bound :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        lower ≤ spatialWeight witness)
    (upper_bound :
      ∀ witness,
        witness ∈
          slabFineFusionWitnesses D source.fineState →
        spatialWeight witness ≤ upper) :
    lower *
        weightedGramQuadratic
          amplifiedBoundaries
          (slabFineFusionWitnesses D source.fineState)
          (retainedFineIntertwinerConditionalKernel source)
          amplitude coefficient ≤
      weightedGramQuadratic
        amplifiedBoundaries
        (slabFineFusionWitnesses D source.fineState)
        (retainedFineIntertwinerSpatialWeight
          source spatialWeight)
        amplitude coefficient ∧
    weightedGramQuadratic
          amplifiedBoundaries
          (slabFineFusionWitnesses D source.fineState)
          (retainedFineIntertwinerSpatialWeight
            source spatialWeight)
          amplitude coefficient ≤
      upper *
        weightedGramQuadratic
          amplifiedBoundaries
          (slabFineFusionWitnesses D source.fineState)
          (retainedFineIntertwinerConditionalKernel source)
          amplitude coefficient := by
  exact weightedGramQuadratic_reference_sandwich_amplified
    amplifiedBoundaries
    (slabFineFusionWitnesses D source.fineState)
    (retainedFineIntertwinerConditionalKernel source)
    (retainedFineIntertwinerSpatialWeight
      source spatialWeight)
    amplitude coefficient lower upper
    (retainedFineIntertwinerReferenceWindow
      source spatialWeight lower upper
      lower_nonnegative upper_nonnegative
      lower_bound upper_bound).lower_bound
    (retainedFineIntertwinerReferenceWindow
      source spatialWeight lower upper
      lower_nonnegative upper_nonnegative
      lower_bound upper_bound).upper_bound

/-! ## 4. Instantiation on the exact row killing the old carrier -/

/-- The positive collar row as a source for the corrected retained kernel. -/
def collarRetainedFineIntertwinerSource :
    RetainedFineIntertwinerSource counterScalePair.fine where
  fineState := collarState
  fineState_mem := collarState_mem
  physicalTerm_pos := collarState_physicalTerm_pos

/-- The old zero row has an exactly normalized retained Haar fiber. -/
theorem collarRetainedFineIntertwinerKernel_normalized :
    listQSum
        (retainedFineIntertwinerConditionalKernel
          collarRetainedFineIntertwinerSource)
        (slabFineFusionWitnesses
          counterScalePair.fine collarState) ≈ 1 :=
  retainedFineIntertwinerConditionalKernel_row_normalized
    collarRetainedFineIntertwinerSource

#print axioms retainedFineIntertwinerConditionalExpectation_nonnegative
#print axioms retainedFineIntertwinerConditionalExpectation_mono
#print axioms retainedFineIntertwinerConditionalExpectation_one
#print axioms retainedFineIntertwinerReferenceWindow
#print axioms retainedFineIntertwinerChoiQuadratic_nonnegative
#print axioms retainedFineIntertwinerChoiQuadratic_cp_order
#print axioms retainedFineIntertwinerChoiQuadratic_cp_order_amplified
#print axioms collarRetainedFineIntertwinerKernel_normalized

end YMGap.Continuum.BF4SU2FineIntertwinerChoiCPOrder
