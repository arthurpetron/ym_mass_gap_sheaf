/-
# Canonical full-sector edge load and finite cleared coercivity

Cross-path loads expose the old/new gluing mechanism, but a finite
within-block coercivity certificate is unnecessary if the same construction
is aggregated over every ordered pair in the full vacuum sector.  This module
does exactly that.

Every full-sector endpoint pair is connected by the already constructed
canonical positive-kernel path.  Its stationary weight times path length is
assigned to each literal edge occurrence.  Regrouping all occurrences gives
one coefficient-independent full-sector edge load and the exact identity

  fullCanonicalPathBudget = Dirichlet(fullEdgeLoad * physicalKernel).

The located maximum of this finite load then supplies a completely inhabited
finite estimate

  edgeFloor * fullVariance <= fullLoadCapacity * fullDirichlet.

Only a cofinal positive lower bound for `edgeFloor / fullLoadCapacity` and a
positive sector-mass floor remain as named inputs to the completed gap
compiler.  No such uniform inputs, thermodynamic/continuum limit, or Clay
conclusion are asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Aggregate the canonical path over every ordered endpoint pair -/

def cutoffTwoCanonicalFullEndpointPairs (later : Nat) : List (Nat × Nat) :=
  cartesian
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)

def cutoffTwoCanonicalFullWeightedEdgeOccurrences (later : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (cutoffTwoCanonicalFullEndpointPairs later).flatMap
    (fun pair =>
      cutoffTwoCanonicalWeightedPathOccurrences
        later pair.1 pair.2)

def cutoffTwoCanonicalFullPairBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      (cutoffTwoEdgeLoadWeight later pair.1 *
          cutoffTwoEdgeLoadWeight later pair.2) *
        cutoffTwoCanonicalFullLengthLinearPathBudget
          later coefficient pair.1 pair.2)
    (cutoffTwoCanonicalFullEndpointPairs later)

def cutoffTwoCanonicalFullLengthLinearAggregateBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedRectangularEndpointBudget
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoCanonicalFullLengthLinearPathBudget later coefficient)

private theorem finiteWeightedRectangularEndpointBudget_eqv_cartesian
    {State : Type}
    (leftStates rightStates : List State)
    (weight : State → Q') (endpointBudget : State → State → Q') :
    finiteWeightedRectangularEndpointBudget
        leftStates rightStates weight endpointBudget ≈
      listQSum
        (fun pair =>
          (weight pair.1 * weight pair.2) *
            endpointBudget pair.1 pair.2)
        (cartesian leftStates rightStates) := by
  unfold finiteWeightedRectangularEndpointBudget cartesian
  let entry : State × State → Q' := fun pair =>
    (weight pair.1 * weight pair.2) *
      endpointBudget pair.1 pair.2
  have hflat := listQSum_flatMap entry
    (fun left => rightStates.map (fun right => (left, right))) leftStates
  have hrows : listQSum
      (fun left =>
        listQSum entry
          (rightStates.map (fun right => (left, right))))
      leftStates ≈
      listQSum
        (fun left => listQSum
          (fun right =>
            (weight left * weight right) * endpointBudget left right)
          rightStates)
        leftStates := by
    apply listQSum_congr
    intro left
    rw [listQSum_map]
    exact Q'.eqv_refl _
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hflat hrows)

theorem cutoffTwoCanonicalFullPairBudget_eqv_aggregateBudget
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoCanonicalFullPairBudget later coefficient ≈
      cutoffTwoCanonicalFullLengthLinearAggregateBudget
        later coefficient := by
  unfold cutoffTwoCanonicalFullPairBudget
    cutoffTwoCanonicalFullEndpointPairs
    cutoffTwoCanonicalFullLengthLinearAggregateBudget
  exact Q'.eqv_symm
    (finiteWeightedRectangularEndpointBudget_eqv_cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadWeight later)
      (cutoffTwoCanonicalFullLengthLinearPathBudget later coefficient))

theorem cutoffTwoCanonicalFullOccurrenceEnergy_eqv_pairBudget
    (later : Nat) (coefficient : Nat → Q') :
    finiteWeightedOccurrenceEnergy
        (cutoffTwoCanonicalFullWeightedEdgeOccurrences later)
        coefficient (cutoffTwoEdgeLoadKernel later) ≈
      cutoffTwoCanonicalFullPairBudget later coefficient := by
  unfold cutoffTwoCanonicalFullWeightedEdgeOccurrences
    cutoffTwoCanonicalFullPairBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        finiteWeightedOccurrenceEnergy
          (cutoffTwoCanonicalWeightedPathOccurrences
            later pair.1 pair.2)
          coefficient (cutoffTwoEdgeLoadKernel later))
      (cutoffTwoCanonicalFullEndpointPairs later)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  apply listQSum_congr_on
  intro pair hpair
  have hparts := (mem_cartesian_iff
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
  exact cutoffTwoCanonicalWeightedPathOccurrenceEnergy_eqv_pairBudget
    later coefficient pair.1 pair.2 hparts.1 hparts.2

/-! ## 2. Exact full-sector edge-load representation -/

def cutoffTwoCanonicalFullEdgeLoad
    (later source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (cutoffTwoCanonicalFullWeightedEdgeOccurrences later)
    source target

def cutoffTwoCanonicalFullLoadedDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoCanonicalFullWeightedEdgeOccurrences later)
    coefficient (cutoffTwoEdgeLoadKernel later)

private theorem cutoffTwoCanonicalFullOccurrence_mem_full
    (later : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      cutoffTwoCanonicalFullWeightedEdgeOccurrences later) :
    occurrence.1.1 ∈ cutoffTwoEdgeLoadFullStates later ∧
      occurrence.1.2 ∈ cutoffTwoEdgeLoadFullStates later := by
  unfold cutoffTwoCanonicalFullWeightedEdgeOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  have hfull := (mem_cartesian_iff
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
  unfold cutoffTwoCanonicalWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  rw [← heq]
  exact
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_mem_support
      hfull.1
      (centralPhysicalFiniteVacuumSectorPositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        pair.1 pair.2 hfull.1 hfull.2)
      edge hedge

/-- The full stationary path aggregate is exactly the Dirichlet form loaded
by the coefficient-independent canonical full edge load. -/
theorem cutoffTwoCanonicalFullLengthLinearAggregateBudget_eqv_loadedDirichlet
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoCanonicalFullLengthLinearAggregateBudget later coefficient ≈
      cutoffTwoCanonicalFullLoadedDirichlet later coefficient := by
  have hregroup :=
    finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
      (cutoffTwoEdgeLoadFullStates later)
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        cutoffTwoHalfCoupling (by decide) later 0)
      coefficient (cutoffTwoEdgeLoadKernel later)
      (cutoffTwoCanonicalFullWeightedEdgeOccurrences later)
      (cutoffTwoCanonicalFullOccurrence_mem_full later)
  exact Q'.eqv_trans _
    (cutoffTwoCanonicalFullPairBudget later coefficient) _
    (Q'.eqv_symm
      (cutoffTwoCanonicalFullPairBudget_eqv_aggregateBudget
        later coefficient))
    (Q'.eqv_trans _
      (finiteWeightedOccurrenceEnergy
        (cutoffTwoCanonicalFullWeightedEdgeOccurrences later)
        coefficient (cutoffTwoEdgeLoadKernel later)) _
      (Q'.eqv_symm
        (cutoffTwoCanonicalFullOccurrenceEnergy_eqv_pairBudget
          later coefficient))
      (Q'.eqv_symm hregroup))

/-! ## 3. The finite full edge-load maximum -/

def cutoffTwoCanonicalFullEdgeLoadCapacity (later : Nat) : Q' :=
  1 + listQMaxZero
    (fun pair => cutoffTwoCanonicalFullEdgeLoad
      later pair.1 pair.2)
    (cutoffTwoCanonicalFullEndpointPairs later)

private theorem listQMaxZero_seed_nonnegative
    {State : Type} (value : State → Q') :
    ∀ states : List State, (0 : Q') ≤ listQMaxZero value states
  | [] => Q'.le_refl' 0
  | _head :: tail =>
      Q'.le_trans' _ _ _
        (listQMaxZero_seed_nonnegative value tail)
        (Q'.le_max'_right _ _)

theorem cutoffTwoCanonicalFullEdgeLoadCapacity_pos (later : Nat) :
    (0 : Q') < cutoffTwoCanonicalFullEdgeLoadCapacity later := by
  unfold cutoffTwoCanonicalFullEdgeLoadCapacity
  exact Q'.pos_add_nonneg (by decide)
    (listQMaxZero_seed_nonnegative _ _)

theorem cutoffTwoCanonicalFullEdgeLoad_le_capacity
    (later source target : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoCanonicalFullEdgeLoad later source target ≤
      cutoffTwoCanonicalFullEdgeLoadCapacity later := by
  have hpair : (source, target) ∈
      cutoffTwoCanonicalFullEndpointPairs later := by
    unfold cutoffTwoCanonicalFullEndpointPairs
    exact (mem_cartesian_iff _ _ _).mpr ⟨hsource, htarget⟩
  have hmax := le_listQMaxZero_of_mem
    (fun pair : Nat × Nat =>
      cutoffTwoCanonicalFullEdgeLoad later pair.1 pair.2)
    (cutoffTwoCanonicalFullEndpointPairs later) hpair
  have hmaxLe : listQMaxZero
      (fun pair : Nat × Nat =>
        cutoffTwoCanonicalFullEdgeLoad later pair.1 pair.2)
      (cutoffTwoCanonicalFullEndpointPairs later) ≤
      cutoffTwoCanonicalFullEdgeLoadCapacity later := by
    unfold cutoffTwoCanonicalFullEdgeLoadCapacity
    have hadd := Q'.add_le_add_right
      (0 : Q') 1
      (listQMaxZero
        (fun pair : Nat × Nat =>
          cutoffTwoCanonicalFullEdgeLoad later pair.1 pair.2)
        (cutoffTwoCanonicalFullEndpointPairs later))
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hmax hmaxLe

private theorem kernel_nonnegative (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadKernel later source target := by
  unfold cutoffTwoEdgeLoadKernel centralPhysicalFiniteKernel
  exact centralNormalizedPhysicalReflectedKernel_nonnegative
    (by decide) later 0 _ _

theorem cutoffTwoCanonicalFullLoadedDirichlet_le_capacity_mul_fullDirichlet
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoCanonicalFullLoadedDirichlet later coefficient ≤
      cutoffTwoCanonicalFullEdgeLoadCapacity later *
        cutoffTwoFullSectorDirichlet later coefficient := by
  unfold cutoffTwoCanonicalFullLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
    cutoffTwoFullSectorDirichlet
  exact finiteLoadedDirichletBlock_le_scale_mul
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)
    coefficient (cutoffTwoEdgeLoadKernel later)
    (weightedDirectedEdgeLoad
      (cutoffTwoCanonicalFullWeightedEdgeOccurrences later))
    (cutoffTwoCanonicalFullEdgeLoadCapacity later)
    (kernel_nonnegative later)
    (fun source hsource target htarget => by
      change cutoffTwoCanonicalFullEdgeLoad later source target ≤
        cutoffTwoCanonicalFullEdgeLoadCapacity later
      exact cutoffTwoCanonicalFullEdgeLoad_le_capacity
        later source target hsource htarget)

/-! ## 4. All finite analytic inputs except mass are now inhabited -/

private theorem weight_nonnegative (later state : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadWeight later state := by
  unfold cutoffTwoEdgeLoadWeight
  exact centralPhysicalRowMarginal_nonnegative
    (by decide) later 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 state)

theorem cutoffTwo_edgeFloor_mul_fullVariance_le_fullAggregateBudget
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoCanonicalFullLengthLinearAggregateBudget
        later coefficient := by
  unfold cutoffTwoFullSectorPairwiseVariance
    centralPhysicalFiniteVacuumSectorPairwiseVariance
    finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    cutoffTwoCanonicalFullLengthLinearAggregateBudget
  exact floor_mul_finiteStationaryRectangularVariance_le_endpointBudget
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadWeight later) coefficient
    (centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) later 0)
    (cutoffTwoCanonicalFullLengthLinearPathBudget later coefficient)
    (fun state _ => weight_nonnegative later state)
    (fun state _ => weight_nonnegative later state)
    (fun left hleft right hright =>
      cutoffTwo_edgeFloor_mul_endpoint_sq_le_lengthLinearPathBudget
        later coefficient left right hleft hright)

theorem cutoffTwo_edgeFloor_mul_fullVariance_le_fullLoadCapacity_mul_Dirichlet
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoCanonicalFullEdgeLoadCapacity later *
        cutoffTwoFullSectorDirichlet later coefficient := by
  exact Q'.le_trans' _ _ _
    (cutoffTwo_edgeFloor_mul_fullVariance_le_fullAggregateBudget
      later coefficient)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (cutoffTwoCanonicalFullLengthLinearAggregateBudget_eqv_loadedDirichlet
          later coefficient))
      (cutoffTwoCanonicalFullLoadedDirichlet_le_capacity_mul_fullDirichlet
        later coefficient))

/-- The finite cleared coercivity certificate is inhabited by the canonical
edge floor and the located full edge-load capacity. -/
def cutoffTwoCanonicalFullEdgeLoadClearedDirichletAt
    (later : Nat) (hlater : 2 ≤ later)
    (massFloor : Q')
    (hmass : massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoCapacityClearedDirichletAt later
      (centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) later 0)
      (cutoffTwoCanonicalFullEdgeLoadCapacity later)
      massFloor where
  later_ge := hlater
  total_cost_pos := cutoffTwoCanonicalFullEdgeLoadCapacity_pos later
  mass_floor_le := hmass
  cleared_coercivity :=
    cutoffTwo_edgeFloor_mul_fullVariance_le_fullLoadCapacity_mul_Dirichlet
      later

/-! ## 5. The remaining cofinal ratio and mass frontier -/

structure CutoffTwoCofinalCanonicalFullEdgeLoadRatio
    (effectiveFloor massFloor : Q') : Type 1 where
  effective_floor_pos : (0 : Q') < effectiveFloor
  mass_floor_pos : (0 : Q') < massFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  mass_floor_le : ∀ request,
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) (anchor request) 0
  ratio_bound : ∀ request,
    effectiveFloor *
        cutoffTwoCanonicalFullEdgeLoadCapacity (anchor request) ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) (anchor request) 0

namespace CutoffTwoCofinalCanonicalFullEdgeLoadRatio

def toCofinalCapacityClearedGluing
    {effectiveFloor massFloor : Q'}
    (family : CutoffTwoCofinalCanonicalFullEdgeLoadRatio
      effectiveFloor massFloor) :
    CutoffTwoCofinalCapacityClearedGluing
      effectiveFloor massFloor where
  effective_floor_pos := family.effective_floor_pos
  mass_floor_pos := family.mass_floor_pos
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  baseFloor := fun request =>
    centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) (family.anchor request) 0
  totalCost := fun request =>
    cutoffTwoCanonicalFullEdgeLoadCapacity (family.anchor request)
  cleared := fun request =>
    cutoffTwoCanonicalFullEdgeLoadClearedDirichletAt
      (family.anchor request)
      (Nat.le_trans (Nat.le_max_left 2 request)
        (family.anchor_ge request))
      massFloor (family.mass_floor_le request)
  ratio_bound := family.ratio_bound

def toCompletedStrictContractionData
    {effectiveFloor massFloor : Q'}
    (family : CutoffTwoCofinalCanonicalFullEdgeLoadRatio
      effectiveFloor massFloor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalCapacityClearedGluing
    |>.toCompletedStrictContractionData

end CutoffTwoCofinalCanonicalFullEdgeLoadRatio

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.cutoffTwoCanonicalFullPairBudget_eqv_aggregateBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.cutoffTwoCanonicalFullOccurrenceEnergy_eqv_pairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.cutoffTwoCanonicalFullLengthLinearAggregateBudget_eqv_loadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.cutoffTwoCanonicalFullEdgeLoadCapacity_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.cutoffTwoCanonicalFullLoadedDirichlet_le_capacity_mul_fullDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.cutoffTwo_edgeFloor_mul_fullVariance_le_fullLoadCapacity_mul_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.cutoffTwoCanonicalFullEdgeLoadClearedDirichletAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.CutoffTwoCofinalCanonicalFullEdgeLoadRatio.toCompletedStrictContractionData
