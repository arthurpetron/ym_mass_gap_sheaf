/-
# Loop-erased full-sector cost at the cutoff-two boundary

The located canonical edge-load maximum is a precise finite coefficient, but
its cutoff dependence is opaque.  Constructive loop erasure supplies a more
transparent alternative.  Every endpoint path can be chosen simple, with
edge length at most the finite vacuum-sector cardinality.  Summing the common
endpoint estimate and using that the stationary sector mass is at most one
gives

  edgeFloor * fullVariance
    <= (1 + sectorCardinality^2) * fullDirichlet.

The sector cardinality is in turn bounded by the explicit BF4 ambient count,
which at half extent zero is `(cutoff + 1)^24`.  Thus a fully explicit, if
very coarse, polynomial cost replaces the opaque path-load maximum.

This module compiles either the sector-size or ambient-size ratio bound to the
completed strict-contraction interface.  It does not prove either ratio
uniform, a fixed positive mass floor, a thermodynamic/continuum limit, or the
Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The canonical vacuum-sector stationary mass is at most one -/

private theorem fullFiniteWeightSum_eqv_one (later : Nat) :
    listQSum
        (centralPhysicalFiniteWeight
          cutoffTwoHalfCoupling (by decide) later 0)
        (List.range
          (centralPhysicalFiniteCarrierSize
            cutoffTwoHalfCoupling (by decide) later 0)) ≈
      1 := by
  let weight := centralPhysicalFiniteWeight
    cutoffTwoHalfCoupling (by decide) later 0
  let coefficient := centralPhysicalFiniteCoefficient
    cutoffTwoHalfCoupling (by decide) later 0 (fun _ => 1)
  have hmassMean :
      listQSum weight
          (List.range
            (centralPhysicalFiniteCarrierSize
              cutoffTwoHalfCoupling (by decide) later 0)) ≈
        finiteWeightedMean
          (centralPhysicalFiniteCarrierSize
            cutoffTwoHalfCoupling (by decide) later 0)
          weight coefficient := by
    unfold finiteWeightedMean
    apply listQSum_congr
    intro index
    unfold coefficient centralPhysicalFiniteCoefficient
    exact Q'.eqv_symm (Q'.one_mul_eqv (weight index))
  exact Q'.eqv_trans _ _ _ hmassMean
    (Q'.eqv_trans _ _ _
      (centralPhysicalFiniteWeightedMean_eqv_stationaryMean
        cutoffTwoHalfCoupling (by decide) later 0 (fun _ => 1))
      (centralPhysicalStationaryMean_one
        cutoffTwoHalfCoupling (by decide) later 0))

theorem cutoffTwoFullSectorMass_le_one (later : Nat) :
    centralPhysicalFiniteVacuumSectorMass
        cutoffTwoHalfCoupling (by decide) later 0 ≤ 1 := by
  let source := centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) later 0
  let target := List.range
    (centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) later 0)
  let weight := centralPhysicalFiniteWeight
    cutoffTwoHalfCoupling (by decide) later 0
  have hsubsum : listQSum weight source ≤
      listQSum weight target := by
    apply listQSum_le_of_injective
      source target weight weight (fun index => index)
    · exact centralPhysicalFiniteVacuumSectorIndices_nodup
        cutoffTwoHalfCoupling (by decide) later 0
    · intro index hindex
      exact List.mem_range.mpr
        (centralPhysicalFiniteVacuumSectorIndex_lt
          cutoffTwoHalfCoupling (by decide) later 0 hindex)
    · intro left _hleft right _hright heq
      exact heq
    · intro index _hindex
      exact Q'.le_refl' _
    · intro index _hindex
      unfold weight centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative
        (by decide) later 0 _
  unfold centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  exact Q'.le_trans' _ _ _ hsubsum
    (Q'.le_of_eqv (fullFiniteWeightSum_eqv_one later))

private theorem cutoffTwoFullSectorMass_square_le_one (later : Nat) :
    let mass := centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0
    mass * mass ≤ 1 := by
  let mass := centralPhysicalFiniteVacuumSectorMass
    cutoffTwoHalfCoupling (by decide) later 0
  have hmass0 : (0 : Q') ≤ mass := Q'.le_of_lt
    (centralPhysicalFiniteVacuumSectorMass_pos
      cutoffTwoHalfCoupling (by decide) later 0)
  have hmass1 : mass ≤ 1 := cutoffTwoFullSectorMass_le_one later
  have hfirst : mass * mass ≤ 1 * mass :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hmass1 hmass0
  have hsecond : 1 * mass ≤ 1 * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmass1
      (by decide : (0 : Q') ≤ 1)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv (Q'.one_mul_eqv 1)))

/-! ## 2. Loop-erased sector-size cost -/

def cutoffTwoSimpleFullSectorCost (later : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    cutoffTwoHalfCoupling (by decide) later 0

theorem cutoffTwoSimpleFullSectorCost_pos (later : Nat) :
    (0 : Q') < cutoffTwoSimpleFullSectorCost later :=
  centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
    cutoffTwoHalfCoupling (by decide) later 0

private theorem cutoffTwoFullSectorDirichlet_nonnegative_local
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoFullSectorDirichlet later coefficient := by
  refine Q'.le_trans' _
    (cutoffTwoWithinBlockDirichlet later coefficient +
      cutoffTwoCrossBlockDirichlet later coefficient) _ ?_ ?_
  · exact Q'.zero_le_add _ _
      (cutoffTwoWithinBlockDirichlet_nonnegative later coefficient)
      (cutoffTwoCrossBlockDirichlet_nonnegative later coefficient)
  exact Q'.ge_of_eqv
    (cutoffTwoFullSectorDirichlet_eqv_within_add_cross
      later coefficient)

/-- Loop erasure and stationary mass at most one give a completely explicit
finite cleared coercivity coefficient. -/
theorem cutoffTwo_edgeFloor_mul_fullVariance_le_simpleCost_mul_Dirichlet
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoSimpleFullSectorCost later *
        cutoffTwoFullSectorDirichlet later coefficient := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) later 0
  let weight := centralPhysicalFiniteWeight
    cutoffTwoHalfCoupling (by decide) later 0
  let mass := centralPhysicalFiniteVacuumSectorMass
    cutoffTwoHalfCoupling (by decide) later 0
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
    cutoffTwoHalfCoupling (by decide) later 0
  let scale := cutoffTwoSimpleFullSectorCost later
  let energy := cutoffTwoFullSectorDirichlet later coefficient
  have hraw : floor *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          cutoffTwoHalfCoupling (by decide) later 0 coefficient ≤
      (mass * mass) * (scale * energy) := by
    exact floor_mul_finiteWeightedPairwiseVariance_le
      states weight coefficient floor scale energy
      (fun state _ => by
        unfold weight centralPhysicalFiniteWeight
        exact centralPhysicalRowMarginal_nonnegative
          (by decide) later 0 _)
      (fun left hleft right hright => by
        unfold floor scale energy cutoffTwoSimpleFullSectorCost
          cutoffTwoFullSectorDirichlet
        exact
          centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_Dirichlet
            cutoffTwoHalfCoupling (by decide) later 0 coefficient
            left right hleft hright)
  have hscaleEnergy0 : (0 : Q') ≤ scale * energy :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt (cutoffTwoSimpleFullSectorCost_pos later))
      (cutoffTwoFullSectorDirichlet_nonnegative_local later coefficient)
  have hmassScaled : (mass * mass) * (scale * energy) ≤
      1 * (scale * energy) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (cutoffTwoFullSectorMass_square_le_one later)
      hscaleEnergy0
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hmassScaled
      (Q'.le_of_eqv (Q'.one_mul_eqv (scale * energy))))

def cutoffTwoSimpleFullSectorClearedDirichletAt
    (later : Nat) (hlater : 2 ≤ later)
    (massFloor : Q')
    (hmass : massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoCapacityClearedDirichletAt later
      (centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) later 0)
      (cutoffTwoSimpleFullSectorCost later)
      massFloor where
  later_ge := hlater
  total_cost_pos := cutoffTwoSimpleFullSectorCost_pos later
  mass_floor_le := hmass
  cleared_coercivity :=
    cutoffTwo_edgeFloor_mul_fullVariance_le_simpleCost_mul_Dirichlet later

/-! ## 3. Explicit ambient polynomial cost -/

def cutoffTwoAmbientFullSectorCost (later : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale later 0

theorem cutoffTwoSimpleFullSectorCost_le_ambient (later : Nat) :
    cutoffTwoSimpleFullSectorCost later ≤
      cutoffTwoAmbientFullSectorCost later :=
  centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_le_ambient
    cutoffTwoHalfCoupling (by decide) later 0

theorem cutoffTwoAmbientFullSectorCost_pos (later : Nat) :
    (0 : Q') < cutoffTwoAmbientFullSectorCost later :=
  centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale_pos later 0

theorem cutoffTwo_edgeFloor_mul_fullVariance_le_ambientCost_mul_Dirichlet
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoAmbientFullSectorCost later *
        cutoffTwoFullSectorDirichlet later coefficient := by
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _
    (cutoffTwoSimpleFullSectorCost_le_ambient later)
    (cutoffTwoFullSectorDirichlet_nonnegative_local later coefficient)
  exact Q'.le_trans' _ _ _
    (cutoffTwo_edgeFloor_mul_fullVariance_le_simpleCost_mul_Dirichlet
      later coefficient)
    hscale

def cutoffTwoAmbientFullSectorClearedDirichletAt
    (later : Nat) (hlater : 2 ≤ later)
    (massFloor : Q')
    (hmass : massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoCapacityClearedDirichletAt later
      (centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) later 0)
      (cutoffTwoAmbientFullSectorCost later)
      massFloor where
  later_ge := hlater
  total_cost_pos := cutoffTwoAmbientFullSectorCost_pos later
  mass_floor_le := hmass
  cleared_coercivity :=
    cutoffTwo_edgeFloor_mul_fullVariance_le_ambientCost_mul_Dirichlet later

/-! ## 4. The explicit ambient ratio is the remaining compiler input -/

structure CutoffTwoCofinalAmbientFullSectorRatio
    (effectiveFloor massFloor : Q') : Type 1 where
  effective_floor_pos : (0 : Q') < effectiveFloor
  mass_floor_pos : (0 : Q') < massFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  mass_floor_le : ∀ request,
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) (anchor request) 0
  ratio_bound : ∀ request,
    effectiveFloor * cutoffTwoAmbientFullSectorCost (anchor request) ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) (anchor request) 0

namespace CutoffTwoCofinalAmbientFullSectorRatio

def toCofinalCapacityClearedGluing
    {effectiveFloor massFloor : Q'}
    (family : CutoffTwoCofinalAmbientFullSectorRatio
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
    cutoffTwoAmbientFullSectorCost (family.anchor request)
  cleared := fun request =>
    cutoffTwoAmbientFullSectorClearedDirichletAt
      (family.anchor request)
      (Nat.le_trans (Nat.le_max_left 2 request)
        (family.anchor_ge request))
      massFloor (family.mass_floor_le request)
  ratio_bound := family.ratio_bound

def toCompletedStrictContractionData
    {effectiveFloor massFloor : Q'}
    (family : CutoffTwoCofinalAmbientFullSectorRatio
      effectiveFloor massFloor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalCapacityClearedGluing
    |>.toCompletedStrictContractionData

end CutoffTwoCofinalAmbientFullSectorRatio

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.cutoffTwoFullSectorMass_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.cutoffTwo_edgeFloor_mul_fullVariance_le_simpleCost_mul_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.cutoffTwoSimpleFullSectorClearedDirichletAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.cutoffTwoSimpleFullSectorCost_le_ambient
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.cutoffTwo_edgeFloor_mul_fullVariance_le_ambientCost_mul_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.cutoffTwoAmbientFullSectorClearedDirichletAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.CutoffTwoCofinalAmbientFullSectorRatio.toCompletedStrictContractionData
