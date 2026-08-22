/-
# A constructed pulled edge floor for every fixed BF4 vacuum carrier

The cutoff-two construction of a persistent canonical-path edge floor uses
only three facts which hold at every fixed representation cutoff: the base
vacuum component is finite, its positive support edges persist after the
canonical cutoff embedding, and every fixed ordered-pair cylinder retains at
least half of its value beyond the common new-label-tail schedule.

This module carries out that construction with the base cutoff and finite
half-extent left arbitrary.  Thus every fixed canonical vacuum component has
one positive rational floor for all of its base-positive edges at every later
cutoff.  The floor and its start may depend on the base component.  No lower
bound uniform in an expanding/cofinal family is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
import YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pair-cylinder retention on an arbitrary old carrier -/

private theorem centralHalfStates_mem_of_le_local
    {anchor later half : Nat} (hcutoff : anchor ≤ later)
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates anchor half) :
    state ∈ centralHalfStates later half := by
  unfold centralHalfStates at hstate ⊢
  have hsound := boundedEdgeLabellings_sound
    anchor (centralLowerFaceIds half) state hstate
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    have hbound := hsound.1 edge hedge
    omega
  · exact hsound.2

/-- Ordered source-target cylinders obey the common half-retention estimate.
The proof is independent of the selected old vacuum component. -/
theorem half_mul_centralNormalizedPhysicalReflectedKernel_le_of_increment_le_one
    {w : Q'} (hw : (0 : Q') ≤ w)
    {anchor later half : Nat} (hcutoff : anchor ≤ later)
    (hincrementOne :
      slabParametricKCutoffIncrement
        w anchor later (centralExtent half) ≤ (1 : Q'))
    {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates anchor half)
    (hright : right ∈ centralHalfStates anchor half) :
    HalfPow.half *
        centralNormalizedPhysicalReflectedKernel
          w hw anchor half left right ≤
      centralNormalizedPhysicalReflectedKernel
        w hw later half left right := by
  have hleftLater : left ∈ centralHalfStates later half :=
    centralHalfStates_mem_of_le_local hcutoff hleft
  have hrightLater : right ∈ centralHalfStates later half :=
    centralHalfStates_mem_of_le_local hcutoff hright
  let observable := centralPairCylinderObservable half left right
  have hretained :=
    half_mul_slabNomeCutoffBoundedObservableExpectation_le_of_increment_le_one
      hw hcutoff hincrementOne observable
  have hanchorEq :=
    centralNormalizedPhysicalReflectedKernel_eq_expectation
      (w := w) (hw := hw) hleft hright
  have hlaterEq :=
    centralNormalizedPhysicalReflectedKernel_eq_expectation
      (w := w) (hw := hw) hleftLater hrightLater
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left HalfPow.half _ _ hanchorEq)) ?_
  exact Q'.le_trans' _ _ _ hretained (Q'.ge_of_eqv hlaterEq)

/-- A base-positive normalized edge remains positive in every later pulled
kernel on the same old index carrier. -/
theorem centralPhysicalFinitePulledKernel_pos_of_base_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half left right : Nat} (hlater : base ≤ later)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w hw base half left right) :
    (0 : Q') <
      centralPhysicalFinitePulledKernel
        w hw base later half left right := by
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw base half hleft
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw base half hright
  have hadjacentBase :
      centralPhysicalFiniteSupportAdjacentB
          w hw base half left right = true :=
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hleft hright).mpr hpositive
  have hadjacentLater :=
    centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap
      hlater hleftLt hrightLt hadjacentBase
  have hleftLater :=
    centralPhysicalFiniteVacuumSectorIndexMap_mem hlater hleft
  have hrightLater :=
    centralPhysicalFiniteVacuumSectorIndexMap_mem hlater hright
  unfold centralPhysicalFinitePulledKernel
  exact centralPhysicalFiniteKernel_pos_of_supportAdjacent
    hleftLater hrightLater hadjacentLater

/-- Pair-cylinder retention recoded on an arbitrary fixed base vacuum-sector
index carrier. -/
theorem half_mul_centralPhysicalFinitePulledKernel_le_of_increment_le_one
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base anchor later half : Nat}
    (hbaseAnchor : base ≤ anchor)
    (hanchorLater : anchor ≤ later)
    (hincrementOne :
      slabParametricKCutoffIncrement
        w anchor later (centralExtent half) ≤ (1 : Q'))
    {left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half) :
    HalfPow.half *
        centralPhysicalFinitePulledKernel
          w hw base anchor half left right ≤
      centralPhysicalFinitePulledKernel
        w hw base later half left right := by
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw base half hleft
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw base half hright
  have hleftAnchor :
      centralPhysicalFiniteStateAt w hw base half left ∈
        centralHalfStates anchor half := by
    have hpositiveAnchor := mem_centralPositiveHalfStates_of_le
      (w := w) hw hbaseAnchor
      (centralPhysicalFiniteStateAt_mem_positive
        w hw base half hleftLt)
    exact (mem_centralPositiveHalfStates_iff.mp hpositiveAnchor).1
  have hrightAnchor :
      centralPhysicalFiniteStateAt w hw base half right ∈
        centralHalfStates anchor half := by
    have hpositiveAnchor := mem_centralPositiveHalfStates_of_le
      (w := w) hw hbaseAnchor
      (centralPhysicalFiniteStateAt_mem_positive
        w hw base half hrightLt)
    exact (mem_centralPositiveHalfStates_iff.mp hpositiveAnchor).1
  rw [centralPhysicalFinitePulledKernel_eq_normalizedKernel
      hbaseAnchor hleftLt hrightLt,
    centralPhysicalFinitePulledKernel_eq_normalizedKernel
      (Nat.le_trans hbaseAnchor hanchorLater) hleftLt hrightLt]
  exact
    half_mul_centralNormalizedPhysicalReflectedKernel_le_of_increment_le_one
      hw hanchorLater hincrementOne hleftAnchor hrightAnchor

/-! ## 2. A finite anchor minimum for every base component -/

/-- The exact persistent-floor datum on one arbitrary fixed old component. -/
structure FixedBasePulledPositiveEdgeFloor
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  start : Nat
  start_ge_base : base ≤ start
  floor_le : ∀ later : Nat, start ≤ later →
    ∀ left right : Nat,
      left ∈ centralPhysicalFiniteVacuumSectorIndices w hw base half →
      right ∈ centralPhysicalFiniteVacuumSectorIndices w hw base half →
      (0 : Q') < centralPhysicalFiniteKernel
        w hw base half left right →
      floor ≤ centralPhysicalFinitePulledKernel
        w hw base later half left right

def fixedBasePulledEdgeFloorAnchor
    (w : Q') (base half : Nat) : Nat :=
  max base (centralPhysicalUniformRowFloorCutoff w half)

theorem fixedBasePulledEdgeFloorAnchor_ge_base
    (w : Q') (base half : Nat) :
    base ≤ fixedBasePulledEdgeFloorAnchor w base half := by
  unfold fixedBasePulledEdgeFloorAnchor
  exact Nat.le_max_left _ _

theorem uniformRowFloorCutoff_le_fixedBasePulledEdgeFloorAnchor
    (w : Q') (base half : Nat) :
    centralPhysicalUniformRowFloorCutoff w half ≤
      fixedBasePulledEdgeFloorAnchor w base half := by
  unfold fixedBasePulledEdgeFloorAnchor
  exact Nat.le_max_right _ _

def fixedBasePulledEdgeAnchorMinimum
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) : Q' :=
  listPositiveMinOne
    (fun pair => positiveOrOne
      (centralPhysicalFinitePulledKernel
        w hw base (fixedBasePulledEdgeFloorAnchor w base half)
        half pair.1 pair.2))
    (cartesian
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)
      (centralPhysicalFiniteVacuumSectorIndices w hw base half))

theorem fixedBasePulledEdgeAnchorMinimum_pos
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) :
    (0 : Q') < fixedBasePulledEdgeAnchorMinimum w hw base half := by
  unfold fixedBasePulledEdgeAnchorMinimum
  apply listPositiveMinOne_pos
  intro pair _hpair
  exact positiveOrOne_pos _

def fixedBasePulledPositiveEdgeFloorValue
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) : Q' :=
  HalfPow.half * fixedBasePulledEdgeAnchorMinimum w hw base half

theorem fixedBasePulledPositiveEdgeFloorValue_pos
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) :
    (0 : Q') < fixedBasePulledPositiveEdgeFloorValue w hw base half := by
  unfold fixedBasePulledPositiveEdgeFloorValue
  exact ExpNeg.half_mul_pos _
    (fixedBasePulledEdgeAnchorMinimum_pos w hw base half)

theorem fixedBasePulledPositiveEdgeFloorValue_le_half_anchor
    {w : Q'} {hw : (0 : Q') ≤ w} {base half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hbasePositive : (0 : Q') <
      centralPhysicalFiniteKernel w hw base half left right) :
    fixedBasePulledPositiveEdgeFloorValue w hw base half ≤
      HalfPow.half *
        centralPhysicalFinitePulledKernel
          w hw base (fixedBasePulledEdgeFloorAnchor w base half)
          half left right := by
  have hanchorPositive : (0 : Q') <
      centralPhysicalFinitePulledKernel
        w hw base (fixedBasePulledEdgeFloorAnchor w base half)
        half left right :=
    centralPhysicalFinitePulledKernel_pos_of_base_pos
      (fixedBasePulledEdgeFloorAnchor_ge_base w base half)
      hleft hright hbasePositive
  have hpair : (left, right) ∈
      cartesian
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)
        (centralPhysicalFiniteVacuumSectorIndices w hw base half) :=
    (mem_cartesian_iff _ _ (left, right)).mpr ⟨hleft, hright⟩
  have hminimum := listPositiveMinOne_le_of_mem
    (fun pair => positiveOrOne
      (centralPhysicalFinitePulledKernel
        w hw base (fixedBasePulledEdgeFloorAnchor w base half)
        half pair.1 pair.2))
    (cartesian
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)
      (centralPhysicalFiniteVacuumSectorIndices w hw base half))
    (left, right) hpair
  unfold fixedBasePulledPositiveEdgeFloorValue
    fixedBasePulledEdgeAnchorMinimum
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (by simpa [positiveOrOne, hanchorPositive] using hminimum)
    HalfPow.half_nonneg

/-! ## 3. Construct the arbitrary-base persistent floor -/

theorem fixedBasePulledEdgeFloor_increment_le_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base half later : Nat}
    (hlater : fixedBasePulledEdgeFloorAnchor w base half ≤ later) :
    slabParametricKCutoffIncrement
        w (fixedBasePulledEdgeFloorAnchor w base half)
        later (centralExtent half) ≤ (1 : Q') := by
  have huniformLater :
      centralPhysicalUniformRowFloorCutoff w half ≤ later :=
    Nat.le_trans
      (uniformRowFloorCutoff_le_fixedBasePulledEdgeFloorAnchor
        w base half) hlater
  have hscheduled :
      slabParametricKCutoffIncrement
          w (centralPhysicalUniformRowFloorCutoff w half)
          later (centralExtent half) ≤ (1 : Q') := by
    unfold centralPhysicalUniformRowFloorCutoff
      centralPhysicalTargetShellCutoff
    exact slabPhysicalNomeCutoffIncrement_le_tolerance
      (w := w) hw0 hw1 (centralExtent half) (by decide) huniformLater
  exact Q'.le_trans' _ _ _
    (slabParametricKCutoffIncrement_antitone_base
      (w := w) (Q'.le_of_lt hw0)
      (uniformRowFloorCutoff_le_fixedBasePulledEdgeFloorAnchor
        w base half) hlater)
    hscheduled

/-- Every fixed canonical vacuum component has a constructed persistent
positive floor on all edges already positive at its base cutoff. -/
opaque fixedBasePulledPositiveEdgeFloor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    FixedBasePulledPositiveEdgeFloor
      w (Q'.le_of_lt hw0) base half :=
  { floor := fixedBasePulledPositiveEdgeFloorValue
      w (Q'.le_of_lt hw0) base half
    floor_pos := fixedBasePulledPositiveEdgeFloorValue_pos
      w (Q'.le_of_lt hw0) base half
    start := fixedBasePulledEdgeFloorAnchor w base half
    start_ge_base := fixedBasePulledEdgeFloorAnchor_ge_base w base half
    floor_le := by
      intro later hlater left right hleft hright hbasePositive
      exact Q'.le_trans' _ _ _
        (fixedBasePulledPositiveEdgeFloorValue_le_half_anchor
          hleft hright hbasePositive)
        (half_mul_centralPhysicalFinitePulledKernel_le_of_increment_le_one
          (fixedBasePulledEdgeFloorAnchor_ge_base w base half)
          hlater
          (fixedBasePulledEdgeFloor_increment_le_one hw0 hw1 hlater)
          hleft hright) }

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor.centralPhysicalFinitePulledKernel_pos_of_base_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor.half_mul_centralPhysicalFinitePulledKernel_le_of_increment_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor.fixedBasePulledPositiveEdgeFloor
