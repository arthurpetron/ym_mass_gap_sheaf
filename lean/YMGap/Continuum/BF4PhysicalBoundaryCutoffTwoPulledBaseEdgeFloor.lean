/-
# A constructed uniform floor on the transported cutoff-two path edges

The fixed cutoff-two canonical paths use only kernel entries already positive
at cutoff two.  Such entries remain positive at every later representation
cutoff.  To make that persistence quantitative, anchor beyond both cutoff two
and the existing unit new-label-tail schedule.  The ordered-pair cylinder
numerator can only gain nonnegative mass, while the partition grows by at most
one and is already at least one.  Hence every anchored normalized pair entry
retains at least half its anchor value at all later cutoffs.

A finite positive minimum over the fixed 65 by 65 ordered carrier pairs at the
anchor, restricted by `positiveOrOne`, then supplies one explicit positive
floor for every transported base-positive edge.  This inhabits the exactly
sufficient canonical-path certificate; it does not claim a floor for entries
which first become positive only at a later cutoff.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
import YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pair-cylinder half retention -/

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

/-- Ordered source-target cylinders obey the same half-retention estimate as
source rows, because the proof uses only cutoff stability, nonnegativity, and
the common partition increment. -/
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

/-- Pair-cylinder half retention recoded on the fixed cutoff-two index
carrier. -/
theorem half_mul_cutoffTwoPulledKernelAt_le_of_increment_le_one
    {anchor later : Nat}
    (hanchorTwo : 2 ≤ anchor)
    (hcutoff : anchor ≤ later)
    (hincrementOne :
      slabParametricKCutoffIncrement
        cutoffTwoHalfCoupling anchor later (centralExtent 0) ≤ (1 : Q'))
    {left right : Nat}
    (hleft : left ∈ cutoffTwoPulledStates)
    (hright : right ∈ cutoffTwoPulledStates) :
    HalfPow.half * cutoffTwoPulledKernelAt anchor left right ≤
      cutoffTwoPulledKernelAt later left right := by
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hleft
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hright
  have hleftAnchor :
      centralPhysicalFiniteStateAt
          cutoffTwoHalfCoupling (by decide) 2 0 left ∈
        centralHalfStates anchor 0 := by
    have hpositiveAnchor := mem_centralPositiveHalfStates_of_le
      (w := cutoffTwoHalfCoupling) (by decide) hanchorTwo
      (centralPhysicalFiniteStateAt_mem_positive
        cutoffTwoHalfCoupling (by decide) 2 0 hleftLt)
    exact (mem_centralPositiveHalfStates_iff.mp hpositiveAnchor).1
  have hrightAnchor :
      centralPhysicalFiniteStateAt
          cutoffTwoHalfCoupling (by decide) 2 0 right ∈
        centralHalfStates anchor 0 := by
    have hpositiveAnchor := mem_centralPositiveHalfStates_of_le
      (w := cutoffTwoHalfCoupling) (by decide) hanchorTwo
      (centralPhysicalFiniteStateAt_mem_positive
        cutoffTwoHalfCoupling (by decide) 2 0 hrightLt)
    exact (mem_centralPositiveHalfStates_iff.mp hpositiveAnchor).1
  unfold cutoffTwoPulledKernelAt
  rw [centralPhysicalFinitePulledKernel_eq_normalizedKernel
      hanchorTwo hleftLt hrightLt,
    centralPhysicalFinitePulledKernel_eq_normalizedKernel
      (Nat.le_trans hanchorTwo hcutoff) hleftLt hrightLt]
  exact
    half_mul_centralNormalizedPhysicalReflectedKernel_le_of_increment_le_one
      (by decide) hcutoff hincrementOne hleftAnchor hrightAnchor

/-! ## 2. One explicit finite anchor and positive minimum -/

def cutoffTwoPulledBaseEdgeFloorAnchor : Nat :=
  max 2 (centralPhysicalUniformRowFloorCutoff cutoffTwoHalfCoupling 0)

theorem cutoffTwoPulledBaseEdgeFloorAnchor_ge_two :
    2 ≤ cutoffTwoPulledBaseEdgeFloorAnchor := by
  unfold cutoffTwoPulledBaseEdgeFloorAnchor
  exact Nat.le_max_left _ _

theorem uniformRowFloorCutoff_le_cutoffTwoPulledBaseEdgeFloorAnchor :
    centralPhysicalUniformRowFloorCutoff cutoffTwoHalfCoupling 0 ≤
      cutoffTwoPulledBaseEdgeFloorAnchor := by
  unfold cutoffTwoPulledBaseEdgeFloorAnchor
  exact Nat.le_max_right _ _

def cutoffTwoPulledBaseEdgeAnchorMinimum : Q' :=
  listPositiveMinOne
    (fun pair => positiveOrOne
      (cutoffTwoPulledKernelAt
        cutoffTwoPulledBaseEdgeFloorAnchor pair.1 pair.2))
    (cartesian cutoffTwoPulledStates cutoffTwoPulledStates)

theorem cutoffTwoPulledBaseEdgeAnchorMinimum_pos :
    (0 : Q') < cutoffTwoPulledBaseEdgeAnchorMinimum := by
  unfold cutoffTwoPulledBaseEdgeAnchorMinimum
  apply listPositiveMinOne_pos
  intro pair _hpair
  exact positiveOrOne_pos _

def cutoffTwoPulledUniformBasePositiveEdgeFloorValue : Q' :=
  HalfPow.half * cutoffTwoPulledBaseEdgeAnchorMinimum

theorem cutoffTwoPulledUniformBasePositiveEdgeFloorValue_pos :
    (0 : Q') < cutoffTwoPulledUniformBasePositiveEdgeFloorValue := by
  unfold cutoffTwoPulledUniformBasePositiveEdgeFloorValue
  exact ExpNeg.half_mul_pos _ cutoffTwoPulledBaseEdgeAnchorMinimum_pos

theorem cutoffTwoPulledUniformBasePositiveEdgeFloorValue_le_half_anchor
    {left right : Nat}
    (hleft : left ∈ cutoffTwoPulledStates)
    (hright : right ∈ cutoffTwoPulledStates)
    (hbasePositive : (0 : Q') <
      centralPhysicalFiniteKernel
        cutoffTwoHalfCoupling (by decide) 2 0 left right) :
    cutoffTwoPulledUniformBasePositiveEdgeFloorValue ≤
      HalfPow.half *
        cutoffTwoPulledKernelAt
          cutoffTwoPulledBaseEdgeFloorAnchor left right := by
  have hanchorPositive : (0 : Q') <
      cutoffTwoPulledKernelAt
        cutoffTwoPulledBaseEdgeFloorAnchor left right :=
    cutoffTwoPulledKernelAt_pos_of_base_pos
      cutoffTwoPulledBaseEdgeFloorAnchor_ge_two
      hleft hright hbasePositive
  have hpair : (left, right) ∈
      cartesian cutoffTwoPulledStates cutoffTwoPulledStates :=
    (mem_cartesian_iff _ _ (left, right)).mpr ⟨hleft, hright⟩
  have hminimum := listPositiveMinOne_le_of_mem
    (fun pair => positiveOrOne
      (cutoffTwoPulledKernelAt
        cutoffTwoPulledBaseEdgeFloorAnchor pair.1 pair.2))
    (cartesian cutoffTwoPulledStates cutoffTwoPulledStates)
    (left, right) hpair
  unfold cutoffTwoPulledUniformBasePositiveEdgeFloorValue
    cutoffTwoPulledBaseEdgeAnchorMinimum
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (by simpa [positiveOrOne, hanchorPositive] using hminimum)
    HalfPow.half_nonneg

/-! ## 3. Construct the canonical-path edge-floor certificate -/

theorem cutoffTwoPulledBaseEdgeFloor_increment_le_one
    {later : Nat}
    (hlater : cutoffTwoPulledBaseEdgeFloorAnchor ≤ later) :
    slabParametricKCutoffIncrement
        cutoffTwoHalfCoupling
        cutoffTwoPulledBaseEdgeFloorAnchor later (centralExtent 0) ≤
      (1 : Q') := by
  have huniformLater :
      centralPhysicalUniformRowFloorCutoff cutoffTwoHalfCoupling 0 ≤
        later :=
    Nat.le_trans
      uniformRowFloorCutoff_le_cutoffTwoPulledBaseEdgeFloorAnchor hlater
  have hscheduled :
      slabParametricKCutoffIncrement
          cutoffTwoHalfCoupling
          (centralPhysicalUniformRowFloorCutoff cutoffTwoHalfCoupling 0)
          later (centralExtent 0) ≤ (1 : Q') := by
    unfold centralPhysicalUniformRowFloorCutoff
      centralPhysicalTargetShellCutoff
    exact slabPhysicalNomeCutoffIncrement_le_tolerance
      (w := cutoffTwoHalfCoupling) (by decide) (by decide)
      (centralExtent 0) (by decide) huniformLater
  exact Q'.le_trans' _ _ _
    (slabParametricKCutoffIncrement_antitone_base
      (w := cutoffTwoHalfCoupling) (by decide)
      uniformRowFloorCutoff_le_cutoffTwoPulledBaseEdgeFloorAnchor hlater)
    hscheduled

/-- The explicit inhabited certificate required by the transported canonical
paths.  It is sealed at this presentation boundary so downstream theorem
application does not normalize the finite Cartesian minimum. -/
opaque cutoffTwoPulledUniformBasePositiveEdgeFloor :
    CutoffTwoPulledUniformBasePositiveEdgeFloor :=
  { floor := cutoffTwoPulledUniformBasePositiveEdgeFloorValue
    floor_pos := cutoffTwoPulledUniformBasePositiveEdgeFloorValue_pos
    start := cutoffTwoPulledBaseEdgeFloorAnchor
    start_ge_two := cutoffTwoPulledBaseEdgeFloorAnchor_ge_two
    floor_le := by
      intro later hlater left right hleft hright hbasePositive
      exact Q'.le_trans' _ _ _
        (cutoffTwoPulledUniformBasePositiveEdgeFloorValue_le_half_anchor
          hleft hright hbasePositive)
        (half_mul_cutoffTwoPulledKernelAt_le_of_increment_le_one
          cutoffTwoPulledBaseEdgeFloorAnchor_ge_two hlater
          (cutoffTwoPulledBaseEdgeFloor_increment_le_one hlater)
          hleft hright) }

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor.half_mul_centralNormalizedPhysicalReflectedKernel_le_of_increment_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor.half_mul_cutoffTwoPulledKernelAt_le_of_increment_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor.cutoffTwoPulledUniformBasePositiveEdgeFloorValue_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor.cutoffTwoPulledUniformBasePositiveEdgeFloor
