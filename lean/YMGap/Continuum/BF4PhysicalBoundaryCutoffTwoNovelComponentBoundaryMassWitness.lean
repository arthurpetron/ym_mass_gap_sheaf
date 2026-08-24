/-
# Quantitative stationary-mass data carried by embedded boundary crossings

The closure decision returns an explicit crossing edge on failure.  This file
records the exact quantitative facts carried by that edge.  Its normalized
later kernel entry and target stationary weight are strictly positive.  The
target weight is bounded by the corresponding shell submass: either the
corrected-slab-controlled outside-positive mass or the uncontrolled
component-merger mass.

Combining these facts with the closure decision gives a proof-carrying
trichotomy: closed boundary with increment-only new-shell control, a positive
outside-positive crossing whose total mass is bounded by the cutoff
increment, or a positive component-merger crossing.

No uniform lower bound on a crossing weight, no cofinal closure, no scalar
edge-floor payment, thermodynamic/continuum construction, or Clay mass gap is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureDecision

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Every boundary edge and target are quantitatively positive -/

theorem cutoffTwoEmbeddedVacuumBoundaryExit_kernel_pos
    {later : Nat} (boundary : CutoffTwoEmbeddedVacuumBoundaryExit later) :
    (0 : Q') < centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0
      boundary.source boundary.target :=
  (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
    boundary.source_mem_later_sector boundary.target_mem_later_sector).mp
      boundary.edge

theorem cutoffTwoEmbeddedVacuumBoundaryExit_targetWeight_pos
    {later : Nat} (boundary : CutoffTwoEmbeddedVacuumBoundaryExit later) :
    (0 : Q') < cutoffTwoEdgeLoadWeight later boundary.target := by
  unfold cutoffTwoEdgeLoadWeight
  exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
    boundary.target_mem_later_sector

private theorem listQSum_member_le_nonnegative_local
    {Item : Type} (value : Item → Q')
    (hnonnegative : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List Item) {item : Item}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hnonnegative tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          value hnonnegative tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem cutoffTwoEdgeLoadWeight_nonnegative
    (later index : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadWeight later index := by
  unfold cutoffTwoEdgeLoadWeight centralPhysicalFiniteWeight
  exact centralPhysicalRowMarginal_nonnegative (by decide) later 0 _

/-! ## 2. The two semantic target branches pay into their exact submasses -/

theorem cutoffTwoBoundaryExitOutsidePositive_targetWeight_le_mass
    {later : Nat}
    (event : CutoffTwoBoundaryExitOutsidePositiveTarget later) :
    cutoffTwoEdgeLoadWeight later event.boundary.target ≤
      cutoffTwoNewOutsidePositiveMass later := by
  unfold cutoffTwoNewOutsidePositiveMass finiteWeightedMass
  exact listQSum_member_le_nonnegative_local
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadWeight_nonnegative later)
    (cutoffTwoNewOutsidePositiveIndices later) event.target_mem

theorem cutoffTwoBoundaryExitOutsidePositive_mass_pos
    {later : Nat}
    (event : CutoffTwoBoundaryExitOutsidePositiveTarget later) :
    (0 : Q') < cutoffTwoNewOutsidePositiveMass later :=
  Q'.pos_of_lt_of_le
    (cutoffTwoEmbeddedVacuumBoundaryExit_targetWeight_pos event.boundary)
    (cutoffTwoBoundaryExitOutsidePositive_targetWeight_le_mass event)

theorem cutoffTwoBoundaryExitComponentMerger_targetWeight_le_mass
    {later : Nat}
    (event : CutoffTwoBoundaryExitComponentMergerTarget later) :
    cutoffTwoEdgeLoadWeight later event.boundary.target ≤
      cutoffTwoNewComponentMergerMass later := by
  unfold cutoffTwoNewComponentMergerMass finiteWeightedMass
  exact listQSum_member_le_nonnegative_local
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadWeight_nonnegative later)
    (cutoffTwoNewComponentMergerIndices later) event.target_mem

theorem cutoffTwoBoundaryExitComponentMerger_mass_pos
    {later : Nat}
    (event : CutoffTwoBoundaryExitComponentMergerTarget later) :
    (0 : Q') < cutoffTwoNewComponentMergerMass later :=
  Q'.pos_of_lt_of_le
    (cutoffTwoEmbeddedVacuumBoundaryExit_targetWeight_pos event.boundary)
    (cutoffTwoBoundaryExitComponentMerger_targetWeight_le_mass event)

/-! ## 3. Quantitative Type-level trichotomy -/

structure CutoffTwoBoundaryClosedIncrementData (later : Nat) : Type where
  closure : CutoffTwoEmbeddedVacuumBoundaryClosedCertificate later
  no_merger : cutoffTwoNoComponentMergerCheck later = true
  merger_zero : cutoffTwoNewComponentMergerMass later ≈ 0
  new_mass_le_increment :
    cutoffTwoNewMass later ≤
      slabParametricKCutoffIncrement
        cutoffTwoHalfCoupling 2 later (centralExtent 0)

structure CutoffTwoBoundaryExitOutsidePositiveMassData
    (later : Nat) : Type where
  event : CutoffTwoBoundaryExitOutsidePositiveTarget later
  kernel_pos : (0 : Q') < centralPhysicalFiniteKernel
    cutoffTwoHalfCoupling (by decide) later 0
    event.boundary.source event.boundary.target
  target_weight_pos :
    (0 : Q') < cutoffTwoEdgeLoadWeight later event.boundary.target
  target_weight_le_mass :
    cutoffTwoEdgeLoadWeight later event.boundary.target ≤
      cutoffTwoNewOutsidePositiveMass later
  mass_pos : (0 : Q') < cutoffTwoNewOutsidePositiveMass later
  mass_le_increment :
    cutoffTwoNewOutsidePositiveMass later ≤
      slabParametricKCutoffIncrement
        cutoffTwoHalfCoupling 2 later (centralExtent 0)

structure CutoffTwoBoundaryExitComponentMergerMassData
    (later : Nat) : Type where
  event : CutoffTwoBoundaryExitComponentMergerTarget later
  kernel_pos : (0 : Q') < centralPhysicalFiniteKernel
    cutoffTwoHalfCoupling (by decide) later 0
    event.boundary.source event.boundary.target
  target_weight_pos :
    (0 : Q') < cutoffTwoEdgeLoadWeight later event.boundary.target
  target_weight_le_mass :
    cutoffTwoEdgeLoadWeight later event.boundary.target ≤
      cutoffTwoNewComponentMergerMass later
  mass_pos : (0 : Q') < cutoffTwoNewComponentMergerMass later

def cutoffTwoEmbeddedVacuumBoundaryMassTrichotomy
    (later : Nat) (hcutoff : 2 ≤ later) :
    Sum (CutoffTwoBoundaryClosedIncrementData later)
      (Sum (CutoffTwoBoundaryExitOutsidePositiveMassData later)
        (CutoffTwoBoundaryExitComponentMergerMassData later)) := by
  cases cutoffTwoEmbeddedVacuumBoundaryTrichotomy later hcutoff with
  | inl closure =>
      have hnoMerger :=
        cutoffTwoNoComponentMergerCheck_of_boundaryClosedCheck
          hcutoff closure.certified
      exact Sum.inl
        { closure := closure
          no_merger := hnoMerger
          merger_zero :=
            cutoffTwoNewComponentMergerMass_eqv_zero_of_check hnoMerger
          new_mass_le_increment :=
            cutoffTwoNewMass_le_increment_of_noComponentMergerCheck
              hcutoff hnoMerger }
  | inr crossing =>
      cases crossing with
      | inl event =>
          exact Sum.inr (Sum.inl
            { event := event
              kernel_pos :=
                cutoffTwoEmbeddedVacuumBoundaryExit_kernel_pos event.boundary
              target_weight_pos :=
                cutoffTwoEmbeddedVacuumBoundaryExit_targetWeight_pos
                  event.boundary
              target_weight_le_mass :=
                cutoffTwoBoundaryExitOutsidePositive_targetWeight_le_mass event
              mass_pos := cutoffTwoBoundaryExitOutsidePositive_mass_pos event
              mass_le_increment :=
                cutoffTwoNewOutsidePositiveMass_le_increment hcutoff })
      | inr event =>
          exact Sum.inr (Sum.inr
            { event := event
              kernel_pos :=
                cutoffTwoEmbeddedVacuumBoundaryExit_kernel_pos event.boundary
              target_weight_pos :=
                cutoffTwoEmbeddedVacuumBoundaryExit_targetWeight_pos
                  event.boundary
              target_weight_le_mass :=
                cutoffTwoBoundaryExitComponentMerger_targetWeight_le_mass event
              mass_pos := cutoffTwoBoundaryExitComponentMerger_mass_pos event })

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness.cutoffTwoEmbeddedVacuumBoundaryExit_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness.cutoffTwoEmbeddedVacuumBoundaryExit_targetWeight_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness.cutoffTwoBoundaryExitOutsidePositive_targetWeight_le_mass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness.cutoffTwoBoundaryExitOutsidePositive_mass_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness.cutoffTwoBoundaryExitComponentMerger_targetWeight_le_mass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness.cutoffTwoBoundaryExitComponentMerger_mass_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness.cutoffTwoEmbeddedVacuumBoundaryMassTrichotomy
