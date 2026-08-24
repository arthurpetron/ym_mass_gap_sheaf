/-
# State semantics and constructive decision for component mergers

The cutoff-two component-merger list is not merely a bookkeeping residual.
An index belongs to it exactly when its later vacuum-sector state

* lies outside the certified cutoff-two cube/vacuum component, yet
* obeys the cutoff-two label bound and has strictly positive cutoff-two row
  marginal.

Thus a listed state was already present in another positive cutoff-two
component and has joined the rooted vacuum component at the later cutoff.
This file proves that iff, packages an explicit witness, and constructs a
finite decision returning either the no-merger certificate or a merger
witness.  Every witness forces strictly positive merger mass.

No witness at a cutoff larger than two is produced here.  No cofinal
stability, uniform gap, thermodynamic/continuum construction, or Clay mass
gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact state-level meaning of merger membership -/

theorem mem_cutoffTwoNewComponentMergerIndices_iff
    {later index : Nat} (hcutoff : 2 ≤ later) :
    index ∈ cutoffTwoNewComponentMergerIndices later ↔
      index ∈ cutoffTwoEdgeLoadFullStates later ∧
        centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
            (by decide) later 0 index ∉ cutoffTwoCubeSectorStates ∧
          labelWithinB 2 (centralLowerFaceIds 0)
              (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                (by decide) later 0 index) = true ∧
            (0 : Q') <
              centralPhysicalRowMarginal cutoffTwoHalfCoupling
                (by decide) 2 0
                (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                  (by decide) later 0 index) := by
  constructor
  · intro hmerger
    have hparts := List.mem_filter.mp hmerger
    have hnew :=
      (mem_cutoffTwoEdgeLoadNewStates_iff_state_not_mem_cubeSector
        hcutoff).mp hparts.1
    have houtsideFalse :
        cutoffTwoNewStateOutsidePositiveCarrierB later index = false := by
      cases houtside :
          cutoffTwoNewStateOutsidePositiveCarrierB later index with
      | false => rfl
      | true =>
          rw [houtside] at hparts
          exact False.elim
            ((by decide : (false : Bool) ≠ true) hparts.2)
    unfold cutoffTwoNewStateOutsidePositiveCarrierB
      centralPhysicalPositiveSourceOutsideB at houtsideFalse
    cases hand :
        (labelWithinB 2 (centralLowerFaceIds 0)
            (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
              (by decide) later 0 index) &&
          decide ((0 : Q') <
            centralPhysicalRowMarginal cutoffTwoHalfCoupling
              (by decide) 2 0
              (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                (by decide) later 0 index))) with
    | false =>
        rw [hand] at houtsideFalse
        exact False.elim
          ((by decide : (true : Bool) ≠ false) houtsideFalse)
    | true =>
        have hinside := Bool.and_eq_true_iff.mp hand
        exact ⟨hnew.1, hnew.2, hinside.1,
          (decide_eq_true_eq.mp hinside.2)⟩
  · rintro ⟨hfull, hnotCube, hwithin, hrow⟩
    apply List.mem_filter.mpr
    refine ⟨
      (mem_cutoffTwoEdgeLoadNewStates_iff_state_not_mem_cubeSector
        hcutoff).mpr ⟨hfull, hnotCube⟩,
      ?_⟩
    have hdecision :
        decide ((0 : Q') <
          centralPhysicalRowMarginal cutoffTwoHalfCoupling
            (by decide) 2 0
            (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
              (by decide) later 0 index)) = true := by
      exact decide_eq_true hrow
    unfold cutoffTwoNewStateOutsidePositiveCarrierB
      centralPhysicalPositiveSourceOutsideB
    simp only [hwithin, hdecision, Bool.true_and, Bool.not_true,
      Bool.not_false]

/-! ## 2. Every merger index carries positive stationary mass -/

private theorem listQSum_pos_of_mem_local
    {A : Type} (value : A → Q')
    (hnonnegative : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      (0 : Q') < value item → (0 : Q') < listQSum value items
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem, hpos => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.pos_of_lt_of_le hpos
          (Q'.add_le_self_of_nonneg
            (value head) (listQSum value tail)
            (listQSum_nonnegative_on value tail
              (fun tailItem _ => hnonnegative tailItem)))
      · have ih := listQSum_pos_of_mem_local
          value hnonnegative tail htail hpos
        have hle :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head)
          rwa [Q'.zero_add'] at h
        exact Q'.pos_of_lt_of_le ih hle

theorem cutoffTwoNewComponentMergerMass_pos_of_index
    {later index : Nat}
    (hindex : index ∈ cutoffTwoNewComponentMergerIndices later) :
    (0 : Q') < cutoffTwoNewComponentMergerMass later := by
  have hnew := (List.mem_filter.mp hindex).1
  have hsector :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hnew).1
  unfold cutoffTwoNewComponentMergerMass finiteWeightedMass
  apply listQSum_pos_of_mem_local
    (cutoffTwoEdgeLoadWeight later)
  · intro candidate
    unfold cutoffTwoEdgeLoadWeight centralPhysicalFiniteWeight
    exact centralPhysicalRowMarginal_nonnegative (by decide) later 0 _
  · exact hindex
  · unfold cutoffTwoEdgeLoadWeight
    exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsector

/-! ## 3. Constructive finite decision with an explicit witness -/

structure CutoffTwoComponentMergerWitness (later : Nat) : Type where
  index : Nat
  index_mem : index ∈ cutoffTwoNewComponentMergerIndices later

structure CutoffTwoNoComponentMergerCertificate (later : Nat) : Type where
  certified : cutoffTwoNoComponentMergerCheck later = true

structure CutoffTwoComponentMergerMassZeroCertificate (later : Nat) : Type where
  zero : cutoffTwoNewComponentMergerMass later ≈ 0

structure CutoffTwoComponentMergerMassPositiveWitness (later : Nat) : Type where
  positive : (0 : Q') < cutoffTwoNewComponentMergerMass later

namespace CutoffTwoComponentMergerWitness

theorem state_semantics
    {later : Nat} (witness : CutoffTwoComponentMergerWitness later)
    (hcutoff : 2 ≤ later) :
    witness.index ∈ cutoffTwoEdgeLoadFullStates later ∧
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 witness.index ∉ cutoffTwoCubeSectorStates ∧
        labelWithinB 2 (centralLowerFaceIds 0)
            (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
              (by decide) later 0 witness.index) = true ∧
          (0 : Q') <
            centralPhysicalRowMarginal cutoffTwoHalfCoupling
              (by decide) 2 0
              (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                (by decide) later 0 witness.index) :=
  (mem_cutoffTwoNewComponentMergerIndices_iff hcutoff).mp witness.index_mem

theorem mergerMass_pos
    {later : Nat} (witness : CutoffTwoComponentMergerWitness later) :
    (0 : Q') < cutoffTwoNewComponentMergerMass later :=
  cutoffTwoNewComponentMergerMass_pos_of_index witness.index_mem

end CutoffTwoComponentMergerWitness

def cutoffTwoComponentMergerDecision (later : Nat) :
    Sum (CutoffTwoNoComponentMergerCertificate later)
      (CutoffTwoComponentMergerWitness later) := by
  cases hindices : cutoffTwoNewComponentMergerIndices later with
  | nil =>
      exact Sum.inl
        { certified :=
            (cutoffTwoNoComponentMergerCheck_true_iff_indices_empty later).mpr
              hindices }
  | cons head tail =>
      exact Sum.inr
        { index := head
          index_mem := by
            rw [hindices]
            exact List.mem_cons_self }

def cutoffTwoComponentMergerMassZeroOrPositiveData (later : Nat) :
    Sum (CutoffTwoComponentMergerMassZeroCertificate later)
      (CutoffTwoComponentMergerMassPositiveWitness later) := by
  cases cutoffTwoComponentMergerDecision later with
  | inl certificate =>
      exact Sum.inl
        { zero := cutoffTwoNewComponentMergerMass_eqv_zero_of_check
            certificate.certified }
  | inr witness =>
      exact Sum.inr { positive := witness.mergerMass_pos }

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics.mem_cutoffTwoNewComponentMergerIndices_iff
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics.cutoffTwoNewComponentMergerMass_pos_of_index
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics.CutoffTwoComponentMergerWitness.state_semantics
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics.CutoffTwoComponentMergerWitness.mergerMass_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics.cutoffTwoComponentMergerDecision
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics.cutoffTwoComponentMergerMassZeroOrPositiveData
