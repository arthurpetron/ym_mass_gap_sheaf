/-
# Generic constructive decision for moving-base component mergers

For arbitrary cutoffs, the generic moving-base mass split leaves one exact
residual: later vacuum-sector states which were already positive at the base
cutoff but belonged to a different base support component.  This file makes
that finite residual executable.

The decision returns either a proof-carrying empty-merger certificate or a
literal merger index.  The successful branch removes the residual from the
moving-base new-mass bound.  The witness branch carries exact state semantics,
strictly positive later stationary weight, and strictly positive total merger
mass.  The equal-cutoff anchor is inhabited.

No larger-cutoff no-merger outcome, uniform merger ceiling, local capacity
payment, cofinal schedule, thermodynamic/continuum construction, or Clay mass
gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact Boolean no-merger certificate -/

def centralPhysicalFiniteNoComponentMergerCheck
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Bool :=
  (centralPhysicalFiniteNewComponentMergerIndices
    w hw base later half).isEmpty

theorem centralPhysicalFiniteNoComponentMergerCheck_true_iff_indices_empty
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteNoComponentMergerCheck
        w hw base later half = true ↔
      centralPhysicalFiniteNewComponentMergerIndices
        w hw base later half = [] := by
  unfold centralPhysicalFiniteNoComponentMergerCheck
  exact List.isEmpty_iff

private theorem filter_not_isEmpty_true_iff_all_true
    (test : Nat → Bool) :
    ∀ items : List Nat,
      ((items.filter (fun index => !(test index))).isEmpty = true ↔
        ∀ index, index ∈ items → test index = true)
  | [] => by
      constructor
      · intro _ index hindex
        exact False.elim (List.not_mem_nil hindex)
      · intro _
        rfl
  | head :: tail => by
      cases hhead : test head with
      | false =>
          constructor
          · intro hempty
            simp only [List.filter_cons, hhead, Bool.not_false, if_true,
              List.isEmpty_cons] at hempty
            exact False.elim ((by decide : (false : Bool) ≠ true) hempty)
          · intro hall
            have hfalse := hall head List.mem_cons_self
            rw [hhead] at hfalse
            exact False.elim ((by decide : (false : Bool) ≠ true) hfalse)
      | true =>
          simp only [List.filter_cons, hhead, Bool.not_true]
          constructor
          · intro hempty index hindex
            rcases List.mem_cons.mp hindex with heq | hmem
            · subst index
              exact hhead
            · exact
                (filter_not_isEmpty_true_iff_all_true test tail).mp
                  hempty index hmem
          · intro hall
            apply (filter_not_isEmpty_true_iff_all_true test tail).mpr
            intro index hindex
            exact hall index (List.mem_cons_of_mem head hindex)

theorem centralPhysicalFiniteNoComponentMergerCheck_true_iff_all_new_outside
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteNoComponentMergerCheck
        w hw base later half = true ↔
      ∀ index,
        index ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
            w hw base later half →
          centralPhysicalFiniteNewStateOutsideBasePositiveB
            w hw base later half index = true := by
  unfold centralPhysicalFiniteNoComponentMergerCheck
    centralPhysicalFiniteNewComponentMergerIndices
  exact filter_not_isEmpty_true_iff_all_true
    (centralPhysicalFiniteNewStateOutsideBasePositiveB
      w hw base later half)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half)

/-! ## 2. Successful checks remove the merger residual -/

theorem centralPhysicalFiniteNewComponentMergerMass_eqv_zero_of_check
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (hcheck : centralPhysicalFiniteNoComponentMergerCheck
      w hw base later half = true) :
    centralPhysicalFiniteNewComponentMergerMass
      w hw base later half ≈ 0 := by
  have hnil :=
    (centralPhysicalFiniteNoComponentMergerCheck_true_iff_indices_empty
      w hw base later half).mp hcheck
  unfold centralPhysicalFiniteNewComponentMergerMass finiteWeightedMass
  rw [hnil]
  exact Q'.eqv_refl 0

theorem centralPhysicalFiniteVacuumSectorNewMass_le_increment_of_check
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (hcheck : centralPhysicalFiniteNoComponentMergerCheck
      w hw base later half = true) :
    centralPhysicalFiniteVacuumSectorNewMass
        w hw base later half ≤
      slabParametricKCutoffIncrement
        w base later (centralExtent half) := by
  let increment :=
    slabParametricKCutoffIncrement w base later (centralExtent half)
  have hbound :=
    centralPhysicalFiniteVacuumSectorNewMass_le_increment_add_merger
      (w := w) (hw := hw) (half := half) hcutoff
  have hzero :=
    centralPhysicalFiniteNewComponentMergerMass_eqv_zero_of_check hcheck
  have hcollapse :
      increment + centralPhysicalFiniteNewComponentMergerMass
          w hw base later half ≈ increment :=
    Q'.eqv_trans _ (increment + 0) _
      (Q'.add_eqv_congr_left increment _ 0 hzero)
      (Q'.eqv_of_eq (Q'.add_zero' increment))
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hcollapse)

/-! ## 3. Every explicit merger witness has positive mass -/

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

theorem centralPhysicalFiniteNewComponentMergerWeight_le_mass_of_index
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hindex : index ∈ centralPhysicalFiniteNewComponentMergerIndices
      w hw base later half) :
    centralPhysicalFiniteWeight w hw later half index ≤
      centralPhysicalFiniteNewComponentMergerMass
        w hw base later half := by
  unfold centralPhysicalFiniteNewComponentMergerMass finiteWeightedMass
  exact listQSum_member_le_nonnegative_local
    (centralPhysicalFiniteWeight w hw later half)
    (fun candidate => by
      unfold centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative
        hw later half
        (centralPhysicalFiniteStateAt w hw later half candidate))
    (centralPhysicalFiniteNewComponentMergerIndices
      w hw base later half) hindex

theorem centralPhysicalFiniteNewComponentMergerWeight_pos_of_index
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hindex : index ∈ centralPhysicalFiniteNewComponentMergerIndices
      w hw base later half) :
    (0 : Q') < centralPhysicalFiniteWeight w hw later half index := by
  have hnew := (List.mem_filter.mp hindex).1
  have hsector :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hnew).1
  exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsector

theorem centralPhysicalFiniteNewComponentMergerMass_pos_of_index
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hindex : index ∈ centralPhysicalFiniteNewComponentMergerIndices
      w hw base later half) :
    (0 : Q') < centralPhysicalFiniteNewComponentMergerMass
      w hw base later half :=
  Q'.pos_of_lt_of_le
    (centralPhysicalFiniteNewComponentMergerWeight_pos_of_index hindex)
    (centralPhysicalFiniteNewComponentMergerWeight_le_mass_of_index hindex)

/-! ## 4. Type-level decision and semantic consequences -/

structure CentralPhysicalFiniteComponentMergerWitness
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Type where
  index : Nat
  index_mem : index ∈ centralPhysicalFiniteNewComponentMergerIndices
    w hw base later half

structure CentralPhysicalFiniteNoComponentMergerCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Type where
  certified : centralPhysicalFiniteNoComponentMergerCheck
    w hw base later half = true

structure CentralPhysicalFiniteComponentMergerMassZeroCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Type where
  zero : centralPhysicalFiniteNewComponentMergerMass
    w hw base later half ≈ 0

structure CentralPhysicalFiniteComponentMergerMassPositiveWitness
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Type where
  positive : (0 : Q') < centralPhysicalFiniteNewComponentMergerMass
    w hw base later half

namespace CentralPhysicalFiniteComponentMergerWitness

theorem state_semantics
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (witness : CentralPhysicalFiniteComponentMergerWitness
      w hw base later half) :
    witness.index ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half ∧
      labelWithinB base (centralLowerFaceIds half)
          (centralPhysicalFiniteStateAt w hw later half witness.index) = true ∧
        (0 : Q') < centralPhysicalRowMarginal w hw base half
          (centralPhysicalFiniteStateAt w hw later half witness.index) :=
  mem_centralPhysicalFiniteNewComponentMergerIndices_iff.mp
    witness.index_mem

theorem later_weight_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (witness : CentralPhysicalFiniteComponentMergerWitness
      w hw base later half) :
    (0 : Q') < centralPhysicalFiniteWeight
      w hw later half witness.index :=
  centralPhysicalFiniteNewComponentMergerWeight_pos_of_index
    witness.index_mem

theorem later_weight_le_mergerMass
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (witness : CentralPhysicalFiniteComponentMergerWitness
      w hw base later half) :
    centralPhysicalFiniteWeight w hw later half witness.index ≤
      centralPhysicalFiniteNewComponentMergerMass
        w hw base later half :=
  centralPhysicalFiniteNewComponentMergerWeight_le_mass_of_index
    witness.index_mem

theorem mergerMass_pos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (witness : CentralPhysicalFiniteComponentMergerWitness
      w hw base later half) :
    (0 : Q') < centralPhysicalFiniteNewComponentMergerMass
      w hw base later half :=
  centralPhysicalFiniteNewComponentMergerMass_pos_of_index
    witness.index_mem

end CentralPhysicalFiniteComponentMergerWitness

namespace CentralPhysicalFiniteNoComponentMergerCertificate

theorem mergerMass_zero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (certificate : CentralPhysicalFiniteNoComponentMergerCertificate
      w hw base later half) :
    centralPhysicalFiniteNewComponentMergerMass
      w hw base later half ≈ 0 :=
  centralPhysicalFiniteNewComponentMergerMass_eqv_zero_of_check
    certificate.certified

theorem newMass_le_increment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (certificate : CentralPhysicalFiniteNoComponentMergerCertificate
      w hw base later half)
    (hcutoff : base ≤ later) :
    centralPhysicalFiniteVacuumSectorNewMass
        w hw base later half ≤
      slabParametricKCutoffIncrement
        w base later (centralExtent half) :=
  centralPhysicalFiniteVacuumSectorNewMass_le_increment_of_check
    hcutoff certificate.certified

end CentralPhysicalFiniteNoComponentMergerCertificate

def centralPhysicalFiniteComponentMergerDecision
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    Sum (CentralPhysicalFiniteNoComponentMergerCertificate
      w hw base later half)
      (CentralPhysicalFiniteComponentMergerWitness
        w hw base later half) := by
  cases hindices : centralPhysicalFiniteNewComponentMergerIndices
      w hw base later half with
  | nil =>
      exact Sum.inl
        { certified :=
            (centralPhysicalFiniteNoComponentMergerCheck_true_iff_indices_empty
              w hw base later half).mpr hindices }
  | cons head tail =>
      exact Sum.inr
        { index := head
          index_mem := by
            rw [hindices]
            exact List.mem_cons_self }

def centralPhysicalFiniteComponentMergerMassZeroOrPositiveData
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    Sum (CentralPhysicalFiniteComponentMergerMassZeroCertificate
      w hw base later half)
      (CentralPhysicalFiniteComponentMergerMassPositiveWitness
        w hw base later half) := by
  cases centralPhysicalFiniteComponentMergerDecision
      w hw base later half with
  | inl certificate =>
      exact Sum.inl { zero := certificate.mergerMass_zero }
  | inr witness =>
      exact Sum.inr { positive := witness.mergerMass_pos }

/-! ## 5. The equal-cutoff anchor is constructively inhabited -/

theorem centralPhysicalFiniteNoComponentMergerCheck_self
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    centralPhysicalFiniteNoComponentMergerCheck
      w hw cutoff cutoff half = true := by
  unfold centralPhysicalFiniteNoComponentMergerCheck
    centralPhysicalFiniteNewComponentMergerIndices
  rw [centralPhysicalFiniteVacuumSectorNewBlockIndices_self]
  rfl

theorem centralPhysicalFiniteNewComponentMergerMass_self_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    centralPhysicalFiniteNewComponentMergerMass
      w hw cutoff cutoff half ≈ 0 :=
  centralPhysicalFiniteNewComponentMergerMass_eqv_zero_of_check
    (centralPhysicalFiniteNoComponentMergerCheck_self
      w hw cutoff half)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.centralPhysicalFiniteNoComponentMergerCheck_true_iff_indices_empty
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.centralPhysicalFiniteNoComponentMergerCheck_true_iff_all_new_outside
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.centralPhysicalFiniteNewComponentMergerMass_eqv_zero_of_check
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.centralPhysicalFiniteVacuumSectorNewMass_le_increment_of_check
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.CentralPhysicalFiniteComponentMergerWitness.state_semantics
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.CentralPhysicalFiniteComponentMergerWitness.later_weight_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.CentralPhysicalFiniteComponentMergerWitness.mergerMass_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.centralPhysicalFiniteComponentMergerDecision
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.centralPhysicalFiniteComponentMergerMassZeroOrPositiveData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.centralPhysicalFiniteNoComponentMergerCheck_self
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision.centralPhysicalFiniteNewComponentMergerMass_self_eqv_zero
