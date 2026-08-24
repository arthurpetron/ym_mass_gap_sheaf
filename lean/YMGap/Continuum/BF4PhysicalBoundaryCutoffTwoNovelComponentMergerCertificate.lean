/-
# Executable certificate for cutoff-two vacuum-component mergers

The component-split payment isolates a finite list of later vacuum-sector
states that already belong to the cutoff-two positive carrier but not to the
cutoff-two vacuum component.  This file exposes an executable emptiness check
for that list and proves its exact soundness consequences:

* a successful check is equivalent to every new state lying outside the
  cutoff-two positive carrier;
* a successful check forces component-merger mass to vanish; and
* the new-shell mass is then bounded by the corrected-slab cutoff increment
  alone.

The check succeeds at the equal-cutoff anchor `later = 2`.  No claim is made
that it succeeds at any larger cutoff or along a cofinal family.  No uniform
gap, thermodynamic/continuum construction, or Clay mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. An executable no-merger check -/

def cutoffTwoNoComponentMergerCheck (later : Nat) : Bool :=
  (cutoffTwoNewComponentMergerIndices later).isEmpty

theorem cutoffTwoNoComponentMergerCheck_true_iff_indices_empty
    (later : Nat) :
    cutoffTwoNoComponentMergerCheck later = true ↔
      cutoffTwoNewComponentMergerIndices later = [] := by
  unfold cutoffTwoNoComponentMergerCheck
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

theorem cutoffTwoNoComponentMergerCheck_true_iff_all_new_outside
    (later : Nat) :
    cutoffTwoNoComponentMergerCheck later = true ↔
      ∀ index, index ∈ cutoffTwoEdgeLoadNewStates later →
        cutoffTwoNewStateOutsidePositiveCarrierB later index = true := by
  unfold cutoffTwoNoComponentMergerCheck
    cutoffTwoNewComponentMergerIndices
  exact filter_not_isEmpty_true_iff_all_true
    (cutoffTwoNewStateOutsidePositiveCarrierB later)
    (cutoffTwoEdgeLoadNewStates later)

/-! ## 2. Soundness for mass and the corrected-slab increment -/

theorem cutoffTwoNewComponentMergerMass_eqv_zero_of_check
    {later : Nat}
    (hcheck : cutoffTwoNoComponentMergerCheck later = true) :
    cutoffTwoNewComponentMergerMass later ≈ 0 := by
  have hnil :=
    (cutoffTwoNoComponentMergerCheck_true_iff_indices_empty later).mp hcheck
  unfold cutoffTwoNewComponentMergerMass finiteWeightedMass
  rw [hnil]
  exact Q'.eqv_refl 0

theorem cutoffTwoNewMass_le_increment_of_noComponentMergerCheck
    {later : Nat} (hcutoff : 2 ≤ later)
    (hcheck : cutoffTwoNoComponentMergerCheck later = true) :
    cutoffTwoNewMass later ≤
      slabParametricKCutoffIncrement
        cutoffTwoHalfCoupling 2 later (centralExtent 0) := by
  let increment :=
    slabParametricKCutoffIncrement
      cutoffTwoHalfCoupling 2 later (centralExtent 0)
  have hbound := cutoffTwoNewMass_le_increment_add_componentMerger hcutoff
  have hzero := cutoffTwoNewComponentMergerMass_eqv_zero_of_check hcheck
  have hcollapse :
      increment + cutoffTwoNewComponentMergerMass later ≈ increment :=
    Q'.eqv_trans _ (increment + 0) _
      (Q'.add_eqv_congr_left increment _ 0 hzero)
      (Q'.eqv_of_eq (Q'.add_zero' increment))
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hcollapse)

/-! ## 3. The equal-cutoff anchor is certified -/

theorem cutoffTwoNoComponentMergerCheck_self :
    cutoffTwoNoComponentMergerCheck 2 = true := by
  unfold cutoffTwoNoComponentMergerCheck
    cutoffTwoNewComponentMergerIndices
  rw [cutoffTwoEdgeLoadNewStates_self]
  rfl

theorem cutoffTwoNewComponentMergerMass_self_eqv_zero :
    cutoffTwoNewComponentMergerMass 2 ≈ 0 :=
  cutoffTwoNewComponentMergerMass_eqv_zero_of_check
    cutoffTwoNoComponentMergerCheck_self

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate.cutoffTwoNoComponentMergerCheck_true_iff_indices_empty
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate.cutoffTwoNoComponentMergerCheck_true_iff_all_new_outside
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate.cutoffTwoNewComponentMergerMass_eqv_zero_of_check
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate.cutoffTwoNewMass_le_increment_of_noComponentMergerCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate.cutoffTwoNoComponentMergerCheck_self
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate.cutoffTwoNewComponentMergerMass_self_eqv_zero
