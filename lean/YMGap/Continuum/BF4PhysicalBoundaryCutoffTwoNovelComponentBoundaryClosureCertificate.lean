/-
# Executable closure certificate for the embedded cutoff-two vacuum component

Every component-merger witness now yields a literal later support edge leaving
the embedded cutoff-two vacuum component.  This file reflects absence of all
such candidate edges into a finite Boolean checker.  A successful check rules
out every component-merger witness, forces merger mass to vanish, and reduces
new-shell mass to the corrected-slab cutoff increment.

The checker succeeds at the equal-cutoff anchor because its new-state list is
empty.  No successful larger-cutoff or cofinal certificate is produced.  No
completed contraction, thermodynamic/continuum construction, or Clay mass gap
is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite boundary-closure scan -/

/-- Scan every ordered pair from the embedded cutoff-two vacuum component to
the later new-state block and certify that it is not a later support edge. -/
def cutoffTwoEmbeddedVacuumBoundaryClosedCheck (later : Nat) : Bool :=
  (cartesian
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0)
      (cutoffTwoEdgeLoadNewStates later)).all
    (fun pair =>
      !(centralPhysicalFiniteSupportAdjacentB
        cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2))

private theorem bool_eq_false_of_not_eq_true
    (value : Bool) (hvalue : (!value) = true) : value = false := by
  cases value <;> simp_all

/-- Soundness of the scan: every candidate embedded-to-new edge is absent. -/
theorem cutoffTwoEmbeddedVacuumBoundaryClosedCheck_sound
    (later : Nat)
    (hcheck : cutoffTwoEmbeddedVacuumBoundaryClosedCheck later = true) :
    ∀ source,
      source ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0 →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadNewStates later →
        centralPhysicalFiniteSupportAdjacentB
          cutoffTwoHalfCoupling (by decide) later 0 source target = false := by
  unfold cutoffTwoEmbeddedVacuumBoundaryClosedCheck at hcheck
  intro source hsource target htarget
  have hpair : (source, target) ∈
      cartesian
        (centralPhysicalFiniteEmbeddedVacuumSectorIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0)
        (cutoffTwoEdgeLoadNewStates later) :=
    (mem_cartesian_iff _ _ (source, target)).mpr ⟨hsource, htarget⟩
  exact bool_eq_false_of_not_eq_true _
    (List.all_eq_true.mp hcheck (source, target) hpair)

/-- Completeness for the stated finite closure predicate. -/
theorem cutoffTwoEmbeddedVacuumBoundaryClosedCheck_complete
    (later : Nat)
    (hclosed :
      ∀ source,
        source ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0 →
        ∀ target,
          target ∈ cutoffTwoEdgeLoadNewStates later →
          centralPhysicalFiniteSupportAdjacentB
            cutoffTwoHalfCoupling (by decide) later 0 source target = false) :
    cutoffTwoEmbeddedVacuumBoundaryClosedCheck later = true := by
  unfold cutoffTwoEmbeddedVacuumBoundaryClosedCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  have hparts :=
    (mem_cartesian_iff
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0)
      (cutoffTwoEdgeLoadNewStates later) pair).mp hpair
  simp only [hclosed pair.1 hparts.1 pair.2 hparts.2, Bool.not_false]

/-! ## 2. Boundary closure excludes component mergers -/

/-- A proof-carrying successful boundary-closure scan. -/
structure CutoffTwoEmbeddedVacuumBoundaryClosedCertificate
    (later : Nat) : Type where
  certified : cutoffTwoEmbeddedVacuumBoundaryClosedCheck later = true

theorem cutoffTwoNoComponentMergerCheck_of_boundaryClosedCheck
    {later : Nat} (hcutoff : 2 ≤ later)
    (hclosed : cutoffTwoEmbeddedVacuumBoundaryClosedCheck later = true) :
    cutoffTwoNoComponentMergerCheck later = true := by
  cases cutoffTwoComponentMergerDecision later with
  | inl certificate =>
      exact certificate.certified
  | inr witness =>
      let boundary :=
        CutoffTwoComponentMergerWitness.toEmbeddedVacuumBoundaryExit
          witness hcutoff
      have htargetNew : boundary.target ∈ cutoffTwoEdgeLoadNewStates later := by
        unfold cutoffTwoEdgeLoadNewStates
        exact
          (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff).mpr
            ⟨boundary.target_mem_later_sector,
              boundary.target_not_mem_embedded⟩
      have hedgeFalse :=
        cutoffTwoEmbeddedVacuumBoundaryClosedCheck_sound later hclosed
          boundary.source boundary.source_mem_embedded
          boundary.target htargetNew
      rw [boundary.edge] at hedgeFalse
      exact False.elim ((by decide : (true : Bool) ≠ false) hedgeFalse)

def CutoffTwoEmbeddedVacuumBoundaryClosedCertificate.toNoComponentMergerCertificate
    {later : Nat}
    (certificate : CutoffTwoEmbeddedVacuumBoundaryClosedCertificate later)
    (hcutoff : 2 ≤ later) :
    CutoffTwoNoComponentMergerCertificate later :=
  { certified := cutoffTwoNoComponentMergerCheck_of_boundaryClosedCheck
      hcutoff certificate.certified }

theorem cutoffTwoNewComponentMergerMass_eqv_zero_of_boundaryClosedCheck
    {later : Nat} (hcutoff : 2 ≤ later)
    (hclosed : cutoffTwoEmbeddedVacuumBoundaryClosedCheck later = true) :
    cutoffTwoNewComponentMergerMass later ≈ 0 :=
  cutoffTwoNewComponentMergerMass_eqv_zero_of_check
    (cutoffTwoNoComponentMergerCheck_of_boundaryClosedCheck hcutoff hclosed)

theorem cutoffTwoNewMass_le_increment_of_boundaryClosedCheck
    {later : Nat} (hcutoff : 2 ≤ later)
    (hclosed : cutoffTwoEmbeddedVacuumBoundaryClosedCheck later = true) :
    cutoffTwoNewMass later ≤
      slabParametricKCutoffIncrement
        cutoffTwoHalfCoupling 2 later (centralExtent 0) :=
  cutoffTwoNewMass_le_increment_of_noComponentMergerCheck hcutoff
    (cutoffTwoNoComponentMergerCheck_of_boundaryClosedCheck hcutoff hclosed)

/-! ## 3. Equal-cutoff anchor -/

theorem cutoffTwoEmbeddedVacuumBoundaryClosedCheck_self :
    cutoffTwoEmbeddedVacuumBoundaryClosedCheck 2 = true := by
  apply cutoffTwoEmbeddedVacuumBoundaryClosedCheck_complete
  intro _ _ target htarget
  rw [cutoffTwoEdgeLoadNewStates_self] at htarget
  exact False.elim (List.not_mem_nil htarget)

def cutoffTwoEmbeddedVacuumBoundaryClosedCertificateSelf :
    CutoffTwoEmbeddedVacuumBoundaryClosedCertificate 2 :=
  { certified := cutoffTwoEmbeddedVacuumBoundaryClosedCheck_self }

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate.cutoffTwoEmbeddedVacuumBoundaryClosedCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate.cutoffTwoEmbeddedVacuumBoundaryClosedCheck_complete
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate.cutoffTwoNoComponentMergerCheck_of_boundaryClosedCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate.CutoffTwoEmbeddedVacuumBoundaryClosedCertificate.toNoComponentMergerCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate.cutoffTwoNewComponentMergerMass_eqv_zero_of_boundaryClosedCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate.cutoffTwoNewMass_le_increment_of_boundaryClosedCheck
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate.cutoffTwoEmbeddedVacuumBoundaryClosedCheck_self
