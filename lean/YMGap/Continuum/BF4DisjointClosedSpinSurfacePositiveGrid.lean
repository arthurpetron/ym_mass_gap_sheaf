/-
# A two-coordinate positive-row grid from disjoint closed surfaces

Inside the corrected extent-one reflected slab, the two disjoint closed
six-face supports

    [0, 2, 4, 6, 20, 40]
    [9, 11, 13, 15, 29, 49]

each meet every physical link in zero or two faces.  They may therefore carry
independent admitted twice-spin labels.  Restricting the resulting physical
labelling to the lower half records the first spin at face zero and the second
spin at face nine.  The resulting Cartesian grid of row states is injective
and every grid point lies in the literal positive carrier.

This is finite-cutoff geometry and positivity.  It gives no quantitative
cutoff-uniform row floor, continuum limit, or Clay mass-gap statement.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay
import YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

namespace YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid

set_option maxRecDepth 500000
set_option maxHeartbeats 6000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm
open YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

/-! ## 1. The two disjoint closed supports -/

def centralFirstGridClosedSpinSurface : ClosedSpinSurface 1 where
  faceIds := [0, 2, 4, 6, 20, 40]
  faceIds_subset_physical := by
    intro id hid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
    rcases hid with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  selected_length_zero_or_two := by
    intro link hlink
    have hcheck :
        (boundaryCompleteSlabLinks 1).all
          (fun candidate =>
            decide
              (((slabIncidentPlaqIds 1 candidate).filter
                  (fun id => decide
                    (id ∈ ([0, 2, 4, 6, 20, 40] : List Nat)))).length = 0 ∨
                ((slabIncidentPlaqIds 1 candidate).filter
                  (fun id => decide
                    (id ∈ ([0, 2, 4, 6, 20, 40] : List Nat)))).length = 2)) =
          true := by
      rfl
    exact of_decide_eq_true
      (List.all_eq_true.mp hcheck link hlink)

def centralSecondGridClosedSpinSurface : ClosedSpinSurface 1 where
  faceIds := [9, 11, 13, 15, 29, 49]
  faceIds_subset_physical := by
    intro id hid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
    rcases hid with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  selected_length_zero_or_two := by
    intro link hlink
    have hcheck :
        (boundaryCompleteSlabLinks 1).all
          (fun candidate =>
            decide
              (((slabIncidentPlaqIds 1 candidate).filter
                  (fun id => decide
                    (id ∈ ([9, 11, 13, 15, 29, 49] : List Nat)))).length = 0 ∨
                ((slabIncidentPlaqIds 1 candidate).filter
                  (fun id => decide
                    (id ∈ ([9, 11, 13, 15, 29, 49] : List Nat)))).length = 2)) =
          true := by
      rfl
    exact of_decide_eq_true
      (List.all_eq_true.mp hcheck link hlink)

def centralDisjointGridSurfaces : DisjointClosedSpinSurfaces 1 where
  first := centralFirstGridClosedSpinSurface
  second := centralSecondGridClosedSpinSurface
  supports_disjoint := by
    intro id hfirst hsecond
    simp only [centralFirstGridClosedSpinSurface, List.mem_cons,
      List.not_mem_nil, or_false] at hfirst
    simp only [centralSecondGridClosedSpinSurface, List.mem_cons,
      List.not_mem_nil, or_false] at hsecond
    rcases hfirst with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp at hsecond

/-! ## 2. Physical labelling and its reflected restrictions -/

def centralGridPhysical (firstSpin secondSpin : Nat) : EdgeLabelling :=
  centralDisjointGridSurfaces.spinLabelling firstSpin secondSpin

def centralGridRowState (firstSpin secondSpin : Nat) : EdgeLabelling :=
  centralLowerRestriction 0 (centralGridPhysical firstSpin secondSpin)

def centralGridBoundary (firstSpin secondSpin : Nat) : EdgeLabelling :=
  centralBoundaryRestriction 0 (centralGridPhysical firstSpin secondSpin)

def centralGridTargetState (firstSpin secondSpin : Nat) : EdgeLabelling :=
  centralReflectedUpperRestriction 0
    (centralGridPhysical firstSpin secondSpin)

theorem centralGridPhysical_mem
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    centralGridPhysical firstSpin secondSpin ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) := by
  exact centralDisjointGridSurfaces.spinLabelling_mem_bounded
    hfirstSpin hsecondSpin

theorem centralGridRowState_mem_centralHalfStates
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    centralGridRowState firstSpin secondSpin ∈ centralHalfStates K 0 := by
  exact centralLowerRestriction_mem
    (centralGridPhysical_mem hfirstSpin hsecondSpin)

theorem centralGridBoundary_mem_channels
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    centralGridBoundary firstSpin secondSpin ∈ centralBoundaryChannels K 0 := by
  exact centralBoundaryRestriction_mem
    (centralGridPhysical_mem hfirstSpin hsecondSpin)

theorem centralGridTargetState_mem_centralHalfStates
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    centralGridTargetState firstSpin secondSpin ∈ centralHalfStates K 0 := by
  exact centralReflectedUpperRestriction_mem
    (centralGridPhysical_mem hfirstSpin hsecondSpin)

theorem centralGrid_assemble_restrictions
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    assembleReflectedSlabLabelling 0
        (centralGridRowState firstSpin secondSpin)
        (centralGridBoundary firstSpin secondSpin)
        (centralGridTargetState firstSpin secondSpin) =
      centralGridPhysical firstSpin secondSpin := by
  exact assembleReflectedSlabLabelling_restrictions
    (centralGridPhysical_mem hfirstSpin hsecondSpin)

theorem centralGridPhysicalTerm_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    (0 : Q') < slabParametricKPhysicalTerm w K 1
      (centralGridPhysical firstSpin secondSpin) := by
  exact centralDisjointGridSurfaces.physicalTerm_pos
    hw hfirstSpin hsecondSpin

/-! ## 3. Strict row positivity -/

private theorem listQSum_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative value hvalue tail)

private theorem listQSum_member_le
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative value hvalue tail)
      · have ih := listQSum_member_le value hvalue tail htail
        have hmono :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

theorem centralGridPhysicalReflectedKernel_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    (0 : Q') < centralPhysicalReflectedKernel w K 0
      (centralGridRowState firstSpin secondSpin)
      (centralGridTargetState firstSpin secondSpin) := by
  let value := fun boundary =>
    slabParametricKPhysicalTerm w K 1
      (assembleReflectedSlabLabelling 0
        (centralGridRowState firstSpin secondSpin) boundary
        (centralGridTargetState firstSpin secondSpin))
  have hmember :
      value (centralGridBoundary firstSpin secondSpin) ≤
        listQSum value (centralBoundaryChannels K 0) :=
    listQSum_member_le value
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative
          (Q'.le_of_lt hw) K 1
          (assembleReflectedSlabLabelling 0
            (centralGridRowState firstSpin secondSpin) boundary
            (centralGridTargetState firstSpin secondSpin)))
      (centralBoundaryChannels K 0)
      (centralGridBoundary_mem_channels hfirstSpin hsecondSpin)
  have hchosen :
      (0 : Q') < value (centralGridBoundary firstSpin secondSpin) := by
    change (0 : Q') < slabParametricKPhysicalTerm w K 1
      (assembleReflectedSlabLabelling 0
        (centralGridRowState firstSpin secondSpin)
        (centralGridBoundary firstSpin secondSpin)
        (centralGridTargetState firstSpin secondSpin))
    rw [centralGrid_assemble_restrictions hfirstSpin hsecondSpin]
    exact centralGridPhysicalTerm_pos hw hfirstSpin hsecondSpin
  unfold centralPhysicalReflectedKernel
  exact Q'.pos_of_lt_of_le hchosen hmember

theorem centralGridNormalizedJoint_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
      w (Q'.le_of_lt hw) K 0
      (centralGridRowState firstSpin secondSpin)
      (centralGridTargetState firstSpin secondSpin) := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.mul_pos
    (centralGridPhysicalReflectedKernel_pos hw hfirstSpin hsecondSpin)
    (Q'.recipPos_pos _ _)

theorem centralGridRowMarginal_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    (0 : Q') < centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0
      (centralGridRowState firstSpin secondSpin) := by
  unfold centralPhysicalRowMarginal
  have hmember := listQSum_member_le
    (centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw) K 0
      (centralGridRowState firstSpin secondSpin))
    (fun target =>
      centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K 0
        (centralGridRowState firstSpin secondSpin) target)
    (centralHalfStates K 0)
    (centralGridTargetState_mem_centralHalfStates
      hfirstSpin hsecondSpin)
  exact Q'.pos_of_lt_of_le
    (centralGridNormalizedJoint_pos hw hfirstSpin hsecondSpin) hmember

theorem centralGridRowState_mem_centralPositiveHalfStates
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    centralGridRowState firstSpin secondSpin ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 := by
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨centralGridRowState_mem_centralHalfStates hfirstSpin hsecondSpin,
      centralGridRowMarginal_pos hw hfirstSpin hsecondSpin⟩

/-! ## 4. The two row coordinates are literal and injective -/

theorem centralGridRowState_at_zero (firstSpin secondSpin : Nat) :
    centralGridRowState firstSpin secondSpin 0 = firstSpin := by
  have hzero : 0 ∈ centralLowerFaceIds 0 := by decide
  simp [centralGridRowState, centralLowerRestriction,
    centralGridPhysical, DisjointClosedSpinSurfaces.spinLabelling,
    centralDisjointGridSurfaces, centralFirstGridClosedSpinSurface, hzero]

theorem centralGridRowState_at_nine (firstSpin secondSpin : Nat) :
    centralGridRowState firstSpin secondSpin 9 = secondSpin := by
  have hnine : 9 ∈ centralLowerFaceIds 0 := by decide
  simp [centralGridRowState, centralLowerRestriction,
    centralGridPhysical, DisjointClosedSpinSurfaces.spinLabelling,
    centralDisjointGridSurfaces, centralFirstGridClosedSpinSurface,
    centralSecondGridClosedSpinSurface, hnine]

theorem centralGridRowState_injective :
    Function.Injective (fun pair : Nat × Nat =>
      centralGridRowState pair.1 pair.2) := by
  intro left right heq
  apply Prod.ext
  · have hvalue := congrFun heq 0
    simpa [centralGridRowState_at_zero] using hvalue
  · have hvalue := congrFun heq 9
    simpa [centralGridRowState_at_nine] using hvalue

end YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid

#print axioms
  YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid.centralDisjointGridSurfaces
#print axioms
  YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid.centralGridPhysicalReflectedKernel_pos
#print axioms
  YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid.centralGridRowState_mem_centralPositiveHalfStates
#print axioms
  YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid.centralGridRowState_injective
