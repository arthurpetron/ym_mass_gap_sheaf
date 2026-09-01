/-
# An all-spin positive ray from the transverse reflected cube

The cutoff-two complement witness is the fundamental-spin member of a full
all-spin family.  Its complete reflected summand has the six-face support

    [39, 40, 41, 44, 49, 59].

Every corrected-slab link meets that support in zero or two faces.  The
generic closed-surface compiler therefore proves strict positivity for every
spin admitted by the production cutoff and every positive coupling.  The
single lower face at identifier 39 is consequently a literal positive-row
state at every cutoff.

This gives a second geometric ray beside the lower spatial cube ray.  It is
finite-cutoff support data, not a cutoff-uniform probability estimate,
continuum theory, or Clay mass-gap theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness
import YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm

namespace YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay

set_option maxRecDepth 300000
set_option maxHeartbeats 6000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm
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

/-! ## 1. The literal transverse closed surface -/

/-- The nonzero support extracted from the already checked fundamental-spin
transverse summand. -/
def centralTransverseCubeSupportIds : List Nat :=
  (slabPhysicalFaceEdges 1).filter
    (fun id => decide (cutoffTwoTransverseCubePhysical id = 1))

theorem centralTransverseCubeSupportIds_eq :
    centralTransverseCubeSupportIds = [39, 40, 41, 44, 49, 59] := by
  rfl

/-- The transverse support is a closed six-face surface in the corrected
slab: every physical link sees zero or two selected faces. -/
def centralTransverseClosedSpinSurface : ClosedSpinSurface 1 where
  faceIds := centralTransverseCubeSupportIds
  faceIds_subset_physical := by
    intro id hid
    exact (List.mem_filter.mp hid).1
  selected_length_zero_or_two := by
    intro link hlink
    have hcheck :
        (boundaryCompleteSlabLinks 1).all
          (fun candidate =>
            decide
              (((slabIncidentPlaqIds 1 candidate).filter
                  (fun id => decide
                    (id ∈ centralTransverseCubeSupportIds))).length = 0 ∨
                ((slabIncidentPlaqIds 1 candidate).filter
                  (fun id => decide
                    (id ∈ centralTransverseCubeSupportIds))).length = 2)) =
          true := by
      rfl
    exact of_decide_eq_true
      (List.all_eq_true.mp hcheck link hlink)

/-! ## 2. All-spin source, boundary, and complete summand -/

/-- Spin `spin` on the one lower transverse face. -/
def centralTransverseSpinSingleFaceState (spin : Nat) : EdgeLabelling :=
  fun id => if id = 39 then spin else 0

/-- The four fixed faces completing the transverse reflected cube. -/
def centralTransverseSpinCubeBoundary (spin : Nat) : EdgeLabelling :=
  fun id => if id ∈ [40, 41, 49, 59] then spin else 0

def centralTransverseSpinCubePhysical (spin : Nat) : EdgeLabelling :=
  assembleReflectedSlabLabelling 0
    (centralTransverseSpinSingleFaceState spin)
    (centralTransverseSpinCubeBoundary spin)
    (centralTransverseSpinSingleFaceState spin)

theorem centralTransverseSpinSingleFaceState_le
    (spin id : Nat) :
    centralTransverseSpinSingleFaceState spin id ≤ spin := by
  unfold centralTransverseSpinSingleFaceState
  by_cases hid : id = 39 <;> simp [hid]

theorem centralTransverseSpinSingleFaceState_mem_centralHalfStates
    {K spin : Nat} (hspin : spin ≤ K) :
    centralTransverseSpinSingleFaceState spin ∈ centralHalfStates K 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le
      (Nat.le_trans (centralTransverseSpinSingleFaceState_le spin id) hspin)
  · intro id hid
    unfold centralTransverseSpinSingleFaceState
    rw [if_neg]
    intro heq
    subst id
    exact hid (by decide)

theorem centralTransverseSpinCubeBoundary_mem_channels
    {K spin : Nat} (hspin : spin ≤ K) :
    centralTransverseSpinCubeBoundary spin ∈
      centralBoundaryChannels K 0 := by
  unfold centralBoundaryChannels
  apply boundedEdgeLabellings_complete
  · intro id _
    unfold centralTransverseSpinCubeBoundary
    by_cases hselected : id ∈ [40, 41, 49, 59]
    · simp only [hselected, if_pos]
      exact Nat.lt_succ_of_le hspin
    · simp [hselected]
  · intro id hid
    unfold centralTransverseSpinCubeBoundary
    rw [if_neg]
    intro hselected
    have hsubset :
        ∀ faceId : Nat, faceId ∈ [40, 41, 49, 59] →
          faceId ∈ centralFixedFaceIds 0 := by
      decide
    exact hid (hsubset id hselected)

/-- Replace every fundamental-spin face of a physical labelling by `spin`. -/
def relabelFundamental (spin : Nat) (physical : EdgeLabelling) : EdgeLabelling :=
  fun id => if physical id = 1 then spin else 0

theorem centralTransverseSpinCubePhysical_eq_relabelFundamental (spin : Nat) :
    centralTransverseSpinCubePhysical spin =
      relabelFundamental spin cutoffTwoTransverseCubePhysical := by
  funext id
  unfold centralTransverseSpinCubePhysical cutoffTwoTransverseCubePhysical
    relabelFundamental assembleReflectedSlabLabelling centralExtent
  by_cases hphysical : id ∈ slabPhysicalFaceEdges 1
  · simp only [hphysical, if_pos]
    cases hside : plaquetteHalfSide 0 (slabPlaquetteAt 1 id)
    · by_cases hid : id = 39 <;>
        simp [centralTransverseSpinSingleFaceState,
          cutoffTwoTransverseSingleFaceState, hid]
    · by_cases hid : id ∈ [40, 41, 49, 59] <;>
        simp [centralTransverseSpinCubeBoundary,
          cutoffTwoTransverseCubeBoundary, hid]
    · by_cases hid : slabFaceReflectId 1 id = 39 <;>
        simp [centralTransverseSpinSingleFaceState,
          cutoffTwoTransverseSingleFaceState, hid]
  · simp [hphysical]

theorem relabelFundamental_eq_spinLabelling (spin : Nat) :
    relabelFundamental spin cutoffTwoTransverseCubePhysical =
      centralTransverseClosedSpinSurface.spinLabelling spin := by
  funext id
  unfold relabelFundamental ClosedSpinSurface.spinLabelling
  change (if cutoffTwoTransverseCubePhysical id = 1 then spin else 0) =
    if id ∈ centralTransverseCubeSupportIds then spin else 0
  unfold centralTransverseCubeSupportIds
  by_cases hphysical : id ∈ slabPhysicalFaceEdges 1
  · simp [hphysical]
  · have hzero :=
      assembleReflectedSlabLabelling_zero_off_physical
        0 cutoffTwoTransverseSingleFaceState
        cutoffTwoTransverseCubeBoundary
        cutoffTwoTransverseSingleFaceState hphysical
    change cutoffTwoTransverseCubePhysical id = 0 at hzero
    simp [hphysical, hzero]

/-- The assembled all-spin transverse cube is exactly the equal-spin
labelling of the extracted closed support. -/
theorem centralTransverseSpinCubePhysical_eq_spinLabelling (spin : Nat) :
    centralTransverseSpinCubePhysical spin =
      centralTransverseClosedSpinSurface.spinLabelling spin := by
  rw [centralTransverseSpinCubePhysical_eq_relabelFundamental,
    relabelFundamental_eq_spinLabelling]

theorem centralTransverseSpinCubePhysicalTerm_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    (0 : Q') < slabParametricKPhysicalTerm w K 1
      (centralTransverseSpinCubePhysical spin) := by
  rw [centralTransverseSpinCubePhysical_eq_spinLabelling]
  exact centralTransverseClosedSpinSurface.physicalTerm_pos hw hspin

/-! ## 3. Positive reflected edge and retained-row membership -/

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

theorem centralTransverseSpinCubePhysicalReflectedKernel_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    (0 : Q') < centralPhysicalReflectedKernel w K 0
      (centralTransverseSpinSingleFaceState spin)
      (centralTransverseSpinSingleFaceState spin) := by
  let value := fun boundary =>
    slabParametricKPhysicalTerm w K 1
      (assembleReflectedSlabLabelling 0
        (centralTransverseSpinSingleFaceState spin) boundary
        (centralTransverseSpinSingleFaceState spin))
  have hmember :
      value (centralTransverseSpinCubeBoundary spin) ≤
        listQSum value (centralBoundaryChannels K 0) :=
    listQSum_member_le value
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative
          (Q'.le_of_lt hw) K 1
          (assembleReflectedSlabLabelling 0
            (centralTransverseSpinSingleFaceState spin) boundary
            (centralTransverseSpinSingleFaceState spin)))
      (centralBoundaryChannels K 0)
      (centralTransverseSpinCubeBoundary_mem_channels hspin)
  have hchosen :
      (0 : Q') < value (centralTransverseSpinCubeBoundary spin) :=
    centralTransverseSpinCubePhysicalTerm_pos hw hspin
  unfold centralPhysicalReflectedKernel
  exact Q'.pos_of_lt_of_le hchosen hmember

theorem centralTransverseSpinCubeNormalizedJoint_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
      w (Q'.le_of_lt hw) K 0
      (centralTransverseSpinSingleFaceState spin)
      (centralTransverseSpinSingleFaceState spin) := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.mul_pos
    (centralTransverseSpinCubePhysicalReflectedKernel_pos hw hspin)
    (Q'.recipPos_pos _ _)

theorem centralTransverseSpinCubeRowMarginal_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    (0 : Q') < centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0
      (centralTransverseSpinSingleFaceState spin) := by
  unfold centralPhysicalRowMarginal
  have hmember := listQSum_member_le
    (centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw) K 0
      (centralTransverseSpinSingleFaceState spin))
    (fun target =>
      centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K 0
        (centralTransverseSpinSingleFaceState spin) target)
    (centralHalfStates K 0)
    (centralTransverseSpinSingleFaceState_mem_centralHalfStates hspin)
  exact Q'.pos_of_lt_of_le
    (centralTransverseSpinCubeNormalizedJoint_pos hw hspin) hmember

/-- Every admitted transverse spin is a literal retained positive-row state. -/
theorem centralTransverseSpinSingleFaceState_mem_centralPositiveHalfStates
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    centralTransverseSpinSingleFaceState spin ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 := by
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨centralTransverseSpinSingleFaceState_mem_centralHalfStates hspin,
      centralTransverseSpinCubeRowMarginal_pos hw hspin⟩

/-- Evaluation on the selected lower face recovers the spin. -/
theorem centralTransverseSpinSingleFaceState_injective :
    Function.Injective centralTransverseSpinSingleFaceState := by
  intro left right heq
  have hvalue := congrFun heq 39
  simpa [centralTransverseSpinSingleFaceState] using hvalue

end YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay

#print axioms
  YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay.centralTransverseClosedSpinSurface
#print axioms
  YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay.centralTransverseSpinCubePhysical_eq_spinLabelling
#print axioms
  YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay.centralTransverseSpinCubePhysicalTerm_pos
#print axioms
  YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay.centralTransverseSpinCubePhysicalReflectedKernel_pos
#print axioms
  YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay.centralTransverseSpinSingleFaceState_mem_centralPositiveHalfStates
#print axioms
  YMGap.Continuum.BF4CentralTransverseSpinCubePositiveRay.centralTransverseSpinSingleFaceState_injective
