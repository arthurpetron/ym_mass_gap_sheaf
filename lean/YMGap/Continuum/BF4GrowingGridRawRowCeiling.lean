/-
# A decorated one-face ceiling for the growing grid raw row

Each of the two closed grid surfaces meets the lower reflected row in exactly
one face: face zero records the source spin and face nine records the replica
spin.  The other ten surface faces belong to the fixed or reflected-upper
coordinates and are summed in the raw row.

Using the generic extent-one decorated-face majorant, this module factors the
two fixed lower-face activities from every grid-row summand and sums the same
66-face residual carrier already controlled for the spin-cube ray.  The
resulting raw-row ceiling pays one degree-thirteen decorated activity for each
grid coordinate.  This is finite-cutoff analytic infrastructure; no replica
obstruction, tail limit, continuum theory, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4ExtentOneSlabDecoratedFaceBound
import YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
import YMGap.Continuum.BF4GrowingGridFullRowEnhancement

namespace YMGap.Continuum.BF4GrowingGridRawRowCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound
open YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
open YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound
open YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid
open YMGap.Continuum.BF4ExtentOneSlabDecoratedFaceBound
open YMGap.Continuum.BF4GrowingGridFullRowEnhancement
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The grid row has exactly two nonzero lower faces -/

/-- Exact support of the lower-row restriction of the two closed surfaces. -/
theorem centralGridRowState_eq_twoFace
    (firstSpin replica : Nat) :
    centralGridRowState firstSpin replica =
      fun id =>
        if id = 0 then firstSpin else if id = 9 then replica else 0 := by
  funext id
  by_cases hlower : id ∈ centralLowerFaceIds 0
  · have hcases :
        id = 0 ∨ id = 1 ∨ id = 3 ∨ id = 9 ∨ id = 10 ∨ id = 12 ∨
        id = 18 ∨ id = 19 ∨ id = 21 ∨ id = 27 ∨ id = 28 ∨ id = 30 ∨
        id = 36 ∨ id = 37 ∨ id = 39 ∨ id = 45 ∨ id = 46 ∨ id = 48 ∨
        id = 54 ∨ id = 55 ∨ id = 57 ∨ id = 63 ∨ id = 64 ∨ id = 66 := by
      simpa only [show centralLowerFaceIds 0 =
          [0, 1, 3, 9, 10, 12, 18, 19, 21, 27, 28, 30,
            36, 37, 39, 45, 46, 48, 54, 55, 57, 63, 64, 66] by rfl,
        List.mem_cons, List.not_mem_nil, or_false] using hlower
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · have hzero : id ≠ 0 := by
      intro hid
      subst id
      exact hlower (by decide)
    have hnine : id ≠ 9 := by
      intro hid
      subst id
      exact hlower (by decide)
    unfold centralGridRowState centralLowerRestriction
    rw [if_neg hlower]
    simp [hzero, hnine]

/-- Assemble an arbitrary boundary and target above one growing-grid source
row. -/
def centralGridSourcePhysical
    (firstSpin replica : Nat)
    (boundary target : EdgeLabelling) : EdgeLabelling :=
  assembleReflectedSlabLabelling 0
    (centralGridRowState firstSpin replica) boundary target

theorem centralGridSourcePhysical_eq_gridRow_on_lower
    (firstSpin replica : Nat) (boundary target : EdgeLabelling)
    {id : Nat} (hid : id ∈ centralLowerFaceIds 0) :
    centralGridSourcePhysical firstSpin replica boundary target id =
      centralGridRowState firstSpin replica id := by
  unfold centralGridSourcePhysical
  have hparts := mem_centralLowerFaceIds.mp hid
  exact assembleReflectedSlabLabelling_lower hparts.1 hparts.2

/-- Away from the six-face comparison cube, the grid source assembly equals
the vacuum-source assembly.  Faces zero and nine are the only nonzero source
coordinates, and both belong to that comparison cube. -/
theorem centralGridSourcePhysical_eq_vacuum_off_cube
    (firstSpin replica : Nat) (boundary target : EdgeLabelling)
    {id : Nat} (hid : id ∉ centralLowerCubeFaceIds) :
    centralGridSourcePhysical firstSpin replica boundary target id =
      centralVacuumSourcePhysical boundary target id := by
  have hzero : id ≠ 0 := by
    intro heq
    subst id
    exact hid (by decide)
  have hnine : id ≠ 9 := by
    intro heq
    subst id
    exact hid (by decide)
  have hsource : centralGridRowState firstSpin replica id =
      zeroEdgeLabelling id := by
    rw [centralGridRowState_eq_twoFace]
    simp [zeroEdgeLabelling, hzero, hnine]
  unfold centralGridSourcePhysical centralVacuumSourcePhysical
  by_cases hphysical :
      id ∈ slabPhysicalFaceEdges (centralExtent 0)
  · cases hside :
        plaquetteHalfSide 0 (slabPlaquetteAt (centralExtent 0) id)
    · rw [assembleReflectedSlabLabelling_lower hphysical hside,
        assembleReflectedSlabLabelling_lower hphysical hside]
      exact hsource
    · rw [assembleReflectedSlabLabelling_fixed hphysical hside,
        assembleReflectedSlabLabelling_fixed hphysical hside]
    · rw [assembleReflectedSlabLabelling_upper hphysical hside,
        assembleReflectedSlabLabelling_upper hphysical hside]
  · rw [assembleReflectedSlabLabelling_zero_off_physical
        0 _ _ _ hphysical,
      assembleReflectedSlabLabelling_zero_off_physical
        0 _ _ _ hphysical]

theorem centralGridSourcePhysical_eq_row_on_cube
    (firstSpin replica : Nat) (boundary target : EdgeLabelling)
    {id : Nat} (hid : id ∈ centralLowerCubeFaceIds) :
    centralGridSourcePhysical firstSpin replica boundary target id =
      (if id = 0 then firstSpin else if id = 9 then replica else 0) := by
  rw [centralGridSourcePhysical_eq_gridRow_on_lower
    firstSpin replica boundary target
    (centralLowerCubeFaceIds_subset_lower id hid),
    centralGridRowState_eq_twoFace]

/-! ## 2. Factor the two decorated source-face activities -/

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on_local
    (left right : Nat → Q') : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl 1
  | id :: rest, hagree =>
      qmul_congr_local
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on_local left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

/-- The full decorated activity of a grid-source assembly is exactly the two
fixed lower-face activities times the existing 66-face residual product. -/
theorem centralGridSourceDecoratedFaceProduct_eqv
    (firstSpin replica : Nat) (boundary target : EdgeLabelling) :
    extentOneSlabAnchorDecoratedFaceProduct
        (centralGridSourcePhysical firstSpin replica boundary target) ≈
      (anchorDecoratedFaceActivity firstSpin *
        anchorDecoratedFaceActivity replica) *
        centralSpinCubeResidualDecoratedFaceProduct
          anchorCoupling boundary target := by
  let physical := centralGridSourcePhysical
    firstSpin replica boundary target
  let value := fun id => anchorDecoratedFaceActivity (physical id)
  let vacuumValue := fun id =>
    anchorDecoratedFaceActivity
      (centralVacuumSourcePhysical boundary target id)
  have hpartition :
      (slabPhysicalFaceEdges 1).Perm
        (centralLowerCubeFaceIds ++ centralSpinCubeNonSourceFaceIds) := by
    exact natListPerm_of_check _ _ (by decide)
  have hsplit : eliminateLinks value (slabPhysicalFaceEdges 1) ≈
      eliminateLinks value centralLowerCubeFaceIds *
        eliminateLinks value centralSpinCubeNonSourceFaceIds := by
    exact Q'.eqv_trans _ _ _
      (eliminateLinks_perm value hpartition)
      (eliminateLinks_append value centralLowerCubeFaceIds
        centralSpinCubeNonSourceFaceIds)
  have hcube : eliminateLinks value centralLowerCubeFaceIds ≈
      anchorDecoratedFaceActivity firstSpin *
        anchorDecoratedFaceActivity replica := by
    let selected := fun id : Nat =>
      if id = 0 then anchorDecoratedFaceActivity firstSpin
      else if id = 9 then anchorDecoratedFaceActivity replica else 1
    have hagree : eliminateLinks value centralLowerCubeFaceIds ≈
        eliminateLinks selected centralLowerCubeFaceIds := by
      apply eliminateLinks_congr_on_local
      intro id hid
      have hphysical := centralGridSourcePhysical_eq_row_on_cube
        firstSpin replica boundary target hid
      rcases (show id = 0 ∨ id = 1 ∨ id = 3 ∨ id = 9 ∨
          id = 19 ∨ id = 39 by
        simpa only [centralLowerCubeFaceIds, List.mem_cons,
          List.not_mem_nil, or_false] using hid) with
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only [value, selected, physical]
      · rw [hphysical]
        exact Q'.eqv_refl _
      · rw [hphysical]
        exact anchorDecoratedFaceActivity_zero_eqv_one
      · rw [hphysical]
        exact anchorDecoratedFaceActivity_zero_eqv_one
      · rw [hphysical]
        exact Q'.eqv_refl _
      · rw [hphysical]
        exact anchorDecoratedFaceActivity_zero_eqv_one
      · rw [hphysical]
        exact anchorDecoratedFaceActivity_zero_eqv_one
    refine Q'.eqv_trans _ _ _ hagree ?_
    unfold selected centralLowerCubeFaceIds eliminateLinks
    show anchorDecoratedFaceActivity firstSpin *
        (1 * (1 * (anchorDecoratedFaceActivity replica *
          (1 * (1 * 1))))) ≈
      anchorDecoratedFaceActivity firstSpin *
        anchorDecoratedFaceActivity replica
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.one_mul_eqv
          (1 * (anchorDecoratedFaceActivity replica *
            (1 * (1 * 1)))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.one_mul_eqv
          (anchorDecoratedFaceActivity replica *
            (1 * (1 * 1))))) ?_
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.one_mul_eqv (1 * 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1)) ?_
    exact Q'.mul_one_eqv _
  have hresidual :
      eliminateLinks value centralSpinCubeNonSourceFaceIds ≈
        centralSpinCubeResidualDecoratedFaceProduct
          anchorCoupling boundary target := by
    refine Q'.eqv_trans _
      (eliminateLinks vacuumValue centralSpinCubeNonSourceFaceIds) _ ?_ ?_
    · apply eliminateLinks_congr_on_local
      intro id hid
      have hnotCube : id ∉ centralLowerCubeFaceIds := by
        have hfalse : decide (id ∈ centralLowerCubeFaceIds) = false := by
          simpa using (List.mem_filter.mp hid).2
        exact of_decide_eq_false hfalse
      unfold value vacuumValue physical
      rw [centralGridSourcePhysical_eq_vacuum_off_cube
        firstSpin replica boundary target hnotCube]
      exact Q'.eqv_refl _
    · unfold vacuumValue centralSpinCubeResidualDecoratedFaceProduct
      exact Q'.eqv_refl _
  unfold extentOneSlabAnchorDecoratedFaceProduct
  exact Q'.eqv_trans _ _ _ hsplit
    (qmul_congr_local hcube hresidual)

/-- Termwise grid-source bound by two fixed decorated activities and the
source-free residual product. -/
theorem centralGridPhysicalTerm_le_decoratedActivities_mul_residual
    {cutoff firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ cutoff) (hreplica : replica ≤ cutoff)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels cutoff 0)
    (htarget : target ∈ centralHalfStates cutoff 0) :
    slabParametricKPhysicalTerm anchorCoupling cutoff 1
        (centralGridSourcePhysical firstSpin replica boundary target) ≤
      (anchorDecoratedFaceActivity firstSpin *
        anchorDecoratedFaceActivity replica) *
        centralSpinCubeResidualDecoratedFaceProduct
          anchorCoupling boundary target := by
  have hsource := centralGridRowState_mem_centralHalfStates
    hfirstSpin hreplica
  have hbounded : SlabFaceLabellingBounded cutoff 1
      (centralGridSourcePhysical firstSpin replica boundary target) := by
    unfold centralGridSourcePhysical
    exact assembleReflectedSlabLabelling_bounded
      hsource hboundary htarget
  exact Q'.le_trans' _ _ _
    (slabParametricKPhysicalTerm_anchor_le_decoratedFaceProduct hbounded)
    (Q'.le_of_eqv
      (centralGridSourceDecoratedFaceProduct_eqv
        firstSpin replica boundary target))

/-! ## 3. Sum the complete literal grid raw row -/

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → left x ≤ right x) →
      listQSum left xs ≤ listQSum right xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun x hx => hle x (List.mem_cons_of_mem head hx)))

private theorem listQSum_filter_le_nonnegative_local {A : Type}
    (weight : A → Q') (hweight : ∀ item, (0 : Q') ≤ weight item)
    (test : A → Bool) (source : List A) :
    listQSum weight (source.filter test) ≤ listQSum weight source := by
  have hcomplement : (0 : Q') ≤
      listQSum weight (source.filter (fun item => !(test item))) := by
    apply listQSum_nonnegative_on
    intro item _hitem
    exact hweight item
  have hadd : listQSum weight (source.filter test) ≤
      listQSum weight (source.filter test) +
        listQSum weight (source.filter (fun item => !(test item))) :=
    Q'.add_le_self_of_nonneg _ _ hcomplement
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv (listQSum_filter_partition weight test source))

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum (fun a => listQSum (fun b => value (a, b)) right) left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem decoratedNestedSum_eqv_carrierSum (cutoff : Nat) :
    listQSum
        (fun target =>
          listQSum
            (fun boundary =>
              centralSpinCubeResidualDecoratedFaceProduct
                anchorCoupling boundary target)
            (centralBoundaryChannels cutoff 0))
        (centralHalfStates cutoff 0) ≈
      listQSum
        (fun pair => centralSpinCubeResidualDecoratedFaceProduct
          anchorCoupling pair.1 pair.2)
        (centralSpinCubeBoundaryTargetPairs cutoff) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        listQSum
          (fun target => centralSpinCubeResidualDecoratedFaceProduct
            anchorCoupling boundary target)
          (centralHalfStates cutoff 0))
      (centralBoundaryChannels cutoff 0)) _
    (listQSum_swap
      (fun boundary target => centralSpinCubeResidualDecoratedFaceProduct
        anchorCoupling boundary target)
      (centralBoundaryChannels cutoff 0)
      (centralHalfStates cutoff 0)) ?_
  unfold centralSpinCubeBoundaryTargetPairs
  exact Q'.eqv_symm
    (listQSum_cartesian_eq_nested_local
      (fun pair : EdgeLabelling × EdgeLabelling =>
        centralSpinCubeResidualDecoratedFaceProduct
          anchorCoupling pair.1 pair.2)
      (centralBoundaryChannels cutoff 0)
      (centralHalfStates cutoff 0))

/-- The complete positive-carrier raw row of an admitted grid source pays one
decorated activity for each of its two lower-face coordinates. -/
theorem centralGridPositiveRawRow_le_decoratedActivities_mul_ceiling
    {cutoff firstSpin replica : Nat}
    (hfirstSpin : firstSpin ≤ cutoff) (hreplica : replica ≤ cutoff) :
    centralPhysicalPositiveRawRowMass
        anchorCoupling (by decide) cutoff 0
        (centralGridRowState firstSpin replica) ≤
      (anchorDecoratedFaceActivity firstSpin *
        anchorDecoratedFaceActivity replica) *
        centralSpinCubeResidualCarrierCeiling := by
  let activity := anchorDecoratedFaceActivity firstSpin *
    anchorDecoratedFaceActivity replica
  let source := centralGridRowState firstSpin replica
  let kernel := centralPhysicalReflectedKernel
    anchorCoupling cutoff 0 source
  let decorated := fun boundary target =>
    centralSpinCubeResidualDecoratedFaceProduct
      anchorCoupling boundary target
  have hfiltered :
      listQSum kernel
          (centralPositiveHalfStates anchorCoupling (by decide) cutoff 0) ≤
        listQSum kernel (centralHalfStates cutoff 0) := by
    unfold centralPositiveHalfStates
    apply listQSum_filter_le_nonnegative_local
    intro target
    unfold kernel
    exact BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_nonnegative
      (by decide) cutoff 0 source target
  have htarget : ∀ target, target ∈ centralHalfStates cutoff 0 →
      kernel target ≤
        activity * listQSum (fun boundary => decorated boundary target)
          (centralBoundaryChannels cutoff 0) := by
    intro target htarget
    unfold kernel centralPhysicalReflectedKernel
    have htermwise :
        listQSum
            (fun boundary => slabParametricKPhysicalTerm
              anchorCoupling cutoff 1
              (assembleReflectedSlabLabelling 0 source boundary target))
            (centralBoundaryChannels cutoff 0) ≤
          listQSum
            (fun boundary => activity * decorated boundary target)
            (centralBoundaryChannels cutoff 0) := by
      apply listQSum_le_termwise_local
      intro boundary hboundary
      change slabParametricKPhysicalTerm anchorCoupling cutoff 1
          (centralGridSourcePhysical firstSpin replica boundary target) ≤
        (anchorDecoratedFaceActivity firstSpin *
          anchorDecoratedFaceActivity replica) *
          centralSpinCubeResidualDecoratedFaceProduct
            anchorCoupling boundary target
      exact centralGridPhysicalTerm_le_decoratedActivities_mul_residual
        hfirstSpin hreplica boundary target hboundary htarget
    exact Q'.le_trans' _ _ _ htermwise
      (Q'.le_of_eqv
        (listQSum_mul_left activity
          (fun boundary => decorated boundary target)
          (centralBoundaryChannels cutoff 0)))
  have houter : listQSum kernel (centralHalfStates cutoff 0) ≤
      listQSum
        (fun target => activity *
          listQSum (fun boundary => decorated boundary target)
            (centralBoundaryChannels cutoff 0))
        (centralHalfStates cutoff 0) := by
    apply listQSum_le_termwise_local
    exact htarget
  have hfactor :
      listQSum
          (fun target => activity *
            listQSum (fun boundary => decorated boundary target)
              (centralBoundaryChannels cutoff 0))
          (centralHalfStates cutoff 0) ≈
        activity *
          listQSum
            (fun target => listQSum
              (fun boundary => decorated boundary target)
              (centralBoundaryChannels cutoff 0))
            (centralHalfStates cutoff 0) :=
    listQSum_mul_left activity
      (fun target => listQSum
        (fun boundary => decorated boundary target)
        (centralBoundaryChannels cutoff 0))
      (centralHalfStates cutoff 0)
  have hcarrier :
      listQSum
          (fun target => listQSum
            (fun boundary => decorated boundary target)
            (centralBoundaryChannels cutoff 0))
          (centralHalfStates cutoff 0) ≈
        listQSum (fun pair => decorated pair.1 pair.2)
          (centralSpinCubeBoundaryTargetPairs cutoff) := by
    unfold decorated
    exact decoratedNestedSum_eqv_carrierSum cutoff
  have hactivity0 : (0 : Q') ≤ activity := by
    unfold activity
    exact Q'.mul_nonneg _ _
      (tailTerm_nonneg (by decide) 13 firstSpin)
      (tailTerm_nonneg (by decide) 13 replica)
  have hceiling := centralSpinCubeResidualCarrierSum_le_ceiling cutoff
  have hmul : activity *
      listQSum (fun pair => decorated pair.1 pair.2)
        (centralSpinCubeBoundaryTargetPairs cutoff) ≤
      activity * centralSpinCubeResidualCarrierCeiling := by
    apply Q'.mul_le_mul_of_nonneg_left
    · unfold decorated
      exact hceiling
    · exact hactivity0
  unfold centralPhysicalPositiveRawRowMass
  exact Q'.le_trans' _ _ _ hfiltered
    (Q'.le_trans' _ _ _ houter
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _ hfactor
            (Q'.mul_eqv_congr_left activity _ _ hcarrier))) hmul))

end YMGap.Continuum.BF4GrowingGridRawRowCeiling

#print axioms
  YMGap.Continuum.BF4GrowingGridRawRowCeiling.centralGridRowState_eq_twoFace
#print axioms
  YMGap.Continuum.BF4GrowingGridRawRowCeiling.centralGridSourcePhysical_eq_vacuum_off_cube
#print axioms
  YMGap.Continuum.BF4GrowingGridRawRowCeiling.centralGridSourceDecoratedFaceProduct_eqv
#print axioms
  YMGap.Continuum.BF4GrowingGridRawRowCeiling.centralGridPhysicalTerm_le_decoratedActivities_mul_residual
#print axioms
  YMGap.Continuum.BF4GrowingGridRawRowCeiling.centralGridPositiveRawRow_le_decoratedActivities_mul_ceiling
