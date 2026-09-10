/-
# Exact global lowering downset of the spin-four raw row

The local spin-four kernel is supported exactly when each target spin is no
larger than its source spin and has the same parity.  This file turns that
local fact into a global carrier theorem for the complete shared-link row.
Every physical target outside the finite pointwise-lowering downset has zero
raw weight, and the entire row sum is exactly the explicit lowering weight
summed only over that downset.

This is an exact support reduction, not yet an estimate of the retained
downset mass.  In particular, global coarse-link admissibility remains inside
the explicit lowering weight rather than being discarded.

Constructive contract: decidable finite-list filtering and exact rational
algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourLoweringKernel

namespace YMGap.Continuum.Z4DyadicSpinFourLoweringDownset

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4DyadicSpinFourWholeSlabTargetExact
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Decidable global lowering carrier -/

/-- Boolean test for pointwise parity-preserving lowering on every physical
coarse face. -/
def spinFourPointwiseLoweringB
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling) : Bool :=
  S.coarse.faceEdges.all fun faceId =>
    decide
      (targetState faceId ≤ sourceState faceId ∧
        targetState faceId % 2 = sourceState faceId % 2)

/-- The physical coarse targets on which the spin-four raw row can be
supported. -/
def spinFourLoweringTargets
    (S : SlabScalePair) (sourceState : EdgeLabelling) :
    List EdgeLabelling :=
  S.coarse.physicalLabellings.filter
    (spinFourPointwiseLoweringB S sourceState)

theorem spinFourPointwiseLoweringB_true_iff
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling) :
    spinFourPointwiseLoweringB S sourceState targetState = true ↔
      ∀ faceId, faceId ∈ S.coarse.faceEdges →
        targetState faceId ≤ sourceState faceId ∧
          targetState faceId % 2 = sourceState faceId % 2 := by
  unfold spinFourPointwiseLoweringB
  rw [List.all_eq_true]
  simp only [decide_eq_true_eq]

theorem mem_spinFourLoweringTargets_iff
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling) :
    targetState ∈ spinFourLoweringTargets S sourceState ↔
      targetState ∈ S.coarse.physicalLabellings ∧
        ∀ faceId, faceId ∈ S.coarse.faceEdges →
          targetState faceId ≤ sourceState faceId ∧
            targetState faceId % 2 = sourceState faceId % 2 := by
  unfold spinFourLoweringTargets
  rw [List.mem_filter]
  exact and_congr_right fun _ =>
    spinFourPointwiseLoweringB_true_iff S sourceState targetState

private theorem exists_false_of_all_false_local {A : Type}
    (test : A → Bool) : ∀ items : List A,
    items.all test = false →
      ∃ item, item ∈ items ∧ test item = false
  | [], hfalse => by cases hfalse
  | head :: tail, hfalse => by
      cases hhead : test head with
      | false => exact ⟨head, List.mem_cons_self, hhead⟩
      | true =>
          have htail : tail.all test = false := by
            simp only [List.all_cons, hhead, Bool.true_and] at hfalse
            exact hfalse
          obtain ⟨item, hitem, htest⟩ :=
            exists_false_of_all_false_local test tail htail
          exact ⟨item, List.mem_cons_of_mem head hitem, htest⟩

/-! ## 2. Every excluded physical target has zero raw weight -/

private theorem wholeSlabFiniteQProduct_eqv_zero_of_member_local {A : Type}
    (value : A → Q') : ∀ (items : List A) {item : A},
    item ∈ items → value item ≈ 0 →
      wholeSlabFiniteQProduct value items ≈ 0
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem, hzero => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst item
        change value head * wholeSlabFiniteQProduct value tail ≈ 0
        exact Q'.eqv_trans _
          (0 * wholeSlabFiniteQProduct value tail) _
          (Q'.mul_eqv_congr_right _ _ _ hzero)
          (Q'.zero_mul_eqv _)
      · change value head * wholeSlabFiniteQProduct value tail ≈ 0
        exact Q'.eqv_trans _ (value head * 0) _
          (Q'.mul_eqv_congr_left _ _ _
            (wholeSlabFiniteQProduct_eqv_zero_of_member_local
              value tail htail hzero))
          (Q'.mul_zero_eqv _)

private theorem mul_eqv_zero_of_left_local
    {left right : Q'} (hleft : left ≈ 0) : left * right ≈ 0 :=
  Q'.eqv_trans _ (0 * right) _
    (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.zero_mul_eqv _)

theorem spinFourLoweringWholeSlabRawWeight_eqv_zero_of_bad_face
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (hsource : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      sourceState faceId ≤ 4)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges)
    (hbad : ¬ (targetState faceId ≤ sourceState faceId ∧
      targetState faceId % 2 = sourceState faceId % 2)) :
    spinFourLoweringWholeSlabRawWeight
        S sourceState targetState ≈ 0 := by
  have htargetSound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges targetState htargetMem
  have htarget : targetState faceId ≤ 4 := by
    have hbound := Nat.le_of_lt_succ (htargetSound.1 faceId hface)
    rw [S.coarse_cutoff, hfineCutoff] at hbound
    omega
  have hmultZero :
      spinFourLoweringMultiplicity
          (sourceState faceId) (targetState faceId) = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hbad
      ((spinFourLoweringMultiplicity_pos_iff
        (hsource faceId hface) htarget).mp hpos)
  have hfaceZero :
      spinFourLoweringFaceWeight S.coarse.coupling
          (sourceState faceId) (targetState faceId) ≈ 0 := by
    unfold spinFourLoweringFaceWeight
    rw [hmultZero]
    exact Q'.eqv_trans _
      (0 * coeffW S.coarse.coupling (targetState faceId)) _
      (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv _)
  unfold spinFourLoweringWholeSlabRawWeight
  exact mul_eqv_zero_of_left_local
    (wholeSlabFiniteQProduct_eqv_zero_of_member_local
      (fun id => spinFourLoweringFaceWeight S.coarse.coupling
        (sourceState id) (targetState id))
      S.coarse.faceEdges hface hfaceZero)

/-- Failure of the global lowering test produces a literal bad face and
therefore annihilates the complete raw weight. -/
theorem spinFourLoweringWholeSlabRawWeight_eqv_zero_of_test_false
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (hsource : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      sourceState faceId ≤ 4)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings)
    (htest : spinFourPointwiseLoweringB
      S sourceState targetState = false) :
    spinFourLoweringWholeSlabRawWeight
        S sourceState targetState ≈ 0 := by
  obtain ⟨faceId, hface, hfaceTest⟩ :=
    exists_false_of_all_false_local
      (fun id => decide
        (targetState id ≤ sourceState id ∧
          targetState id % 2 = sourceState id % 2))
      S.coarse.faceEdges (by
        simpa only [spinFourPointwiseLoweringB] using htest)
  exact spinFourLoweringWholeSlabRawWeight_eqv_zero_of_bad_face
    S sourceState targetState hfineCutoff hsource htargetMem faceId hface
    (of_decide_eq_false hfaceTest)

/-- The original globally glued raw row also vanishes at every excluded
physical target. -/
theorem wholeSlabRecouplingRawWeight_spinFourProfile_eqv_zero_of_test_false
    (S : SlabScalePair) (fineState sourceState targetState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (profile : SpinFourWholeSlabPacketProfile S fineState sourceState)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings)
    (htest : spinFourPointwiseLoweringB
      S sourceState targetState = false) :
    wholeSlabRecouplingRawWeight S fineState targetState ≈ 0 :=
  Q'.eqv_trans _ _ _
    (wholeSlabRecouplingRawWeight_spinFourProfile_eqv_loweringWeight
      S fineState sourceState targetState hfineCutoff profile)
    (spinFourLoweringWholeSlabRawWeight_eqv_zero_of_test_false
      S sourceState targetState hfineCutoff profile.spin_le_four
        htargetMem htest)

/-! ## 3. Restrict the complete row sum exactly -/

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ source : List A,
      (∀ item, item ∈ source → test item = false → value item ≈ 0) →
      listQSum value source ≈ listQSum value (source.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false → value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test tail htail)

/-- Exact row-partition formula: sum the explicit lower-triangular weight
only over the finite physical lowering downset. -/
theorem wholeSlabRawRowMass_spinFourProfile_eqv_loweringDownset
    (S : SlabScalePair) (fineState sourceState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (profile : SpinFourWholeSlabPacketProfile S fineState sourceState) :
    listQSum (wholeSlabRecouplingRawWeight S fineState)
        S.coarse.physicalLabellings ≈
      listQSum (spinFourLoweringWholeSlabRawWeight S sourceState)
        (spinFourLoweringTargets S sourceState) := by
  refine Q'.eqv_trans _
    (listQSum (wholeSlabRecouplingRawWeight S fineState)
      (spinFourLoweringTargets S sourceState)) _ ?_ ?_
  · unfold spinFourLoweringTargets
    apply listQSum_eq_filter_of_zero_local
    intro targetState htarget htest
    exact
      wholeSlabRecouplingRawWeight_spinFourProfile_eqv_zero_of_test_false
        S fineState sourceState targetState hfineCutoff profile
          htarget htest
  · apply listQSum_congr_on
    intro targetState _
    exact
      wholeSlabRecouplingRawWeight_spinFourProfile_eqv_loweringWeight
        S fineState sourceState targetState hfineCutoff profile

/-- The intended endpoint itself belongs to its lowering downset. -/
theorem attachedEndpoint_mem_spinFourLoweringTargets
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) :
    endpoint.1.1 ∈ spinFourLoweringTargets S endpoint.1.1 := by
  apply (mem_spinFourLoweringTargets_iff S endpoint.1.1 endpoint.1.1).mpr
  constructor
  · exact (mem_slabExpandedFineSources_iff.mp endpoint.2).1
  · intro faceId _
    exact ⟨Nat.le_refl _, rfl⟩

/-- Concrete accepted-endpoint form of the exact downset normalization. -/
theorem wholeSlabJointRawRowMass_attachedEndpointSpinFour_eqv_loweringDownset
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1) :
    wholeSlabJointRawRowMass S
        (attachedEndpointSpinFourFineState S endpoint) ≈
      listQSum (spinFourLoweringWholeSlabRawWeight S endpoint.1.1)
        (spinFourLoweringTargets S endpoint.1.1) := by
  unfold wholeSlabJointRawRowMass
  exact wholeSlabRawRowMass_spinFourProfile_eqv_loweringDownset
    S (attachedEndpointSpinFourFineState S endpoint) endpoint.1.1
      hfineCutoff
      (attachedEndpointSpinFourWholeSlabPacketProfile
        S endpoint hfineCutoff)

#print axioms spinFourPointwiseLoweringB_true_iff
#print axioms mem_spinFourLoweringTargets_iff
#print axioms spinFourLoweringWholeSlabRawWeight_eqv_zero_of_bad_face
#print axioms spinFourLoweringWholeSlabRawWeight_eqv_zero_of_test_false
#print axioms wholeSlabRecouplingRawWeight_spinFourProfile_eqv_zero_of_test_false
#print axioms wholeSlabRawRowMass_spinFourProfile_eqv_loweringDownset
#print axioms attachedEndpoint_mem_spinFourLoweringTargets
#print axioms wholeSlabJointRawRowMass_attachedEndpointSpinFour_eqv_loweringDownset

end YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
