/-
# Boundary sums of coarse-repair completion columns

The exact coarse repair column fixes one reflected-upper target and one
boundary channel, then sums over every lower state.  Summing those columns
over the boundary channel gives the complete raw column of that target.
Reflection symmetry turns it into the target's raw row, and zero-marginal
states may be removed exactly.  Thus the boundary sum is precisely the
positive-carrier raw row.

This is a finite structural identity.  It does not prove the pointwise
completion-column Harnack estimate, spin-ray compression, a cofinal gap, a
continuum limit, or the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumnSum

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_filter_eq_of_zero_local
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈
        listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ _ _
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem)))
            (Q'.eqv_symm
              (Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr'
                  (hzero head List.mem_cons_self hp)
                  (Q'.eqv_refl _))
                (Q'.eqv_of_eq (Q'.zero_add' _))))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_eqv_zero_of_all_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_all_local value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem))))
        (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm =>
      Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Raw zero columns outside the positive carrier -/

private theorem centralPhysicalReflectedKernel_eqv_zero_of_target_not_pos_local
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {source target : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half)
    (htarget : target ∈ centralHalfStates K half)
    (hnot : ¬ (0 : Q') <
      centralPhysicalRowMarginal w hw K half target) :
    centralPhysicalReflectedKernel w K half source target ≈ 0 := by
  unfold centralPhysicalReflectedKernel
  apply listQSum_eqv_zero_of_all_local
  intro boundary hboundary
  have hfull := assembleReflectedSlabLabelling_mem_full
    hsource hboundary htarget
  have hphysical :
      assembleReflectedSlabLabelling half source boundary target ∈
        centralPhysicalPartitionStates K half := by
    simpa only [centralPhysicalPartitionStates] using hfull
  have hupperNot : ¬ (0 : Q') <
      centralPhysicalRowMarginal w hw K half
        (centralReflectedUpperRestriction half
          (assembleReflectedSlabLabelling
            half source boundary target)) := by
    rw [centralReflectedUpperRestriction_assemble htarget]
    exact hnot
  have hzero :=
    centralPhysicalPartitionWeight_eqv_zero_of_upper_not_pos
      hphysical hupperNot
  simpa only [centralPhysicalPartitionWeight] using hzero

/-! ## 2. The boundary-summed completion column -/

/-- Fix a positive growing target and sum its literal completion columns over
all boundary channels. -/
def growingTargetCompletionColumnSum
    (w : Q') (K volume : Nat) (target : EdgeLabelling) : Q' :=
  listQSum
    (fun boundary =>
      growingCompletionColumnWeight
        w K volume (target, boundary))
    (centralBoundaryChannels K (volume + 1))

/-- The boundary sum of all completion columns at a positive target is
exactly that target's positive-carrier raw row. -/
theorem growingTargetCompletionColumnSum_eqv_positiveRawRowMass
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat)
    {target : EdgeLabelling}
    (htarget : target ∈
      centralPositiveHalfStates w hw K (volume + 1)) :
    growingTargetCompletionColumnSum w K volume target ≈
      centralPhysicalPositiveRawRowMass
        w hw K (volume + 1) target := by
  have htargetHalf :=
    (mem_centralPositiveHalfStates_iff.mp htarget).1
  have hswap :
      growingTargetCompletionColumnSum w K volume target ≈
        listQSum
          (fun lower =>
            centralPhysicalReflectedKernel
              w K (volume + 1) lower target)
          (centralHalfStates K (volume + 1)) := by
    simpa only [growingTargetCompletionColumnSum,
      growingCompletionColumnWeight,
      centralPositiveCompletionWeight,
      centralPhysicalReflectedKernel] using
      (listQSum_swap
        (fun lower boundary =>
          slabParametricKPhysicalTerm w K
            (centralExtent (volume + 1))
            (assembleReflectedSlabLabelling
              (volume + 1) lower boundary target))
        (centralHalfStates K (volume + 1))
        (centralBoundaryChannels K (volume + 1)))
  have hreorient :
      listQSum
          (fun lower =>
            centralPhysicalReflectedKernel
              w K (volume + 1) lower target)
          (centralHalfStates K (volume + 1)) ≈
        listQSum
          (centralPhysicalReflectedKernel
            w K (volume + 1) target)
          (centralHalfStates K (volume + 1)) := by
    apply listQSum_congr_on
    intro lower hlower
    exact centralPhysicalReflectedKernel_symm
      w hlower htargetHalf
  have hfilter :
      centralPhysicalPositiveRawRowMass
          w hw K (volume + 1) target ≈
        listQSum
          (centralPhysicalReflectedKernel
            w K (volume + 1) target)
          (centralHalfStates K (volume + 1)) := by
    unfold centralPhysicalPositiveRawRowMass
      centralPositiveHalfStates
    apply listQSum_filter_eq_of_zero_local
    intro candidate hcandidate hfalse
    have hnot : ¬ (0 : Q') <
        centralPhysicalRowMarginal
          w hw K (volume + 1) candidate := by
      simpa only [decide_eq_false_iff_not] using hfalse
    exact
      centralPhysicalReflectedKernel_eqv_zero_of_target_not_pos_local
        htargetHalf hcandidate hnot
  exact Q'.eqv_trans _ _ _ hswap
    (Q'.eqv_trans _ _ _ hreorient (Q'.eqv_symm hfilter))

/-! ## 3. The necessary target-row consequence of column Harnack -/

/-- The boundary-averaged consequence of the pointwise completion-column
Harnack producer.  It compares every positive target's whole raw row with the
single raw kernel entry from the literal low-spin reference state. -/
structure CoarseGrowingTargetRawRowCrossBound
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (ceiling : Q') : Type where
  weighted_target_row_cross : ∀ target,
    target ∈ centralPositiveHalfStates
        w (Q'.le_of_lt hw) K (volume + 1) →
      fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
          centralPhysicalPositiveRawRowMass
            w (Q'.le_of_lt hw) K (volume + 1) target ≤
        ceiling *
          (centralPhysicalReflectedKernel w K (volume + 1)
              (lowSpinCentralReferenceState volume) target *
            fixedHalfPhysicalPartition w K)

/-- Summing a pointwise completion-column Harnack bound over every boundary
channel yields the target-row cross bound.  The converse is deliberately not
claimed: the target-row statement is only an averaged necessary condition. -/
def CoarseGrowingCompletionColumnCrossBound.toTargetRawRowCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingCompletionColumnCrossBound
      w hw K hK volume ceiling) :
    CoarseGrowingTargetRawRowCrossBound
      w hw K hK volume ceiling where
  weighted_target_row_cross := by
    intro target htarget
    let hw0 := Q'.le_of_lt hw
    let boundaries := centralBoundaryChannels K (volume + 1)
    let fixedRaw := fixedHalfSpinOneRawRow w hw0 K
    let fixedPartition := fixedHalfPhysicalPartition w K
    let column := fun boundary =>
      growingCompletionColumnWeight w K volume (target, boundary)
    let referenceEntry := fun boundary =>
      centralPositiveCompletionWeight w K (volume + 1)
        (lowSpinCentralReferenceState volume) (target, boundary)
    have hterm : ∀ boundary,
        boundary ∈ boundaries →
        fixedRaw * column boundary ≤
          ceiling * (referenceEntry boundary * fixedPartition) := by
      intro boundary hboundary
      apply bound.weighted_column_cross (target, boundary)
      apply (mem_cartesian_iff _ _ _).mpr
      exact ⟨htarget, hboundary⟩
    have hsum :
        listQSum (fun boundary => fixedRaw * column boundary)
            boundaries ≤
          listQSum
            (fun boundary =>
              ceiling * (referenceEntry boundary * fixedPartition))
            boundaries :=
      listQSum_le_termwise_local _ _ boundaries hterm
    have hcolumnSum :
        listQSum column boundaries ≈
          centralPhysicalPositiveRawRowMass
            w hw0 K (volume + 1) target := by
      simpa only [column, boundaries, hw0,
        growingTargetCompletionColumnSum] using
        (growingTargetCompletionColumnSum_eqv_positiveRawRowMass
          hw0 K volume htarget)
    have hleft :
        listQSum (fun boundary => fixedRaw * column boundary)
            boundaries ≈
          fixedRaw *
            centralPhysicalPositiveRawRowMass
              w hw0 K (volume + 1) target := by
      exact Q'.eqv_trans _ _ _
        (listQSum_mul_left fixedRaw column boundaries)
        (Q'.mul_eqv_congr_left fixedRaw _ _ hcolumnSum)
    have hrefSum :
        listQSum referenceEntry boundaries ≈
          centralPhysicalReflectedKernel w K (volume + 1)
            (lowSpinCentralReferenceState volume) target := by
      unfold referenceEntry boundaries
        centralPositiveCompletionWeight centralPhysicalReflectedKernel
      exact Q'.eqv_refl _
    have hright :
        listQSum
            (fun boundary =>
              ceiling * (referenceEntry boundary * fixedPartition))
            boundaries ≈
          ceiling *
            (centralPhysicalReflectedKernel w K (volume + 1)
                (lowSpinCentralReferenceState volume) target *
              fixedPartition) := by
      exact Q'.eqv_trans _ _ _
        (listQSum_mul_left ceiling
          (fun boundary => referenceEntry boundary * fixedPartition)
          boundaries)
        (Q'.mul_eqv_congr_left ceiling _ _
          (Q'.eqv_trans _ _ _
            (listQSum_mul_right referenceEntry fixedPartition boundaries)
            (Q'.mul_eqv_congr_right _ _ fixedPartition hrefSum)))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hright))

/-! ## 4. Matched-diagonal necessary consequence -/

structure MatchedDyadicCoarseGrowingTargetRawRowCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  targetRowBound : ∀ scale,
    CoarseGrowingTargetRawRowCrossBound
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale ceiling

/-- Every matched pointwise completion-column producer has the matched
target-row cross bound as a necessary averaged consequence. -/
def MatchedDyadicCoarseGrowingCompletionColumnCrossBound.toTargetRawRowCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound : MatchedDyadicCoarseGrowingCompletionColumnCrossBound bridge) :
    MatchedDyadicCoarseGrowingTargetRawRowCrossBound bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  targetRowBound := fun scale =>
    CoarseGrowingCompletionColumnCrossBound.toTargetRawRowCrossBound
      (bound.columnBound scale)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumnSum

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumnSum.growingTargetCompletionColumnSum_eqv_positiveRawRowMass
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumnSum.CoarseGrowingCompletionColumnCrossBound.toTargetRawRowCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumnSum.MatchedDyadicCoarseGrowingCompletionColumnCrossBound.toTargetRawRowCrossBound
