/-
# Positive-carrier boundary amplitudes for coarse repair columns

The first boundary-amplitude factorization sums over the complete bounded
lower-state carrier.  This module proves that every physical summand whose
lower row has zero normalized marginal is itself zero.  The column may
therefore be filtered exactly to the positive lower carrier, replacing the
unfiltered amplitude sum by the already established physical positive-
boundary total.

This connects the coarse repair producer to the retained half-amplitude
Harnack infrastructure without asserting that a uniform estimate exists.
No cofinal gap, continuum limit, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryAmplitude

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryAmplitude
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem mul_column_scale_reorder_local
    (a b c d : Q') :
    (a * b) * (c * d) ≈ a * (c * (b * d)) := by
  show ((a * b) * (c * d)).num *
      ((a * (c * (b * d))).den : Int) =
    (a * (c * (b * d))).num *
      (((a * b) * (c * d)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

private theorem mul_column_target_reorder_local
    (a b c d e : Q') :
    (a * (b * c)) * (d * e) ≈
      a * ((d * (b * e)) * c) := by
  show ((a * (b * c)) * (d * e)).num *
      ((a * ((d * (b * e)) * c)).den : Int) =
    (a * ((d * (b * e)) * c)).num *
      (((a * (b * c)) * (d * e)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe : listQSum value tail ≤
            value head + listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ ih htailLe

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

/-! ## 1. Exceptional lower rows carry no physical weight -/

/-- If the lower restriction has no positive normalized row, the individual
full-slab physical term is exactly zero. -/
theorem centralPhysicalPartitionWeight_eqv_zero_of_lower_not_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {physical : EdgeLabelling}
    (hphysical : physical ∈ centralPhysicalPartitionStates K half)
    (hnot : ¬ (0 : Q') <
      centralPhysicalRowMarginal w hw K half
        (centralLowerRestriction half physical)) :
    centralPhysicalPartitionWeight w K half physical ≈ 0 := by
  have hphysical' : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half)) := by
    simpa only [centralPhysicalPartitionStates] using hphysical
  let lower := centralLowerRestriction half physical
  let upper := centralReflectedUpperRestriction half physical
  let boundary := centralBoundaryRestriction half physical
  have hlower : lower ∈ centralHalfStates K half := by
    unfold lower centralHalfStates
    exact centralLowerRestriction_mem hphysical'
  have hupper : upper ∈ centralHalfStates K half := by
    unfold upper centralHalfStates
    exact centralReflectedUpperRestriction_mem hphysical'
  have hboundary : boundary ∈ centralBoundaryChannels K half := by
    unfold boundary centralBoundaryChannels
    exact centralBoundaryRestriction_mem hphysical'
  have htermLeKernel :
      centralPhysicalPartitionWeight w K half physical ≤
        centralPhysicalReflectedKernel w K half lower upper := by
    unfold centralPhysicalPartitionWeight centralPhysicalReflectedKernel
    rw [← assembleReflectedSlabLabelling_restrictions hphysical']
    exact listQSum_member_le_nonnegative_local
      (fun fixed =>
        slabParametricKPhysicalTerm w K (centralExtent half)
          (assembleReflectedSlabLabelling half lower fixed upper))
      (fun fixed =>
        slabParametricKPhysicalTerm_nonnegative hw K
          (centralExtent half)
          (assembleReflectedSlabLabelling half lower fixed upper))
      (centralBoundaryChannels K half) hboundary
  let partition := slabParametricKPhysicalPartition
    w K (centralExtent half)
  let hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos hw K (centralExtent half)
  let reciprocal := Q'.recipPos partition hpartition
  have hreciprocal : (0 : Q') < reciprocal :=
    Q'.recipPos_pos partition hpartition
  have hscaled :
      centralPhysicalPartitionWeight w K half physical * reciprocal ≤
        centralPhysicalReflectedKernel w K half lower upper * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ reciprocal htermLeKernel
      (Q'.le_of_lt hreciprocal)
  have hnormalized :
      centralPhysicalReflectedKernel w K half lower upper * reciprocal ≈ 0 := by
    have hzero :=
      centralNormalizedPhysicalReflectedKernel_eqv_zero_of_row_not_pos
        hupper hnot
    simpa only [centralNormalizedPhysicalReflectedKernel,
      Q'.divPos, partition, reciprocal, lower, upper] using hzero
  have hscaledZero :
      centralPhysicalPartitionWeight w K half physical * reciprocal ≤ 0 :=
    Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hnormalized)
  have hcancelReady :
      reciprocal * centralPhysicalPartitionWeight w K half physical ≤
        reciprocal * 0 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv reciprocal
          (centralPhysicalPartitionWeight w K half physical)))
      (Q'.le_trans' _ _ _ hscaledZero
        (Q'.le_of_eqv
          (Q'.eqv_symm (Q'.mul_zero_eqv reciprocal))))
  have hnonpositive :
      centralPhysicalPartitionWeight w K half physical ≤ 0 :=
    Q'.le_of_mul_le_mul_left hcancelReady hreciprocal
  exact Q'.eqv_of_le_le hnonpositive
    (centralPhysicalPartitionWeight_nonnegative hw K half physical)

/-! ## 2. Positive-carrier column factorization -/

theorem growingCompletionColumnWeight_eqv_positiveBoundaryAmplitudeFactorization
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {target boundary : EdgeLabelling}
    (htarget : target ∈
      centralPositiveHalfStates w hw K (volume + 1))
    (hboundary : boundary ∈
      centralBoundaryChannels K (volume + 1)) :
    growingCompletionColumnWeight
        w K volume (target, boundary) ≈
      centralBoundaryWeight w K (volume + 1) boundary *
        (centralPositiveBoundaryTotalHalfAmplitude
            w hw K (volume + 1) boundary *
          centralHalfAmplitude
            w K (volume + 1) target boundary) := by
  let value := fun lower =>
    centralPositiveCompletionWeight w K (volume + 1)
      lower (target, boundary)
  let predicate := fun lower =>
    decide ((0 : Q') <
      centralPhysicalRowMarginal w hw K (volume + 1) lower)
  have hfilter :
      listQSum value
          ((centralHalfStates K (volume + 1)).filter predicate) ≈
        listQSum value (centralHalfStates K (volume + 1)) := by
    apply listQSum_filter_eq_of_zero_local
    intro lower hlower hfalse
    have hnot : ¬ (0 : Q') <
        centralPhysicalRowMarginal w hw K (volume + 1) lower := by
      simpa only [predicate, decide_eq_false_iff_not] using hfalse
    have hphysicalFull := assembleReflectedSlabLabelling_mem_full
      hlower hboundary
      (mem_centralPositiveHalfStates_iff.mp htarget).1
    have hphysical :
        assembleReflectedSlabLabelling
            (volume + 1) lower boundary target ∈
          centralPhysicalPartitionStates K (volume + 1) := by
      simpa only [centralPhysicalPartitionStates] using hphysicalFull
    have hlowerNot : ¬ (0 : Q') <
        centralPhysicalRowMarginal w hw K (volume + 1)
          (centralLowerRestriction (volume + 1)
            (assembleReflectedSlabLabelling
              (volume + 1) lower boundary target)) := by
      rw [centralLowerRestriction_assemble hlower]
      exact hnot
    have hzero :=
      centralPhysicalPartitionWeight_eqv_zero_of_lower_not_pos
        hphysical hlowerNot
    simpa only [value, centralPositiveCompletionWeight,
      centralPhysicalPartitionWeight] using hzero
  have hterms :
      listQSum value
          (centralPositiveHalfStates w hw K (volume + 1)) ≈
        listQSum
          (fun lower =>
            centralBoundaryWeight w K (volume + 1) boundary *
              (centralHalfAmplitude
                  w K (volume + 1) lower boundary *
                centralHalfAmplitude
                  w K (volume + 1) target boundary))
          (centralPositiveHalfStates w hw K (volume + 1)) := by
    apply listQSum_congr_on
    intro lower hlower
    unfold value centralPositiveCompletionWeight
    exact centralPhysicalTerm_eq_gram_integrand
      w (mem_centralPositiveHalfStates_iff.mp hlower).1
      hboundary (mem_centralPositiveHalfStates_iff.mp htarget).1
  refine Q'.eqv_trans _
    (listQSum value
      (centralPositiveHalfStates w hw K (volume + 1))) _ ?_ ?_
  · change listQSum value (centralHalfStates K (volume + 1)) ≈
      listQSum value
        ((centralHalfStates K (volume + 1)).filter predicate)
    exact Q'.eqv_symm hfilter
  · exact Q'.eqv_trans _ _ _ hterms
      (Q'.eqv_trans _ _ _
        (listQSum_mul_left
          (centralBoundaryWeight w K (volume + 1) boundary)
          (fun lower =>
            centralHalfAmplitude w K (volume + 1) lower boundary *
              centralHalfAmplitude w K (volume + 1) target boundary)
          (centralPositiveHalfStates w hw K (volume + 1)))
        (Q'.mul_eqv_congr_left
          (centralBoundaryWeight w K (volume + 1) boundary) _ _
          (Q'.eqv_trans _ _ _
            (listQSum_mul_right
              (fun lower =>
                centralHalfAmplitude w K (volume + 1) lower boundary)
              (centralHalfAmplitude w K (volume + 1) target boundary)
              (centralPositiveHalfStates w hw K (volume + 1)))
            (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_refl _)))))

/-! ## 3. The retained positive-boundary producer -/

structure CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (ceiling : Q') : Type where
  weighted_positive_boundary_cross : ∀ boundary,
    boundary ∈ centralBoundaryChannels K (volume + 1) →
      fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
          centralPositiveBoundaryTotalHalfAmplitude
            w (Q'.le_of_lt hw) K (volume + 1) boundary ≤
        ceiling *
          (centralHalfAmplitude w K (volume + 1)
              (lowSpinCentralReferenceState volume) boundary *
            fixedHalfPhysicalPartition w K)

/-- The positive-carrier boundary comparison is sufficient for the exact
completion-column Harnack producer. -/
def CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
      w hw K hK volume ceiling) :
    CoarseGrowingCompletionColumnCrossBound
      w hw K hK volume ceiling := by
  refine {
    weighted_column_cross := ?_
  }
  intro completion hcompletion
  let hw0 := Q'.le_of_lt hw
  have hparts := (mem_cartesian_iff
    (centralPositiveHalfStates w hw0 K (volume + 1))
    (centralBoundaryChannels K (volume + 1)) completion).mp hcompletion
  let target := completion.1
  let boundary := completion.2
  let fixedRaw := fixedHalfSpinOneRawRow w hw0 K
  let fixedPartition := fixedHalfPhysicalPartition w K
  let positiveTotal := centralPositiveBoundaryTotalHalfAmplitude
    w hw0 K (volume + 1) boundary
  let boundaryWeight := centralBoundaryWeight w K (volume + 1) boundary
  let targetAmplitude :=
    centralHalfAmplitude w K (volume + 1) target boundary
  let referenceAmplitude :=
    centralHalfAmplitude w K (volume + 1)
      (lowSpinCentralReferenceState volume) boundary
  have hcolumn :=
    growingCompletionColumnWeight_eqv_positiveBoundaryAmplitudeFactorization
      hparts.1 hparts.2
  have hrefPositive :=
    (lowSpinCentralKPositiveRawReplication
      w hw K hK volume).reference_mem
  have href := centralPhysicalTerm_eq_gram_integrand
    w (mem_centralPositiveHalfStates_iff.mp hrefPositive).1 hparts.2
      (mem_centralPositiveHalfStates_iff.mp hparts.1).1
  have hcommon : (0 : Q') ≤ boundaryWeight * targetAmplitude :=
    Q'.mul_nonneg _ _
      (centralBoundaryWeight_nonnegative_on hw0 boundary hparts.2)
      (centralHalfAmplitude_nonnegative
        hw0 K (volume + 1) target boundary)
  have hbase := bound.weighted_positive_boundary_cross boundary hparts.2
  have hscaled :
      (fixedRaw * positiveTotal) * (boundaryWeight * targetAmplitude) ≤
        (ceiling * (referenceAmplitude * fixedPartition)) *
          (boundaryWeight * targetAmplitude) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hcommon
  have hleft :
      fixedRaw * growingCompletionColumnWeight w K volume completion ≈
        (fixedRaw * positiveTotal) *
          (boundaryWeight * targetAmplitude) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left fixedRaw _ _ (by
        simpa only [target, boundary] using hcolumn))
      (Q'.eqv_symm
        (mul_column_scale_reorder_local
          fixedRaw positiveTotal boundaryWeight targetAmplitude))
  have hright :
      (ceiling * (referenceAmplitude * fixedPartition)) *
          (boundaryWeight * targetAmplitude) ≈
        ceiling *
          (centralPositiveCompletionWeight w K (volume + 1)
              (lowSpinCentralReferenceState volume) completion *
            fixedPartition) := by
    refine Q'.eqv_trans _ _ _
      (mul_column_target_reorder_local
        ceiling referenceAmplitude fixedPartition
        boundaryWeight targetAmplitude) ?_
    exact Q'.mul_eqv_congr_left ceiling _ _
      (Q'.mul_eqv_congr_right _ _ fixedPartition
        (Q'.eqv_symm (by
          simpa only [target, boundary] using href)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-! ## 4. Matched-diagonal compiler -/

structure MatchedDyadicCoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  positiveBoundaryBound : ∀ scale,
    CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale ceiling

def MatchedDyadicCoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound :
      MatchedDyadicCoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
        bridge) :
    MatchedDyadicCoarseGrowingCompletionColumnCrossBound bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  columnBound := fun scale =>
    CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
      (bound.positiveBoundaryBound scale)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude.centralPhysicalPartitionWeight_eqv_zero_of_lower_not_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude.growingCompletionColumnWeight_eqv_positiveBoundaryAmplitudeFactorization
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude.CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude.MatchedDyadicCoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toCompletionColumnCrossBound
