/-
# Growing-volume low-spin to matched-ray comparison gate

The all-cutoff low-spin replication theorem makes the slice-zero spin-one
stationary marginal tend to zero when the reflection half grows.  The matched
cofinal obstruction instead uses the sum of the spin-cube states `1,...,K` at
fixed reflection half zero.  These are different normalized finite objects.

This module names the exact diagonal comparison that would connect them and
proves its downstream consequence.  The comparison structure is intentionally
not inhabited: no fixed-half/growing-half volume comparison, ray-sum bound,
all-vector gap, continuum limit, or Clay theorem is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
import YMGap.Continuum.BF4DyadicCubeVacuumCalibration
import YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabQuadraticRemainder

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate

set_option maxRecDepth 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCorrectedSlabQuadraticRemainder
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_term_le_of_mem_nonnegative_local
    {A : Type} (weight : A → Q') :
    ∀ items item,
      item ∈ items →
      (∀ source, source ∈ items → (0 : Q') ≤ weight source) →
      weight item ≤ listQSum weight items
  | [], _item, hitem, _ => False.elim (List.not_mem_nil hitem)
  | head :: tail, item, hitem, hweight => by
      change weight item ≤ weight head + listQSum weight tail
      rcases List.mem_cons.mp hitem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on weight tail
            (fun source hsource =>
              hweight source (List.mem_cons_of_mem _ hsource)))
      · have hterm := listQSum_term_le_of_mem_nonnegative_local
          weight tail item htail
          (fun source hsource =>
            hweight source (List.mem_cons_of_mem head hsource))
        have hhead : (0 : Q') ≤ weight head :=
          hweight head List.mem_cons_self
        exact Q'.le_trans' _ _ _ hterm
          (Q'.le_trans' _ _ _
            (Q'.add_le_self_of_nonneg _ _ hhead)
            (Q'.le_of_eqv
              (Q'.add_comm_eqv (listQSum weight tail) (weight head))))

/-! ## 1. The exact missing comparison -/

/-- A diagonal comparison from the fixed-half matched spin-cube ray to a
cutoff- and scale-independent multiple of the single growing-half slice-zero
low-spin atom at the same matched cutoff and coupling.  These fields
deliberately expose both missing ingredients: control of the complete spin ray
by one low-spin atom and comparison of the normalized half-zero law with the
law at reflection half `scale + 1`. -/
structure MatchedDyadicLowSpinGrowingVolumeRayDomination
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  rayMass_le_ceiling_mul_growingReference : ∀ scale,
    centralLowerExcitedSpinCubeRayMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) ≤
      ceiling *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale)
          (scale + 1)
          (lowSpinCentralReferenceState scale)

/-! ## 2. A necessary fixed-half volume comparison -/

/-- The fixed-half spin-one marginal is already one literal nonnegative
summand of the excited spin-cube ray. -/
theorem fixedHalfSpinOneMarginal_le_rayMass
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≤
      centralLowerExcitedSpinCubeRayMass
        w (Q'.le_of_lt hw) K := by
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K 0
  have hindex : index ∈
      centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K := by
    unfold index centralLowerExcitedSpinCubeIndices
    apply List.mem_map.mpr
    exact ⟨0, List.mem_range.mpr hK, rfl⟩
  have hterm : weight index ≤
      listQSum weight
        (centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K) :=
    listQSum_term_le_of_mem_nonnegative_local
      weight _ index hindex (by
        intro source _hsource
        unfold weight centralPhysicalFiniteWeight
        exact centralPhysicalRowMarginal_nonnegative
          (Q'.le_of_lt hw) K 0
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw) K 0 source))
  have hstate := centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hK
  unfold index centralLowerExcitedSpinCubeIndex at hterm
  unfold weight centralPhysicalFiniteWeight at hterm
  rw [hstate] at hterm
  simpa only [centralLowerExcitedSpinCubeRayMass] using hterm

/-! ## 3. Exact raw-row/partition cross multiplication -/

def fixedHalfSpinOneRawRow
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  centralPhysicalPositiveRawRowMass
    w hw K 0 (centralLowerSpinCubeState 1)

def growingHalfSpinOneRawRow
    (w : Q') (hw : (0 : Q') ≤ w)
    (K volume : Nat) : Q' :=
  centralPhysicalPositiveRawRowMass
    w hw K (volume + 1) (lowSpinCentralReferenceState volume)

def fixedHalfPhysicalPartition (w : Q') (K : Nat) : Q' :=
  slabParametricKPhysicalPartition w K (centralExtent 0)

def growingHalfPhysicalPartition
    (w : Q') (K volume : Nat) : Q' :=
  slabParametricKPhysicalPartition w K (centralExtent (volume + 1))

private theorem centralPhysicalRowMarginal_eqv_rawRow_divPos_local
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half) :
    centralPhysicalRowMarginal w hw K half source ≈
      Q'.divPos
        (centralPhysicalPositiveRawRowMass w hw K half source)
        (slabParametricKPhysicalPartition w K (centralExtent half))
        (slabParametricKPhysicalPartition_pos hw K (centralExtent half)) := by
  have hrow :=
    centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
      (w := w) (hw := hw) (K := K) (half := half)
      (source := source) hsource
  simpa only [centralPhysicalPositiveRawRowMass,
    centralPhysicalFiniteVacuumSectorPartitionReciprocal,
    Q'.divPos] using hrow

/-- The necessary fixed-half/growing-half marginal comparison is exactly a
division-free inequality between the two raw rows and the two positive slab
partitions. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference_iff_cross
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K)
    (ceiling : Q') (volume : Nat) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≤
      ceiling *
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (volume + 1)
          (lowSpinCentralReferenceState volume) ↔
    fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
        growingHalfPhysicalPartition w K volume ≤
      (ceiling *
          growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) *
        fixedHalfPhysicalPartition w K := by
  let fixedRaw := fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K
  let growingRaw :=
    growingHalfSpinOneRawRow w (Q'.le_of_lt hw) K volume
  let fixedPartition := fixedHalfPhysicalPartition w K
  let growingPartition := growingHalfPhysicalPartition w K volume
  have hfixedPartition : (0 : Q') < fixedPartition := by
    unfold fixedPartition fixedHalfPhysicalPartition
    exact slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw) K (centralExtent 0)
  have hgrowingPartition : (0 : Q') < growingPartition := by
    unfold growingPartition growingHalfPhysicalPartition
    exact slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw) K (centralExtent (volume + 1))
  have hfixed :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≈
        Q'.divPos fixedRaw fixedPartition hfixedPartition := by
    unfold fixedRaw fixedPartition fixedHalfSpinOneRawRow
      fixedHalfPhysicalPartition
    exact centralPhysicalRowMarginal_eqv_rawRow_divPos_local
      (centralLowerSpinCubeState_mem_centralHalfStates hK)
  have hgrowingState : lowSpinCentralReferenceState volume ∈
      centralHalfStates K (volume + 1) := by
    have href :=
      (lowSpinCentralKPositiveRawReplication
        w hw K hK volume).reference_mem
    change lowSpinCentralReferenceState volume ∈
      centralPositiveHalfStates
        w (Q'.le_of_lt hw) K (volume + 1) at href
    exact (mem_centralPositiveHalfStates_iff.mp href).1
  have hgrowingMarginal :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (volume + 1)
            (lowSpinCentralReferenceState volume) ≈
        Q'.divPos growingRaw growingPartition
          hgrowingPartition := by
    unfold growingRaw growingPartition growingHalfSpinOneRawRow
      growingHalfPhysicalPartition
    exact centralPhysicalRowMarginal_eqv_rawRow_divPos_local
      hgrowingState
  have hgrowingScaled :
      ceiling *
          centralPhysicalRowMarginal
            w (Q'.le_of_lt hw) K (volume + 1)
              (lowSpinCentralReferenceState volume) ≈
        Q'.divPos (ceiling * growingRaw) growingPartition
          hgrowingPartition := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ceiling _ _ hgrowingMarginal)
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv ceiling growingRaw
          (Q'.recipPos growingPartition hgrowingPartition)))
  have hquotient := divPos_le_divPos_iff_cross
    fixedRaw fixedPartition
    (ceiling * growingRaw) growingPartition
    hfixedPartition hgrowingPartition
  constructor
  · intro hnormalized
    apply hquotient.mp
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hfixed)
      (Q'.le_trans' _ _ _ hnormalized
        (Q'.le_of_eqv hgrowingScaled))
  · intro hcross
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hfixed)
      (Q'.le_trans' _ _ _
        (hquotient.mpr (by
          simpa only [fixedRaw, growingRaw, fixedPartition,
            growingPartition] using hcross))
        (Q'.ge_of_eqv hgrowingScaled))

namespace MatchedDyadicLowSpinGrowingVolumeRayDomination

theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (comparison :
      MatchedDyadicLowSpinGrowingVolumeRayDomination bridge)
    (scale : Nat) :
    centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (Q'.le_of_lt
          (matchedAllSpinWeight_pos family coupling scale))
        (matchedAllSpinCutoff family coupling scale) 0
        (centralLowerSpinCubeState 1) ≤
      comparison.ceiling *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale)
          (scale + 1)
          (lowSpinCentralReferenceState scale) := by
  exact Q'.le_trans' _ _ _
    (fixedHalfSpinOneMarginal_le_rayMass
      (matchedAllSpinWeight_pos family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale))
    (comparison.rayMass_le_ceiling_mul_growingReference scale)

/-! ## 4. Compilation to the existing matched no-go branch -/

/-- The all-cutoff `1 / (volume + 1)` theorem turns the comparison field into
located tail-zero data for the exact fixed-half matched ray. -/
def toMatchedRayMassTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (comparison :
      MatchedDyadicLowSpinGrowingVolumeRayDomination bridge) :
    MatchedDyadicExcitedSpinCubeRayMassTailZero bridge where
  rate epsilon :=
    (Q'.divPos epsilon comparison.ceiling comparison.ceiling_pos).den
  rayMass_le := by
    intro epsilon hepsilon scale hscale
    let w := matchedAllSpinWeight family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    let delta :=
      Q'.divPos epsilon comparison.ceiling comparison.ceiling_pos
    have hw : (0 : Q') < w :=
      matchedAllSpinWeight_pos family coupling scale
    have hK : 1 ≤ K := one_le_matchedAllSpinCutoff bridge scale
    have hdelta : (0 : Q') < delta := by
      unfold delta
      exact Q'.divPos_pos epsilon comparison.ceiling
        comparison.ceiling_pos hepsilon
    have hscale' : delta.den ≤ scale := by
      simpa only [delta] using hscale
    have hgrowing := lowSpinCentralKReferenceMarginal_le_epsilon
      w hw K hK delta hdelta scale hscale'
    have hscaled :
        comparison.ceiling *
            centralPhysicalRowMarginal
              w (Q'.le_of_lt hw) K (scale + 1)
                (lowSpinCentralReferenceState scale) ≤
          comparison.ceiling * delta :=
      Q'.mul_le_mul_of_nonneg_left _ _ comparison.ceiling hgrowing
        (Q'.le_of_lt comparison.ceiling_pos)
    have hcollapse : comparison.ceiling * delta ≈ epsilon := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv comparison.ceiling delta)
        (by
          unfold delta
          exact Q'.divPos_mul_eqv epsilon comparison.ceiling
            comparison.ceiling_pos)
    exact Q'.le_trans' _ _ _
      (comparison.rayMass_le_ceiling_mul_growingReference scale)
      (Q'.le_trans' _ _ _
        (by simpa only [w, K] using hscaled)
        (Q'.le_of_eqv hcollapse))

/-- Consequently, inhabiting the exact comparison closes the cofinal assigned
stationary-ratio route as a no-go; it does not produce a spectral gap. -/
theorem excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (comparison :
      MatchedDyadicLowSpinGrowingVolumeRayDomination bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) :=
  tailZero_excludes_cofinalAssignedRatio
    comparison.toMatchedRayMassTailZero

end MatchedDyadicLowSpinGrowingVolumeRayDomination

end YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate.fixedHalfSpinOneMarginal_le_rayMass
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference_iff_cross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate.MatchedDyadicLowSpinGrowingVolumeRayDomination.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate.MatchedDyadicLowSpinGrowingVolumeRayDomination.toMatchedRayMassTailZero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate.MatchedDyadicLowSpinGrowingVolumeRayDomination.excludes_cofinalAssignedRatio
