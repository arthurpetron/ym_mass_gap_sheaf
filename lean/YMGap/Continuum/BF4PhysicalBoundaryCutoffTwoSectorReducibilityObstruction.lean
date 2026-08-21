/-
# Reducibility obstructs a strict gap on the full cutoff-two carrier

The exact 65-state cube sector and its nonempty transverse complement are
distinct closed blocks of the literal all-positive cutoff-two physical
kernel.  This module turns that block decomposition into a centered,
positive-norm eigenvalue-one observable for the physical Markov operator.
Consequently no strict upper contraction can hold on the full centered
carrier at this cutoff.

This finite obstruction says that a vacuum/ergodic sector must be selected
before stating a physical gap.  It is not a thermodynamic, continuum, or
Clay mass-gap theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness
import YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComplementWitness
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A decidable code for the exact closed sector -/

/-- Faithful finite codes of the 65 exact sector states. -/
def cutoffTwoCubeSectorCodes : List Nat :=
  cutoffTwoCubeSectorStates.map (bf4StateCode 2 0)

/-- The characteristic function of the exact sector, expressed through the
faithful finite-state code so that it remains executable. -/
def cutoffTwoSectorIndicator (state : EdgeLabelling) : Q' :=
  if bf4StateCode 2 0 state ∈ cutoffTwoCubeSectorCodes then 1 else 0

theorem cutoffTwoSectorCode_mem_iff_of_halfState
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates 2 0) :
    bf4StateCode 2 0 state ∈ cutoffTwoCubeSectorCodes ↔
      state ∈ cutoffTwoCubeSectorStates := by
  constructor
  · intro hcode
    rcases List.mem_map.mp hcode with ⟨candidate, hcand, hsameCode⟩
    have hcandHalf := cutoffTwoCubeSectorState_mem_halfStates hcand
    have hsame := bf4StateCode_injective_on_centralHalfStates
      hstate hcandHalf (Eq.symm hsameCode)
    subst candidate
    exact hcand
  · intro hsector
    exact List.mem_map.mpr ⟨state, hsector, rfl⟩

theorem zeroEdgeLabelling_mem_cutoffTwoCubeSectorStates :
    zeroEdgeLabelling ∈ cutoffTwoCubeSectorStates := by
  apply (mem_cutoffTwoCubeSectorStates_iff zeroEdgeLabelling).mpr
  right
  constructor
  · intro id _
    exact Or.inl rfl
  · intro id _
    rfl

theorem cutoffTwoSectorIndicator_vacuum_eq_one :
    cutoffTwoSectorIndicator zeroEdgeLabelling = 1 := by
  unfold cutoffTwoSectorIndicator
  rw [if_pos]
  exact (cutoffTwoSectorCode_mem_iff_of_halfState
    (zeroEdgeLabelling_mem_centralHalfStates 2 0)).mpr
      zeroEdgeLabelling_mem_cutoffTwoCubeSectorStates

theorem cutoffTwoSectorIndicator_transverse_eq_zero :
    cutoffTwoSectorIndicator cutoffTwoTransverseSingleFaceState = 0 := by
  unfold cutoffTwoSectorIndicator
  rw [if_neg]
  intro hcode
  exact cutoffTwoTransverseSingleFaceState_not_mem_sector
    ((cutoffTwoSectorCode_mem_iff_of_halfState
      cutoffTwoTransverseSingleFaceState_mem_halfStates).mp hcode)

/-! ## 2. Exact conditional-kernel block separation -/

private theorem centralNormalizedPhysicalReflectedKernel_eqv_zero_of_raw
    {source target : EdgeLabelling}
    (hraw :
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        source target ≈ 0) :
    centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        source target ≈ 0 := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos
      (slabParametricKPhysicalPartition cutoffTwoHalfCoupling 2
        (centralExtent 0))
      (slabParametricKPhysicalPartition_pos
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2
        (centralExtent 0))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hraw
  · exact Q'.zero_mul_eqv _

private theorem cutoffTwoConditionalKernel_eqv_zero_of_raw
    {source target : EdgeLabelling}
    (hsource : source ∈ cutoffTwoVacuumColumnCarrier)
    (hraw :
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        source target ≈ 0) :
    centralPhysicalConditionalKernel cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        source target ≈ 0 := by
  have hrow := (mem_centralPositiveHalfStates_iff.mp hsource).2
  rw [centralPhysicalConditionalKernel_eq_divPos hrow]
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos
      (centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 source)
      hrow) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralNormalizedPhysicalReflectedKernel_eqv_zero_of_raw hraw)
  · exact Q'.zero_mul_eqv _

theorem cutoffTwoConditionalKernel_sector_outside_eqv_zero
    {source target : EdgeLabelling}
    (hsource : source ∈ cutoffTwoVacuumColumnCarrier)
    (htarget : target ∈ cutoffTwoVacuumColumnCarrier)
    (hsourceSector : source ∈ cutoffTwoCubeSectorStates)
    (htargetOutside : target ∉ cutoffTwoCubeSectorStates) :
    centralPhysicalConditionalKernel cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        source target ≈ 0 := by
  apply cutoffTwoConditionalKernel_eqv_zero_of_raw hsource
  exact centralPhysicalReflectedKernel_cutoffTwo_cubeSector_eqv_zero
    source target hsourceSector
    (mem_centralPositiveHalfStates_iff.mp htarget).1 htargetOutside

theorem cutoffTwoConditionalKernel_outside_sector_eqv_zero
    {source target : EdgeLabelling}
    (hsource : source ∈ cutoffTwoVacuumColumnCarrier)
    (htarget : target ∈ cutoffTwoVacuumColumnCarrier)
    (hsourceOutside : source ∉ cutoffTwoCubeSectorStates)
    (htargetSector : target ∈ cutoffTwoCubeSectorStates) :
    centralPhysicalConditionalKernel cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        source target ≈ 0 := by
  apply cutoffTwoConditionalKernel_eqv_zero_of_raw hsource
  have hsymm := centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
    (mem_centralPositiveHalfStates_iff.mp hsource).1
    (mem_centralPositiveHalfStates_iff.mp htarget).1
  exact Q'.eqv_trans _ _ _ hsymm
    (centralPhysicalReflectedKernel_cutoffTwo_cubeSector_eqv_zero
      target source htargetSector
      (mem_centralPositiveHalfStates_iff.mp hsource).1 hsourceOutside)

/-! ## 3. The sector indicator is an eigenvalue-one observable -/

private theorem cutoffTwoSectorIndicator_kernel_term_eqv_source
    {source target : EdgeLabelling}
    (hsource : source ∈ cutoffTwoVacuumColumnCarrier)
    (htarget : target ∈ cutoffTwoVacuumColumnCarrier) :
    centralPhysicalConditionalKernel cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 source target *
        cutoffTwoSectorIndicator target ≈
      centralPhysicalConditionalKernel cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 source target *
        cutoffTwoSectorIndicator source := by
  have hsourceHalf := (mem_centralPositiveHalfStates_iff.mp hsource).1
  have htargetHalf := (mem_centralPositiveHalfStates_iff.mp htarget).1
  by_cases hsCode : bf4StateCode 2 0 source ∈ cutoffTwoCubeSectorCodes
  · have hsSector :=
      (cutoffTwoSectorCode_mem_iff_of_halfState hsourceHalf).mp hsCode
    by_cases htCode : bf4StateCode 2 0 target ∈ cutoffTwoCubeSectorCodes
    · unfold cutoffTwoSectorIndicator
      rw [if_pos hsCode, if_pos htCode]
      exact Q'.eqv_refl _
    · have htOutside : target ∉ cutoffTwoCubeSectorStates := by
        intro htSector
        exact htCode
          ((cutoffTwoSectorCode_mem_iff_of_halfState htargetHalf).mpr htSector)
      have hzero := cutoffTwoConditionalKernel_sector_outside_eqv_zero
        hsource htarget hsSector htOutside
      unfold cutoffTwoSectorIndicator
      rw [if_pos hsCode, if_neg htCode]
      exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _)
        (Q'.eqv_symm
          (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) hzero))
  · have hsOutside : source ∉ cutoffTwoCubeSectorStates := by
      intro hsSector
      exact hsCode
        ((cutoffTwoSectorCode_mem_iff_of_halfState hsourceHalf).mpr hsSector)
    by_cases htCode : bf4StateCode 2 0 target ∈ cutoffTwoCubeSectorCodes
    · have htSector :=
        (cutoffTwoSectorCode_mem_iff_of_halfState htargetHalf).mp htCode
      have hzero := cutoffTwoConditionalKernel_outside_sector_eqv_zero
        hsource htarget hsOutside htSector
      unfold cutoffTwoSectorIndicator
      rw [if_neg hsCode, if_pos htCode]
      exact Q'.eqv_trans _ 0 _
        (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) hzero)
        (Q'.eqv_symm (Q'.mul_zero_eqv _))
    · unfold cutoffTwoSectorIndicator
      rw [if_neg hsCode, if_neg htCode]
      exact Q'.eqv_refl _

theorem centralPhysicalMarkovApply_cutoffTwoSectorIndicator
    {source : EdgeLabelling}
    (hsource : source ∈ cutoffTwoVacuumColumnCarrier) :
    centralPhysicalMarkovApply cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        cutoffTwoSectorIndicator source ≈
      cutoffTwoSectorIndicator source := by
  unfold centralPhysicalMarkovApply
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        centralPhysicalConditionalKernel cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
            source target * cutoffTwoSectorIndicator source)
      cutoffTwoVacuumColumnCarrier) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact cutoffTwoSectorIndicator_kernel_term_eqv_source hsource htarget
  · refine Q'.eqv_trans _
      (listQSum
        (centralPhysicalConditionalKernel cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 source)
        cutoffTwoVacuumColumnCarrier * cutoffTwoSectorIndicator source) _ ?_ ?_
    · exact listQSum_mul_right _ _ _
    · exact Q'.eqv_trans _ (1 * cutoffTwoSectorIndicator source) _
        (Q'.mul_eqv_congr_right _ _ _
          (centralPhysicalConditionalKernel_row_normalized hsource))
        (Q'.one_mul_eqv _)

/-! ## 4. Centering preserves the eigenvalue-one mode -/

/-- The nonconstant block indicator after subtraction of its exact physical
stationary mean. -/
def cutoffTwoCenteredSectorIndicator : EdgeLabelling → Q' :=
  centralPhysicalCenteredObservable cutoffTwoHalfCoupling
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
    cutoffTwoSectorIndicator

theorem cutoffTwoCenteredSectorIndicator_meanZero :
    CentralPhysicalMeanZero cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
      cutoffTwoCenteredSectorIndicator := by
  exact centralPhysicalCenteredObservable_meanZero
    cutoffTwoHalfCoupling
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
    cutoffTwoSectorIndicator

private theorem centralPhysicalMarkovApply_constant
    (constant : Q') {source : EdgeLabelling}
    (hsource : source ∈ cutoffTwoVacuumColumnCarrier) :
    centralPhysicalMarkovApply cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        (fun _ => constant) source ≈ constant := by
  refine Q'.eqv_trans _
    (centralPhysicalMarkovApply cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
      (fun _ => constant * 1) source) _ ?_ ?_
  · exact centralPhysicalMarkovApply_congr cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
      (fun _ => Q'.eqv_symm (Q'.mul_one_eqv constant)) source
  · refine Q'.eqv_trans _
      (constant * centralPhysicalMarkovApply cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        (fun _ => 1) source) _ ?_ ?_
    · exact centralPhysicalMarkovApply_smul cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        constant (fun _ => 1) source
    · exact Q'.eqv_trans _ (constant * 1) _
        (Q'.mul_eqv_congr_left constant _ _
          (centralPhysicalMarkovApply_one hsource))
        (Q'.mul_one_eqv constant)

theorem centralPhysicalMarkovApply_cutoffTwoCenteredSectorIndicator
    {source : EdgeLabelling}
    (hsource : source ∈ cutoffTwoVacuumColumnCarrier) :
    centralPhysicalMarkovApply cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        cutoffTwoCenteredSectorIndicator source ≈
      cutoffTwoCenteredSectorIndicator source := by
  let mean := centralPhysicalStationaryMean cutoffTwoHalfCoupling
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
    cutoffTwoSectorIndicator
  change
    centralPhysicalMarkovApply cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        (fun state => cutoffTwoSectorIndicator state + -mean) source ≈
      cutoffTwoSectorIndicator source + -mean
  exact Q'.eqv_trans _
    (centralPhysicalMarkovApply cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        cutoffTwoSectorIndicator source +
      centralPhysicalMarkovApply cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        (fun _ => -mean) source) _
    (centralPhysicalMarkovApply_add cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
      cutoffTwoSectorIndicator (fun _ => -mean) source)
    (Q'.add_eqv_congr'
      (centralPhysicalMarkovApply_cutoffTwoSectorIndicator hsource)
      (centralPhysicalMarkovApply_constant (-mean) hsource))

/-! ## 5. The centered fixed mode has strictly positive norm -/

private theorem eqv_zero_iff_num_zero (x : Q') :
    x ≈ 0 ↔ x.num = 0 := by
  constructor
  · intro h
    have h' : x.num * (1 : Int) = (0 : Int) * (x.den : Int) := h
    simpa only [Int.mul_one, Int.zero_mul] using h'
  · intro h
    unfold Q'.eqv
    change x.num * (1 : Int) = (0 : Int) * (x.den : Int)
    rw [h]
    simp only [Int.zero_mul]

private theorem self_mul_pos_of_not_eqv_zero (x : Q')
    (hx : ¬ x ≈ 0) :
    (0 : Q') < x * x := by
  apply CReal.pos_of_num_pos
  rw [Q'.mul_num_cast]
  have hn : x.num ≠ 0 :=
    fun h => hx ((eqv_zero_iff_num_zero x).mpr h)
  rcases Int.lt_or_gt_of_ne hn with hneg | hpos
  · have hp : 0 < (-x.num) * (-x.num) :=
      Int.mul_pos (Int.neg_pos.mpr hneg) (Int.neg_pos.mpr hneg)
    simpa only [Int.neg_mul, Int.mul_neg, Int.neg_neg] using hp
  · exact Int.mul_pos hpos hpos

private theorem listQSum_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A}, selected ∈ items →
      value selected ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_local value hvalue tail)
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

private theorem cutoffTwoWeightedInner_pos_of_mem_ne_zero
    (observable : EdgeLabelling → Q') {selected : EdgeLabelling}
    (hselected : selected ∈ cutoffTwoVacuumColumnCarrier)
    (hselectedValue : ¬ observable selected ≈ 0) :
    (0 : Q') <
      centralPhysicalWeightedInner cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        observable observable := by
  let term : EdgeLabelling → Q' := fun state =>
    centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 state *
      (observable state * observable state)
  have htermNonnegative : ∀ state, (0 : Q') ≤ term state := by
    intro state
    exact Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 state)
      (q_mul_self_nonneg (observable state))
  have htermPositive : (0 : Q') < term selected :=
    Q'.mul_pos
      (mem_centralPositiveHalfStates_iff.mp hselected).2
      (self_mul_pos_of_not_eqv_zero
        (observable selected) hselectedValue)
  unfold centralPhysicalWeightedInner
  exact Q'.pos_of_lt_of_le htermPositive
    (listQSum_member_le_nonnegative_local term htermNonnegative
      cutoffTwoVacuumColumnCarrier hselected)

theorem cutoffTwoCenteredSectorIndicator_norm_pos :
    (0 : Q') <
      centralPhysicalWeightedInner cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        cutoffTwoCenteredSectorIndicator
        cutoffTwoCenteredSectorIndicator := by
  have hvacuum := zeroEdgeLabelling_mem_centralPositiveHalfStates
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
  have htransverse := cutoffTwoTransverseSingleFaceState_mem_carrier
  have hrelation :
      cutoffTwoCenteredSectorIndicator zeroEdgeLabelling ≈
        1 + cutoffTwoCenteredSectorIndicator
          cutoffTwoTransverseSingleFaceState := by
    unfold cutoffTwoCenteredSectorIndicator
      centralPhysicalCenteredObservable
    rw [cutoffTwoSectorIndicator_vacuum_eq_one,
      cutoffTwoSectorIndicator_transverse_eq_zero]
    exact Q'.add_eqv_congr' (Q'.eqv_refl 1)
      (Q'.eqv_symm
        (Q'.eqv_of_eq
          (Q'.zero_add'
            (-centralPhysicalStationaryMean cutoffTwoHalfCoupling
              (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
              cutoffTwoSectorIndicator))))
  let vacuumValue :=
    cutoffTwoCenteredSectorIndicator zeroEdgeLabelling
  have hdecidable : Decidable (vacuumValue ≈ 0) := by
    unfold Q'.eqv
    infer_instance
  cases hdecidable with
  | isFalse hvacuumNonzero =>
      exact cutoffTwoWeightedInner_pos_of_mem_ne_zero
        cutoffTwoCenteredSectorIndicator hvacuum hvacuumNonzero
  | isTrue hvacuumZero =>
      have htransverseNonzero :
          ¬ cutoffTwoCenteredSectorIndicator
              cutoffTwoTransverseSingleFaceState ≈ 0 := by
        intro htransverseZero
        have hzeroOne : (0 : Q') ≈ 1 :=
          Q'.eqv_trans _ vacuumValue _
            (Q'.eqv_symm hvacuumZero)
            (Q'.eqv_trans _
              (1 + cutoffTwoCenteredSectorIndicator
                cutoffTwoTransverseSingleFaceState) _ hrelation
              (Q'.eqv_trans _ (1 + 0) _
                (Q'.add_eqv_congr' (Q'.eqv_refl 1) htransverseZero)
                (Q'.eqv_of_eq (Q'.add_zero' 1))))
        exact (by decide : ¬ (0 : Q') ≈ 1) hzeroOne
      exact cutoffTwoWeightedInner_pos_of_mem_ne_zero
        cutoffTwoCenteredSectorIndicator htransverse
        htransverseNonzero

/-! ## 6. No strict full-carrier centered contraction -/

theorem cutoffTwoCenteredSectorIndicator_joint_eqv_norm :
    centralPhysicalJointQuadratic cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        cutoffTwoCenteredSectorIndicator ≈
      centralPhysicalWeightedInner cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        cutoffTwoCenteredSectorIndicator
        cutoffTwoCenteredSectorIndicator := by
  have hmarkovInner :
      centralPhysicalWeightedInner cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
          cutoffTwoCenteredSectorIndicator
          (centralPhysicalMarkovApply cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
            cutoffTwoCenteredSectorIndicator) ≈
        centralPhysicalWeightedInner cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
          cutoffTwoCenteredSectorIndicator
          cutoffTwoCenteredSectorIndicator := by
    unfold centralPhysicalWeightedInner
    apply listQSum_congr_on
    intro state hstate
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left
        (cutoffTwoCenteredSectorIndicator state) _ _
        (centralPhysicalMarkovApply_cutoffTwoCenteredSectorIndicator hstate))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (centralPhysicalWeightedMarkovQuadratic_eq_joint
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
        cutoffTwoCenteredSectorIndicator))
    hmarkovInner

/-- Upper-only strict contraction already fails on the literal full positive
carrier. -/
theorem no_cutoffTwo_fullCarrier_strict_upper_gap
    (q : Q') (hq : q < (1 : Q')) :
    ¬ (∀ observable : EdgeLabelling → Q',
      CentralPhysicalMeanZero cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 observable →
        centralPhysicalJointQuadratic cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
            observable ≤
          q * centralPhysicalWeightedInner cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
            observable observable) := by
  intro hgap
  let norm := centralPhysicalWeightedInner cutoffTwoHalfCoupling
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
    cutoffTwoCenteredSectorIndicator cutoffTwoCenteredSectorIndicator
  have hbound := hgap cutoffTwoCenteredSectorIndicator
    cutoffTwoCenteredSectorIndicator_meanZero
  have hnormLe : norm ≤ q * norm :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv cutoffTwoCenteredSectorIndicator_joint_eqv_norm)
      hbound
  have hstrict : q * norm < (1 : Q') * norm :=
    mul_lt_mul_of_pos_right cutoffTwoCenteredSectorIndicator_norm_pos hq
  have hstrictNorm : q * norm < norm :=
    lt_of_lt_of_le hstrict
      (Q'.le_of_eqv (Q'.one_mul_eqv norm))
  exact lt_irrefl' norm
    (Q'.lt_of_le_of_lt hnormLe hstrictNorm)

/-- Therefore the absolute-value form used by the cofinal gap compiler also
cannot hold at cutoff two on the all-positive carrier. -/
theorem no_cutoffTwo_fullCarrier_strict_abs_gap
    (q : Q') (hq : q < (1 : Q')) :
    ¬ (∀ observable : EdgeLabelling → Q',
      CentralPhysicalMeanZero cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 observable →
        Q'.abs
          (centralPhysicalJointQuadratic cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
            observable) ≤
          q * centralPhysicalWeightedInner cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
            observable observable) := by
  intro hgap
  apply no_cutoffTwo_fullCarrier_strict_upper_gap q hq
  intro observable hmean
  have habs := hgap observable hmean
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (centralPhysicalJointQuadratic_nonnegative cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 observable)] at habs
  exact habs

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction.centralPhysicalMarkovApply_cutoffTwoSectorIndicator
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction.cutoffTwoCenteredSectorIndicator_norm_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction.no_cutoffTwo_fullCarrier_strict_abs_gap
