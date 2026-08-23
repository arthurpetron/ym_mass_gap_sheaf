/-
# The cutoff-one canonical stationary law is the vacuum-column posterior

The canonical cutoff-one component is the multiplicity-free vacuum/cube
block, and its genuine Gram rows are a common posterior refresh.  This module
computes the normalization selected by the original physical joint law.  The
cube row marginal is exactly the six-face activity times the vacuum row
marginal, so the component mass is the vacuum marginal times the same
two-term denominator used by the vacuum-column posterior.  Consequently the
indexed component-conditioned stationary law is pointwise that posterior.

This is finite `K = 1`, half-extent zero only.  It does not supply a cofinal
or continuum estimate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation
import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
import YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

private theorem one_num_local : (1 : Q').num = 1 := rfl

private theorem one_den_local : (1 : Q').den = 1 := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofInt, Q'.ofNat, Q'.neg,
               one_num_local, one_den_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try simp;
             try omega;
             try ac_rfl))

private theorem qmul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQSum_filter_eq_of_zero_local
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈ listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true, if_false,
            listQSum]
          have hhead := hzero head List.mem_cons_self hp
          have htail := listQSum_filter_eq_of_zero_local
            value predicate tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem))
          exact Q'.eqv_trans _ (listQSum value tail) _ htail
            (Q'.eqv_trans _ (0 + listQSum value tail) _
              (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
              (Q'.add_eqv_congr'
                (Q'.eqv_symm hhead) (Q'.eqv_refl _)))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Raw positive-row mass and normalized marginal -/

/-- A physical row marginal is its raw reflected-kernel mass over the
positive carrier, multiplied by the common partition reciprocal. -/
theorem centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half) :
    centralPhysicalRowMarginal w hw K half source ≈
      listQSum
          (centralPhysicalReflectedKernel w K half source)
          (centralPositiveHalfStates w hw K half) *
        centralPhysicalFiniteVacuumSectorPartitionReciprocal
          w hw K half := by
  let full := centralHalfStates K half
  let positive := centralPositiveHalfStates w hw K half
  let reciprocal :=
    centralPhysicalFiniteVacuumSectorPartitionReciprocal w hw K half
  have hfilter :
      listQSum
          (centralNormalizedPhysicalReflectedKernel w hw K half source)
          positive ≈
        listQSum
          (centralNormalizedPhysicalReflectedKernel w hw K half source)
          full := by
    unfold positive centralPositiveHalfStates
    apply listQSum_filter_eq_of_zero_local
    intro target htarget hfalse
    exact centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
      hsource htarget (by
        simpa only [decide_eq_false_iff_not] using hfalse)
  refine Q'.eqv_trans _
    (listQSum
      (centralNormalizedPhysicalReflectedKernel w hw K half source)
      positive) _ (Q'.eqv_symm hfilter) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        centralPhysicalReflectedKernel w K half source target * reciprocal)
      positive) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.eqv_refl _
  · exact listQSum_mul_right
      (centralPhysicalReflectedKernel w K half source)
      reciprocal positive

theorem centralPhysicalRowMarginal_cutoffOne_vacuum_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
        zeroEdgeLabelling ≈
      cutoffOneVacuumPhysicalGramRowMass w hw *
        centralPhysicalFiniteVacuumSectorPartitionReciprocal
          w (Q'.le_of_lt hw) 1 0 := by
  simpa [cutoffOneVacuumPhysicalGramRowMass] using
    (centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
      (w := w) (hw := Q'.le_of_lt hw) (K := 1) (half := 0)
      (source := zeroEdgeLabelling)
      (zeroEdgeLabelling_mem_centralHalfStates 1 0))

theorem centralPhysicalRowMarginal_cutoffOne_cube_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
        centralLowerCubeState ≈
      cutoffOneCubePhysicalGramRowMass w hw *
        centralPhysicalFiniteVacuumSectorPartitionReciprocal
          w (Q'.le_of_lt hw) 1 0 := by
  have hcubeHalf :=
    (mem_centralPositiveHalfStates_iff.mp
      (centralLowerCubeState_mem_centralPositiveHalfStates
        hw (by decide : 1 ≤ 1))).1
  simpa [cutoffOneCubePhysicalGramRowMass] using
    (centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
      (w := w) (hw := Q'.le_of_lt hw) (K := 1) (half := 0)
      (source := centralLowerCubeState) hcubeHalf)

/-! ## 2. Exact relative marginal and component mass -/

theorem centralPhysicalRowMarginal_cutoffOne_cube_eqv_activity_mul_vacuum
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
        centralLowerCubeState ≈
      (coeffW w 1) ^ 6 *
        centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
          zeroEdgeLabelling := by
  let reciprocal :=
    centralPhysicalFiniteVacuumSectorPartitionReciprocal
      w (Q'.le_of_lt hw) 1 0
  let boundaryWeight :=
    centralBoundaryWeight w 1 0 zeroEdgeLabelling
  let activity := (coeffW w 1) ^ 6
  let denominator := cutoffOneVacuumColumnDenominator w
  refine Q'.eqv_trans _
    ((boundaryWeight * (activity * denominator)) * reciprocal) _
    (Q'.eqv_trans _
      (cutoffOneCubePhysicalGramRowMass w hw * reciprocal) _
      (centralPhysicalRowMarginal_cutoffOne_cube_eqv hw)
      (Q'.mul_eqv_congr_right _ _ reciprocal
        (cutoffOneCubePhysicalGramRowMass_eqv hw))) ?_
  refine Q'.eqv_trans _
    (activity * ((boundaryWeight * denominator) * reciprocal)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (((boundaryWeight * activity) * denominator) * reciprocal) _
      (Q'.mul_eqv_congr_right _ _ reciprocal
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv boundaryWeight activity denominator))) ?_
    refine Q'.eqv_trans _
      (((activity * boundaryWeight) * denominator) * reciprocal) _
      (Q'.mul_eqv_congr_right _ _ reciprocal
        (Q'.mul_eqv_congr_right _ _ denominator
          (Q'.mul_comm_eqv boundaryWeight activity))) ?_
    refine Q'.eqv_trans _
      ((activity * (boundaryWeight * denominator)) * reciprocal) _
      (Q'.mul_eqv_congr_right _ _ reciprocal
        (Q'.mul_assoc_eqv activity boundaryWeight denominator)) ?_
    exact Q'.mul_assoc_eqv activity
      (boundaryWeight * denominator) reciprocal
  exact Q'.mul_eqv_congr_left activity _ _
    (Q'.eqv_trans _
      (cutoffOneVacuumPhysicalGramRowMass w hw * reciprocal) _
      (Q'.mul_eqv_congr_right _ _ reciprocal
        (Q'.eqv_symm (cutoffOneVacuumPhysicalGramRowMass_eqv hw)))
      (Q'.eqv_symm
        (centralPhysicalRowMarginal_cutoffOne_vacuum_eqv hw)))

theorem centralPhysicalFiniteVacuumSectorMass_cutoffOne_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) 1 0 ≈
      cutoffOneVacuumColumnDenominator w *
        centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
          zeroEdgeLabelling := by
  let indices := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) 1 0
  let stateAt := centralPhysicalFiniteStateAt
    w (Q'.le_of_lt hw) 1 0
  let marginal := centralPhysicalRowMarginal
    w (Q'.le_of_lt hw) 1 0
  let vacuumMarginal := marginal zeroEdgeLabelling
  let activity := (coeffW w 1) ^ 6
  refine Q'.eqv_trans _
    (listQSum marginal
      (centralPhysicalFiniteVacuumSectorStates
        w (Q'.le_of_lt hw) 1 0)) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
      centralPhysicalFiniteWeight
      centralPhysicalFiniteVacuumSectorStates
    exact Q'.eqv_of_eq
      (listQSum_map marginal stateAt
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) 1 0)).symm
  refine Q'.eqv_trans _
    (listQSum marginal cutoffOneVacuumCubePhysicalSources) _
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_sum_eqv
      hw marginal) ?_
  refine Q'.eqv_trans _
    (vacuumMarginal + marginal centralLowerCubeState) _ ?_ ?_
  · unfold cutoffOneVacuumCubePhysicalSources listQSum
    exact Q'.add_eqv_congr_left vacuumMarginal _ _
      (Q'.eqv_of_eq (Q'.add_zero' _))
  refine Q'.eqv_trans _
    (vacuumMarginal + activity * vacuumMarginal) _
    (Q'.add_eqv_congr_left vacuumMarginal _ _
      (centralPhysicalRowMarginal_cutoffOne_cube_eqv_activity_mul_vacuum
        hw)) ?_
  unfold cutoffOneVacuumColumnDenominator activity vacuumMarginal marginal
  refine Q'.eqv_trans _
    ((1 : Q') *
        centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
          zeroEdgeLabelling +
      (coeffW w 1) ^ 6 *
        centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
          zeroEdgeLabelling) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm
        (Q'.one_mul_eqv
          (centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
            zeroEdgeLabelling)))
      (Q'.eqv_refl _)
  exact Q'.eqv_symm
    (Q'.add_mul_eqv 1 ((coeffW w 1) ^ 6)
      (centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
        zeroEdgeLabelling))

/-! ## 3. The indexed conditioned stationary law is the posterior -/

private theorem cutoffOneVacuumColumnPosterior_mul_sectorMass_eqv_vacuumMarginal
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumColumnPosterior w hw zeroEdgeLabelling *
        centralPhysicalFiniteVacuumSectorMass
          w (Q'.le_of_lt hw) 1 0 ≈
      centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
        zeroEdgeLabelling := by
  let denominator := cutoffOneVacuumColumnDenominator w
  let vacuumMarginal :=
    centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
      zeroEdgeLabelling
  refine Q'.eqv_trans _
    (Q'.divPos 1 denominator
        (cutoffOneVacuumColumnDenominator_pos hw) *
      (denominator * vacuumMarginal)) _ ?_ ?_
  · exact qmul_congr
      (cutoffOneVacuumColumnPosterior_vacuum_eqv hw)
      (centralPhysicalFiniteVacuumSectorMass_cutoffOne_eqv hw)
  refine Q'.eqv_trans _
    ((Q'.divPos 1 denominator
        (cutoffOneVacuumColumnDenominator_pos hw) * denominator) *
      vacuumMarginal) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ (1 * vacuumMarginal) _
    (Q'.mul_eqv_congr_right _ _ vacuumMarginal
      (Q'.divPos_mul_eqv 1 denominator
        (cutoffOneVacuumColumnDenominator_pos hw)))
    (Q'.one_mul_eqv vacuumMarginal)

private theorem cutoffOneVacuumColumnPosterior_mul_sectorMass_eqv_cubeMarginal
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumColumnPosterior w hw centralLowerCubeState *
        centralPhysicalFiniteVacuumSectorMass
          w (Q'.le_of_lt hw) 1 0 ≈
      centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
        centralLowerCubeState := by
  let denominator := cutoffOneVacuumColumnDenominator w
  let vacuumMarginal :=
    centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
      zeroEdgeLabelling
  let activity := (coeffW w 1) ^ 6
  refine Q'.eqv_trans _
    (Q'.divPos activity denominator
        (cutoffOneVacuumColumnDenominator_pos hw) *
      (denominator * vacuumMarginal)) _ ?_ ?_
  · exact qmul_congr
      (cutoffOneVacuumColumnPosterior_cube_eqv hw)
      (centralPhysicalFiniteVacuumSectorMass_cutoffOne_eqv hw)
  refine Q'.eqv_trans _
    ((Q'.divPos activity denominator
        (cutoffOneVacuumColumnDenominator_pos hw) * denominator) *
      vacuumMarginal) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (activity * vacuumMarginal) _
    (Q'.mul_eqv_congr_right _ _ vacuumMarginal
      (Q'.divPos_mul_eqv activity denominator
        (cutoffOneVacuumColumnDenominator_pos hw))) ?_
  exact Q'.eqv_symm
    (centralPhysicalRowMarginal_cutoffOne_cube_eqv_activity_mul_vacuum hw)

private theorem centralPhysicalRowMarginal_cutoffOne_eqv_posterior_mul_sectorMass
    {w : Q'} (hw : (0 : Q') < w) {state : EdgeLabelling}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0 state ≈
      cutoffOneVacuumColumnPosterior w hw state *
        centralPhysicalFiniteVacuumSectorMass
          w (Q'.le_of_lt hw) 1 0 := by
  have hblock :=
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff
      hw state).mp hstate
  simp only [cutoffOneVacuumCubePhysicalSources,
    List.mem_cons, List.not_mem_nil, or_false] at hblock
  rcases hblock with hstateVacuum | hstateCube
  · subst state
    exact Q'.eqv_symm
      (cutoffOneVacuumColumnPosterior_mul_sectorMass_eqv_vacuumMarginal hw)
  · subst state
    exact Q'.eqv_symm
      (cutoffOneVacuumColumnPosterior_mul_sectorMass_eqv_cubeMarginal hw)

theorem centralPhysicalFiniteVacuumSectorMassNormalizedWeight_cutoffOne_eqv_posterior
    {w : Q'} (hw : (0 : Q') < w) {index : Nat}
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w (Q'.le_of_lt hw) 1 0 index ≈
      cutoffOneVacuumColumnPosterior w hw
        (centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw) 1 0 index) := by
  have hstateSector :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) 1 0 index ∈
      centralPhysicalFiniteVacuumSectorStates
        w (Q'.le_of_lt hw) 1 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w (Q'.le_of_lt hw) 1 0 hindex rfl
  apply Q'.mul_left_cancel_of_pos
    (centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) 1 0)
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w (Q'.le_of_lt hw) 1 0 index *
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) 1 0) _
    (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _
    (centralPhysicalFiniteWeight
      w (Q'.le_of_lt hw) 1 0 index) _
    (finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
      (centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) 1 0)
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w (Q'.le_of_lt hw) 1 0)
      (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) 1 0)
      index) ?_
  refine Q'.eqv_trans _
    (centralPhysicalRowMarginal w (Q'.le_of_lt hw) 1 0
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) 1 0 index)) _
    (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _
    (cutoffOneVacuumColumnPosterior w hw
        (centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw) 1 0 index) *
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) 1 0) _
    (centralPhysicalRowMarginal_cutoffOne_eqv_posterior_mul_sectorMass
      hw hstateSector) (Q'.mul_comm_eqv _ _)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior.centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior.centralPhysicalRowMarginal_cutoffOne_cube_eqv_activity_mul_vacuum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior.centralPhysicalFiniteVacuumSectorMass_cutoffOne_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior.centralPhysicalFiniteVacuumSectorMassNormalizedWeight_cutoffOne_eqv_posterior
