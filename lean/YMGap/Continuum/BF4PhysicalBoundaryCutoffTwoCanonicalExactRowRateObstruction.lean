/-
# The named cutoff-two exact row rate is not subunit

The normalized 65-state row-ten obstruction is transported through the exact
permutation between the stored table and the canonical vacuum-sector index
list.  After clearing the positive canonical component mass, the violating
row contradicts any hypothetical bound `h_2 <= 1` for the named exact
mass-normalized row maximum.

This is a finite diagnostic theorem.  It eliminates row total variation as a
uniform-gap mechanism already at cutoff two, but it does not contradict the
proved cancellation-preserving `49/50` signed-form gap and does not establish
a cofinal, thermodynamic, continuum, or Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
import YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add]; ac_rfl))

private theorem listQSum_perm_local {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ permutation =>
      Q'.add_eqv_congr_left _ _ _
        (listQSum_perm_local value permutation)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      exact Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
        (Q'.eqv_trans _
          ((value first + value second) + listQSum value rest) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
          (Q'.add_assoc_eqv _ _ _))
  | _, _, List.Perm.trans first second =>
      Q'.eqv_trans _ _ _
        (listQSum_perm_local value first)
        (listQSum_perm_local value second)

private theorem mul_eqv_congr_local {a b c d : Q'}
    (hac : a ≈ c) (hbd : b ≈ d) : a * b ≈ c * d :=
  Q'.eqv_trans _ (c * b) _
    (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

/-! ## 1. The table row has a canonical vacuum-sector source index -/

theorem exists_cutoffTwoCanonicalVacuumSectorIndex_rowTen :
    ∃ source,
      source ∈ centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0 ∧
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) 2 0 source = cutoffTwoSectorStateAt 10 := by
  have htable : cutoffTwoSectorStateAt 10 ∈ cutoffTwoCubeSectorStates :=
    cutoffTwoSectorStateAt_mem (by decide)
  have hcanonical : cutoffTwoSectorStateAt 10 ∈
      centralPhysicalFiniteVacuumSectorStates
        cutoffTwoHalfCoupling (by decide) 2 0 :=
    (List.Perm.mem_iff cutoffTwoCanonicalVacuumSectorStates_perm).2 htable
  unfold centralPhysicalFiniteVacuumSectorStates at hcanonical
  exact List.mem_map.mp hcanonical

/-! ## 2. The table mass is the canonical component mass -/

theorem cutoffTwoSectorNormalizedMass_eqv_canonicalVacuumSectorMass :
    cutoffTwoSectorNormalizedMass ≈
      centralPhysicalFiniteVacuumSectorMass
        cutoffTwoHalfCoupling (by decide) 2 0 := by
  let observable := fun _state : EdgeLabelling => (1 : Q')
  have hmean :=
    cutoffTwoSectorObservableWeightedMean_eqv_canonical observable
  refine Q'.eqv_trans _
    (finiteWeightedMean 65 cutoffTwoSectorCanonicalPhysicalWeight
      (cutoffTwoSectorObservableCoefficient observable)) _ ?_ ?_
  · unfold cutoffTwoSectorNormalizedMass finiteWeightedMean
      cutoffTwoSectorCanonicalPhysicalWeight
      cutoffTwoSectorObservableCoefficient observable
    apply listQSum_congr_on
    intro row _
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · refine Q'.eqv_trans _
      (centralPhysicalFiniteVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 0
        (cutoffTwoCanonicalVacuumObservableCoefficient observable)) _
      hmean ?_
    unfold centralPhysicalFiniteVacuumSectorWeightedMean
      cutoffTwoCanonicalVacuumObservableCoefficient observable
      centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
    apply listQSum_congr
    intro source
    exact Q'.one_mul_eqv _

/-! ## 3. The cleared row sum is coordinate invariant -/

private def cutoffTwoCanonicalClearedStateValue
    (source target : EdgeLabelling) : Q' :=
  Q'.abs
    (centralPhysicalFiniteVacuumSectorMass
          cutoffTwoHalfCoupling (by decide) 2 0 *
        centralNormalizedPhysicalReflectedKernel
          cutoffTwoHalfCoupling (by decide) 2 0 source target +
      (-(centralPhysicalRowMarginal
            cutoffTwoHalfCoupling (by decide) 2 0 source *
          centralPhysicalRowMarginal
            cutoffTwoHalfCoupling (by decide) 2 0 target)))

private theorem listQSum_eqv_indexed_of_length
    {State : Type} (states : List State) (fallback : State)
    (value : State → Q') (indexedValue : Nat → Q')
    (hlength : states.length = 65)
    (hvalue : ∀ index, index < 65 →
      value (finiteListStateAt states fallback index) ≈
        indexedValue index) :
    listQSum value states ≈
      listQSum indexedValue (List.range 65) := by
  have hindexed := Q'.eqv_symm
    (Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum states fallback value))
  rw [hlength] at hindexed
  exact Q'.eqv_trans _ _ _ hindexed
    (listQSum_congr_on
      (fun index => value (finiteListStateAt states fallback index))
      indexedValue (List.range 65)
      (fun index hindex => hvalue index (List.mem_range.mp hindex)))

private theorem clearedEntry_eqv_of_components
    (canonicalMass actualKernel sourceMarginal targetMarginal : Q')
    (normalizedMass normalizedKernel normalizedSource normalizedTarget : Q')
    (hmass : canonicalMass ≈ normalizedMass)
    (hkernel : actualKernel ≈ normalizedKernel)
    (hsource : sourceMarginal ≈ normalizedSource)
    (htarget : targetMarginal ≈ normalizedTarget) :
    Q'.abs
        (canonicalMass * actualKernel +
          (-(sourceMarginal * targetMarginal))) ≈
      Q'.abs
        (normalizedMass * normalizedKernel +
          (-(normalizedSource * normalizedTarget))) := by
  apply Q'.abs_eqv_congr
  apply Q'.add_eqv_congr'
  · exact mul_eqv_congr_local hmass hkernel
  · exact Q'.neg_eqv_congr _ _
      (mul_eqv_congr_local hsource htarget)

theorem cutoffTwoCanonicalClearedStateValue_rowTen_eqv_normalizedEntry
    (column : Nat) (hcolumnLt : column < 65) :
    cutoffTwoCanonicalClearedStateValue
        (cutoffTwoSectorStateAt 10) (cutoffTwoSectorStateAt column) ≈
      Q'.abs
        (cutoffTwoSectorNormalizedMass *
            cutoffTwoSectorNormalizedKernel 10 column +
          (-(cutoffTwoSectorNormalizedRowSum 10 *
            cutoffTwoSectorNormalizedRowSum column))) := by
  unfold cutoffTwoCanonicalClearedStateValue
  exact clearedEntry_eqv_of_components _ _ _ _ _ _ _ _
    (Q'.eqv_symm
      cutoffTwoSectorNormalizedMass_eqv_canonicalVacuumSectorMass)
    (Q'.eqv_symm cutoffTwoSectorNormalizedKernel_eqv_actual)
    (Q'.eqv_symm
      (cutoffTwoSectorNormalizedRowSum_eqv_centralPhysicalRowMarginal
        (by decide : 10 < 65)))
    (Q'.eqv_symm
      (cutoffTwoSectorNormalizedRowSum_eqv_centralPhysicalRowMarginal
        hcolumnLt))

structure CutoffTwoCanonicalRowTenClearedValueCertificate where
  value : EdgeLabelling → Q'
  value_eqv_actual : ∀ target,
    value target ≈
      cutoffTwoCanonicalClearedStateValue
        (cutoffTwoSectorStateAt 10) target
  value_eqv_normalizedEntry : ∀ column,
    column < 65 →
    value (cutoffTwoSectorStateAt column) ≈
      Q'.abs
        (cutoffTwoSectorNormalizedMass *
            cutoffTwoSectorNormalizedKernel 10 column +
          (-(cutoffTwoSectorNormalizedRowSum 10 *
            cutoffTwoSectorNormalizedRowSum column)))

opaque cutoffTwoCanonicalRowTenClearedValueCertificate :
    CutoffTwoCanonicalRowTenClearedValueCertificate := {
  value := cutoffTwoCanonicalClearedStateValue (cutoffTwoSectorStateAt 10)
  value_eqv_actual := fun target => Q'.eqv_refl
    (cutoffTwoCanonicalClearedStateValue (cutoffTwoSectorStateAt 10) target)
  value_eqv_normalizedEntry :=
    cutoffTwoCanonicalClearedStateValue_rowTen_eqv_normalizedEntry
}

def cutoffTwoCanonicalRowTenClearedStateValue : EdgeLabelling → Q' :=
  cutoffTwoCanonicalRowTenClearedValueCertificate.value

theorem cutoffTwoCanonicalRowTenClearedStateValue_eqv_actual
    (target : EdgeLabelling) :
    cutoffTwoCanonicalRowTenClearedStateValue target ≈
      cutoffTwoCanonicalClearedStateValue
        (cutoffTwoSectorStateAt 10) target :=
  cutoffTwoCanonicalRowTenClearedValueCertificate.value_eqv_actual target

theorem cutoffTwoCanonicalRowTenClearedStateValue_eqv_normalizedEntry
    (column : Nat) (hcolumnLt : column < 65) :
    cutoffTwoCanonicalRowTenClearedStateValue
        (cutoffTwoSectorStateAt column) ≈
      Q'.abs
        (cutoffTwoSectorNormalizedMass *
            cutoffTwoSectorNormalizedKernel 10 column +
          (-(cutoffTwoSectorNormalizedRowSum 10 *
            cutoffTwoSectorNormalizedRowSum column))) :=
  cutoffTwoCanonicalRowTenClearedValueCertificate.value_eqv_normalizedEntry
    column hcolumnLt

def cutoffTwoCanonicalVacuumSectorClearedMassNormalizedRowTenDistance : Q' :=
  listQSum cutoffTwoCanonicalRowTenClearedStateValue
    (centralPhysicalFiniteVacuumSectorStates
      cutoffTwoHalfCoupling (by decide) 2 0)

theorem cutoffTwoCanonicalClearedRowTen_eqv_tableStateSum :
    cutoffTwoCanonicalVacuumSectorClearedMassNormalizedRowTenDistance ≈
      listQSum cutoffTwoCanonicalRowTenClearedStateValue
        cutoffTwoCubeSectorStates := by
  unfold cutoffTwoCanonicalVacuumSectorClearedMassNormalizedRowTenDistance
  exact listQSum_perm_local _ cutoffTwoCanonicalVacuumSectorStates_perm

theorem cutoffTwoCanonicalClearedTableStateSum_eqv_normalizedRowTen :
    listQSum cutoffTwoCanonicalRowTenClearedStateValue
        cutoffTwoCubeSectorStates ≈
      cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
        cutoffTwoSectorNormalizedMass 10 := by
  unfold cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
  apply listQSum_eqv_indexed_of_length
    cutoffTwoCubeSectorStates zeroEdgeLabelling
  · exact cutoffTwoCubeSectorStates_length
  · intro column hcolumnLt
    change cutoffTwoCanonicalRowTenClearedStateValue
        (cutoffTwoSectorStateAt column) ≈
      Q'.abs
        (cutoffTwoSectorNormalizedMass *
            cutoffTwoSectorNormalizedKernel 10 column +
          (-(cutoffTwoSectorNormalizedRowSum 10 *
            cutoffTwoSectorNormalizedRowSum column)))
    exact
      cutoffTwoCanonicalRowTenClearedStateValue_eqv_normalizedEntry
        column hcolumnLt

theorem cutoffTwoCanonicalClearedRowTen_eqv_normalizedRowTen :
    cutoffTwoCanonicalVacuumSectorClearedMassNormalizedRowTenDistance ≈
      cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
        cutoffTwoSectorNormalizedMass 10 := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoCanonicalClearedRowTen_eqv_tableStateSum
    cutoffTwoCanonicalClearedTableStateSum_eqv_normalizedRowTen

/-! ## 4. Clearing the canonical reciprocal component mass -/

private theorem mass_mul_rowDistance_eqv_cleared_generic
    {State : Type} (states : List State)
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (joint : State → State → Q') (weight : State → Q')
    (source : State) :
    mass *
        finiteJointDifferenceAbsRowMass states joint
          (finiteCarrierMassNormalizedStationaryProductJoint
            mass mass_pos weight) source ≈
      listQSum
        (fun target =>
          Q'.abs
            (mass * joint source target +
              (-(weight source * weight target))))
        states := by
  let rightJoint :=
    finiteCarrierMassNormalizedStationaryProductJoint
      mass mass_pos weight
  let difference := fun target =>
    joint source target + (-rightJoint source target)
  refine Q'.eqv_trans _
    (listQSum (fun target => mass * Q'.abs (difference target)) states) _
    (Q'.eqv_symm
      (listQSum_mul_left mass (fun target => Q'.abs (difference target))
        states)) ?_
  apply listQSum_congr
  intro target
  refine Q'.eqv_trans _
    (Q'.abs (difference target) * mass) _
    (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _
    (Q'.abs (difference target * mass)) _
    (Q'.eqv_symm
      (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        (difference target) (Q'.le_of_lt mass_pos))) ?_
  apply Q'.abs_eqv_congr
  unfold difference rightJoint
    finiteCarrierMassNormalizedStationaryProductJoint
    finiteStationaryProductJoint
  refine Q'.eqv_trans _
    (mass * joint source target +
      (-((weight source * weight target) *
        (mass * Q'.recipPos mass mass_pos)))) _ ?_ ?_
  · ring_qeqv
  · apply Q'.add_eqv_congr'
    · exact Q'.eqv_refl _
    · apply Q'.neg_eqv_congr
      refine Q'.eqv_trans _
        ((weight source * weight target) * 1) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_recipPos_eqv mass mass_pos)
      · exact Q'.mul_one_eqv _

theorem cutoffTwoCanonicalIndexClearedEntry_eqv_rowTenStateValue
    {source : Nat}
    (hstate : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 source = cutoffTwoSectorStateAt 10)
    (target : Nat) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMass
              cutoffTwoHalfCoupling (by decide) 2 0 *
            centralPhysicalFiniteKernel
              cutoffTwoHalfCoupling (by decide) 2 0 source target +
          (-(centralPhysicalFiniteWeight
                cutoffTwoHalfCoupling (by decide) 2 0 source *
              centralPhysicalFiniteWeight
                cutoffTwoHalfCoupling (by decide) 2 0 target))) ≈
      cutoffTwoCanonicalRowTenClearedStateValue
        (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) 2 0 target) := by
  unfold centralPhysicalFiniteKernel centralPhysicalFiniteWeight
  rw [hstate]
  exact Q'.eqv_symm
    (cutoffTwoCanonicalRowTenClearedStateValue_eqv_actual
      (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) 2 0 target))

private theorem listQSum_index_eqv_mapped_of_pointwise
    {Index State : Type} (indices : List Index) (map : Index → State)
    (indexValue : Index → Q') (stateValue : State → Q')
    (hvalue : ∀ index, index ∈ indices →
      indexValue index ≈ stateValue (map index)) :
    listQSum indexValue indices ≈
      listQSum stateValue (indices.map map) := by
  refine Q'.eqv_trans _
    (listQSum (fun index => stateValue (map index)) indices) _ ?_ ?_
  · exact listQSum_congr_on indexValue
      (fun index => stateValue (map index)) indices hvalue
  · exact Q'.eqv_of_eq (Eq.symm (listQSum_map stateValue map indices))

private theorem mass_mul_rowDistance_eqv_mappedCleared_generic
    {Index State : Type} (indices : List Index) (map : Index → State)
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (joint : Index → Index → Q') (weight : Index → Q')
    (source : Index) (stateValue : State → Q')
    (hvalue : ∀ target, target ∈ indices →
      Q'.abs
          (mass * joint source target +
            (-(weight source * weight target))) ≈
        stateValue (map target)) :
    mass *
        finiteJointDifferenceAbsRowMass indices joint
          (finiteCarrierMassNormalizedStationaryProductJoint
            mass mass_pos weight) source ≈
      listQSum stateValue (indices.map map) := by
  exact Q'.eqv_trans _ _ _
    (mass_mul_rowDistance_eqv_cleared_generic
      indices mass mass_pos joint weight source)
    (listQSum_index_eqv_mapped_of_pointwise
      indices map
      (fun target =>
        Q'.abs
          (mass * joint source target +
            (-(weight source * weight target))))
      stateValue hvalue)

theorem cutoffTwoCanonicalMass_mul_rowDistance_eqv_rowTenCleared
    {source : Nat}
    (hstate : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 source = cutoffTwoSectorStateAt 10) :
    centralPhysicalFiniteVacuumSectorMass
          cutoffTwoHalfCoupling (by decide) 2 0 *
        centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
          cutoffTwoHalfCoupling (by decide) 2 0 source ≈
      cutoffTwoCanonicalVacuumSectorClearedMassNormalizedRowTenDistance := by
  unfold centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
    cutoffTwoCanonicalVacuumSectorClearedMassNormalizedRowTenDistance
    centralPhysicalFiniteVacuumSectorStates
  apply mass_mul_rowDistance_eqv_mappedCleared_generic
  intro target _htarget
  exact cutoffTwoCanonicalIndexClearedEntry_eqv_rowTenStateValue
    hstate target

/-! ## 5. The named exact cutoff-two rate is superunit -/

theorem cutoffTwoCanonicalVacuumSector_productRowObstruction_of_state
    {source : Nat}
    (hstate : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 source = cutoffTwoSectorStateAt 10) :
    centralPhysicalFiniteVacuumSectorMass
          cutoffTwoHalfCoupling (by decide) 2 0 *
        centralPhysicalFiniteWeight
          cutoffTwoHalfCoupling (by decide) 2 0 source <
      centralPhysicalFiniteVacuumSectorMass
            cutoffTwoHalfCoupling (by decide) 2 0 *
        centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
          cutoffTwoHalfCoupling (by decide) 2 0 source := by
  have hweight :
      centralPhysicalFiniteWeight
          cutoffTwoHalfCoupling (by decide) 2 0 source ≈
        cutoffTwoSectorNormalizedRowSum 10 := by
    unfold centralPhysicalFiniteWeight
    rw [hstate]
    exact Q'.eqv_symm
      (cutoffTwoSectorNormalizedRowSum_eqv_centralPhysicalRowMarginal
        (by decide : 10 < 65))
  have hleft :
      centralPhysicalFiniteVacuumSectorMass
            cutoffTwoHalfCoupling (by decide) 2 0 *
          centralPhysicalFiniteWeight
            cutoffTwoHalfCoupling (by decide) 2 0 source ≈
        cutoffTwoSectorNormalizedMass *
          cutoffTwoSectorNormalizedRowSum 10 :=
    mul_eqv_congr_local
      (Q'.eqv_symm
        cutoffTwoSectorNormalizedMass_eqv_canonicalVacuumSectorMass)
      hweight
  have hright :
      centralPhysicalFiniteVacuumSectorMass
            cutoffTwoHalfCoupling (by decide) 2 0 *
          centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
            cutoffTwoHalfCoupling (by decide) 2 0 source ≈
        cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
          cutoffTwoSectorNormalizedMass 10 :=
    Q'.eqv_trans _ _ _
      (cutoffTwoCanonicalMass_mul_rowDistance_eqv_rowTenCleared hstate)
      cutoffTwoCanonicalClearedRowTen_eqv_normalizedRowTen
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft)
      cutoffTwoSectorNormalizedClearedRowTen_gt_mass_mul_rowSum)
    (Q'.ge_of_eqv hright)

theorem exists_cutoffTwoCanonicalVacuumSector_productRowObstruction :
    ∃ source,
      source ∈ centralPhysicalFiniteVacuumSectorIndices
          cutoffTwoHalfCoupling (by decide) 2 0 ∧
      centralPhysicalFiniteVacuumSectorMass
            cutoffTwoHalfCoupling (by decide) 2 0 *
          centralPhysicalFiniteWeight
            cutoffTwoHalfCoupling (by decide) 2 0 source <
        centralPhysicalFiniteVacuumSectorMass
              cutoffTwoHalfCoupling (by decide) 2 0 *
          centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
            cutoffTwoHalfCoupling (by decide) 2 0 source := by
  obtain ⟨source, hsource, hstate⟩ :=
    exists_cutoffTwoCanonicalVacuumSectorIndex_rowTen
  exact ⟨source, hsource,
    cutoffTwoCanonicalVacuumSector_productRowObstruction_of_state hstate⟩

private theorem exactRate_not_le_one_of_productRowObstruction
    (mass weight rowDistance rate : Q')
    (hmassPos : (0 : Q') < mass)
    (hweightPos : (0 : Q') < weight)
    (hrow : rowDistance ≤ rate * weight)
    (hstrict : mass * weight < mass * rowDistance) :
    ¬ rate ≤ (1 : Q') := by
  intro hrate
  have hrateWeight : rate * weight ≤ (1 : Q') * weight :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hrate (Q'.le_of_lt hweightPos)
  have hrowWeight : rowDistance ≤ weight :=
    Q'.le_trans' _ _ _ hrow
      (Q'.le_trans' _ _ _ hrateWeight
        (Q'.le_of_eqv (Q'.one_mul_eqv weight)))
  have hscaled : mass * rowDistance ≤ mass * weight :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrowWeight
      (Q'.le_of_lt hmassPos)
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' (mass * weight)
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hstrict hscaled)

structure CutoffTwoCanonicalExactRowRateSeal where
  rate : Q'
  rate_eqv_exact : rate ≈
    centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
      cutoffTwoHalfCoupling (by decide) 2 0
  row_bound : ∀ source,
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0) →
    centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
        cutoffTwoHalfCoupling (by decide) 2 0 source ≤
      rate * centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) 2 0 source

opaque cutoffTwoCanonicalExactRowRateSeal :
    CutoffTwoCanonicalExactRowRateSeal := {
  rate := centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
    cutoffTwoHalfCoupling (by decide) 2 0
  rate_eqv_exact := Q'.eqv_refl _
  row_bound := fun _source hsource =>
    centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_le_exactRate_mul_weight
      hsource
}

private theorem exactRate_not_le_one_of_existsProductRowObstruction
    (mass rate : Q')
    (weight rowDistance : Nat → Q')
    (isSource : Nat → Prop)
    (hmassPos : (0 : Q') < mass)
    (hweightPos : ∀ source, isSource source → (0 : Q') < weight source)
    (hrow : ∀ source, isSource source →
      rowDistance source ≤ rate * weight source)
    (hexists : ∃ source, isSource source ∧
      mass * weight source < mass * rowDistance source) :
    ¬ rate ≤ (1 : Q') := by
  intro hrate
  obtain ⟨source, hsource, hstrict⟩ := hexists
  exact (exactRate_not_le_one_of_productRowObstruction
    mass (weight source) (rowDistance source) rate hmassPos
    (hweightPos source hsource) (hrow source hsource) hstrict) hrate

theorem cutoffTwoCanonicalVacuumSectorMass_pos :
    (0 : Q') < centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) 2 0 :=
  Q'.pos_of_lt_of_le cutoffTwoSectorNormalizedMass_pos
    (Q'.le_of_eqv
      cutoffTwoSectorNormalizedMass_eqv_canonicalVacuumSectorMass)

theorem cutoffTwoCanonicalVacuumSectorWeight_pos
    {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0) :
    (0 : Q') < centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) 2 0 source :=
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity.centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
    hsource

theorem cutoffTwoCanonicalSealedRate_row_bound
    {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0) :
    centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
        cutoffTwoHalfCoupling (by decide) 2 0 source ≤
      cutoffTwoCanonicalExactRowRateSeal.rate *
        centralPhysicalFiniteWeight
          cutoffTwoHalfCoupling (by decide) 2 0 source :=
  cutoffTwoCanonicalExactRowRateSeal.row_bound source hsource

theorem cutoffTwoCanonicalExactMassNormalizedRowRate_not_le_one :
    ¬ centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        cutoffTwoHalfCoupling (by decide) 2 0 ≤ (1 : Q') := by
  have hsealed : ¬ cutoffTwoCanonicalExactRowRateSeal.rate ≤ (1 : Q') := by
    apply exactRate_not_le_one_of_existsProductRowObstruction
      (centralPhysicalFiniteVacuumSectorMass
        cutoffTwoHalfCoupling (by decide) 2 0)
      cutoffTwoCanonicalExactRowRateSeal.rate
      (centralPhysicalFiniteWeight cutoffTwoHalfCoupling (by decide) 2 0)
      (centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance
        cutoffTwoHalfCoupling (by decide) 2 0)
      (fun source => source ∈ centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0)
    · exact cutoffTwoCanonicalVacuumSectorMass_pos
    · intro source hsource
      exact cutoffTwoCanonicalVacuumSectorWeight_pos hsource
    · intro source hsource
      exact cutoffTwoCanonicalSealedRate_row_bound hsource
    · exact exists_cutoffTwoCanonicalVacuumSector_productRowObstruction
  intro hrate
  apply hsealed
  exact
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv cutoffTwoCanonicalExactRowRateSeal.rate_eqv_exact)
      hrate

theorem cutoffTwoCanonicalExactMassNormalizedRowRate_one_lt :
    (1 : Q') <
      centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate
        cutoffTwoHalfCoupling (by decide) 2 0 :=
  YMGap.Continuum.TsumDeriv.Q'.lt_of_not_le
    cutoffTwoCanonicalExactMassNormalizedRowRate_not_le_one

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction.cutoffTwoSectorNormalizedMass_eqv_canonicalVacuumSectorMass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction.cutoffTwoCanonicalClearedRowTen_eqv_normalizedRowTen
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction.cutoffTwoCanonicalMass_mul_rowDistance_eqv_rowTenCleared
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction.cutoffTwoCanonicalExactMassNormalizedRowRate_not_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction.cutoffTwoCanonicalExactMassNormalizedRowRate_one_lt
