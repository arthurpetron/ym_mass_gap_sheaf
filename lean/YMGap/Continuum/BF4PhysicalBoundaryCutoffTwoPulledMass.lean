/-
# Uniform normalization bounds for the fixed pulled BF4 carrier

The stationary mass retained on the fixed cutoff-two vacuum component is
strictly positive at every later cutoff and never exceeds one.  Positivity is
witnessed by the pulled vacuum root.  The upper bound maps the fixed component
injectively into the complete later positive-row carrier and uses exact
normalization of the physical stationary law.

These bounds remove the pulled mass as an additional quantitative hypothesis
from the fixed-carrier Poincare argument.  No positive edge floor or strict
form rate is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledDirichletEmbedding
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Total pulled stationary mass on the fixed cutoff-two vacuum component. -/
def cutoffTwoPulledMassAt (later : Nat) : Q' :=
  finiteWeightedMass cutoffTwoPulledStates (cutoffTwoPulledWeightAt later)

private theorem listQSum_member_le_nonnegative_local
    {State : Type} (value : State → Q')
    (hnonnegative : ∀ state, (0 : Q') ≤ value state) :
    ∀ (states : List State) {state : State},
      state ∈ states → value state ≤ listQSum value states
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, state, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst state
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item _ => hnonnegative item))
      · have ih := listQSum_member_le_nonnegative_local
          value hnonnegative tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          exact Q'.le_trans' _ (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head) (hnonnegative head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

/-- The pulled mass stays positive because its fixed carrier contains the
vacuum root and the later pulled root weight is strictly positive. -/
theorem cutoffTwoPulledMassAt_pos (later : Nat) :
    (0 : Q') < cutoffTwoPulledMassAt later := by
  have hrootMem : 0 ∈ cutoffTwoPulledStates := by
    unfold cutoffTwoPulledStates
    exact zero_mem_centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0
  have hrootPos : (0 : Q') < cutoffTwoPulledWeightAt later 0 := by
    unfold cutoffTwoPulledWeightAt
    exact centralPhysicalFinitePulledWeight_zero_pos
      cutoffTwoHalfCoupling (by decide) 2 later 0
  have hrootLe : cutoffTwoPulledWeightAt later 0 ≤
      cutoffTwoPulledMassAt later := by
    unfold cutoffTwoPulledMassAt finiteWeightedMass
    exact listQSum_member_le_nonnegative_local
      (cutoffTwoPulledWeightAt later)
      (fun index => by
        unfold cutoffTwoPulledWeightAt
        exact centralPhysicalFinitePulledWeight_nonnegative
          cutoffTwoHalfCoupling (by decide) 2 later 0 index)
      cutoffTwoPulledStates hrootMem
  exact Q'.pos_of_lt_of_le hrootPos hrootLe

private theorem laterFullFiniteWeightSum_eqv_one
    (later : Nat) :
    listQSum
        (centralPhysicalFiniteWeight
          cutoffTwoHalfCoupling (by decide) later 0)
        (List.range
          (centralPhysicalFiniteCarrierSize
            cutoffTwoHalfCoupling (by decide) later 0)) ≈
      1 := by
  let weight := centralPhysicalFiniteWeight
    cutoffTwoHalfCoupling (by decide) later 0
  let coefficient := centralPhysicalFiniteCoefficient
    cutoffTwoHalfCoupling (by decide) later 0 (fun _ => 1)
  have hmassMean :
      listQSum weight
          (List.range
            (centralPhysicalFiniteCarrierSize
              cutoffTwoHalfCoupling (by decide) later 0)) ≈
        finiteWeightedMean
          (centralPhysicalFiniteCarrierSize
            cutoffTwoHalfCoupling (by decide) later 0)
          weight coefficient := by
    unfold finiteWeightedMean
    apply listQSum_congr
    intro index
    unfold coefficient centralPhysicalFiniteCoefficient
    exact Q'.eqv_symm (Q'.one_mul_eqv (weight index))
  exact Q'.eqv_trans _ _ _ hmassMean
    (Q'.eqv_trans _ _ _
      (centralPhysicalFiniteWeightedMean_eqv_stationaryMean
        cutoffTwoHalfCoupling (by decide) later 0 (fun _ => 1))
      (centralPhysicalStationaryMean_one
        cutoffTwoHalfCoupling (by decide) later 0))

/-- At every later cutoff, the fixed pulled component has mass at most the
complete normalized physical carrier and therefore at most one. -/
theorem cutoffTwoPulledMassAt_le_one
    (later : Nat) (hlater : 2 ≤ later) :
    cutoffTwoPulledMassAt later ≤ 1 := by
  let target := List.range
    (centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) later 0)
  let indexMap := centralPhysicalFiniteCutoffIndexMap
    cutoffTwoHalfCoupling (by decide) 2 later 0
  let targetWeight := centralPhysicalFiniteWeight
    cutoffTwoHalfCoupling (by decide) later 0
  have hsubsum :
      listQSum (cutoffTwoPulledWeightAt later) cutoffTwoPulledStates ≤
        listQSum targetWeight target := by
    apply listQSum_le_of_injective
      cutoffTwoPulledStates target
      (cutoffTwoPulledWeightAt later) targetWeight indexMap
    · exact centralPhysicalFiniteVacuumSectorIndices_nodup
        cutoffTwoHalfCoupling (by decide) 2 0
    · intro index hindex
      exact List.mem_range.mpr
        (centralPhysicalFiniteCutoffIndexMap_lt hlater
          (centralPhysicalFiniteVacuumSectorIndex_lt
            cutoffTwoHalfCoupling (by decide) 2 0 hindex))
    · intro left hleft right hright heq
      exact centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
        hlater hleft hright heq
    · intro index _hindex
      exact Q'.le_refl' _
    · intro index _hindex
      unfold targetWeight centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative
        (by decide) later 0 _
  unfold cutoffTwoPulledMassAt finiteWeightedMass
  exact Q'.le_trans' _ _ _ hsubsum
    (Q'.le_of_eqv (laterFullFiniteWeightSum_eqv_one later))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass.cutoffTwoPulledMassAt_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass.cutoffTwoPulledMassAt_le_one
