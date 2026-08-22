/-
# Normalization bounds for every fixed pulled BF4 vacuum carrier

The stationary mass retained on any fixed base vacuum component is positive
at every later cutoff and is at most one once the canonical cutoff embedding
is valid.  The root gives positivity.  Injecting the fixed component into the
complete later positive-row carrier and using exact stationary normalization
gives the upper bound.

These estimates are uniform in the later cutoff for each selected base; no
lower mass bound uniform in the base component is claimed or needed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMass

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Total later stationary mass retained on one fixed base component. -/
def fixedBasePulledMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  finiteWeightedMass
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (centralPhysicalFinitePulledWeight w hw base later half)

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

theorem fixedBasePulledMass_pos
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (0 : Q') < fixedBasePulledMass w hw base later half := by
  have hrootMem : 0 ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half :=
    zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw base half
  have hrootPos : (0 : Q') <
      centralPhysicalFinitePulledWeight w hw base later half 0 :=
    centralPhysicalFinitePulledWeight_zero_pos
      w hw base later half
  have hrootLe :
      centralPhysicalFinitePulledWeight w hw base later half 0 ≤
        fixedBasePulledMass w hw base later half := by
    unfold fixedBasePulledMass finiteWeightedMass
    exact listQSum_member_le_nonnegative_local
      (centralPhysicalFinitePulledWeight w hw base later half)
      (fun index =>
        centralPhysicalFinitePulledWeight_nonnegative
          w hw base later half index)
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)
      hrootMem
  exact Q'.pos_of_lt_of_le hrootPos hrootLe

private theorem laterFullFiniteWeightSum_eqv_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (later half : Nat) :
    listQSum
        (centralPhysicalFiniteWeight w hw later half)
        (List.range
          (centralPhysicalFiniteCarrierSize w hw later half)) ≈
      1 := by
  let weight := centralPhysicalFiniteWeight w hw later half
  let coefficient := centralPhysicalFiniteCoefficient
    w hw later half (fun _ => 1)
  have hmassMean :
      listQSum weight
          (List.range
            (centralPhysicalFiniteCarrierSize w hw later half)) ≈
        finiteWeightedMean
          (centralPhysicalFiniteCarrierSize w hw later half)
          weight coefficient := by
    unfold finiteWeightedMean
    apply listQSum_congr
    intro index
    unfold coefficient centralPhysicalFiniteCoefficient
    exact Q'.eqv_symm (Q'.one_mul_eqv (weight index))
  exact Q'.eqv_trans _ _ _ hmassMean
    (Q'.eqv_trans _ _ _
      (centralPhysicalFiniteWeightedMean_eqv_stationaryMean
        w hw later half (fun _ => 1))
      (centralPhysicalStationaryMean_one w hw later half))

theorem fixedBasePulledMass_le_one
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hlater : base ≤ later) :
    fixedBasePulledMass w hw base later half ≤ 1 := by
  let source := centralPhysicalFiniteVacuumSectorIndices
    w hw base half
  let target := List.range
    (centralPhysicalFiniteCarrierSize w hw later half)
  let indexMap := centralPhysicalFiniteCutoffIndexMap
    w hw base later half
  let sourceWeight := centralPhysicalFinitePulledWeight
    w hw base later half
  let targetWeight := centralPhysicalFiniteWeight w hw later half
  have hsubsum : listQSum sourceWeight source ≤
      listQSum targetWeight target := by
    apply listQSum_le_of_injective
      source target sourceWeight targetWeight indexMap
    · exact centralPhysicalFiniteVacuumSectorIndices_nodup
        w hw base half
    · intro index hindex
      exact List.mem_range.mpr
        (centralPhysicalFiniteCutoffIndexMap_lt hlater
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw base half hindex))
    · intro left hleft right hright heq
      exact centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
        hlater hleft hright heq
    · intro index _hindex
      exact Q'.le_refl' _
    · intro index _hindex
      unfold targetWeight centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative hw later half _
  unfold fixedBasePulledMass finiteWeightedMass
  exact Q'.le_trans' _ _ _ hsubsum
    (Q'.le_of_eqv
      (laterFullFiniteWeightSum_eqv_one w hw later half))

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMass

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMass.fixedBasePulledMass_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMass.fixedBasePulledMass_le_one
