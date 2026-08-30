/-
# A cutoff-uniform guarded insertion rate

The inserted reflected pattern uses only labels zero and one.  Hence its
heat-face factor is exactly stable from cutoff one onward: increasing the
packet cutoff changes neither coefficient lookup nor the finite face product.
The capped cutoff-one factor therefore gives one positive receiver rate for
all `K ≥ 1` at extent five.

The rate still depends explicitly on the coupling.  No coupling-, spacing-,
volume-, or posterior-variance uniformity is claimed.

Constructive contract: exact coefficient lookup, finite products, and rational
order only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeightCutoffPersistence
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRate

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRateCutoffUniform

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeightCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRate
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity

/-! ## 1. The fixed binary pattern is exactly cutoff-stable -/

theorem reflectedBentGuardRawInsertionFactor_cutoff_stable
    (coupling : Q') (K : Nat) (hcutoff : 1 ≤ K) :
    slabParametricKPhysicalFaceFactor coupling K 5
        reflectedBentSwitchLeftPhysical =
      slabParametricKPhysicalFaceFactor coupling 1 5
        reflectedBentSwitchLeftPhysical := by
  unfold slabParametricKPhysicalFaceFactor
  apply eliminateLinks_congr_eq
  intro faceId hface
  have hspinOne : reflectedBentSwitchLeftPhysical faceId < 1 + 1 :=
    Nat.lt_succ_of_le
      (reflectedBentSwitchLeftPhysical_bounded faceId hface)
  have hspinK : reflectedBentSwitchLeftPhysical faceId < K + 1 := by
    omega
  rw [coeffAt_heatKernelPacket hspinK,
    coeffAt_heatKernelPacket hspinOne]

/-! ## 2. One coupling-visible rate for every cutoff -/

def reflectedBentGuardCutoffUniformInsertionRate (coupling : Q') : Q' :=
  capAtOne
    (slabParametricKPhysicalFaceFactor coupling 1 5
      reflectedBentSwitchLeftPhysical)

theorem reflectedBentGuardInsertionRate_eq_cutoffUniform
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5) :
    reflectedBentGuardInsertionRate D =
      reflectedBentGuardCutoffUniformInsertionRate D.coupling := by
  unfold reflectedBentGuardInsertionRate
    reflectedBentGuardCutoffUniformInsertionRate
  rw [hextent,
    reflectedBentGuardRawInsertionFactor_cutoff_stable
      D.coupling D.cutoff hcutoff]

theorem reflectedBentGuardCutoffUniformInsertionRate_pos
    (coupling : Q') (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < reflectedBentGuardCutoffUniformInsertionRate coupling := by
  let D : SlabPhysicalData :=
    { coupling := coupling
      coupling_nonnegative := Q'.le_of_lt hcoupling
      cutoff := 1
      half := 2 }
  have hcutoff : D.cutoff = 1 := rfl
  have hextent : D.extent = 5 := rfl
  have hone : 1 ≤ D.cutoff := Nat.le_refl 1
  have hpos := reflectedBentGuardInsertionRate_pos
    D hcutoff hextent hcoupling
  rw [reflectedBentGuardInsertionRate_eq_cutoffUniform
    D hone hextent] at hpos
  exact hpos

theorem reflectedBentGuardCutoffUniformInsertionRate_le_one
    (coupling : Q') :
    reflectedBentGuardCutoffUniformInsertionRate coupling ≤ (1 : Q') :=
  capAtOne_le_one _

/-! ## 3. The cutoff-uniform receiver floor -/

theorem reflectedBentGuardGraftObservableSourcePairAtCutoffWeight_floor
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardCutoffUniformInsertionRate D.coupling *
        (slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.1 *
          slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.2) ≤
      slabObservableTwoReplicaPairWeight D
        (reflectedBentGuardGraftObservableSourcePairAtCutoff
          D hcutoff hextent state) := by
  have hterminal :
      (0 : Q') ≤
        slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.1 *
          slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.2 :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (slabExpandedFineEntryWeight_pos_of_coupling_pos D hcoupling
          (reflectedBentGuardCanonicalPeeling D hextent state).1.1))
      (Q'.le_of_lt
        (slabExpandedFineEntryWeight_pos_of_coupling_pos D hcoupling
          (reflectedBentGuardCanonicalPeeling D hextent state).1.2))
  have hrate : reflectedBentGuardCutoffUniformInsertionRate D.coupling ≤
      slabParametricKPhysicalFaceFactor
        D.coupling D.cutoff D.extent reflectedBentSwitchLeftPhysical := by
    rw [hextent,
      reflectedBentGuardRawInsertionFactor_cutoff_stable
        D.coupling D.cutoff hcutoff]
    exact capAtOne_le _
  have hcapped := Q'.mul_le_mul_of_nonneg_right _ _ _ hrate hterminal
  exact Q'.le_trans' _ _ _ hcapped
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (reflectedBentGuardGraftObservableSourcePairAtCutoffWeight_eqv
          D hcutoff hextent state)))

#print axioms reflectedBentGuardRawInsertionFactor_cutoff_stable
#print axioms reflectedBentGuardInsertionRate_eq_cutoffUniform
#print axioms reflectedBentGuardCutoffUniformInsertionRate_pos
#print axioms reflectedBentGuardCutoffUniformInsertionRate_le_one
#print axioms reflectedBentGuardGraftObservableSourcePairAtCutoffWeight_floor

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRateCutoffUniform
