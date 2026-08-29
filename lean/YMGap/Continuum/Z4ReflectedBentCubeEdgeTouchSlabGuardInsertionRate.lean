/-
# A positive capped rate for the reflected guarded insertion

The cleared-support identity isolates the exact heat cost of inserting the
reflected bent pattern.  At positive coupling and at its proved cutoff-one,
extent-five geometry, that isolated face factor is strictly positive.  Capping
it at one produces the explicit repair rate required by the finite receiver
interface:

  0 < kappa <= 1,
  kappa * peeled-terminal weight <= guarded-source weight.

The definition retains the coupling, cutoff, and extent in the raw face
factor.  Thus this module proves a coupling-visible finite-volume floor, not a
beta-uniform, spacing-uniform, or volume-uniform estimate.

Constructive contract: decidable rational order, exact finite-product
positivity, and the preceding receiver-weight identity only; no `Classical`,
choice, `native_decide`, `sorry`, new axiom, noncomputable declaration, or
unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeight
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRate

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionObservableWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Constructive capping at one -/

private theorem qLeTotal (a b : Q') : a <= b \/ b <= a := by
  exact Int.le_total
    (a.num * (b.den : Int))
    (b.num * (a.den : Int))

/-- The semantic minimum of a rational rate and one, written explicitly so
the capping operation remains computational. -/
def capAtOne (rate : Q') : Q' :=
  if rate <= (1 : Q') then rate else 1

theorem capAtOne_pos {rate : Q'} (hpos : (0 : Q') < rate) :
    (0 : Q') < capAtOne rate := by
  unfold capAtOne
  by_cases hle : rate <= (1 : Q')
  · rw [if_pos hle]
    exact hpos
  · rw [if_neg hle]
    decide

theorem capAtOne_le_one (rate : Q') :
    capAtOne rate <= (1 : Q') := by
  unfold capAtOne
  by_cases hle : rate <= (1 : Q')
  · rw [if_pos hle]
    exact hle
  · rw [if_neg hle]
    exact Q'.le_refl' 1

theorem capAtOne_le (rate : Q') : capAtOne rate <= rate := by
  unfold capAtOne
  by_cases hle : rate <= (1 : Q')
  · rw [if_pos hle]
    exact Q'.le_refl' rate
  · rw [if_neg hle]
    exact (qLeTotal rate 1).resolve_left hle

/-! ## 2. The explicit reflected-pattern rate -/

/-- The coupling-visible heat cost of the reflected guarded insertion, capped
at one. -/
def reflectedBentGuardInsertionRate (D : SlabPhysicalData) : Q' :=
  capAtOne
    (slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent reflectedBentSwitchLeftPhysical)

theorem reflectedBentGuardRawInsertionRate_pos
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling) :
    (0 : Q') < slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent reflectedBentSwitchLeftPhysical := by
  apply slabParametricKPhysicalFaceFactor_pos_of_bounded D hcoupling
  simpa only [hcutoff, hextent] using reflectedBentSwitchLeftPhysical_bounded

theorem reflectedBentGuardInsertionRate_pos
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling) :
    (0 : Q') < reflectedBentGuardInsertionRate D :=
  capAtOne_pos
    (reflectedBentGuardRawInsertionRate_pos
      D hcutoff hextent hcoupling)

theorem reflectedBentGuardInsertionRate_le_one (D : SlabPhysicalData) :
    reflectedBentGuardInsertionRate D <= (1 : Q') :=
  capAtOne_le_one _

/-! ## 3. The finite receiver-weight floor -/

/-- **Positive guarded receiver floor.**  At positive coupling, inserting the
reflected pattern into the canonically cleared terminal costs at most the
explicit capped rate. -/
theorem reflectedBentGuardGraftObservableSourcePairWeight_floor
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardInsertionRate D *
        (slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.1 *
          slabExpandedFineEntryWeight D
            (reflectedBentGuardCanonicalPeeling D hextent state).1.2) <=
      slabObservableTwoReplicaPairWeight D
        (reflectedBentGuardGraftObservableSourcePair
          D hcutoff hextent state) := by
  have hterminal :
      (0 : Q') <=
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
  have hcapped := Q'.mul_le_mul_of_nonneg_right _ _ _
    (capAtOne_le
      (slabParametricKPhysicalFaceFactor
        D.coupling D.cutoff D.extent reflectedBentSwitchLeftPhysical))
    hterminal
  exact Q'.le_trans' _ _ _ hcapped
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (reflectedBentGuardGraftObservableSourcePairWeight_eqv
          D hcutoff hextent state)))

/-- The same floor written against the production anchor's accepted-state
weight.  This is the literal cutoff-one, half-two instance consumed by the
current reflected gadget. -/
theorem reflectedBentGuardGraftObservableSourcePairWeight_anchor_floor
    (state : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData 1 2)) :
    reflectedBentGuardInsertionRate (anchorSlabPhysicalData 1 2) *
        slabAcceptedTwoReplicaStateWeight 1 2
          (reflectedBentGuardCanonicalPeeling
            (anchorSlabPhysicalData 1 2) (by decide) state).1 <=
      slabObservableTwoReplicaPairWeight (anchorSlabPhysicalData 1 2)
        (reflectedBentGuardGraftObservableSourcePair
          (anchorSlabPhysicalData 1 2) (by decide) (by decide) state) := by
  unfold slabAcceptedTwoReplicaStateWeight
  exact reflectedBentGuardGraftObservableSourcePairWeight_floor
    (anchorSlabPhysicalData 1 2) (by decide) (by decide) (by decide) state

#print axioms capAtOne_pos
#print axioms capAtOne_le_one
#print axioms capAtOne_le
#print axioms reflectedBentGuardRawInsertionRate_pos
#print axioms reflectedBentGuardInsertionRate_pos
#print axioms reflectedBentGuardInsertionRate_le_one
#print axioms reflectedBentGuardGraftObservableSourcePairWeight_floor
#print axioms reflectedBentGuardGraftObservableSourcePairWeight_anchor_floor

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRate
