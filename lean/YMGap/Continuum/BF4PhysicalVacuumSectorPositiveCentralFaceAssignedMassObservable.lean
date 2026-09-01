/-
# The assigned central-face terminal mass as a physical observable

The raw assigned terminal fiber is still a routing-defined finite list.  This
module embeds it into a genuine `[0,1]`-valued observable on the full physical
lower-state carrier: the state is non-vacuum and its repaired central
face-zero label equals the selected spin.  A constructive weighted injection
then bounds the raw fiber's stationary mass by the physical stationary mean
of that observable.

Combining this comparison with the unconditional normalized-fiber
decomposition replaces the assigned routing term by an ordinary physical
expectation.  The remaining cutoff-uniform task is a quantitative comparison
of that expectation, and of the prefix-to-vacuum traffic, with the displayed
spin-cube-to-vacuum conductance.  No such comparison, congestion certificate,
finite gap, physical scaling, continuum theory, or Clay conclusion is proved
here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawTerminalFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings

/-! ## 1. A full-carrier unit observable for one repaired face label -/

private theorem zeroEdgeLabelling_mem_bounded_local
    (K : Nat) (ids : List Nat) :
    zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  apply boundedEdgeLabellings_complete
  · intro _ _
    simp [zeroEdgeLabelling]
  · intro _ _
    rfl

def positiveCentralFaceAssignedIndicator
    (K spin : Nat) (state : EdgeLabelling) : Q' :=
  if labellingsAgreeOnB
      (centralLowerFaceIds 0) state zeroEdgeLabelling then 0
  else if positiveCentralFaceTerminalSpin K (state 0) = spin then 1
  else 0

def positiveCentralFaceAssignedUnitObservable
    (K spin : Nat) : CentralPhysicalUnitObservable where
  value := positiveCentralFaceAssignedIndicator K spin
  nonnegative := by
    intro state
    unfold positiveCentralFaceAssignedIndicator
    split
    · decide
    · split <;> decide
  le_one := by
    intro state
    unfold positiveCentralFaceAssignedIndicator
    split
    · decide
    · split <;> decide

theorem positiveCentralFaceAssignedIndicator_eq_one_of_rawTerminalFiber
    {w : Q'} (hw : (0 : Q') < w) {K spin state : Nat}
    (hK : 1 ≤ K) (hspin : spin ≤ K)
    (hmem : state ∈
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin)) :
    positiveCentralFaceAssignedIndicator K spin
        (centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw) K 0 state) = 1 := by
  obtain ⟨hstate, hne, hlabel⟩ :=
    mem_positiveCentralFaceRawTerminalFiber_iff
      hw hK hspin |>.mp hmem
  have hstateLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w (Q'.le_of_lt hw) K 0 hstate
  have hzeroLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w (Q'.le_of_lt hw) K 0
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
  have hphysicalPositive := centralPhysicalFiniteStateAt_mem_positive
    w (Q'.le_of_lt hw) K 0 hstateLt
  have hphysicalBounded : centralPhysicalFiniteStateAt
      w (Q'.le_of_lt hw) K 0 state ∈
        boundedEdgeLabellings K (centralLowerFaceIds 0) :=
    (mem_centralPositiveHalfStates_iff.mp hphysicalPositive).1
  have hagreeNe : labellingsAgreeOnB
      (centralLowerFaceIds 0)
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) K 0 state)
      zeroEdgeLabelling ≠ true := by
    intro hagree
    have hphysical := eq_of_labellingsAgreeOnB_of_bounded
      hphysicalBounded
      (zeroEdgeLabelling_mem_bounded_local K (centralLowerFaceIds 0))
      hagree
    apply hne
    apply centralPhysicalFiniteStateAt_injective_of_lt hstateLt hzeroLt
    rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
    exact hphysical
  have hagreeFalse : labellingsAgreeOnB
      (centralLowerFaceIds 0)
      (centralPhysicalFiniteStateAt
        w (Q'.le_of_lt hw) K 0 state)
      zeroEdgeLabelling = false := by
    cases hagree : labellingsAgreeOnB
        (centralLowerFaceIds 0)
        (centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw) K 0 state)
        zeroEdgeLabelling
    · rfl
    · exact False.elim (hagreeNe hagree)
  unfold positiveCentralFaceAssignedIndicator
  simp only [hagreeFalse, Bool.false_eq_true, if_false, hlabel, if_true]

/-! ## 2. Raw assigned mass is bounded by a physical stationary mean -/

theorem rawAssignedTerminalFiberStationaryMass_le_stationaryMean
    {w : Q'} (hw : (0 : Q') < w) {K spin : Nat}
    (hK : 1 ≤ K) (hspin : spin ≤ K) :
    let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting source ≤
      centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
        (positiveCentralFaceAssignedUnitObservable K spin).value := by
  let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
  let fiber := centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
    (positiveCentralFaceSpinTerminalPrefixAssignment
      hw K hK).toPositiveRouting source
  let weight := centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
  let observable := positiveCentralFaceAssignedUnitObservable K spin
  let coefficient := centralPhysicalFiniteCoefficient
    w (Q'.le_of_lt hw) K 0 observable.value
  have hfiberNodup : fiber.Nodup := by
    unfold fiber centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber
    exact List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (Q'.le_of_lt hw) K 0)
  have hfinite : listQSum weight fiber ≤
      finiteWeightedMean
        (centralPhysicalFiniteCarrierSize w (Q'.le_of_lt hw) K 0)
        weight coefficient := by
    unfold finiteWeightedMean
    apply listQSum_le_of_injective
      fiber
      (List.range
        (centralPhysicalFiniteCarrierSize w (Q'.le_of_lt hw) K 0))
      weight (fun state => coefficient state * weight state)
      (fun state => state) hfiberNodup
    · intro state hstate
      obtain ⟨hsector, _hne, _hterminal⟩ :=
        mem_centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber_iff.mp
          hstate
      exact List.mem_range.mpr
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw) K 0 hsector)
    · intro left _ right _ heq
      exact heq
    · intro state hstate
      have hindicator :=
        positiveCentralFaceAssignedIndicator_eq_one_of_rawTerminalFiber
          hw hK hspin hstate
      unfold coefficient centralPhysicalFiniteCoefficient observable
      change weight state ≤
        positiveCentralFaceAssignedIndicator K spin
            (centralPhysicalFiniteStateAt
              w (Q'.le_of_lt hw) K 0 state) * weight state
      rw [hindicator]
      exact Q'.ge_of_eqv (Q'.one_mul_eqv (weight state))
    · intro state _hstate
      apply Q'.mul_nonneg
      · exact observable.nonnegative
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw) K 0 state)
      · unfold weight centralPhysicalFiniteWeight
        exact centralPhysicalRowMarginal_nonnegative
          (Q'.le_of_lt hw) K 0 _
  exact Q'.le_trans' _ _ _ hfinite
    (Q'.le_of_eqv
      (centralPhysicalFiniteWeightedMean_eqv_stationaryMean
        w (Q'.le_of_lt hw) K 0 observable.value))

/-! ## 3. The normalized demand now displays only physical expectation terms -/

theorem normalizedTerminalFiberStationaryMass_le_prefix_add_stationaryMean
    {w : Q'} (hw : (0 : Q') < w) {K spin : Nat}
    (hK : 1 ≤ K) (hspin : spin ≤ K) :
    let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
        (simplePositiveCentralFaceRouting hw K hK) source ≤
      positiveCentralFacePrefixEdgeUsingStationaryMass hw hK source 0 +
        centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
          (positiveCentralFaceAssignedUnitObservable K spin).value := by
  let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
  exact Q'.le_trans' _ _ _
    (normalizedTerminalFiberStationaryMass_le_prefix_add_assigned
      hw hK hspin)
    (Q'.add_le_add_left _ _ _
      (rawAssignedTerminalFiberStationaryMass_le_stationaryMean
        hw hK hspin))

theorem normalizedTerminalFiberResistanceDemand_le_prefix_add_stationaryMean
    {w : Q'} (hw : (0 : Q') < w) {K spin : Nat}
    (hK : 1 ≤ K) (hspin : spin ≤ K) :
    let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
    let hpositive :=
      centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw hspin
    let massBound :=
      positiveCentralFacePrefixEdgeUsingStationaryMass hw hK source 0 +
        centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
          (positiveCentralFaceAssignedUnitObservable K spin).value
    let reciprocal := Q'.recipPos
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0)
      hpositive
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        (simplePositiveCentralFaceRouting hw K hK) source hpositive ≤
      massBound * reciprocal + massBound * reciprocal := by
  let source := centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K spin
  let hpositive :=
    centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw hspin
  let actualMass :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
      (simplePositiveCentralFaceRouting hw K hK) source
  let massBound :=
    positiveCentralFacePrefixEdgeUsingStationaryMass hw hK source 0 +
      centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
        (positiveCentralFaceAssignedUnitObservable K spin).value
  let reciprocal := Q'.recipPos
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0)
    hpositive
  have hmass : actualMass ≤ massBound :=
    normalizedTerminalFiberStationaryMass_le_prefix_add_stationaryMean
      hw hK hspin
  have hmul : actualMass * reciprocal ≤ massBound * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ reciprocal hmass
      (Q'.le_of_lt (Q'.recipPos_pos _ hpositive))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (terminalFiberResistanceDemand_eqv_mass_mul_reciprocal_add_self
        (simplePositiveCentralFaceRouting hw K hK) source hpositive))
    (Q'.add_le_add hmul hmul)

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable.positiveCentralFaceAssignedUnitObservable
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable.positiveCentralFaceAssignedIndicator_eq_one_of_rawTerminalFiber
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable.rawAssignedTerminalFiberStationaryMass_le_stationaryMean
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable.normalizedTerminalFiberStationaryMass_le_prefix_add_stationaryMean
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable.normalizedTerminalFiberResistanceDemand_le_prefix_add_stationaryMean
