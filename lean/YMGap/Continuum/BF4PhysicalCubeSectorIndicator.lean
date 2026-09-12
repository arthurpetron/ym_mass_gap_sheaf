/-
# A cutoff-independent indicator of the physical cube vacuum sector

The event examines only the finite lower-face list: labels outside the cube
vanish, and the six cube labels have common parity. On every half-state
carrier it is precisely the cube-supported common-parity class, hence the
canonical vacuum component at positive coupling and cutoff at least one.

The same bounded observable is fixed by EVERY finite physical conditional
operator on its retained carrier. This supplies an actual stationary event,
not an assumed eigenvector or a strict-gap estimate. Its approximation in
the completed root-sector cylinder carrier is a separate construction.
-/

import YMGap.Continuum.BF4PhysicalCubeGNSData
import YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm

namespace YMGap.Continuum.BF4PhysicalCubeSectorIndicator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-- A finite decision procedure, with no spin-cutoff or coupling parameter. -/
def cubeSectorB (state : EdgeLabelling) : Bool :=
  (centralLowerFaceIds 0).all (fun face =>
    decide (face ∈ centralLowerCubeFaceIds ∨ state face = 0)) &&
  centralLowerCubeFaceIds.all (fun face => decide (state face % 2 = state 0 % 2))

theorem cubeSectorB_iff (state : EdgeLabelling)
    (hsupport : ∀ face, face ∉ centralLowerFaceIds 0 → state face = 0) :
    cubeSectorB state = true ↔ CubeSupportedCommonParity state := by
  simp only [cubeSectorB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hz, hp⟩
    refine ⟨?_, hp⟩
    intro face hoff
    by_cases hlower : face ∈ centralLowerFaceIds 0
    · exact (hz face hlower).resolve_left hoff
    · exact hsupport face hlower
  · rintro ⟨hz, hp⟩
    refine ⟨?_, hp⟩
    intro face _
    by_cases hcube : face ∈ centralLowerCubeFaceIds
    · exact Or.inl hcube
    · exact Or.inr (hz face hcube)

/-- The computable event is the exact physical component on every finite
carrier, not just a superset of the root orbit. -/
theorem cubeSectorB_iff_finiteSector {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hstate : state ∈ centralHalfStates K 0) :
    cubeSectorB state = true ↔
      state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 := by
  have hb := boundedEdgeLabellings_sound K (centralLowerFaceIds 0) state hstate
  rw [cubeSectorB_iff state hb.2, vacuumSector_iff_cubeSupportedCommonParity hw K hK state]
  constructor
  · intro hc
    exact ⟨fun face hf => Nat.le_of_lt_succ (hb.1 face
      (centralLowerCubeFaceIds_subset_lower face hf)), hc⟩
  · exact And.right

def cubeSectorIndicator (state : EdgeLabelling) : Q' := if cubeSectorB state then 1 else 0

def cubeSectorObservable : CentralPhysicalUnitObservable where
  value := cubeSectorIndicator
  nonnegative := fun state => by
    unfold cubeSectorIndicator
    cases cubeSectorB state <;> decide
  le_one := fun state => by
    unfold cubeSectorIndicator
    cases cubeSectorB state <;> decide

theorem cubeSectorIndicator_zero : cubeSectorIndicator zeroEdgeLabelling = 1 := by
  have hb : cubeSectorB zeroEdgeLabelling = true :=
    (cubeSectorB_iff _ (fun _ _ => rfl)).mpr ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  simp only [cubeSectorIndicator, hb, if_true]

theorem cubeSectorB_kernel_invariant (w : Q') (K : Nat) (left right : EdgeLabelling)
    (hl : left ∈ centralHalfStates K 0) (hr : right ∈ centralHalfStates K 0)
    (hne : ¬ centralPhysicalReflectedKernel w K 0 left right ≈ 0) :
    cubeSectorB left = cubeSectorB right := by
  have hliff := cubeSectorB_iff left (boundedEdgeLabellings_sound K _ left hl).2
  have hriff := cubeSectorB_iff right (boundedEdgeLabellings_sound K _ right hr).2
  have hreverse : ¬ centralPhysicalReflectedKernel w K 0 right left ≈ 0 := fun hz =>
    hne (Q'.eqv_trans _ _ _ (centralPhysicalReflectedKernel_symm w hl hr) hz)
  cases hleft : cubeSectorB left with
  | false =>
      cases hright : cubeSectorB right with
      | false => rfl
      | true =>
          have hc := kernel_preserves_cubeSupportedCommonParity w K right left hr hl hreverse
            (hriff.mp hright)
          have hf := hliff.mpr hc
          rw [hleft] at hf
          exact Bool.noConfusion hf
  | true =>
      exact (hriff.mpr (kernel_preserves_cubeSupportedCommonParity w K left right hl hr hne
        (hliff.mp hleft))).symm

private theorem mul_zero_of_eqv {a : Q'} (ha : a ≈ 0) (b : Q') : a * b ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.zero_mul_eqv b)

theorem conditional_zero_of_raw_zero (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (left right : EdgeLabelling)
    (hz : centralPhysicalReflectedKernel w K 0 left right ≈ 0) :
    centralPhysicalConditionalKernel w hw K 0 left right ≈ 0 := by
  unfold centralPhysicalConditionalKernel
  split
  · exact mul_zero_of_eqv (mul_zero_of_eqv hz _) _
  · exact Q'.eqv_refl 0

theorem cubeSectorIndicator_conditional_pair (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (left right : EdgeLabelling)
    (hl : left ∈ centralHalfStates K 0) (hr : right ∈ centralHalfStates K 0) :
    centralPhysicalConditionalKernel w hw K 0 left right * cubeSectorIndicator right ≈
      centralPhysicalConditionalKernel w hw K 0 left right * cubeSectorIndicator left := by
  by_cases hz : centralPhysicalReflectedKernel w K 0 left right ≈ 0
  · have hk := conditional_zero_of_raw_zero w hw K left right hz
    exact Q'.eqv_trans _ _ _ (mul_zero_of_eqv hk _) (Q'.eqv_symm (mul_zero_of_eqv hk _))
  · have hb := cubeSectorB_kernel_invariant w K left right hl hr hz
    unfold cubeSectorIndicator
    rw [hb]
    exact Q'.eqv_refl _

/-- The SAME cutoff-independent physical event is stationary at every cutoff. -/
theorem cubeSectorIndicator_markov_fixed (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (source : EdgeLabelling)
    (hs : source ∈ centralPositiveHalfStates w hw K 0) :
    centralPhysicalMarkovApply w hw K 0 cubeSectorIndicator source ≈ cubeSectorIndicator source := by
  unfold centralPhysicalMarkovApply
  refine Q'.eqv_trans _
    (listQSum (fun target => centralPhysicalConditionalKernel w hw K 0 source target *
      cubeSectorIndicator source) (centralPositiveHalfStates w hw K 0)) _ ?_ ?_
  · apply listQSum_congr_on
    intro target ht
    exact cubeSectorIndicator_conditional_pair w hw K source target
      (mem_centralPositiveHalfStates_iff.mp hs).1 (mem_centralPositiveHalfStates_iff.mp ht).1
  exact Q'.eqv_trans _ _ _ (listQSum_mul_right _ _ _) (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (centralPhysicalConditionalKernel_row_normalized hs))
    (Q'.one_mul_eqv _))

end YMGap.Continuum.BF4PhysicalCubeSectorIndicator

#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorB
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorB_iff
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorB_iff_finiteSector
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorIndicator
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorObservable
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorIndicator_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorB_kernel_invariant
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.conditional_zero_of_raw_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorIndicator_conditional_pair
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorIndicator.cubeSectorIndicator_markov_fixed
