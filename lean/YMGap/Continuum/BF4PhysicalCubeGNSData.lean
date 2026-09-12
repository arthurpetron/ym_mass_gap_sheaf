/-
# The all-spin physical cube-sector pre-Hilbert carrier

At extent one and positive w the states below are exactly the union of the
canonical finite vacuum components. Every state carries its literal labelling
and the proved cube/common-parity condition, and has an explicit admission
cutoff. There is no fixed spin ceiling on this carrier.

Every finite signed term list is realized in one original physical boundary
Gram at a computed common cutoff. This constructs GNSData for the stabilized
RAW reflected kernel, not the marginal-weighted normalized Markov form. The
zero labelling supplies a nonzero root vector, not yet a transfer-fixed vacuum.
Normalized transfer compatibility, uniform gap and continuum remain open.
-/

import YMGap.Continuum.RationalKernelSpan
import YMGap.Continuum.BF4PhysicalCubeStableGram
import YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
import YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget

namespace YMGap.Continuum.BF4PhysicalCubeGNSData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalCubeKernelSaturation
open YMGap.Continuum.BF4PhysicalCubeStableGram
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def CubeSectorState := {state : EdgeLabelling // CubeSupportedCommonParity state}

def stateCutoff (state : CubeSectorState) : Nat := cubeSpinSum state.val + 1

/-- A computed finite-sector witness for every state of the unbounded carrier. -/
theorem state_mem_finite_sector {w : Q'} (hw : (0 : Q') < w) (state : CubeSectorState) :
    state.val ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw)
      (stateCutoff state) 0 := by
  apply cubeSupportedCommonParity_mem_sector hw (stateCutoff state) (by
    unfold stateCutoff; omega) state.val _ state.property
  intro face hf
  exact Nat.le_trans (cubeSpinSum_bounds state.val face hf) (Nat.le_succ _)

/-- Inclusion of every actual finite component, with the labelling unchanged. -/
def stateOfFiniteSector (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (state : EdgeLabelling)
    (hs : state ∈ centralPhysicalFiniteVacuumSectorStates w hw K 0) : CubeSectorState :=
  ⟨state, vacuumSector_cubeSupportedCommonParity w hw K hs⟩

def kernel (w : Q') (left right : CubeSectorState) : Q' :=
  cubeStableRawKernel w left.val right.val

theorem kernel_symm (w : Q') (left right : CubeSectorState) :
    kernel w left right ≈ kernel w right left := by
  let R := cubeSpinSum left.val + cubeSpinSum right.val
  have hl : cubeSpinSum left.val ≤ R := Nat.le_add_right _ _
  have hr : cubeSpinSum right.val ≤ R := Nat.le_add_left _ _
  refine Q'.eqv_trans _ _ _ (cubeStableRawKernel_common_gram w R left.val right.val
    hl hr left.property.1 right.property.1) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (cubeStableRawKernel_common_gram w R
    right.val left.val hr hl right.property.1 left.property.1))
  unfold weightedGram
  apply listQSum_congr
  intro channel
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)

abbrev CubeSpan := Span CubeSectorState

def termSpinBound : CubeSpan → Nat
  | [] => 0
  | term :: terms => cubeSpinSum term.1.val + termSpinBound terms

theorem termSpinBound_member : ∀ (terms : CubeSpan) {term : CubeSectorState × Q'},
    term ∈ terms → cubeSpinSum term.1.val ≤ termSpinBound terms
  | [], _, h => False.elim (List.not_mem_nil h)
  | head :: tail, term, h => by
      rcases List.mem_cons.mp h with heq | ht
      · subst term; unfold termSpinBound; omega
      · have ih := termSpinBound_member tail ht
        unfold termSpinBound; omega

def termGramCutoff (terms : CubeSpan) : Nat := 4 * termSpinBound terms

/-- Full signed-form identification; duplicate states need not be aggregated. -/
theorem form_eq_physicalGram (w : Q') (terms : CubeSpan) :
    form (kernel w) terms terms ≈ weightedGramQuadratic terms
      (centralBoundaryChannels (termGramCutoff terms) 0)
      (centralBoundaryWeight w (termGramCutoff terms) 0)
      (fun term channel => centralHalfAmplitude w (termGramCutoff terms) 0 term.1.val channel)
      (fun term => term.2) := by
  refine Q'.eqv_trans _ _ _ (form_expansion (kernel w) terms terms) ?_
  unfold weightedGramQuadratic
  apply listQSum_congr_on
  intro right hr
  apply listQSum_congr_on
  intro left hl
  apply Q'.mul_eqv_congr_left
  exact Q'.eqv_trans _ _ _ (kernel_symm w left.1 right.1)
    (cubeStableRawKernel_common_gram w (termSpinBound terms) right.1.val left.1.val
      (termSpinBound_member terms hr) (termSpinBound_member terms hl)
      right.1.property.1 left.1.property.1)

theorem form_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (terms : CubeSpan) :
    (0 : Q') ≤ form (kernel w) terms terms := by
  have hgram := weightedGramQuadratic_nonnegative terms
    (centralBoundaryChannels (termGramCutoff terms) 0)
    (centralBoundaryWeight w (termGramCutoff terms) 0)
    (fun term channel => centralHalfAmplitude w (termGramCutoff terms) 0 term.1.val channel)
    (fun term => term.2) (centralBoundaryWeight_nonnegative_on hw)
  exact Q'.le_trans' _ _ _ hgram (Q'.ge_of_eqv (form_eq_physicalGram w terms))

/-- All algebra and positivity fields are constructed for this physical form. -/
def cubeGNSData (w : Q') (hw : (0 : Q') ≤ w) : GNSData :=
  RationalKernelSpan.toGNSData (kernel w) (kernel_symm w) (form_nonnegative hw)

def rootState : CubeSectorState :=
  ⟨zeroEdgeLabelling, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩

def rootVector : CubeSpan := basis rootState

theorem root_norm_lower_bound (w : Q') (hw : (0 : Q') ≤ w) :
    (1 : Q') ≤ (cubeGNSData w hw).B rootVector rootVector := by
  have h := one_le_centralPhysicalReflectedKernel_vacuum hw
    (cubeKernelSaturationCutoff zeroEdgeLabelling zeroEdgeLabelling) 0
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (form_basis (kernel w) rootState rootState))

theorem root_not_radical (w : Q') (hw : (0 : Q') ≤ w) :
    ¬ (cubeGNSData w hw).rad rootVector (cubeGNSData w hw).zero := by
  intro h
  have hz := ((cubeGNSData w hw).rad_zero_iff rootVector).mp h
  have hbad := Q'.le_trans' _ _ _ (root_norm_lower_bound w hw) (Q'.le_of_eqv hz)
  exact (by decide : ¬ ((1 : Q') ≤ 0)) hbad

end YMGap.Continuum.BF4PhysicalCubeGNSData

#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.stateCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.state_mem_finite_sector
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.stateOfFiniteSector
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.kernel_symm
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.termSpinBound_member
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.termGramCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.form_eq_physicalGram
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.form_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.cubeGNSData
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.root_norm_lower_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeGNSData.root_not_radical
