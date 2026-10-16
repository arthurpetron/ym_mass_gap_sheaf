/-
# Nested terminal carriers for the AF cofinal block family

Every member of `afCofinalTrajectory` ends on the same corrected slab of
half-size zero, but its terminal representation cutoff is
`4^(depth+1)`.  Therefore terminal state spaces are not to be identified by
an equality of physical data.  They instead form a directed family under the
literal identity-on-labellings cutoff inclusion.

This module constructs that inclusion and proves exact compatibility of any
fixed global rational observable with restriction along it.  Pointwise unit
bounds also transport from a later carrier to every earlier carrier.  These
facts provide the carrier-level seam needed before comparing terminal laws
or recursively pulled-back observables across outer depths.

No probability-law compatibility is proved here: the terminal cutoff and AF
nome both vary with depth.  In particular this module supplies no remainder
bound, Cauchy modulus, continuum limit, spectral gap, or Clay theorem.

Constructive contract: exact finite carriers and natural-number order only;
no choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTrajectory
import YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics

namespace
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTrajectory
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration.AllCutoffOriginalActionTrajectory
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Exact terminal data -/

def afTerminalData (depth : Nat) : SlabPhysicalData :=
  (lastStep (afCofinalTrajectory depth)).pair.coarse

theorem afTerminalData_cutoff (depth : Nat) :
    (afTerminalData depth).cutoff = 4 ^ (depth + 1) := by
  exact afCofinalTrajectory_lastCoarseCutoff depth

theorem afTerminalData_half (depth : Nat) :
    (afTerminalData depth).half = 0 := by
  exact afCofinalTrajectory_lastCoarseHalf depth

theorem afTerminalData_extent (depth : Nat) :
    (afTerminalData depth).extent = 1 := by
  unfold SlabPhysicalData.extent
  rw [afTerminalData_half depth]
  rfl

theorem afTerminalData_faceEdges (depth : Nat) :
    (afTerminalData depth).faceEdges = slabPhysicalFaceEdges 1 := by
  unfold SlabPhysicalData.faceEdges
  rw [afTerminalData_extent depth]

theorem afTerminalData_coupling (depth : Nat) :
    (afTerminalData depth).coupling =
      afNomeSchedule.nome (depth + 1) := by
  simpa only [Nat.zero_add] using
    afScheduledTrajectory_lastCoarseCoupling depth

theorem afTerminalData_cutoff_mono
    {earlier later : Nat} (hdepth : earlier ≤ later) :
    (afTerminalData earlier).cutoff ≤
      (afTerminalData later).cutoff := by
  rw [afTerminalData_cutoff earlier, afTerminalData_cutoff later]
  exact Nat.pow_le_pow_right (by decide)
    (Nat.add_le_add_right hdepth 1)

/-! ## 2. The directed terminal carrier -/

theorem afTerminalPhysical_mem_of_le
    {earlier later : Nat} (hdepth : earlier ≤ later)
    {state : EdgeLabelling}
    (hstate :
      state ∈ (afTerminalData earlier).physicalLabellings) :
    state ∈ (afTerminalData later).physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings at hstate ⊢
  rw [afTerminalData_faceEdges earlier] at hstate
  rw [afTerminalData_faceEdges later]
  exact boundedEdgeLabellings_mem_of_le
    (afTerminalData_cutoff_mono hdepth)
    (slabPhysicalFaceEdges 1) hstate

structure AFCofinalTerminalState (depth : Nat) : Type where
  state : EdgeLabelling
  mem : state ∈ (afTerminalData depth).physicalLabellings

def embedTerminalState
    {earlier later : Nat} (hdepth : earlier ≤ later) :
    AFCofinalTerminalState earlier → AFCofinalTerminalState later
  | ⟨state, hstate⟩ =>
      ⟨state, afTerminalPhysical_mem_of_le hdepth hstate⟩

theorem embedTerminalState_state
    {earlier later : Nat} (hdepth : earlier ≤ later)
    (source : AFCofinalTerminalState earlier) :
    (embedTerminalState hdepth source).state = source.state := by
  cases source
  rfl

/-- Directed-system composition is literal on the underlying physical
labelling.  Membership proofs may differ, but no state coordinate changes. -/
theorem embedTerminalState_trans_state
    {first second third : Nat}
    (hfirstSecond : first ≤ second)
    (hsecondThird : second ≤ third)
    (source : AFCofinalTerminalState first) :
    (embedTerminalState hsecondThird
        (embedTerminalState hfirstSecond source)).state =
      (embedTerminalState
        (Nat.le_trans hfirstSecond hsecondThird) source).state := by
  cases source
  rfl

/-! ## 3. Compatible restrictions of fixed observables -/

def afTerminalObservable
    (observable : EdgeLabelling → Q') (depth : Nat) :
    AFCofinalTerminalState depth → Q' :=
  fun source => observable source.state

theorem afTerminalObservable_embed
    (observable : EdgeLabelling → Q')
    {earlier later : Nat} (hdepth : earlier ≤ later)
    (source : AFCofinalTerminalState earlier) :
    afTerminalObservable observable later
        (embedTerminalState hdepth source) =
      afTerminalObservable observable earlier source := by
  cases source
  rfl

theorem afTerminalObservable_embed_trans
    (observable : EdgeLabelling → Q')
    {first second third : Nat}
    (hfirstSecond : first ≤ second)
    (hsecondThird : second ≤ third)
    (source : AFCofinalTerminalState first) :
    afTerminalObservable observable third
        (embedTerminalState hsecondThird
          (embedTerminalState hfirstSecond source)) =
      afTerminalObservable observable first source := by
  cases source
  rfl

/-- A unit bound proved on a later terminal carrier automatically applies to
every earlier member through the exact carrier inclusion. -/
theorem afTerminalObservable_unitBounded_of_le
    (observable : EdgeLabelling → Q')
    {earlier later : Nat} (hdepth : earlier ≤ later)
    (hbound : ∀ state,
      state ∈ (afTerminalData later).physicalLabellings →
        Q'.abs (observable state) ≤ (1 : Q')) :
    ∀ state,
      state ∈ (afTerminalData earlier).physicalLabellings →
        Q'.abs (observable state) ≤ (1 : Q') := by
  intro state hstate
  exact hbound state
    (afTerminalPhysical_mem_of_le hdepth hstate)

/-! ## Axiom audit -/

#print axioms afTerminalData
#print axioms afTerminalData_cutoff
#print axioms afTerminalData_half
#print axioms afTerminalData_extent
#print axioms afTerminalData_faceEdges
#print axioms afTerminalData_coupling
#print axioms afTerminalData_cutoff_mono
#print axioms afTerminalPhysical_mem_of_le
#print axioms AFCofinalTerminalState
#print axioms embedTerminalState
#print axioms embedTerminalState_state
#print axioms embedTerminalState_trans_state
#print axioms afTerminalObservable
#print axioms afTerminalObservable_embed
#print axioms afTerminalObservable_embed_trans
#print axioms afTerminalObservable_unitBounded_of_le

end
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalCarrier
