/-
# One cutoff-independent positive physical cube kernel

Every finite collection of cube-supported states admits a computed common
cutoff at which all stable raw entries are exactly the original physical
OS Gram entries. Hence every finite quadratic form of this single kernel is
nonnegative. The certificate retains the original boundary channels, weights,
and amplitudes; it is not a free positive model.

This supplies a positive kernel on the algebraic finite-span carrier. It does
not construct a bounded completed transfer or identify normalized row limits,
vacuum isolation, uniform gap, volume limits, or continuum QFT.
-/

import YMGap.Continuum.BF4PhysicalCubeKernelSaturation

namespace YMGap.Continuum.BF4PhysicalCubeStableGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalCubeKernelSaturation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def cubeListSpinBound : List EdgeLabelling → Nat
  | [] => 0
  | state :: states => cubeSpinSum state + cubeListSpinBound states

theorem cubeListSpinBound_member : ∀ (states : List EdgeLabelling) {state : EdgeLabelling},
    state ∈ states → cubeSpinSum state ≤ cubeListSpinBound states
  | [], _, h => False.elim (List.not_mem_nil h)
  | head :: tail, state, h => by
      rcases List.mem_cons.mp h with heq | ht
      · subst state; unfold cubeListSpinBound; omega
      · have ih := cubeListSpinBound_member tail ht
        unfold cubeListSpinBound
        omega

def cubeListGramCutoff (states : List EdgeLabelling) : Nat := 4 * cubeListSpinBound states

def cubeStableQuadratic (w : Q') (states : List EdgeLabelling) (coefficient : EdgeLabelling → Q') : Q' :=
  listQSum (fun left => listQSum (fun right => (coefficient left * coefficient right) *
    cubeStableRawKernel w left right) states) states

/-- All entries of a bounded finite family use one actual production Gram. -/
theorem cubeStableRawKernel_common_gram (w : Q') (R : Nat) (left right : EdgeLabelling)
    (hl : cubeSpinSum left ≤ R) (hr : cubeSpinSum right ≤ R)
    (hlz : ∀ face, face ∉ centralLowerCubeFaceIds → left face = 0)
    (hrz : ∀ face, face ∉ centralLowerCubeFaceIds → right face = 0) :
    cubeStableRawKernel w left right ≈ weightedGram
      (centralBoundaryChannels (4 * R) 0) (centralBoundaryWeight w (4 * R) 0)
      (centralHalfAmplitude w (4 * R) 0) left right := by
  have hcut : cubeKernelSaturationCutoff left right ≤ 4 * R := by
    unfold cubeKernelSaturationCutoff; omega
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm
    (cubeStableRawKernel_eventual w left right hlz hrz (4 * R) hcut)) ?_
  apply centralPhysicalReflectedKernel_eq_weightedGram
  · apply cubeSupported_mem_halfStates (4 * R) left _ hlz
    apply cubeSupported_bounded _ left _ hlz
    intro face hf
    have hs := cubeSpinSum_bounds left face hf
    omega
  · apply cubeSupported_mem_halfStates (4 * R) right _ hrz
    apply cubeSupported_bounded _ right _ hrz
    intro face hf
    have hs := cubeSpinSum_bounds right face hf
    omega

theorem cubeStableQuadratic_eq_physicalGram (w : Q') (states : List EdgeLabelling)
    (coefficient : EdgeLabelling → Q')
    (hs : ∀ state, state ∈ states → ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    cubeStableQuadratic w states coefficient ≈ weightedGramQuadratic states
      (centralBoundaryChannels (cubeListGramCutoff states) 0)
      (centralBoundaryWeight w (cubeListGramCutoff states) 0)
      (centralHalfAmplitude w (cubeListGramCutoff states) 0) coefficient := by
  unfold cubeStableQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro left hl
  apply listQSum_congr_on
  intro right hr
  exact Q'.mul_eqv_congr_left _ _ _ (cubeStableRawKernel_common_gram w
    (cubeListSpinBound states) left right (cubeListSpinBound_member states hl)
    (cubeListSpinBound_member states hr) (hs left hl) (hs right hr))

/-- Positivity of the same stable kernel for every finite rational observable. -/
theorem cubeStableQuadratic_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (states : List EdgeLabelling) (coefficient : EdgeLabelling → Q')
    (hs : ∀ state, state ∈ states → ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    (0 : Q') ≤ cubeStableQuadratic w states coefficient := by
  have hgram := weightedGramQuadratic_nonnegative states
    (centralBoundaryChannels (cubeListGramCutoff states) 0)
    (centralBoundaryWeight w (cubeListGramCutoff states) 0)
    (centralHalfAmplitude w (cubeListGramCutoff states) 0) coefficient
    (centralBoundaryWeight_nonnegative_on hw)
  exact Q'.le_trans' _ _ _ hgram (Q'.ge_of_eqv (cubeStableQuadratic_eq_physicalGram w states coefficient hs))

end YMGap.Continuum.BF4PhysicalCubeStableGram

#print axioms YMGap.Continuum.BF4PhysicalCubeStableGram.cubeListSpinBound_member
#print axioms YMGap.Continuum.BF4PhysicalCubeStableGram.cubeListGramCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeStableGram.cubeStableQuadratic
#print axioms YMGap.Continuum.BF4PhysicalCubeStableGram.cubeStableRawKernel_common_gram
#print axioms YMGap.Continuum.BF4PhysicalCubeStableGram.cubeStableQuadratic_eq_physicalGram
#print axioms YMGap.Continuum.BF4PhysicalCubeStableGram.cubeStableQuadratic_nonnegative
