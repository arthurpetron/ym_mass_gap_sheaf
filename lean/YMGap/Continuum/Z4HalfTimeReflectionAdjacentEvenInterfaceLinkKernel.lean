/-
# Exact adjacent-even interface-link kernel

At an even reflection plane a fixed spatial link is incident to temporal
plaquettes from both halves.  The local SU(2) Haar elimination is therefore
not a state-independent boundary weight.  Its exact replacement is the
finite fusion-channel convolution: reverse the reflected incident-spin word
and split the vacuum multiplicity through the open channel.

This file constructs that local joint kernel directly from the production
fusion-path count, proves its exact weighted-Gram resolution, and derives
finite reflection positivity for every rational coefficient table.  It is a
local interface-link theorem; identifying the product of these kernels with
the complete adjacent-even slab remains a separate gluing problem.
-/

import YMGap.Continuum.Z4FusionChannelConvolution
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenInterfaceLinkKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Nat-to-rational finite-sum transport -/

private theorem ofNat_natListSum_map_eqv
    {A : Type} (value : A → Nat) : ∀ xs : List A,
    Q'.ofNat (natListSum (xs.map value)) ≈
      listQSum (fun item => Q'.ofNat (value item)) xs
  | [] => Q'.eqv_refl _
  | head :: tail => by
      simp only [List.map_cons, natListSum, listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.ofNat_add_eqv (value head)
          (natListSum (tail.map value)))
        (Q'.add_eqv_congr_left _ _ _
          (ofNat_natListSum_map_eqv value tail))

/-! ## 2. Exact local interface kernel and channel Gram -/

/-- Vacuum multiplicity for lower incident spins followed by the reversed
reflected-half word. -/
def adjacentEvenInterfaceLinkKernel
    (cutoff : Nat) (left right : List Nat) : Q' :=
  Q'.ofNat
    (fusionPathMultiplicity cutoff (left ++ right.reverse))

def adjacentEvenInterfaceLinkAmplitude
    (cutoff : Nat) (state : List Nat) (channel : Nat) : Q' :=
  Q'.ofNat (fusionChannelAmplitude cutoff state channel)

def adjacentEvenInterfaceLinkChannelWeight (_channel : Nat) : Q' := 1

theorem adjacentEvenInterfaceLinkKernel_nonnegative
    (cutoff : Nat) (left right : List Nat) :
    (0 : Q') ≤ adjacentEvenInterfaceLinkKernel cutoff left right :=
  zero_le_ofNat _

/-- Exact Peter--Weyl/fusion-channel resolution of one fixed spatial-link
kernel. -/
theorem adjacentEvenInterfaceLinkKernel_eqv_weightedGram
    {cutoff : Nat} {left right : List Nat}
    (hleft : SpinsBounded cutoff left)
    (hright : SpinsBounded cutoff right) :
    adjacentEvenInterfaceLinkKernel cutoff left right ≈
      weightedGram (List.range (cutoff + 1))
        adjacentEvenInterfaceLinkChannelWeight
        (adjacentEvenInterfaceLinkAmplitude cutoff)
        left right := by
  have hbounded : SpinsBounded cutoff (left ++ right.reverse) := by
    intro spin hspin
    rcases List.mem_append.mp hspin with hsource | hreflected
    · exact hleft spin hsource
    · exact hright spin (List.mem_reverse.mp hreflected)
  have hconvolution :=
    fusionPathMultiplicity_reflection_convolution
      left right.reverse hbounded
  unfold adjacentEvenInterfaceLinkKernel
  rw [hconvolution]
  refine Q'.eqv_trans _ _ _
    (ofNat_natListSum_map_eqv
      (fun channel =>
        fusionChannelAmplitude cutoff left channel *
          fusionChannelAmplitude cutoff right.reverse.reverse channel)
      (List.range (cutoff + 1))) ?_
  unfold weightedGram adjacentEvenInterfaceLinkChannelWeight
    adjacentEvenInterfaceLinkAmplitude
  apply listQSum_congr
  intro channel
  simp only [List.reverse_reverse]
  exact Q'.eqv_trans _ _ _
    (ofNat_mul_eqv
      (fusionChannelAmplitude cutoff left channel)
      (fusionChannelAmplitude cutoff right channel))
    (Q'.eqv_symm (Q'.one_mul_eqv _))

/-! ## 3. Finite local reflection positivity -/

def adjacentEvenInterfaceLinkQuadratic
    (cutoff : Nat) (states : List (List Nat))
    (coefficient : List Nat → Q') : Q' :=
  listQSum (fun left => listQSum (fun right =>
    (coefficient left * coefficient right) *
      adjacentEvenInterfaceLinkKernel cutoff left right) states) states

theorem adjacentEvenInterfaceLinkQuadratic_eqv_weightedGram
    (cutoff : Nat) (states : List (List Nat))
    (hstates : ∀ state, state ∈ states → SpinsBounded cutoff state)
    (coefficient : List Nat → Q') :
    adjacentEvenInterfaceLinkQuadratic cutoff states coefficient ≈
      weightedGramQuadratic states (List.range (cutoff + 1))
        adjacentEvenInterfaceLinkChannelWeight
        (adjacentEvenInterfaceLinkAmplitude cutoff)
        coefficient := by
  unfold adjacentEvenInterfaceLinkQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_left _ _ _
    (adjacentEvenInterfaceLinkKernel_eqv_weightedGram
      (hstates left hleft) (hstates right hright))

/-- Constructive local reflection positivity of the exact adjacent-even
interface-link law. -/
theorem adjacentEvenInterfaceLinkQuadratic_nonnegative
    (cutoff : Nat) (states : List (List Nat))
    (hstates : ∀ state, state ∈ states → SpinsBounded cutoff state)
    (coefficient : List Nat → Q') :
    (0 : Q') ≤
      adjacentEvenInterfaceLinkQuadratic cutoff states coefficient := by
  have hgram := weightedGramQuadratic_nonnegative
    states (List.range (cutoff + 1))
    adjacentEvenInterfaceLinkChannelWeight
    (adjacentEvenInterfaceLinkAmplitude cutoff)
    coefficient
    (fun channel hchannel => by
      unfold adjacentEvenInterfaceLinkChannelWeight
      decide)
  exact Q'.le_trans' _ _ _ hgram
    (Q'.le_of_eqv (Q'.eqv_symm
      (adjacentEvenInterfaceLinkQuadratic_eqv_weightedGram
        cutoff states hstates coefficient)))

#print axioms adjacentEvenInterfaceLinkKernel_nonnegative
#print axioms adjacentEvenInterfaceLinkKernel_eqv_weightedGram
#print axioms adjacentEvenInterfaceLinkQuadratic_eqv_weightedGram
#print axioms adjacentEvenInterfaceLinkQuadratic_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenInterfaceLinkKernel
