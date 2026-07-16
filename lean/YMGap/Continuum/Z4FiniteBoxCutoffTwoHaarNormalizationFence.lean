/-
# A fixed-cutoff normalization fence for the finite-box Haar bridge

This module tests the existing cutoff-two trivalent packet carrier against an
exact local Haar integral at a genuine four-valent link of the side-two Z4
box.  The test is a necessary specialization of any full oriented
matrix-coefficient expansion: after the matrix diagonal indices are summed,
the local factors are the corresponding SU(2) characters.

The link `((0,1,0,0), x0)` has exactly four incident box plaquettes.  The
repository's canonical `fuseLabels` construction resolves them through one
auxiliary representation.  At cutoff two that auxiliary label is also forced
to lie in `0,1,2`.  This is too small even though every external plaquette
label lies in `0,1,2`:

* four external spin-two labels also have the auxiliary spin-four channel;
* a spin-one/spin-two pair on each side also has auxiliary spin three.

Both losses are visible with the actual cutoff-two heat-kernel coefficients.
After the all-vacuum contribution is restored explicitly, the ordinary Haar
value exceeds the complete projected packet/fusion sum by the exact positive
quantity

    4 * coeffW(coupling,1)^2 * coeffW(coupling,2)^2
      + coeffW(coupling,2)^4.

Thus the present fixed-cutoff packet basis cannot be identified with the full
finite-box Haar expansion.  A valid successor must enlarge auxiliary cutoffs
according to fusion growth (or use an equivalent untruncated channel
carrier) before attempting the global sector sum.  The result does not rule
out that growing-cutoff repair; it rules out only the current fixed-cutoff
normalization.

Everything below is an exact finite rational/list calculation in the current
constructive substrate.
-/

import YMGap.Continuum.Z4UnitCubeHaarSectorBridge
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A genuine four-valent link in the finite Z4 box -/

/-- A boundary link of the side-two box with exactly four incident
plaquettes. -/
def fourValentBoxLink : Z4Link := ((0, 1, 0, 0), .x0)

/-- The four incident plaquette identifiers are obtained from the actual box
enumeration, not stipulated abstractly. -/
theorem fourValentBoxLink_incident_ids :
    incidentPlaqIds 2 fourValentBoxLink = [0, 24, 25, 26] := by
  decide

/-- This link is the entry with identifier two in the actual duplicate-free
box-link enumeration. -/
theorem fourValentBoxLink_enumerated :
    (2, fourValentBoxLink) ∈ enumerate (distinctBoxLinks 2) := by
  decide

/-- The physical face identifiers and the one internal fusion identifier
used by the canonical link resolution. -/
def boxFourValentEdges : List Nat := [0, 24, 25, 26, 113]

/-- The actual canonical trivalent resolution attached to that box link. -/
def boxFourValentVertices : List TrivalentVertex :=
  linkResolutionVertices 2 2 fourValentBoxLink

theorem boxFourValentVertices_exact :
    boxFourValentVertices = [(0, 24, 113), (113, 25, 26)] := by
  decide

theorem boxFourValent_first_vertex_global :
    (0, 24, 113) ∈ resolutionVertices 2 := by
  decide

theorem boxFourValent_second_vertex_global :
    (113, 25, 26) ∈ resolutionVertices 2 := by
  decide

/-! ## 2. Exact missing-channel census -/

/-- Intermediate channels allowed by a four-leg pairing at a specified
auxiliary cutoff. -/
def pairedChannels (K a b c d : Nat) : List Nat :=
  (List.range (K + 1)).filter fun channel =>
    fusionOK a b channel && fusionOK channel c d

/-- Cutoff two retains only two of the three channels for four spin-two
external labels. -/
theorem spinTwo_channels_cutoff_two :
    pairedChannels 2 2 2 2 2 = [0, 2] := by
  decide

theorem spinTwo_channels_full_window :
    pairedChannels 4 2 2 2 2 = [0, 2, 4] := by
  decide

/-- A spin-one/spin-two pair on each side loses the auxiliary spin-three
channel at cutoff two. -/
theorem mixed_channels_cutoff_two :
    pairedChannels 2 1 2 1 2 = [1] := by
  decide

theorem mixed_channels_full_window :
    pairedChannels 3 1 2 1 2 = [1, 3] := by
  decide

/-! ## 3. Pure spin-two normalization failure -/

def fourSpinTwoCharacter : Poly :=
  pmul (pmul (chebPoly 2) (chebPoly 2))
    (pmul (chebPoly 2) (chebPoly 2))

/-- The exact character Haar value counts all three singlet channels. -/
theorem fourSpinTwoCharacter_haar_three :
    bareVacuumHaar fourSpinTwoCharacter ≈ 3 := by
  decide

def pureSpinTwoPackets : Nat → CharacterPacket 2 := fun edge =>
  if edge ∈ incidentPlaqIds 2 fourValentBoxLink
    then basisPacket spinTwoIndex else allOnesPacket 2

/-- The complete cutoff-two Cartesian packet sum on the actual resolved link.
All external coefficients force spin two, while the auxiliary all-ones packet
sums every available cutoff-two channel. -/
def cutoffTwoPureSpinTwoResolvedSum : Q' :=
  listQSum
    (packetGraphProjectedAmplitude boxFourValentEdges boxFourValentVertices
      pureSpinTwoPackets)
    (boundedEdgeLabellings 2 boxFourValentEdges)

theorem cutoffTwoPureSpinTwoResolvedSum_two :
    cutoffTwoPureSpinTwoResolvedSum ≈ 2 := by
  decide

theorem cutoffTwoPureSpinTwo_ne_characterHaar :
    ¬ cutoffTwoPureSpinTwoResolvedSum ≈
      bareVacuumHaar fourSpinTwoCharacter := by
  decide

/-! ## 4. The actual heat-kernel defect, with vacuum restored -/

/-- Actual cutoff-two heat-kernel packets on the four physical face edges and
the exact all-channel packet on the internal fusion edge. -/
def boxHeatKernelPackets : Nat → CharacterPacket 2 := fun edge =>
  if edge ∈ incidentPlaqIds 2 fourValentBoxLink
    then heatKernelPacket 2 coupling else allOnesPacket 2

/-- The exact local cutoff-two heat-kernel character polynomial. -/
def localHeatKernelCharacter : Poly :=
  synthesis (heatKernelPacket 2 coupling)

def localHeatKernelFourthPower : Poly :=
  pmul (pmul localHeatKernelCharacter localHeatKernelCharacter)
    (pmul localHeatKernelCharacter localHeatKernelCharacter)

/-- Complete projected packet/fusion sum on the resolved link.  By definition
the graph projector removes the globally all-zero label. -/
def boxCutoffTwoHeatKernelResolvedSum : Q' :=
  listQSum
    (packetGraphProjectedAmplitude boxFourValentEdges boxFourValentVertices
      boxHeatKernelPackets)
    (boundedEdgeLabellings 2 boxFourValentEdges)

/-- Before the global excitation projector, the all-vacuum local labelling
has its correctly normalized value one. -/
theorem boxHeatKernel_vacuum_bare_one :
    packetGraphBareAmplitude boxFourValentEdges boxHeatKernelPackets
      zeroEdgeLabelling ≈ 1 := by
  decide

/-- The current physical projector deletes that vacuum term, as intended for
its excited spectral carrier. -/
theorem boxHeatKernel_vacuum_projected_zero :
    packetGraphProjectedAmplitude boxFourValentEdges boxFourValentVertices
      boxHeatKernelPackets zeroEdgeLabelling ≈ 0 := by
  decide

/-- Add back the derived unit vacuum contribution before comparing with the
full local Haar functional. -/
def boxCutoffTwoHeatKernelVacuumCompletedSum : Q' :=
  1 + boxCutoffTwoHeatKernelResolvedSum

/-- The exact omitted-channel weight.  The factor four counts the two orders
of the spin-one/spin-two pair independently on the two sides. -/
def cutoffTwoMissingChannelDefect : Q' :=
  (4 : Q') * ((coeffW coupling 1) ^ 2 * (coeffW coupling 2) ^ 2) +
    (coeffW coupling 2) ^ 4

theorem cutoffTwoMissingChannelDefect_pos :
    (0 : Q') < cutoffTwoMissingChannelDefect := by
  decide

/-- **Exact normalization fence.**  Even after restoring the vacuum, the
complete current cutoff-two packet/fusion sum is smaller than the ordinary
Haar value by the derived positive spin-three/spin-four channel defect. -/
theorem boxCutoffTwoHeatKernel_missing_channel_exact :
    bareVacuumHaar localHeatKernelFourthPower ≈
      boxCutoffTwoHeatKernelVacuumCompletedSum +
        cutoffTwoMissingChannelDefect := by
  decide

theorem boxCutoffTwoHeatKernel_ne_fullHaar :
    ¬ boxCutoffTwoHeatKernelVacuumCompletedSum ≈
      bareVacuumHaar localHeatKernelFourthPower := by
  decide

end YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.fourValentBoxLink_incident_ids
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.fourValentBoxLink_enumerated
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.boxFourValentVertices_exact
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.boxFourValent_first_vertex_global
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.boxFourValent_second_vertex_global
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.spinTwo_channels_cutoff_two
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.spinTwo_channels_full_window
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.mixed_channels_cutoff_two
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.mixed_channels_full_window
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.fourSpinTwoCharacter_haar_three
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.cutoffTwoPureSpinTwoResolvedSum_two
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.cutoffTwoPureSpinTwo_ne_characterHaar
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.boxHeatKernel_vacuum_bare_one
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.boxHeatKernel_vacuum_projected_zero
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.cutoffTwoMissingChannelDefect_pos
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.boxCutoffTwoHeatKernel_missing_channel_exact
#print axioms YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence.boxCutoffTwoHeatKernel_ne_fullHaar
