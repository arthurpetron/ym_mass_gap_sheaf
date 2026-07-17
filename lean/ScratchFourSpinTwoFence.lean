import YMGap.Continuum.Z4UnitCubeHaarSectorBridge
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace ScratchFourSpinTwoFence

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

def fourSpinTwoCharacter : Poly :=
  pmul (pmul (chebPoly 2) (chebPoly 2))
    (pmul (chebPoly 2) (chebPoly 2))

theorem fourSpinTwoCharacter_haar_three :
    bareVacuumHaar fourSpinTwoCharacter ≈ 3 := by
  decide

def fourSpinTwoEdges : List Nat := [0, 1, 2, 3, 4]

def fourValentBoxLink :
    YMGap.Continuum.ClusterCount4DProgress.Z4Link :=
  ((0, 1, 0, 0), .x0)

#eval incidentPlaqIds 2 fourValentBoxLink
#eval (((enumerate (distinctBoxLinks 2)).filter fun indexed =>
  decide (indexed.2 = fourValentBoxLink)).map Prod.fst)

def fourSpinTwoVertices : List TrivalentVertex :=
  [(0, 1, 4), (4, 2, 3)]

theorem fourSpinTwoVertices_are_canonical_resolution :
    fourSpinTwoVertices = fuseLabels 5 4 [0, 1, 2, 3] := by
  decide

def fourSpinTwoPackets : Nat → CharacterPacket 2 := fun edge =>
  if edge < 4 then basisPacket spinTwoIndex else allOnesPacket 2

def cutoffTwoResolvedHaarSum : Q' :=
  listQSum
    (packetGraphProjectedAmplitude fourSpinTwoEdges fourSpinTwoVertices
      fourSpinTwoPackets)
    (boundedEdgeLabellings 2 fourSpinTwoEdges)

theorem cutoffTwoResolvedHaarSum_two : cutoffTwoResolvedHaarSum ≈ 2 := by
  decide

theorem cutoffTwoResolvedHaarSum_ne_characterHaar :
    ¬ cutoffTwoResolvedHaarSum ≈ bareVacuumHaar fourSpinTwoCharacter := by
  decide

def vacuumPlusSpinTwoPacket : CharacterPacket 2 where
  coeff i := if i.val = 1 then 0 else 1

def vacuumPlusSpinTwoCharacter : Poly :=
  padd YMGap.Continuum.SU2ClassPolynomialAlgebra.pone (chebPoly 2)

def vacuumPlusSpinTwoFourthPower : Poly :=
  pmul (pmul vacuumPlusSpinTwoCharacter vacuumPlusSpinTwoCharacter)
    (pmul vacuumPlusSpinTwoCharacter vacuumPlusSpinTwoCharacter)

def vacuumPlusSpinTwoPackets : Nat → CharacterPacket 2 := fun edge =>
  if edge < 4 then vacuumPlusSpinTwoPacket else allOnesPacket 2

def cutoffTwoVacuumIncludedResolvedHaarSum : Q' :=
  listQSum
    (packetGraphProjectedAmplitude fourSpinTwoEdges fourSpinTwoVertices
      vacuumPlusSpinTwoPackets)
    (boundedEdgeLabellings 2 fourSpinTwoEdges)

def boxFourValentEdges : List Nat := [0, 24, 25, 26, 113]

def boxFourValentVertices : List TrivalentVertex :=
  linkResolutionVertices 2 2 fourValentBoxLink

theorem boxFourValentVertices_exact :
    boxFourValentVertices = [(0, 24, 113), (113, 25, 26)] := by
  decide

def boxHeatKernelPackets : Nat → CharacterPacket 2 := fun edge =>
  if edge ∈ incidentPlaqIds 2 fourValentBoxLink
    then heatKernelPacket 2 coupling else allOnesPacket 2

def boxCutoffTwoHeatKernelResolvedSum : Q' :=
  listQSum
    (packetGraphProjectedAmplitude boxFourValentEdges boxFourValentVertices
      boxHeatKernelPackets)
    (boundedEdgeLabellings 2 boxFourValentEdges)

def localHeatKernelCharacter : Poly := synthesis (heatKernelPacket 2 coupling)

def localHeatKernelFourthPower : Poly :=
  pmul (pmul localHeatKernelCharacter localHeatKernelCharacter)
    (pmul localHeatKernelCharacter localHeatKernelCharacter)

def boxCutoffTwoHeatKernelVacuumCompletedSum : Q' :=
  1 + boxCutoffTwoHeatKernelResolvedSum

theorem boxCutoffTwoHeatKernel_missing_channel_exact :
    bareVacuumHaar localHeatKernelFourthPower ≈
      boxCutoffTwoHeatKernelVacuumCompletedSum +
        ((4 : Q') * ((coeffW coupling 1) ^ 2 * (coeffW coupling 2) ^ 2) +
          (coeffW coupling 2) ^ 4) := by
  decide

theorem boxCutoffTwoHeatKernel_ne_fullHaar :
    ¬ boxCutoffTwoHeatKernelVacuumCompletedSum ≈
      bareVacuumHaar localHeatKernelFourthPower := by
  decide

end ScratchFourSpinTwoFence
