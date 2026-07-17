import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalTowerLimit

local infix:50 " ≈ " => Q'.eqv

def seed : CompensatedGraphState 1 where
  edges := [0]
  vertices := []
  packet := fun _ =>
    YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude.allOnesPacket 1
  copiedEdges := []
  copied_mem := by intro edge h; cases h

#eval supportedGraphCorr seed 0
#eval supportedGraphCorr seed 1

example : (0 : Q') < supportedGraphCorr seed 0 := by decide
example : supportedGraphCorr seed 1 ≈
    YMGap.Continuum.SU2PeterWeylWilsonBlock.eighth *
      YMGap.Continuum.SU2PeterWeylWilsonBlock.eighth := by decide
