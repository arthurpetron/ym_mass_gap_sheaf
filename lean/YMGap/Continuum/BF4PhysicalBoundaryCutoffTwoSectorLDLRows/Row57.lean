/- Generated exact LDL row 57; composed from column chunks. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row57Chunk15

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow57_checked :
    finiteLDLClearedRowCheck 64
      cutoffTwoSectorMeanZeroMatrix
      cutoffTwoSectorLower
      cutoffTwoSectorDiagonal
      cutoffTwoSectorCommonDenominator 57 = true := by
  unfold finiteLDLClearedRowCheck
  rw [show List.range 64 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] ++ [24, 25, 26, 27] ++ [28, 29, 30, 31] ++ [32, 33, 34, 35] ++ [36, 37, 38, 39] ++ [40, 41, 42, 43] ++ [44, 45, 46, 47] ++ [48, 49, 50, 51] ++ [52, 53, 54, 55] ++ [56, 57, 58, 59] ++ [60, 61, 62, 63] by decide]
  simp only [List.all_append,
    cutoffTwoSectorLDLRow57Chunk00_checked,
    cutoffTwoSectorLDLRow57Chunk01_checked,
    cutoffTwoSectorLDLRow57Chunk02_checked,
    cutoffTwoSectorLDLRow57Chunk03_checked,
    cutoffTwoSectorLDLRow57Chunk04_checked,
    cutoffTwoSectorLDLRow57Chunk05_checked,
    cutoffTwoSectorLDLRow57Chunk06_checked,
    cutoffTwoSectorLDLRow57Chunk07_checked,
    cutoffTwoSectorLDLRow57Chunk08_checked,
    cutoffTwoSectorLDLRow57Chunk09_checked,
    cutoffTwoSectorLDLRow57Chunk10_checked,
    cutoffTwoSectorLDLRow57Chunk11_checked,
    cutoffTwoSectorLDLRow57Chunk12_checked,
    cutoffTwoSectorLDLRow57Chunk13_checked,
    cutoffTwoSectorLDLRow57Chunk14_checked,
    cutoffTwoSectorLDLRow57Chunk15_checked]
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow57_checked
