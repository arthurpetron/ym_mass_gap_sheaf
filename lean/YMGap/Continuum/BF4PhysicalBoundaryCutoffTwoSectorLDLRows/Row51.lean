/- Generated exact LDL row 51; composed from column chunks. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row51Chunk15

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow51_checked :
    finiteLDLClearedRowCheck 64
      cutoffTwoSectorMeanZeroMatrix
      cutoffTwoSectorLower
      cutoffTwoSectorDiagonal
      cutoffTwoSectorCommonDenominator 51 = true := by
  unfold finiteLDLClearedRowCheck
  rw [show List.range 64 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] ++ [24, 25, 26, 27] ++ [28, 29, 30, 31] ++ [32, 33, 34, 35] ++ [36, 37, 38, 39] ++ [40, 41, 42, 43] ++ [44, 45, 46, 47] ++ [48, 49, 50, 51] ++ [52, 53, 54, 55] ++ [56, 57, 58, 59] ++ [60, 61, 62, 63] by decide]
  simp only [List.all_append,
    cutoffTwoSectorLDLRow51Chunk00_checked,
    cutoffTwoSectorLDLRow51Chunk01_checked,
    cutoffTwoSectorLDLRow51Chunk02_checked,
    cutoffTwoSectorLDLRow51Chunk03_checked,
    cutoffTwoSectorLDLRow51Chunk04_checked,
    cutoffTwoSectorLDLRow51Chunk05_checked,
    cutoffTwoSectorLDLRow51Chunk06_checked,
    cutoffTwoSectorLDLRow51Chunk07_checked,
    cutoffTwoSectorLDLRow51Chunk08_checked,
    cutoffTwoSectorLDLRow51Chunk09_checked,
    cutoffTwoSectorLDLRow51Chunk10_checked,
    cutoffTwoSectorLDLRow51Chunk11_checked,
    cutoffTwoSectorLDLRow51Chunk12_checked,
    cutoffTwoSectorLDLRow51Chunk13_checked,
    cutoffTwoSectorLDLRow51Chunk14_checked,
    cutoffTwoSectorLDLRow51Chunk15_checked]
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow51_checked
