/- Generated exact LDL row 29; composed from column chunks. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row29Chunk15

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow29_checked :
    finiteLDLClearedRowCheck 64
      cutoffTwoSectorMeanZeroMatrix
      cutoffTwoSectorLower
      cutoffTwoSectorDiagonal
      cutoffTwoSectorCommonDenominator 29 = true := by
  unfold finiteLDLClearedRowCheck
  rw [show List.range 64 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] ++ [24, 25, 26, 27] ++ [28, 29, 30, 31] ++ [32, 33, 34, 35] ++ [36, 37, 38, 39] ++ [40, 41, 42, 43] ++ [44, 45, 46, 47] ++ [48, 49, 50, 51] ++ [52, 53, 54, 55] ++ [56, 57, 58, 59] ++ [60, 61, 62, 63] by decide]
  simp only [List.all_append,
    cutoffTwoSectorLDLRow29Chunk00_checked,
    cutoffTwoSectorLDLRow29Chunk01_checked,
    cutoffTwoSectorLDLRow29Chunk02_checked,
    cutoffTwoSectorLDLRow29Chunk03_checked,
    cutoffTwoSectorLDLRow29Chunk04_checked,
    cutoffTwoSectorLDLRow29Chunk05_checked,
    cutoffTwoSectorLDLRow29Chunk06_checked,
    cutoffTwoSectorLDLRow29Chunk07_checked,
    cutoffTwoSectorLDLRow29Chunk08_checked,
    cutoffTwoSectorLDLRow29Chunk09_checked,
    cutoffTwoSectorLDLRow29Chunk10_checked,
    cutoffTwoSectorLDLRow29Chunk11_checked,
    cutoffTwoSectorLDLRow29Chunk12_checked,
    cutoffTwoSectorLDLRow29Chunk13_checked,
    cutoffTwoSectorLDLRow29Chunk14_checked,
    cutoffTwoSectorLDLRow29Chunk15_checked]
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow29_checked
