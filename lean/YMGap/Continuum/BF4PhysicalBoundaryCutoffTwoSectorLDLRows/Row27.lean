/- Generated exact LDL row 27; composed from column chunks. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row27Chunk15

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow27_checked :
    finiteLDLClearedRowCheck 64
      cutoffTwoSectorMeanZeroMatrix
      cutoffTwoSectorLower
      cutoffTwoSectorDiagonal
      cutoffTwoSectorCommonDenominator 27 = true := by
  unfold finiteLDLClearedRowCheck
  rw [show List.range 64 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] ++ [24, 25, 26, 27] ++ [28, 29, 30, 31] ++ [32, 33, 34, 35] ++ [36, 37, 38, 39] ++ [40, 41, 42, 43] ++ [44, 45, 46, 47] ++ [48, 49, 50, 51] ++ [52, 53, 54, 55] ++ [56, 57, 58, 59] ++ [60, 61, 62, 63] by decide]
  simp only [List.all_append,
    cutoffTwoSectorLDLRow27Chunk00_checked,
    cutoffTwoSectorLDLRow27Chunk01_checked,
    cutoffTwoSectorLDLRow27Chunk02_checked,
    cutoffTwoSectorLDLRow27Chunk03_checked,
    cutoffTwoSectorLDLRow27Chunk04_checked,
    cutoffTwoSectorLDLRow27Chunk05_checked,
    cutoffTwoSectorLDLRow27Chunk06_checked,
    cutoffTwoSectorLDLRow27Chunk07_checked,
    cutoffTwoSectorLDLRow27Chunk08_checked,
    cutoffTwoSectorLDLRow27Chunk09_checked,
    cutoffTwoSectorLDLRow27Chunk10_checked,
    cutoffTwoSectorLDLRow27Chunk11_checked,
    cutoffTwoSectorLDLRow27Chunk12_checked,
    cutoffTwoSectorLDLRow27Chunk13_checked,
    cutoffTwoSectorLDLRow27Chunk14_checked,
    cutoffTwoSectorLDLRow27Chunk15_checked]
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow27_checked
