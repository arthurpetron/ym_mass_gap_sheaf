/- Generated exact LDL row 1; composed from column chunks. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLChunks.Row01Chunk15

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow01_checked :
    finiteLDLClearedRowCheck 64
      cutoffTwoSectorMeanZeroMatrix
      cutoffTwoSectorLower
      cutoffTwoSectorDiagonal
      cutoffTwoSectorCommonDenominator 1 = true := by
  unfold finiteLDLClearedRowCheck
  rw [show List.range 64 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] ++ [24, 25, 26, 27] ++ [28, 29, 30, 31] ++ [32, 33, 34, 35] ++ [36, 37, 38, 39] ++ [40, 41, 42, 43] ++ [44, 45, 46, 47] ++ [48, 49, 50, 51] ++ [52, 53, 54, 55] ++ [56, 57, 58, 59] ++ [60, 61, 62, 63] by decide]
  simp only [List.all_append,
    cutoffTwoSectorLDLRow01Chunk00_checked,
    cutoffTwoSectorLDLRow01Chunk01_checked,
    cutoffTwoSectorLDLRow01Chunk02_checked,
    cutoffTwoSectorLDLRow01Chunk03_checked,
    cutoffTwoSectorLDLRow01Chunk04_checked,
    cutoffTwoSectorLDLRow01Chunk05_checked,
    cutoffTwoSectorLDLRow01Chunk06_checked,
    cutoffTwoSectorLDLRow01Chunk07_checked,
    cutoffTwoSectorLDLRow01Chunk08_checked,
    cutoffTwoSectorLDLRow01Chunk09_checked,
    cutoffTwoSectorLDLRow01Chunk10_checked,
    cutoffTwoSectorLDLRow01Chunk11_checked,
    cutoffTwoSectorLDLRow01Chunk12_checked,
    cutoffTwoSectorLDLRow01Chunk13_checked,
    cutoffTwoSectorLDLRow01Chunk14_checked,
    cutoffTwoSectorLDLRow01Chunk15_checked]
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow01_checked
