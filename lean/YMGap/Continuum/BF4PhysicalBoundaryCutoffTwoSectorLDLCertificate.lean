/-
# Exact cutoff-two 65-sector mean-zero LDL certificate

The 64 independently compiled row checks and the pivot-sign check compose the
exact rational `L D L^T` certificate.  External arithmetic proposes the
tables only; Lean's kernel validates every entry and sign.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row15
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row16
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row17
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row18
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row19
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row20
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row21
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row22
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row23
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row24
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row25
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row26
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row27
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row28
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row29
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row30
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row31
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row32
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row33
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row34
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row35
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row36
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row37
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row38
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row39
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row40
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row41
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row42
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row43
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row44
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row45
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row46
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row47
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row48
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row49
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row50
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row51
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row52
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row53
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row54
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row55
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row56
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row57
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row58
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row59
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row60
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row61
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row62
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLRows.Row63

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRows_checked :
    finiteLDLClearedRowsCheck 64
      cutoffTwoSectorMeanZeroMatrix
      cutoffTwoSectorLower
      cutoffTwoSectorDiagonal
      cutoffTwoSectorCommonDenominator = true := by
  unfold finiteLDLClearedRowsCheck
  rw [show List.range 64 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] by decide]
  simp only [List.all_cons, List.all_nil,
    cutoffTwoSectorLDLRow00_checked,
    cutoffTwoSectorLDLRow01_checked,
    cutoffTwoSectorLDLRow02_checked,
    cutoffTwoSectorLDLRow03_checked,
    cutoffTwoSectorLDLRow04_checked,
    cutoffTwoSectorLDLRow05_checked,
    cutoffTwoSectorLDLRow06_checked,
    cutoffTwoSectorLDLRow07_checked,
    cutoffTwoSectorLDLRow08_checked,
    cutoffTwoSectorLDLRow09_checked,
    cutoffTwoSectorLDLRow10_checked,
    cutoffTwoSectorLDLRow11_checked,
    cutoffTwoSectorLDLRow12_checked,
    cutoffTwoSectorLDLRow13_checked,
    cutoffTwoSectorLDLRow14_checked,
    cutoffTwoSectorLDLRow15_checked,
    cutoffTwoSectorLDLRow16_checked,
    cutoffTwoSectorLDLRow17_checked,
    cutoffTwoSectorLDLRow18_checked,
    cutoffTwoSectorLDLRow19_checked,
    cutoffTwoSectorLDLRow20_checked,
    cutoffTwoSectorLDLRow21_checked,
    cutoffTwoSectorLDLRow22_checked,
    cutoffTwoSectorLDLRow23_checked,
    cutoffTwoSectorLDLRow24_checked,
    cutoffTwoSectorLDLRow25_checked,
    cutoffTwoSectorLDLRow26_checked,
    cutoffTwoSectorLDLRow27_checked,
    cutoffTwoSectorLDLRow28_checked,
    cutoffTwoSectorLDLRow29_checked,
    cutoffTwoSectorLDLRow30_checked,
    cutoffTwoSectorLDLRow31_checked,
    cutoffTwoSectorLDLRow32_checked,
    cutoffTwoSectorLDLRow33_checked,
    cutoffTwoSectorLDLRow34_checked,
    cutoffTwoSectorLDLRow35_checked,
    cutoffTwoSectorLDLRow36_checked,
    cutoffTwoSectorLDLRow37_checked,
    cutoffTwoSectorLDLRow38_checked,
    cutoffTwoSectorLDLRow39_checked,
    cutoffTwoSectorLDLRow40_checked,
    cutoffTwoSectorLDLRow41_checked,
    cutoffTwoSectorLDLRow42_checked,
    cutoffTwoSectorLDLRow43_checked,
    cutoffTwoSectorLDLRow44_checked,
    cutoffTwoSectorLDLRow45_checked,
    cutoffTwoSectorLDLRow46_checked,
    cutoffTwoSectorLDLRow47_checked,
    cutoffTwoSectorLDLRow48_checked,
    cutoffTwoSectorLDLRow49_checked,
    cutoffTwoSectorLDLRow50_checked,
    cutoffTwoSectorLDLRow51_checked,
    cutoffTwoSectorLDLRow52_checked,
    cutoffTwoSectorLDLRow53_checked,
    cutoffTwoSectorLDLRow54_checked,
    cutoffTwoSectorLDLRow55_checked,
    cutoffTwoSectorLDLRow56_checked,
    cutoffTwoSectorLDLRow57_checked,
    cutoffTwoSectorLDLRow58_checked,
    cutoffTwoSectorLDLRow59_checked,
    cutoffTwoSectorLDLRow60_checked,
    cutoffTwoSectorLDLRow61_checked,
    cutoffTwoSectorLDLRow62_checked,
    cutoffTwoSectorLDLRow63_checked]
  decide

theorem cutoffTwoSectorLDLDiagonal_checked :
    finiteLDLDiagonalCheck 64 cutoffTwoSectorDiagonal = true := by
  decide

theorem cutoffTwoSectorMeanZeroMatrixQuadratic_nonnegative
    (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteMatrixQuadratic 64
      cutoffTwoSectorMeanZeroMatrix coefficient :=
  finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
    cutoffTwoSectorLDLRows_checked
    cutoffTwoSectorLower_upper_zero
    cutoffTwoSectorLDLDiagonal_checked coefficient

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRows_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorMeanZeroMatrixQuadratic_nonnegative
