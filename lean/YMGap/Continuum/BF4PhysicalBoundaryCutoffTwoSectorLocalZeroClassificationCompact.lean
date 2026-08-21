/-
# Compact local-zero classification aggregate

All expensive local-support row checks live in separate modules.  This file
combines them through a literal Boolean list, avoiding the historical deeply
nested append proof.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row15
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row16
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row17
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row18
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row19
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row20
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row21
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row22
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row23
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row24
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row25
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row26
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row27
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row28
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row29
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row30
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row31
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row32
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row33
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row34
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row35
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row36
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row37
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row38
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row39
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row40
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row41
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row42
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row43
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row44
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row45
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row46
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row47
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row48
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row49
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row50
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row51
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row52
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row53
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row54
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row55
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row56
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row57
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row58
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row59
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row60
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row61
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row62
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row63
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroRows.Row64

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassificationCompact

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Compact composition of all 65 independently checked zero rows. -/
theorem cutoffTwoSectorLocalZeroRows_compact_checked :
    (List.range 65).all cutoffTwoSectorLocalZeroRowCheck = true := by
  rw [show List.range 65 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64] by decide]
  simp only [List.all_cons, List.all_nil,
    cutoffTwoSectorLocalZeroRow00_checked,
    cutoffTwoSectorLocalZeroRow01_checked,
    cutoffTwoSectorLocalZeroRow02_checked,
    cutoffTwoSectorLocalZeroRow03_checked,
    cutoffTwoSectorLocalZeroRow04_checked,
    cutoffTwoSectorLocalZeroRow05_checked,
    cutoffTwoSectorLocalZeroRow06_checked,
    cutoffTwoSectorLocalZeroRow07_checked,
    cutoffTwoSectorLocalZeroRow08_checked,
    cutoffTwoSectorLocalZeroRow09_checked,
    cutoffTwoSectorLocalZeroRow10_checked,
    cutoffTwoSectorLocalZeroRow11_checked,
    cutoffTwoSectorLocalZeroRow12_checked,
    cutoffTwoSectorLocalZeroRow13_checked,
    cutoffTwoSectorLocalZeroRow14_checked,
    cutoffTwoSectorLocalZeroRow15_checked,
    cutoffTwoSectorLocalZeroRow16_checked,
    cutoffTwoSectorLocalZeroRow17_checked,
    cutoffTwoSectorLocalZeroRow18_checked,
    cutoffTwoSectorLocalZeroRow19_checked,
    cutoffTwoSectorLocalZeroRow20_checked,
    cutoffTwoSectorLocalZeroRow21_checked,
    cutoffTwoSectorLocalZeroRow22_checked,
    cutoffTwoSectorLocalZeroRow23_checked,
    cutoffTwoSectorLocalZeroRow24_checked,
    cutoffTwoSectorLocalZeroRow25_checked,
    cutoffTwoSectorLocalZeroRow26_checked,
    cutoffTwoSectorLocalZeroRow27_checked,
    cutoffTwoSectorLocalZeroRow28_checked,
    cutoffTwoSectorLocalZeroRow29_checked,
    cutoffTwoSectorLocalZeroRow30_checked,
    cutoffTwoSectorLocalZeroRow31_checked,
    cutoffTwoSectorLocalZeroRow32_checked,
    cutoffTwoSectorLocalZeroRow33_checked,
    cutoffTwoSectorLocalZeroRow34_checked,
    cutoffTwoSectorLocalZeroRow35_checked,
    cutoffTwoSectorLocalZeroRow36_checked,
    cutoffTwoSectorLocalZeroRow37_checked,
    cutoffTwoSectorLocalZeroRow38_checked,
    cutoffTwoSectorLocalZeroRow39_checked,
    cutoffTwoSectorLocalZeroRow40_checked,
    cutoffTwoSectorLocalZeroRow41_checked,
    cutoffTwoSectorLocalZeroRow42_checked,
    cutoffTwoSectorLocalZeroRow43_checked,
    cutoffTwoSectorLocalZeroRow44_checked,
    cutoffTwoSectorLocalZeroRow45_checked,
    cutoffTwoSectorLocalZeroRow46_checked,
    cutoffTwoSectorLocalZeroRow47_checked,
    cutoffTwoSectorLocalZeroRow48_checked,
    cutoffTwoSectorLocalZeroRow49_checked,
    cutoffTwoSectorLocalZeroRow50_checked,
    cutoffTwoSectorLocalZeroRow51_checked,
    cutoffTwoSectorLocalZeroRow52_checked,
    cutoffTwoSectorLocalZeroRow53_checked,
    cutoffTwoSectorLocalZeroRow54_checked,
    cutoffTwoSectorLocalZeroRow55_checked,
    cutoffTwoSectorLocalZeroRow56_checked,
    cutoffTwoSectorLocalZeroRow57_checked,
    cutoffTwoSectorLocalZeroRow58_checked,
    cutoffTwoSectorLocalZeroRow59_checked,
    cutoffTwoSectorLocalZeroRow60_checked,
    cutoffTwoSectorLocalZeroRow61_checked,
    cutoffTwoSectorLocalZeroRow62_checked,
    cutoffTwoSectorLocalZeroRow63_checked,
    cutoffTwoSectorLocalZeroRow64_checked]
  decide

theorem cutoffTwoSectorLocalZeroRow_compact_checked
    {row : Nat} (hrow : row < 65) :
    cutoffTwoSectorLocalZeroRowCheck row = true := by
  exact List.all_eq_true.mp cutoffTwoSectorLocalZeroRows_compact_checked
    row (List.mem_range.mpr hrow)

theorem cutoffTwoSectorLocalZeroWitness_of_raw_eqv_zero_compact
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65)
    (hzero : cutoffTwoSectorRawKernel row column ≈ 0) :
    cutoffTwoSectorLocalZeroWitness row column ∈
        YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.centralFixedFaceIds 0 ∧
      cutoffTwoSectorIndexPairLocalZeroAtCheck row column
        (cutoffTwoSectorLocalZeroWitness row column) = true :=
  cutoffTwoSectorLocalZeroRowCheck_sound
    (cutoffTwoSectorLocalZeroRow_compact_checked hrow) hcolumn hzero

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_index_eqv_zero_of_raw_compact
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65)
    (hzero : cutoffTwoSectorRawKernel row column ≈ 0) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt row)
      (cutoffTwoSectorLocalZeroStateAt column) ≈ 0 := by
  have hwitness := cutoffTwoSectorLocalZeroWitness_of_raw_eqv_zero_compact
    hrow hcolumn hzero
  exact
    centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_zero_of_local_at_check
      (cutoffTwoSectorLocalZeroStateAt row)
      (cutoffTwoSectorLocalZeroStateAt column)
      (cutoffTwoSectorLocalZeroWitness row column)
      (cutoffTwoSectorLocalZeroStateAt_mem hrow)
      (cutoffTwoSectorLocalZeroStateAt_mem hcolumn)
      hwitness.1 hwitness.2

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassificationCompact

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassificationCompact.cutoffTwoSectorLocalZeroRows_compact_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassificationCompact.centralPhysicalReflectedKernel_cutoffTwo_sector_index_eqv_zero_of_raw_compact

