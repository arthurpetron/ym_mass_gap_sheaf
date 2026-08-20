/-
# Exact cutoff-two 65-sector raw physical kernel certificate

All 65 row checks are separate build shards.  The theorem below combines them
without rerunning any entry computation.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row14
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row15
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row16
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row17
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row18
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row19
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row20
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row21
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row22
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row23
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row24
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row25
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row26
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row27
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row28
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row29
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row30
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row31
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row32
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row33
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row34
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row35
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row36
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row37
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row38
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row39
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row40
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row41
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row42
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row43
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row44
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row45
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row46
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row47
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row48
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row49
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row50
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row51
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row52
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row53
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row54
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row55
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row56
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row57
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row58
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row59
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row60
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row61
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row62
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row63
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows.Row64

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoSectorRawKernelRows_checked
    (row : Nat) (hrow : row < 65) :
    cutoffTwoSectorRawKernelRowCheck row = true := by
  have hcases :
      row = 0 ∨
      row = 1 ∨
      row = 2 ∨
      row = 3 ∨
      row = 4 ∨
      row = 5 ∨
      row = 6 ∨
      row = 7 ∨
      row = 8 ∨
      row = 9 ∨
      row = 10 ∨
      row = 11 ∨
      row = 12 ∨
      row = 13 ∨
      row = 14 ∨
      row = 15 ∨
      row = 16 ∨
      row = 17 ∨
      row = 18 ∨
      row = 19 ∨
      row = 20 ∨
      row = 21 ∨
      row = 22 ∨
      row = 23 ∨
      row = 24 ∨
      row = 25 ∨
      row = 26 ∨
      row = 27 ∨
      row = 28 ∨
      row = 29 ∨
      row = 30 ∨
      row = 31 ∨
      row = 32 ∨
      row = 33 ∨
      row = 34 ∨
      row = 35 ∨
      row = 36 ∨
      row = 37 ∨
      row = 38 ∨
      row = 39 ∨
      row = 40 ∨
      row = 41 ∨
      row = 42 ∨
      row = 43 ∨
      row = 44 ∨
      row = 45 ∨
      row = 46 ∨
      row = 47 ∨
      row = 48 ∨
      row = 49 ∨
      row = 50 ∨
      row = 51 ∨
      row = 52 ∨
      row = 53 ∨
      row = 54 ∨
      row = 55 ∨
      row = 56 ∨
      row = 57 ∨
      row = 58 ∨
      row = 59 ∨
      row = 60 ∨
      row = 61 ∨
      row = 62 ∨
      row = 63 ∨
      row = 64 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact cutoffTwoSectorRawKernelRow00_checked | exact cutoffTwoSectorRawKernelRow01_checked | exact cutoffTwoSectorRawKernelRow02_checked | exact cutoffTwoSectorRawKernelRow03_checked | exact cutoffTwoSectorRawKernelRow04_checked | exact cutoffTwoSectorRawKernelRow05_checked | exact cutoffTwoSectorRawKernelRow06_checked | exact cutoffTwoSectorRawKernelRow07_checked | exact cutoffTwoSectorRawKernelRow08_checked | exact cutoffTwoSectorRawKernelRow09_checked | exact cutoffTwoSectorRawKernelRow10_checked | exact cutoffTwoSectorRawKernelRow11_checked | exact cutoffTwoSectorRawKernelRow12_checked | exact cutoffTwoSectorRawKernelRow13_checked | exact cutoffTwoSectorRawKernelRow14_checked | exact cutoffTwoSectorRawKernelRow15_checked | exact cutoffTwoSectorRawKernelRow16_checked | exact cutoffTwoSectorRawKernelRow17_checked | exact cutoffTwoSectorRawKernelRow18_checked | exact cutoffTwoSectorRawKernelRow19_checked | exact cutoffTwoSectorRawKernelRow20_checked | exact cutoffTwoSectorRawKernelRow21_checked | exact cutoffTwoSectorRawKernelRow22_checked | exact cutoffTwoSectorRawKernelRow23_checked | exact cutoffTwoSectorRawKernelRow24_checked | exact cutoffTwoSectorRawKernelRow25_checked | exact cutoffTwoSectorRawKernelRow26_checked | exact cutoffTwoSectorRawKernelRow27_checked | exact cutoffTwoSectorRawKernelRow28_checked | exact cutoffTwoSectorRawKernelRow29_checked | exact cutoffTwoSectorRawKernelRow30_checked | exact cutoffTwoSectorRawKernelRow31_checked | exact cutoffTwoSectorRawKernelRow32_checked | exact cutoffTwoSectorRawKernelRow33_checked | exact cutoffTwoSectorRawKernelRow34_checked | exact cutoffTwoSectorRawKernelRow35_checked | exact cutoffTwoSectorRawKernelRow36_checked | exact cutoffTwoSectorRawKernelRow37_checked | exact cutoffTwoSectorRawKernelRow38_checked | exact cutoffTwoSectorRawKernelRow39_checked | exact cutoffTwoSectorRawKernelRow40_checked | exact cutoffTwoSectorRawKernelRow41_checked | exact cutoffTwoSectorRawKernelRow42_checked | exact cutoffTwoSectorRawKernelRow43_checked | exact cutoffTwoSectorRawKernelRow44_checked | exact cutoffTwoSectorRawKernelRow45_checked | exact cutoffTwoSectorRawKernelRow46_checked | exact cutoffTwoSectorRawKernelRow47_checked | exact cutoffTwoSectorRawKernelRow48_checked | exact cutoffTwoSectorRawKernelRow49_checked | exact cutoffTwoSectorRawKernelRow50_checked | exact cutoffTwoSectorRawKernelRow51_checked | exact cutoffTwoSectorRawKernelRow52_checked | exact cutoffTwoSectorRawKernelRow53_checked | exact cutoffTwoSectorRawKernelRow54_checked | exact cutoffTwoSectorRawKernelRow55_checked | exact cutoffTwoSectorRawKernelRow56_checked | exact cutoffTwoSectorRawKernelRow57_checked | exact cutoffTwoSectorRawKernelRow58_checked | exact cutoffTwoSectorRawKernelRow59_checked | exact cutoffTwoSectorRawKernelRow60_checked | exact cutoffTwoSectorRawKernelRow61_checked | exact cutoffTwoSectorRawKernelRow62_checked | exact cutoffTwoSectorRawKernelRow63_checked | exact cutoffTwoSectorRawKernelRow64_checked

theorem cutoffTwoSectorComputedRawKernel_eqv_raw
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65) :
    cutoffTwoSectorComputedRawKernel row column ≈
      cutoffTwoSectorRawKernel row column :=
  cutoffTwoSectorRawKernelRowCheck_sound
    (cutoffTwoSectorRawKernelRows_checked row hrow) hcolumn

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorComputedRawKernel_eqv_raw
