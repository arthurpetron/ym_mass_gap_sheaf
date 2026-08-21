/- Exact Boolean row-sum check for the cutoff-two 65-state table. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSectorRawRowSumCheck (row : Nat) : Bool :=
  decide
    (listQSum (cutoffTwoSectorRawKernel row) (List.range 65) ≈
      cutoffTwoSectorRawRowSum row)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck
