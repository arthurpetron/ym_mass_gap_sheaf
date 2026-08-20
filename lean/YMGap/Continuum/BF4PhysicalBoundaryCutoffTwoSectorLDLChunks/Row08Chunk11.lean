/- Generated LDL row 8, columns 44..47. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteClearedRationalSumCertificate
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow08Chunk11_checked :
    [44, 45, 46, 47].all (fun column =>
      decide (ClearedSumValid
        (cutoffTwoSectorMeanZeroMatrix 8 column)
        (finiteLDLPrefixTerms cutoffTwoSectorLower
          cutoffTwoSectorDiagonal 8 column)
        (cutoffTwoSectorCommonDenominator 8 column))) = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow08Chunk11_checked
