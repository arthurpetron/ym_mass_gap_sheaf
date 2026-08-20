/- Generated LDL row 34, columns 4..7. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteClearedRationalSumCertificate
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow34Chunk01_checked :
    [4, 5, 6, 7].all (fun column =>
      decide (ClearedSumValid
        (cutoffTwoSectorMeanZeroMatrix 34 column)
        (finiteLDLPrefixTerms cutoffTwoSectorLower
          cutoffTwoSectorDiagonal 34 column)
        (cutoffTwoSectorCommonDenominator 34 column))) = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow34Chunk01_checked
