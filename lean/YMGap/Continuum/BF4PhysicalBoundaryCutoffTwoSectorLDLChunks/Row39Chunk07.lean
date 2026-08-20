/- Generated LDL row 39, columns 28..31. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.FiniteClearedRationalSumCertificate
open YMGap.Continuum.FiniteRationalLDLCertificate

theorem cutoffTwoSectorLDLRow39Chunk07_checked :
    [28, 29, 30, 31].all (fun column =>
      decide (ClearedSumValid
        (cutoffTwoSectorMeanZeroMatrix 39 column)
        (finiteLDLPrefixTerms cutoffTwoSectorLower
          cutoffTwoSectorDiagonal 39 column)
        (cutoffTwoSectorCommonDenominator 39 column))) = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate.cutoffTwoSectorLDLRow39Chunk07_checked
