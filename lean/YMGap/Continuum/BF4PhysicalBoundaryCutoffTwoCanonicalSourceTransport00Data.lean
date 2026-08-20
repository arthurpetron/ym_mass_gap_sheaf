/- Six-factor views for source state 0. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoCanonicalSource00SourceRest0 : List ScopedQFactor :=
  cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 0)

def cutoffTwoCanonicalSource00TargetRest0 : List ScopedQFactor :=
  cutoffTwoCanonicalSourceFactorsAt 0

def cutoffTwoCanonicalSource00SourceChunk00 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest0.take 6

def cutoffTwoCanonicalSource00TargetChunk00 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest0.take 6

def cutoffTwoCanonicalSource00SourceRest1 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest0.drop 6

def cutoffTwoCanonicalSource00TargetRest1 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest0.drop 6

def cutoffTwoCanonicalSource00SourceChunk01 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest1.take 6

def cutoffTwoCanonicalSource00TargetChunk01 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest1.take 6

def cutoffTwoCanonicalSource00SourceRest2 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest1.drop 6

def cutoffTwoCanonicalSource00TargetRest2 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest1.drop 6

def cutoffTwoCanonicalSource00SourceChunk02 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest2.take 6

def cutoffTwoCanonicalSource00TargetChunk02 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest2.take 6

def cutoffTwoCanonicalSource00SourceRest3 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest2.drop 6

def cutoffTwoCanonicalSource00TargetRest3 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest2.drop 6

def cutoffTwoCanonicalSource00SourceChunk03 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest3.take 6

def cutoffTwoCanonicalSource00TargetChunk03 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest3.take 6

def cutoffTwoCanonicalSource00SourceRest4 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest3.drop 6

def cutoffTwoCanonicalSource00TargetRest4 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest3.drop 6

def cutoffTwoCanonicalSource00SourceChunk04 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest4.take 6

def cutoffTwoCanonicalSource00TargetChunk04 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest4.take 6

def cutoffTwoCanonicalSource00SourceRest5 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest4.drop 6

def cutoffTwoCanonicalSource00TargetRest5 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest4.drop 6

def cutoffTwoCanonicalSource00SourceChunk05 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest5.take 6

def cutoffTwoCanonicalSource00TargetChunk05 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest5.take 6

def cutoffTwoCanonicalSource00SourceRest6 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest5.drop 6

def cutoffTwoCanonicalSource00TargetRest6 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest5.drop 6

def cutoffTwoCanonicalSource00SourceChunk06 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest6.take 6

def cutoffTwoCanonicalSource00TargetChunk06 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest6.take 6

def cutoffTwoCanonicalSource00SourceRest7 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest6.drop 6

def cutoffTwoCanonicalSource00TargetRest7 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest6.drop 6

def cutoffTwoCanonicalSource00SourceChunk07 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00SourceRest7

def cutoffTwoCanonicalSource00TargetChunk07 : List ScopedQFactor :=
  cutoffTwoCanonicalSource00TargetRest7

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data
