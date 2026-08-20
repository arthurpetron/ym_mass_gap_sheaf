/- Six-factor views for source state 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Data

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoCanonicalSource01SourceRest0 : List ScopedQFactor :=
  cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1)

def cutoffTwoCanonicalSource01TargetRest0 : List ScopedQFactor :=
  cutoffTwoCanonicalSourceFactorsAt 1

def cutoffTwoCanonicalSource01SourceChunk00 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest0.take 6

def cutoffTwoCanonicalSource01TargetChunk00 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest0.take 6

def cutoffTwoCanonicalSource01SourceRest1 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest0.drop 6

def cutoffTwoCanonicalSource01TargetRest1 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest0.drop 6

def cutoffTwoCanonicalSource01SourceChunk01 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest1.take 6

def cutoffTwoCanonicalSource01TargetChunk01 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest1.take 6

def cutoffTwoCanonicalSource01SourceRest2 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest1.drop 6

def cutoffTwoCanonicalSource01TargetRest2 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest1.drop 6

def cutoffTwoCanonicalSource01SourceChunk02 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest2.take 6

def cutoffTwoCanonicalSource01TargetChunk02 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest2.take 6

def cutoffTwoCanonicalSource01SourceRest3 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest2.drop 6

def cutoffTwoCanonicalSource01TargetRest3 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest2.drop 6

def cutoffTwoCanonicalSource01SourceChunk03 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest3.take 6

def cutoffTwoCanonicalSource01TargetChunk03 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest3.take 6

def cutoffTwoCanonicalSource01SourceRest4 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest3.drop 6

def cutoffTwoCanonicalSource01TargetRest4 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest3.drop 6

def cutoffTwoCanonicalSource01SourceChunk04 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest4.take 6

def cutoffTwoCanonicalSource01TargetChunk04 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest4.take 6

def cutoffTwoCanonicalSource01SourceRest5 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest4.drop 6

def cutoffTwoCanonicalSource01TargetRest5 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest4.drop 6

def cutoffTwoCanonicalSource01SourceChunk05 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest5.take 6

def cutoffTwoCanonicalSource01TargetChunk05 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest5.take 6

def cutoffTwoCanonicalSource01SourceRest6 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest5.drop 6

def cutoffTwoCanonicalSource01TargetRest6 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest5.drop 6

def cutoffTwoCanonicalSource01SourceChunk06 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest6.take 6

def cutoffTwoCanonicalSource01TargetChunk06 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest6.take 6

def cutoffTwoCanonicalSource01SourceRest7 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest6.drop 6

def cutoffTwoCanonicalSource01TargetRest7 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest6.drop 6

def cutoffTwoCanonicalSource01SourceChunk07 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01SourceRest7

def cutoffTwoCanonicalSource01TargetChunk07 : List ScopedQFactor :=
  cutoffTwoCanonicalSource01TargetRest7

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Data
