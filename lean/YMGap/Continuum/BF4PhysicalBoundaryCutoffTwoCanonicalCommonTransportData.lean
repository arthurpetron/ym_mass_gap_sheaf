/- Six-factor views of the genuine and canonical common lists. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoCanonicalTransportIdentity (id : Nat) : Nat := id

def cutoffTwoCanonicalCommonSourceRest0 : List ScopedQFactor :=
  cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors

def cutoffTwoCanonicalCommonTargetRest0 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors

def cutoffTwoCanonicalCommonSourceChunk00 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest0.take 3

def cutoffTwoCanonicalCommonTargetChunk00 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest0.take 3

def cutoffTwoCanonicalCommonSourceRest1 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest0.drop 3

def cutoffTwoCanonicalCommonTargetRest1 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest0.drop 3

def cutoffTwoCanonicalCommonSourceChunk01 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest1.take 3

def cutoffTwoCanonicalCommonTargetChunk01 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest1.take 3

def cutoffTwoCanonicalCommonSourceRest2 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest1.drop 3

def cutoffTwoCanonicalCommonTargetRest2 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest1.drop 3

def cutoffTwoCanonicalCommonSourceChunk02 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest2.take 3

def cutoffTwoCanonicalCommonTargetChunk02 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest2.take 3

def cutoffTwoCanonicalCommonSourceRest3 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest2.drop 3

def cutoffTwoCanonicalCommonTargetRest3 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest2.drop 3

def cutoffTwoCanonicalCommonSourceChunk03 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest3.take 3

def cutoffTwoCanonicalCommonTargetChunk03 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest3.take 3

def cutoffTwoCanonicalCommonSourceRest4 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest3.drop 3

def cutoffTwoCanonicalCommonTargetRest4 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest3.drop 3

def cutoffTwoCanonicalCommonSourceChunk04 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest4.take 3

def cutoffTwoCanonicalCommonTargetChunk04 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest4.take 3

def cutoffTwoCanonicalCommonSourceRest5 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest4.drop 3

def cutoffTwoCanonicalCommonTargetRest5 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest4.drop 3

def cutoffTwoCanonicalCommonSourceChunk05 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest5.take 3

def cutoffTwoCanonicalCommonTargetChunk05 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest5.take 3

def cutoffTwoCanonicalCommonSourceRest6 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest5.drop 3

def cutoffTwoCanonicalCommonTargetRest6 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest5.drop 3

def cutoffTwoCanonicalCommonSourceChunk06 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest6.take 3

def cutoffTwoCanonicalCommonTargetChunk06 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest6.take 3

def cutoffTwoCanonicalCommonSourceRest7 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest6.drop 3

def cutoffTwoCanonicalCommonTargetRest7 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest6.drop 3

def cutoffTwoCanonicalCommonSourceChunk07 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest7.take 3

def cutoffTwoCanonicalCommonTargetChunk07 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest7.take 3

def cutoffTwoCanonicalCommonSourceRest8 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest7.drop 3

def cutoffTwoCanonicalCommonTargetRest8 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest7.drop 3

def cutoffTwoCanonicalCommonSourceChunk08 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest8.take 3

def cutoffTwoCanonicalCommonTargetChunk08 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest8.take 3

def cutoffTwoCanonicalCommonSourceRest9 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest8.drop 3

def cutoffTwoCanonicalCommonTargetRest9 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest8.drop 3

def cutoffTwoCanonicalCommonSourceChunk09 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest9.take 3

def cutoffTwoCanonicalCommonTargetChunk09 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest9.take 3

def cutoffTwoCanonicalCommonSourceRest10 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest9.drop 3

def cutoffTwoCanonicalCommonTargetRest10 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest9.drop 3

def cutoffTwoCanonicalCommonSourceChunk10 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest10.take 3

def cutoffTwoCanonicalCommonTargetChunk10 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest10.take 3

def cutoffTwoCanonicalCommonSourceRest11 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest10.drop 3

def cutoffTwoCanonicalCommonTargetRest11 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest10.drop 3

def cutoffTwoCanonicalCommonSourceChunk11 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest11.take 3

def cutoffTwoCanonicalCommonTargetChunk11 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest11.take 3

def cutoffTwoCanonicalCommonSourceRest12 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest11.drop 3

def cutoffTwoCanonicalCommonTargetRest12 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest11.drop 3

def cutoffTwoCanonicalCommonSourceChunk12 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest12.take 3

def cutoffTwoCanonicalCommonTargetChunk12 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest12.take 3

def cutoffTwoCanonicalCommonSourceRest13 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest12.drop 3

def cutoffTwoCanonicalCommonTargetRest13 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest12.drop 3

def cutoffTwoCanonicalCommonSourceChunk13 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest13.take 3

def cutoffTwoCanonicalCommonTargetChunk13 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest13.take 3

def cutoffTwoCanonicalCommonSourceRest14 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest13.drop 3

def cutoffTwoCanonicalCommonTargetRest14 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest13.drop 3

def cutoffTwoCanonicalCommonSourceChunk14 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonSourceRest14

def cutoffTwoCanonicalCommonTargetChunk14 : List ScopedQFactor :=
  cutoffTwoCanonicalCommonTargetRest14

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
