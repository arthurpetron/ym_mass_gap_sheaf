/- Checked transport of the 44 genuine common factors. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalIdentity (id : Nat) : Nat := id

def cutoffTwoCanonicalCommonTransportCheck : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    cutoffTwoBoundaryHeatFactors cutoffTwoCanonicalBoundaryHeatFactors

def cutoffTwoCanonicalFixedLinkPrefixTransportCheck : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoCubeFixedLinkFactors.take 10)
    (cutoffTwoCanonicalCubeFixedLinkFactors.take 10)

def cutoffTwoCanonicalFixedLinkSuffixTransportCheck : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoCubeFixedLinkFactors.drop 10)
    (cutoffTwoCanonicalCubeFixedLinkFactors.drop 10)

theorem cutoffTwoCanonicalCommonTransportCheck_checked :
    cutoffTwoCanonicalCommonTransportCheck = true := by
  decide

theorem cutoffTwoCanonicalFixedLinkPrefixTransportCheck_checked :
    cutoffTwoCanonicalFixedLinkPrefixTransportCheck = true := by
  decide

theorem cutoffTwoCanonicalFixedLinkSuffixTransportCheck_checked :
    cutoffTwoCanonicalFixedLinkSuffixTransportCheck = true := by
  decide

theorem cutoffTwoCanonicalBoundaryHeatTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalIdentity
      cutoffTwoBoundaryHeatFactors
      cutoffTwoCanonicalBoundaryHeatFactors :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    cutoffTwoBoundaryHeatFactors cutoffTwoCanonicalBoundaryHeatFactors
    cutoffTwoCanonicalCommonTransportCheck_checked

theorem cutoffTwoCanonicalFixedLinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalIdentity
      cutoffTwoCubeFixedLinkFactors
      cutoffTwoCanonicalCubeFixedLinkFactors := by
  have hprefix := factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoCubeFixedLinkFactors.take 10)
    (cutoffTwoCanonicalCubeFixedLinkFactors.take 10)
    cutoffTwoCanonicalFixedLinkPrefixTransportCheck_checked
  have hsuffix := factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoCubeFixedLinkFactors.drop 10)
    (cutoffTwoCanonicalCubeFixedLinkFactors.drop 10)
    cutoffTwoCanonicalFixedLinkSuffixTransportCheck_checked
  simpa only [List.take_append_drop] using
    FactorListTransport.append hprefix hsuffix

theorem cutoffTwoCanonicalCommonTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalIdentity
      (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors)
      cutoffTwoCanonicalCommonFactors :=
  FactorListTransport.append
    cutoffTwoCanonicalBoundaryHeatTransport
    cutoffTwoCanonicalFixedLinkTransport

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport.cutoffTwoCanonicalCommonTransport
