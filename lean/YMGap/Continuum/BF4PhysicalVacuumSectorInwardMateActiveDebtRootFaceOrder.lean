/-
# A root-first physical face order for the active cube debt

The local fusion certificate previously retained only the reordered spin word.
For global strand gluing, equal spin values are not enough: every external
position must still name its literal plaquette face.  This file reruns the
same constructive two-head extraction on the duplicate-free production
incidence list and retains the residual face identifiers as data.

The resulting root-first face order is a permutation of the production order,
is duplicate-free, and maps under the physical labelling to the exact ordered
source spin word already carrying the lifted auxiliary.  Thus the next strand
compiler can work in the root-first presentation without losing observable
face identity.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Retain the root-first order of literal face identifiers -/

def cubeInwardMateLinkFaceOrderCertificate
    (linked : CubeProductionIncidenceMember) :
    Σ' restIds : List Nat,
      (slabIncidentPlaqIds 1 linked.1.link).Perm
        (centralLowerCubeFaceId linked.1.left ::
          centralLowerCubeFaceId linked.1.right :: restIds) :=
  let hgeometry := cubeProductionIncidence_numeric_exact linked.2
  twoHeadPermOfMem hgeometry.1 hgeometry.2.1 hgeometry.2.2.1

def cubeInwardMateLinkRestFaceIds
    (linked : CubeProductionIncidenceMember) : List Nat :=
  (cubeInwardMateLinkFaceOrderCertificate linked).1

def rootOrderedFaceIds
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : List Nat :=
  (leftRootCopy carrier).faceId :: (rightRootCopy carrier).faceId ::
    cubeInwardMateLinkRestFaceIds (cubeDebtRootIncidence carrier.word)

theorem rootProductionFaceIds_perm_orderedFaceIds
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (slabIncidentPlaqIds 1
        (cubeDebtRootIncidence carrier.word).1.link).Perm
      (rootOrderedFaceIds carrier) := by
  simpa [rootOrderedFaceIds] using
    (cubeInwardMateLinkFaceOrderCertificate
      (cubeDebtRootIncidence carrier.word)).2

theorem rootOrderedFaceIds_nodup
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootOrderedFaceIds carrier).Nodup := by
  exact (rootProductionFaceIds_perm_orderedFaceIds carrier).nodup
    (slabIncidentPlaqIds_nodup 1
      (cubeDebtRootIncidence carrier.word).1.link)

/-! ## 2. The face order carries the already accepted spin word -/

theorem cubeInwardMateLinkRest_eq_map_restFaceIds
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    cubeInwardMateLinkRest K physical hK hbounded linked =
      (cubeInwardMateLinkRestFaceIds linked).map physical := by
  rfl

theorem rootOrderedFaceIds_map_eq_orderedSourceSpins
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootOrderedFaceIds carrier).map physical =
      rootOrderedSourceSpins carrier := by
  simp [rootOrderedFaceIds, rootOrderedSourceSpins,
    rootLeftSpin, rootRightSpin,
    cubeInwardMateLinkRest_eq_map_restFaceIds]

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.cubeInwardMateLinkFaceOrderCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.rootProductionFaceIds_perm_orderedFaceIds
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.rootOrderedFaceIds_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.rootOrderedFaceIds_map_eq_orderedSourceSpins
