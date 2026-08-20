/-
# Genuine cutoff-two sector-pair factor graph

This module expresses the physical reflected-kernel integrand for any two
members of the exact 65-state sector as a scalar lower-face heat factor times
a 24-variable scoped factor graph.  The graph consists of

* 24 fixed-face heat factors;
* 20 audited fixed-link multiplicity factors;
* 48 genuine lower-link factors for the left state; and
* 48 genuine lower-link factors for the right state.

The state-dependent lower-link factors retain the production multiplicity as
their value and carry a proof that it depends only on the listed fixed-face
scope.  Consequently an external variable-elimination program may propose
sparse intermediate tables, while Lean checks every local equation against
the genuine production factor.

This is finite cutoff-two, half-extent-zero infrastructure.  It does not yet
certify the 65 by 65 table, a spectral gap, or any uniform/continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQProduct_append_local
    {Item : Type} (value : Item → Q') : ∀ left right,
    listQProduct value (left ++ right) ≈
      listQProduct value left * listQProduct value right
  | [], right => Q'.eqv_symm (Q'.one_mul_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, listQProduct]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (listQProduct_append_local value tail right))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem q_sector_integrand_rearrange
    (heat fixed leftScalar leftLinks rightScalar rightLinks : Q') :
    (heat * fixed) *
        ((leftScalar * leftLinks) * (rightScalar * rightLinks)) ≈
      (leftScalar * rightScalar) *
        ((heat * fixed) * (leftLinks * rightLinks)) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-! ## 1. Scoped genuine factors -/

/-- One genuine fixed-face heat factor with its singleton locality scope. -/
def cutoffTwoBoundaryHeatFactor (faceId : Nat) : ScopedQFactor where
  scope := [faceId]
  value := fun boundary => coeffW cutoffTwoHalfCoupling (boundary faceId)
  local_eq := by
    intro left right hagree
    rw [hagree faceId List.mem_cons_self]

def cutoffTwoBoundaryHeatFactors : List ScopedQFactor :=
  (centralFixedFaceIds 0).map cutoffTwoBoundaryHeatFactor

/-- A genuine production lower-link factor, localized only to the fixed faces
incident to that link.  Lower labels are frozen by `source`; upper labels are
the production vacuum. -/
def cutoffTwoSourceLinkFactor
    (source : EdgeLabelling) (link : Z4Link) : ScopedQFactor where
  scope := cutoffTwoFixedIncidentFaceIds link
  value := fun boundary =>
    centralHalfLinkLocalFactor 2 0 source boundary link
  local_eq := by
    intro left right hagree
    unfold centralHalfLinkLocalFactor
    apply centralHalfLinkLocalFactor_eq_of_incident_eq
    intro id hid
    have hphysical : id ∈ slabPhysicalFaceEdges 1 :=
      slabIncidentPlaqId_physical hid
    cases hside : plaquetteHalfSide 0 (slabPlaquetteAt 1 id)
    · rw [assembleReflectedSlabLabelling_lower hphysical hside,
        assembleReflectedSlabLabelling_lower hphysical hside]
    · rw [assembleReflectedSlabLabelling_fixed hphysical hside,
        assembleReflectedSlabLabelling_fixed hphysical hside]
      apply hagree id
      unfold cutoffTwoFixedIncidentFaceIds
      exact List.mem_filter.mpr
        ⟨hid, by
          have hfixed : id ∈ centralFixedFaceIds 0 :=
            mem_centralFixedFaceIds.mpr ⟨hphysical, hside⟩
          simp [hfixed]⟩
    · rw [assembleReflectedSlabLabelling_upper hphysical hside,
        assembleReflectedSlabLabelling_upper hphysical hside]

def cutoffTwoSourceLinkFactors
    (source : EdgeLabelling) : List ScopedQFactor :=
  (centralLowerLinks 0).map (cutoffTwoSourceLinkFactor source)

/-- The complete 140-factor graph in the same order used by the exact
external contraction. -/
def cutoffTwoSectorPairInterfaceFactors
    (left right : EdgeLabelling) : List ScopedQFactor :=
  cutoffTwoBoundaryHeatFactors ++
    cutoffTwoCubeFixedLinkFactors ++
    cutoffTwoSourceLinkFactors left ++
    cutoffTwoSourceLinkFactors right

theorem cutoffTwoSectorPairInterfaceFactor_count
    (left right : EdgeLabelling) :
    (cutoffTwoSectorPairInterfaceFactors left right).length = 140 := by
  unfold cutoffTwoSectorPairInterfaceFactors
    cutoffTwoBoundaryHeatFactors cutoffTwoCubeFixedLinkFactors
    cutoffTwoSourceLinkFactors
  simp only [List.length_append, List.length_map]
  decide

/-! ## 2. Identification of the two half amplitudes -/

def cutoffTwoLowerFaceScalar (source : EdgeLabelling) : Q' :=
  listQProduct
    (fun faceId => coeffW cutoffTwoHalfCoupling (source faceId))
    (centralLowerFaceIds 0)

theorem cutoffTwoLowerFaceProduct_eqv_scalar
    (source boundary : EdgeLabelling)
    (hsource : source ∈ centralHalfStates 2 0) :
    listQProduct
        (centralHalfFaceLocalFactor cutoffTwoHalfCoupling 2 0
          source boundary)
        (centralLowerFaceIds 0) ≈
      cutoffTwoLowerFaceScalar source := by
  unfold cutoffTwoLowerFaceScalar
  apply listQProduct_congr_eqv
  intro faceId hfaceId
  have hparts := mem_centralLowerFaceIds.mp hfaceId
  have hspin := (boundedEdgeLabellings_sound 2
    (centralLowerFaceIds 0) source hsource).1 faceId hfaceId
  unfold centralHalfFaceLocalFactor
  rw [assembleReflectedSlabLabelling_lower hparts.1 hparts.2,
    coeffAt_heatKernelPacket hspin]
  exact Q'.eqv_refl _

theorem cutoffTwoSourceLinkProduct_eqv_scopedProduct
    (source boundary : EdgeLabelling) :
    listQProduct
        (centralHalfLinkLocalFactor 2 0 source boundary)
        (centralLowerLinks 0) ≈
      scopedFactorProduct (cutoffTwoSourceLinkFactors source) boundary := by
  unfold cutoffTwoSourceLinkFactors scopedFactorProduct
  rw [listQProduct_map]
  exact Q'.eqv_refl _

theorem centralHalfAmplitude_cutoffTwo_sector_eqv_scopedProduct
    (source boundary : EdgeLabelling)
    (hsource : source ∈ centralHalfStates 2 0) :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source boundary ≈
      cutoffTwoLowerFaceScalar source *
        scopedFactorProduct (cutoffTwoSourceLinkFactors source) boundary := by
  refine Q'.eqv_trans _
    (centralHalfAmplitudeFactorProduct cutoffTwoHalfCoupling 2 0
      source boundary) _
    (centralHalfAmplitude_eqv_factorProduct
      cutoffTwoHalfCoupling 2 0 source boundary) ?_
  unfold centralHalfAmplitudeFactorProduct
  exact q_mul_congr
    (cutoffTwoLowerFaceProduct_eqv_scalar source boundary hsource)
    (cutoffTwoSourceLinkProduct_eqv_scopedProduct source boundary)

/-! ## 3. Identification of the complete physical integrand -/

theorem cutoffTwoBoundaryHeatProduct_eqv_scopedProduct
    (boundary : EdgeLabelling) :
    listQProduct (cutoffTwoFixedHeatValue boundary)
        (centralFixedFaceIds 0) ≈
      scopedFactorProduct cutoffTwoBoundaryHeatFactors boundary := by
  unfold cutoffTwoBoundaryHeatFactors scopedFactorProduct
  rw [listQProduct_map]
  exact Q'.eqv_refl _

theorem centralBoundaryWeight_cutoffTwo_eqv_sectorCommonProduct
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0) :
    centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary ≈
      scopedFactorProduct cutoffTwoBoundaryHeatFactors boundary *
        scopedFactorProduct cutoffTwoCubeFixedLinkFactors boundary := by
  have hweight := centralBoundaryWeight_cutoffTwo_eqv_scopedProduct
    boundary hboundary
  have hheat := centralBoundaryFixedFaceFactor_eqv_heatProduct
    boundary hboundary
  exact Q'.eqv_trans _ _ _ hweight
    (q_mul_congr
      (Q'.eqv_trans _ _ _ hheat
        (cutoffTwoBoundaryHeatProduct_eqv_scopedProduct boundary))
      (Q'.eqv_refl _))

/-- Pointwise equality between the genuine physical Gram integrand and the
state-pair factor graph consumed by the exact elimination checker. -/
theorem cutoffTwoSectorPhysicalGramIntegrand_eqv_factorGraph
    (left right boundary : EdgeLabelling)
    (hleft : left ∈ cutoffTwoCubeSectorStates)
    (hright : right ∈ cutoffTwoCubeSectorStates)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0) :
    centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary *
        (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 left boundary *
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0 right boundary) ≈
      (cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right) *
        scopedFactorProduct
          (cutoffTwoSectorPairInterfaceFactors left right) boundary := by
  have hleftState := cutoffTwoCubeSectorState_mem_halfStates hleft
  have hrightState := cutoffTwoCubeSectorState_mem_halfStates hright
  let heat := scopedFactorProduct cutoffTwoBoundaryHeatFactors boundary
  let fixed := scopedFactorProduct cutoffTwoCubeFixedLinkFactors boundary
  let leftScalar := cutoffTwoLowerFaceScalar left
  let leftLinks :=
    scopedFactorProduct (cutoffTwoSourceLinkFactors left) boundary
  let rightScalar := cutoffTwoLowerFaceScalar right
  let rightLinks :=
    scopedFactorProduct (cutoffTwoSourceLinkFactors right) boundary
  have hweight :
      centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary ≈
        heat * fixed :=
    centralBoundaryWeight_cutoffTwo_eqv_sectorCommonProduct
      boundary hboundary
  have hleftAmplitude :
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 left boundary ≈
        leftScalar * leftLinks :=
    centralHalfAmplitude_cutoffTwo_sector_eqv_scopedProduct
      left boundary hleftState
  have hrightAmplitude :
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 right boundary ≈
        rightScalar * rightLinks :=
    centralHalfAmplitude_cutoffTwo_sector_eqv_scopedProduct
      right boundary hrightState
  refine Q'.eqv_trans _
    ((heat * fixed) *
      ((leftScalar * leftLinks) * (rightScalar * rightLinks))) _
    (q_mul_congr hweight
      (q_mul_congr hleftAmplitude hrightAmplitude)) ?_
  refine Q'.eqv_trans _
    ((leftScalar * rightScalar) *
      ((heat * fixed) * (leftLinks * rightLinks))) _
    (q_sector_integrand_rearrange
      heat fixed leftScalar leftLinks rightScalar rightLinks) ?_
  apply Q'.mul_eqv_congr_left
  unfold cutoffTwoSectorPairInterfaceFactors
    heat fixed leftLinks rightLinks
  refine Q'.eqv_trans _
    (scopedFactorProduct
      (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors)
      boundary *
      scopedFactorProduct
        (cutoffTwoSourceLinkFactors left ++
          cutoffTwoSourceLinkFactors right) boundary) _ ?_ ?_
  · exact q_mul_congr
      (Q'.eqv_symm
        (listQProduct_append_local
          (fun factor : ScopedQFactor => factor.value boundary)
          cutoffTwoBoundaryHeatFactors cutoffTwoCubeFixedLinkFactors))
      (Q'.eqv_symm
        (listQProduct_append_local
          (fun factor : ScopedQFactor => factor.value boundary)
          (cutoffTwoSourceLinkFactors left)
          (cutoffTwoSourceLinkFactors right)))
  · exact Q'.eqv_symm
      (listQProduct_append_local
        (fun factor : ScopedQFactor => factor.value boundary)
        (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors)
        (cutoffTwoSourceLinkFactors left ++
          cutoffTwoSourceLinkFactors right))

/-- The genuine production spin-foam summand itself has the same factor graph. -/
theorem cutoffTwoSectorPhysicalTerm_eqv_factorGraph
    (left right boundary : EdgeLabelling)
    (hleft : left ∈ cutoffTwoCubeSectorStates)
    (hright : right ∈ cutoffTwoCubeSectorStates)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0) :
    slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        (assembleReflectedSlabLabelling 0 left boundary right) ≈
      (cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right) *
        scopedFactorProduct
          (cutoffTwoSectorPairInterfaceFactors left right) boundary := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalTerm_eq_gram_integrand cutoffTwoHalfCoupling
      (cutoffTwoCubeSectorState_mem_halfStates hleft) hboundary
      (cutoffTwoCubeSectorState_mem_halfStates hright))
    (cutoffTwoSectorPhysicalGramIntegrand_eqv_factorGraph
      left right boundary hleft hright hboundary)

/-- The complete genuine physical kernel entry is the lower-face scalar pair
times the exact fixed-interface partition sum of the 140-factor graph. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
    (left right : EdgeLabelling)
    (hleft : left ∈ cutoffTwoCubeSectorStates)
    (hright : right ∈ cutoffTwoCubeSectorStates) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0 left right ≈
      (cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right) *
        scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
          (cutoffTwoSectorPairInterfaceFactors left right) := by
  unfold centralPhysicalReflectedKernel centralBoundaryChannels
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        (cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right) *
          scopedFactorProduct
            (cutoffTwoSectorPairInterfaceFactors left right) boundary)
      (boundedEdgeLabellings 2 (centralFixedFaceIds 0))) _ ?_ ?_
  · apply listQSum_congr_on
    intro boundary hboundary
    exact cutoffTwoSectorPhysicalTerm_eqv_factorGraph
      left right boundary hleft hright hboundary
  · exact Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right)
        (scopedFactorProduct
          (cutoffTwoSectorPairInterfaceFactors left right))
        (boundedEdgeLabellings 2 (centralFixedFaceIds 0)))
      (Q'.eqv_refl _)

theorem cutoffTwoLowerFaceScalar_cube_eqv :
    cutoffTwoLowerFaceScalar centralLowerCubeState ≈
      (Q'.mkPos 1 4096 (by decide) : Q') := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph.centralHalfAmplitude_cutoffTwo_sector_eqv_scopedProduct
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph.cutoffTwoSectorPhysicalGramIntegrand_eqv_factorGraph
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph.cutoffTwoSectorPhysicalTerm_eqv_factorGraph
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph.centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph.cutoffTwoLowerFaceScalar_cube_eqv
