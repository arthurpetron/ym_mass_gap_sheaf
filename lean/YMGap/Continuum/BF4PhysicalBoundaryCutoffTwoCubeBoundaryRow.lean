/-
# Exact cutoff-two lower-cube boundary row

For the six-face fundamental lower-cube source, every production lower link
meets at most one of the 24 fixed-interface faces.  Lean evaluates the local
SU(2) factors directly: twelve fixed coordinates have ternary table
`[1, 0, 1]`, while the other twelve have `[1, 0, 0]`.  The link factor graph
is therefore unary and has exactly `2^12` nonzero boundary words.

At coupling one half the six source heat factors multiply to `1 / 4096`, so
the complete genuine half-amplitude boundary-row mass is exactly one.  The
external 16-process scout only proposed the sparse pattern; all geometry,
locality, table equations, and the final contraction are checked here from
the production definitions.

This is finite `K = 2`, half extent zero data.  It is not yet a statement
about the complete reflected Gram row, an invariant block, a spectral gap,
cutoff or volume uniformity, or the continuum limit.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
import YMGap.Continuum.FiniteScopedFactorTableCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationTrace
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
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

private theorem eliminateLinks_congr_on
    (left right : Nat → Q') : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl _
  | id :: rest, hagree =>
      q_mul_congr
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

private theorem ofNat_natListProduct_eqv_listQProduct
    {Item : Type} (value : Item → Nat) : ∀ items : List Item,
    Q'.ofNat (natListProduct value items) ≈
      listQProduct (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [natListProduct, listQProduct]
      exact Q'.eqv_trans _ _ _
        (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv
          (value head) (natListProduct value tail))
        (Q'.mul_eqv_congr_left _ _ _
          (ofNat_natListProduct_eqv_listQProduct value tail))

/-! ## 1. Unary fixed-interface factor graph -/

/-- Fixed-interface incident coordinates of one lower link. -/
def cutoffTwoCubeFixedIncidentFaceIds (link : Z4Link) : List Nat :=
  (slabIncidentPlaqIds 1 link).filter fun faceId =>
    decide (faceId ∈ centralFixedFaceIds 0)

/-- The fixed-interface scopes in production lower-link order. -/
def cutoffTwoCubeProductionFixedScopes : List (List Nat) :=
  (centralLowerLinks 0).map cutoffTwoCubeFixedIncidentFaceIds

/-- Literal unary-or-empty scope list emitted by the external scout. -/
def cutoffTwoCubeExpectedFixedScopes : List (List Nat) :=
  [[2], [4], [20], [40], [5], [11], [41], [13], [23], [29], [49],
   [14], [], [50], [], [32], [22], [], [58], [59], [31], [], [], [67],
   [], [68], [], [], [38], [56], [], [47], [], [65], [], [], [], [],
   [], [], [], [], [], [], [], [], [], []]

/-- The twelve fixed faces on the temporal continuation of a cube edge. -/
def cutoffTwoCubeActiveFixedFaceIds : List Nat :=
  [2, 4, 5, 11, 13, 20, 23, 29, 40, 41, 49, 59]

theorem cutoffTwoCubeFixedScopes_checked :
    cutoffTwoCubeProductionFixedScopes =
      cutoffTwoCubeExpectedFixedScopes := by
  decide

theorem cutoffTwoCubeFixedScopes_unary_checked :
    cutoffTwoCubeExpectedFixedScopes.all
      (fun scope => decide (scope.length ≤ 1)) = true := by
  decide

private theorem cubeBoundaryLinkLocality
    (link : Z4Link) (left right : EdgeLabelling)
    (hagree : ∀ id, id ∈ cutoffTwoCubeFixedIncidentFaceIds link →
      left id = right id) :
    centralHalfLinkLocalFactor 2 0 centralLowerCubeState left link =
      centralHalfLinkLocalFactor 2 0 centralLowerCubeState right link := by
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
    unfold cutoffTwoCubeFixedIncidentFaceIds
    exact List.mem_filter.mpr
      ⟨hid, by
        have hfixed : id ∈ centralFixedFaceIds 0 :=
          mem_centralFixedFaceIds.mpr ⟨hphysical, hside⟩
        simp [hfixed]⟩
  · rw [assembleReflectedSlabLabelling_upper hphysical hside,
      assembleReflectedSlabLabelling_upper hphysical hside]

/-- Literal table proposed for one unary-or-empty production scope. -/
def cutoffTwoCubeExpectedLinkTable (link : Z4Link) : List Q' :=
  match cutoffTwoCubeFixedIncidentFaceIds link with
  | [] => [(1 : Q')]
  | faceId :: _ =>
      if faceId ∈ cutoffTwoCubeActiveFixedFaceIds then
        [(1 : Q'), 0, 1]
      else
        [(1 : Q'), 0, 0]

/-- One literal table factor for every production lower link. -/
def cutoffTwoCubeLinkTableFactor (link : Z4Link) : ScopedQFactor :=
  scopedTableFactor 3 (cutoffTwoCubeFixedIncidentFaceIds link)
    (cutoffTwoCubeExpectedLinkTable link)

/-- Complete 48-table fixed-interface graph for the cube half amplitude. -/
def cutoffTwoCubeBoundaryLinkFactors : List ScopedQFactor :=
  (centralLowerLinks 0).map cutoffTwoCubeLinkTableFactor

theorem cutoffTwoCubeBoundaryLinkFactor_count :
    cutoffTwoCubeBoundaryLinkFactors.length = 48 := by
  decide

/-- Each proposed table is exhaustively compared with the corresponding
production link multiplicity on its complete scope of at most one ternary
coordinate. -/
theorem cutoffTwoCubeLinkLocalEquations_checked :
    ((centralLowerLinks 0).all fun link =>
      boundedLocalEquationCheck 2
          (cutoffTwoCubeFixedIncidentFaceIds link)
          (cutoffTwoCubeLinkTableFactor link).value
          (fun boundary =>
            centralHalfLinkLocalFactor 2 0 centralLowerCubeState boundary link))
      = true := by
  decide

private theorem cutoffTwoCubeLinkTable_eqv_direct
    (link : Z4Link) (hlink : link ∈ centralLowerLinks 0)
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    (cutoffTwoCubeLinkTableFactor link).value boundary ≈
      centralHalfLinkLocalFactor 2 0 centralLowerCubeState boundary link := by
  apply localEquation_of_check 2
    (cutoffTwoCubeFixedIncidentFaceIds link)
    (cutoffTwoCubeLinkTableFactor link).value
    (fun candidate =>
      centralHalfLinkLocalFactor 2 0 centralLowerCubeState candidate link)
  · unfold cutoffTwoCubeFixedIncidentFaceIds
    exact (slabIncidentPlaqIds_nodup 1 link).filter _
  · exact (cutoffTwoCubeLinkTableFactor link).local_eq
  · exact cubeBoundaryLinkLocality link
  · exact List.all_eq_true.mp cutoffTwoCubeLinkLocalEquations_checked
      link hlink
  · intro id hid
    have hfixed : id ∈ centralFixedFaceIds 0 := by
      have hparts := List.mem_filter.mp hid
      exact of_decide_eq_true hparts.2
    exact (boundedEdgeLabellings_sound 2 (centralFixedFaceIds 0)
      boundary hboundary).1 id hfixed

/-! ## 2. Kernel-computed local tables and contraction -/

/-- The generic checker computes all 24 unary eliminations from the actual
production link factors. -/
def cutoffTwoCubeBoundaryTraceOption :=
  checkedComputedEliminationTrace? 2 (centralFixedFaceIds 0)
    (centralFixedFaceIds 0) cutoffTwoCubeBoundaryLinkFactors

theorem cutoffTwoCubeBoundaryTraceOption_isSome :
    cutoffTwoCubeBoundaryTraceOption.isSome = true := by
  decide

/-- Proof-carrying exact unary elimination trace. -/
def cutoffTwoCubeBoundaryTrace :
    CheckedScopedEliminationTrace 2 (centralFixedFaceIds 0)
      cutoffTwoCubeBoundaryLinkFactors :=
  cutoffTwoCubeBoundaryTraceOption.get
    cutoffTwoCubeBoundaryTraceOption_isSome

theorem cutoffTwoCubeBoundaryTrace_bottom_eqv :
    cutoffTwoCubeBoundaryTrace.bottomValue ≈ (4096 : Q') := by
  decide

theorem cutoffTwoCubeBoundaryLinkPartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCubeBoundaryLinkFactors ≈
      (4096 : Q') := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoCubeBoundaryTrace.partitionSum_eqv_bottom
    cutoffTwoCubeBoundaryTrace_bottom_eqv

/-! ## 3. Identification with the genuine half amplitude -/

theorem centralLowerCube_lowerFaceFactor_cutoffTwo_eqv
    (boundary : EdgeLabelling) :
    slabFaceFactorOn cutoffTwoHalfCoupling 2
        (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
          zeroEdgeLabelling)
        (centralLowerFaceIds 0) ≈
      (Q'.mkPos 1 4096 (by decide) : Q') := by
  let cubePhysical := assembleReflectedSlabLabelling 0
    centralLowerCubeState boundary zeroEdgeLabelling
  have hcompare :
      slabFaceFactorOn cutoffTwoHalfCoupling 2 cubePhysical
          (centralLowerFaceIds 0) ≈
        slabFaceFactorOn cutoffTwoHalfCoupling 1 centralLowerCubePhysical
          (centralLowerFaceIds 0) := by
    unfold slabFaceFactorOn
    apply eliminateLinks_congr_on
    intro id hid
    have hparts := mem_centralLowerFaceIds.mp hid
    have hvalue : cubePhysical id = centralLowerCubeState id := by
      exact assembleReflectedSlabLabelling_lower hparts.1 hparts.2
    have hcentral : centralLowerCubePhysical id = centralLowerCubeState id := by
      unfold centralLowerCubePhysical
      exact assembleReflectedSlabLabelling_lower hparts.1 hparts.2
    have hbound := centralLowerCubeState_le_one id
    rw [hvalue, hcentral,
      coeffAt_heatKernelPacket (by omega : centralLowerCubeState id < 3),
      coeffAt_heatKernelPacket (by omega : centralLowerCubeState id < 2)]
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hcompare
    (Q'.eqv_trans _ _ _
      (centralLowerCube_lowerFaceFactor_eqv cutoffTwoHalfCoupling)
      (by decide))

theorem cutoffTwoCubeLinkProduct_eqv_scopedProduct
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    Q'.ofNat
        (slabLinkMultiplicityProductOn 2 1
          (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
            zeroEdgeLabelling)
          (centralLowerLinks 0)) ≈
      scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors boundary := by
  refine Q'.eqv_trans _
    (listQProduct
      (fun link =>
        Q'.ofNat
          (slabExplicitLinkMultiplicity 2 1
            (assembleReflectedSlabLabelling 0 centralLowerCubeState boundary
              zeroEdgeLabelling) link))
      (centralLowerLinks 0)) _ ?_ ?_
  · unfold slabLinkMultiplicityProductOn
    exact ofNat_natListProduct_eqv_listQProduct _ _
  · unfold scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors
    rw [listQProduct_map]
    apply listQProduct_congr_eqv
    intro link hlink
    exact Q'.eqv_symm
      (cutoffTwoCubeLinkTable_eqv_direct link hlink boundary hboundary)

theorem centralHalfAmplitude_cutoffTwo_cube_eqv_factorProduct
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerCubeState boundary ≈
      (Q'.mkPos 1 4096 (by decide) : Q') *
        scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors boundary := by
  unfold centralHalfAmplitude centralLowerFactor
  exact q_mul_congr
    (centralLowerCube_lowerFaceFactor_cutoffTwo_eqv boundary)
    (cutoffTwoCubeLinkProduct_eqv_scopedProduct boundary hboundary)

/-- The complete genuine cutoff-two cube boundary row has exact mass one. -/
theorem centralHalfAmplitudeBoundaryRowMass_cutoffTwo_cube_eqv_one :
    centralHalfAmplitudeBoundaryRowMass cutoffTwoHalfCoupling 2 0
        centralLowerCubeState ≈ 1 := by
  unfold centralHalfAmplitudeBoundaryRowMass centralBoundaryChannels
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        (Q'.mkPos 1 4096 (by decide) : Q') *
          scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors boundary)
      (boundedEdgeLabellings 2 (centralFixedFaceIds 0))) _ ?_ ?_
  · apply listQSum_congr_on
    intro boundary hboundary
    exact centralHalfAmplitude_cutoffTwo_cube_eqv_factorProduct
      boundary hboundary
  refine Q'.eqv_trans _
    ((Q'.mkPos 1 4096 (by decide) : Q') *
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCubeBoundaryLinkFactors) _ ?_ ?_
  · exact listQSum_mul_left
      (Q'.mkPos 1 4096 (by decide) : Q')
      (scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors)
      (boundedEdgeLabellings 2 (centralFixedFaceIds 0))
  · exact Q'.eqv_trans _
      ((Q'.mkPos 1 4096 (by decide) : Q') * (4096 : Q')) _
      (Q'.mul_eqv_congr_left _ _ _
        cutoffTwoCubeBoundaryLinkPartitionSum_eqv)
      (by decide)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow.cutoffTwoCubeFixedScopes_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow.cutoffTwoCubeBoundaryLinkPartitionSum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow.centralHalfAmplitude_cutoffTwo_cube_eqv_factorProduct
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow.centralHalfAmplitudeBoundaryRowMass_cutoffTwo_cube_eqv_one
