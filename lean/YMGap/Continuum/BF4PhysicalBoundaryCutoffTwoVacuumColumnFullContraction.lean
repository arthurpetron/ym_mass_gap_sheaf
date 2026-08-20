/-
# Exact full-carrier cutoff-two BF4 vacuum-column contraction

The sparse 72-factor certificate is connected here to the genuine production
BF4 half amplitude.  For every cutoff-two lower-half source, each literal
heat table is matched to the production heat coefficient and each literal
link table is exhaustively matched on its active scope to the production
SU(2) fusion multiplicity.  The generic finite-table soundness theorem then
lifts those local checks to the full 24-coordinate source.

After a kernel-checked change of coordinate order, the complete sum over all
bounded lower-half sources is therefore the exact rational

  281543696188121 / 281474976710656.

This file intentionally states the all-source column first.  Identifying it
with the separately defined retained-positive column requires an additional
support theorem and is not assumed here.  The result is finite at `K = 2`,
half-extent zero, and coupling `1/2`; it makes no cutoff-uniform,
volume-uniform, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnFullContraction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQProduct_append_eqv {A : Type}
    (value : A → Q') : ∀ left right : List A,
    listQProduct value (left ++ right) ≈
      listQProduct value left * listQProduct value right
  | [], right => Q'.eqv_symm (Q'.one_mul_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, listQProduct]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (listQProduct_append_eqv value tail right))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

/-! ## 1. Checked local table equations -/

/-- The direct production heat value read by one lower-face variable. -/
def cutoffTwoDirectHeatValue
    (faceId : Nat) (source : EdgeLabelling) : Q' :=
  coeffW cutoffTwoHalfCoupling (source faceId)

/-- The direct active SU(2) multiplicity read by one lower-link scope. -/
def cutoffTwoDirectLinkValue
    (scope : List Nat) (source : EdgeLabelling) : Q' :=
  Q'.ofNat (cutoffTwoActiveMultiplicity (scope.map source))

/-- Lean evaluates every proposed link table on its complete local carrier.
There are only 48 scopes, each of arity at most four. -/
theorem cutoffTwoVacuumLinkLocalEquations_checked :
    cutoffTwoExpectedActiveLinkFaceIds.all (fun scope =>
      boundedLocalEquationCheck 2 scope
        (scopedTableValue 3 scope
          (cutoffTwoMultiplicityQTable scope.length))
        (cutoffTwoDirectLinkValue scope)) = true := by
  decide

/-- The checked link scopes are duplicate-free. -/
theorem cutoffTwoVacuumLinkScopes_nodup_checked :
    cutoffTwoExpectedActiveLinkFaceIds.all
      (fun scope => decide scope.Nodup) = true := by
  decide

/-- Every active link coordinate is one of the 24 checked lower faces. -/
theorem cutoffTwoVacuumLinkScopes_lower_checked :
    cutoffTwoExpectedActiveLinkFaceIds.all (fun scope =>
      scope.all (fun faceId =>
        decide (faceId ∈ cutoffTwoExpectedLowerFaceIds))) = true := by
  decide

private theorem cutoffTwoDirectLinkValue_local
    (scope : List Nat) (first second : EdgeLabelling)
    (hagree : ∀ id, id ∈ scope → first id = second id) :
    cutoffTwoDirectLinkValue scope first =
      cutoffTwoDirectLinkValue scope second := by
  unfold cutoffTwoDirectLinkValue
  apply congrArg Q'.ofNat
  apply congrArg cutoffTwoActiveMultiplicity
  apply List.map_congr_left
  intro id hid
  exact hagree id hid

/-- One checked literal link table agrees with the corresponding active
production multiplicity on every globally bounded lower-half source. -/
theorem cutoffTwoVacuumLinkTable_eqv_direct
    (scope : List Nat)
    (hscope : scope ∈ cutoffTwoExpectedActiveLinkFaceIds)
    (source : EdgeLabelling)
    (hsource : source ∈
      boundedEdgeLabellings 2 cutoffTwoExpectedLowerFaceIds) :
    scopedTableValue 3 scope
        (cutoffTwoMultiplicityQTable scope.length) source ≈
      cutoffTwoDirectLinkValue scope source := by
  have hcheck := List.all_eq_true.mp
    cutoffTwoVacuumLinkLocalEquations_checked scope hscope
  have hnodup : scope.Nodup := of_decide_eq_true
    (List.all_eq_true.mp cutoffTwoVacuumLinkScopes_nodup_checked
      scope hscope)
  have hscopeLower := List.all_eq_true.mp
    cutoffTwoVacuumLinkScopes_lower_checked scope hscope
  have hsourceSound := boundedEdgeLabellings_sound 2
    cutoffTwoExpectedLowerFaceIds source hsource
  apply localEquation_of_check 2 scope
    (scopedTableValue 3 scope
      (cutoffTwoMultiplicityQTable scope.length))
    (cutoffTwoDirectLinkValue scope)
    hnodup
  · exact (scopedTableFactor 3 scope
      (cutoffTwoMultiplicityQTable scope.length)).local_eq
  · exact cutoffTwoDirectLinkValue_local scope
  · exact hcheck
  · intro id hid
    exact hsourceSound.1 id
      (of_decide_eq_true
        (List.all_eq_true.mp hscopeLower id hid))

private theorem cutoffTwoVacuumHeatTable_eqv_direct
    (faceId : Nat)
    (hface : faceId ∈ cutoffTwoExpectedLowerFaceIds)
    (source : EdgeLabelling)
    (hsource : source ∈
      boundedEdgeLabellings 2 cutoffTwoExpectedLowerFaceIds) :
    scopedTableValue 3 [faceId] cutoffTwoExpectedHeatTable source ≈
      cutoffTwoDirectHeatValue faceId source := by
  have hspin := (boundedEdgeLabellings_sound 2
    cutoffTwoExpectedLowerFaceIds source hsource).1 faceId hface
  unfold cutoffTwoDirectHeatValue scopedTableValue scopedTableIndex
  simp only [List.map_cons, List.map_nil, List.length_nil, Nat.pow_zero,
    Nat.mul_one]
  exact Q'.eqv_symm
    (cutoffTwoHeatFactor_eqv_expected (source faceId) hspin)

/-! ## 2. The table graph is the genuine half amplitude pointwise -/

private theorem cutoffTwoVacuumAssembly_eq_source
    (source : EdgeLabelling)
    (hsource : source ∈
      boundedEdgeLabellings 2 cutoffTwoExpectedLowerFaceIds) :
    assembleReflectedSlabLabelling 0 source zeroEdgeLabelling
        zeroEdgeLabelling = source := by
  have hsourceSound := boundedEdgeLabellings_sound 2
    cutoffTwoExpectedLowerFaceIds source hsource
  funext faceId
  by_cases hphysical : faceId ∈ slabPhysicalFaceEdges 1
  · cases hside : plaquetteHalfSide 0 (slabPlaquetteAt 1 faceId)
    · exact assembleReflectedSlabLabelling_lower hphysical hside
    · rw [assembleReflectedSlabLabelling_fixed hphysical hside]
      exact (hsourceSound.2 faceId (by
        intro hmem
        have hlower : faceId ∈ centralLowerFaceIds 0 := by
          simpa only [cutoffTwoLowerFaceIds_checked] using hmem
        have := (mem_centralLowerFaceIds.mp hlower).2
        change plaquetteHalfSide 0 (slabPlaquetteAt 1 faceId) =
          .lower at this
        rw [hside] at this
        contradiction)).symm
    · rw [assembleReflectedSlabLabelling_upper hphysical hside]
      exact (hsourceSound.2 faceId (by
        intro hmem
        have hlower : faceId ∈ centralLowerFaceIds 0 := by
          simpa only [cutoffTwoLowerFaceIds_checked] using hmem
        have := (mem_centralLowerFaceIds.mp hlower).2
        change plaquetteHalfSide 0 (slabPlaquetteAt 1 faceId) =
          .lower at this
        rw [hside] at this
        contradiction)).symm
  · rw [assembleReflectedSlabLabelling_zero_off_physical
      0 source zeroEdgeLabelling zeroEdgeLabelling hphysical]
    exact (hsourceSound.2 faceId (by
      intro hmem
      have hlower : faceId ∈ centralLowerFaceIds 0 := by
        simpa only [cutoffTwoLowerFaceIds_checked] using hmem
      exact hphysical (mem_centralLowerFaceIds.mp hlower).1)).symm

private theorem cutoffTwoSource_le_two
    (source : EdgeLabelling)
    (hsource : source ∈
      boundedEdgeLabellings 2 cutoffTwoExpectedLowerFaceIds) :
    ∀ faceId, source faceId ≤ 2 := by
  have hsourceSound := boundedEdgeLabellings_sound 2
    cutoffTwoExpectedLowerFaceIds source hsource
  intro faceId
  by_cases hface : faceId ∈ cutoffTwoExpectedLowerFaceIds
  · exact Nat.le_of_lt_succ (hsourceSound.1 faceId hface)
  · rw [hsourceSound.2 faceId hface]
    omega

private theorem cutoffTwoDirectHeat_eqv_physicalFace
    (source : EdgeLabelling)
    (hsource : source ∈
      boundedEdgeLabellings 2 cutoffTwoExpectedLowerFaceIds)
    (faceId : Nat) (hface : faceId ∈ cutoffTwoExpectedLowerFaceIds) :
    cutoffTwoDirectHeatValue faceId source ≈
      centralHalfFaceLocalFactor cutoffTwoHalfCoupling 2 0 source
        zeroEdgeLabelling faceId := by
  have hspin := (boundedEdgeLabellings_sound 2
    cutoffTwoExpectedLowerFaceIds source hsource).1 faceId hface
  unfold cutoffTwoDirectHeatValue centralHalfFaceLocalFactor
  rw [congrFun (cutoffTwoVacuumAssembly_eq_source source hsource) faceId,
    coeffAt_heatKernelPacket hspin]
  exact Q'.eqv_refl _

private theorem cutoffTwoDirectLink_eqv_physicalLink
    (source : EdgeLabelling)
    (hsource : source ∈
      boundedEdgeLabellings 2 cutoffTwoExpectedLowerFaceIds)
    (link : Z4Link) :
    cutoffTwoDirectLinkValue
        (cutoffTwoActiveIncidentFaceIds link) source ≈
      centralHalfLinkLocalFactor 2 0 source zeroEdgeLabelling link := by
  have hsourceSound := boundedEdgeLabellings_sound 2
    cutoffTwoExpectedLowerFaceIds source hsource
  have hproduction := slabExplicitLinkMultiplicity_cutoffTwo_eq_active
    source link (cutoffTwoSource_le_two source hsource) (by
      intro faceId hincident hnotLower
      apply hsourceSound.2 faceId
      intro hmem
      apply hnotLower
      simpa only [cutoffTwoLowerFaceIds_checked] using hmem)
  unfold cutoffTwoDirectLinkValue centralHalfLinkLocalFactor
  rw [cutoffTwoVacuumAssembly_eq_source source hsource]
  exact Q'.eqv_of_eq (congrArg Q'.ofNat hproduction.symm)

/-- For every bounded source, the complete literal 72-factor table graph is
exactly the genuine production source-to-vacuum half amplitude. -/
theorem cutoffTwoVacuumScopedFactorProduct_eqv_halfAmplitude
    (source : EdgeLabelling)
    (hsource : source ∈
      boundedEdgeLabellings 2 cutoffTwoExpectedLowerFaceIds) :
    scopedFactorProduct cutoffTwoVacuumInitialFactors source ≈
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
        zeroEdgeLabelling := by
  let heatValue : Nat → Q' := fun faceId =>
    cutoffTwoDirectHeatValue faceId source
  let linkValue : List Nat → Q' := fun scope =>
    cutoffTwoDirectLinkValue scope source
  have hsplit :
      scopedFactorProduct cutoffTwoVacuumInitialFactors source ≈
        listQProduct
            (fun faceId =>
              (scopedTableFactor 3 [faceId]
                cutoffTwoExpectedHeatTable).value source)
            cutoffTwoExpectedLowerFaceIds *
          listQProduct
            (fun scope =>
              (scopedTableFactor 3 scope
                (cutoffTwoMultiplicityQTable scope.length)).value source)
            cutoffTwoExpectedActiveLinkFaceIds := by
    unfold scopedFactorProduct cutoffTwoVacuumInitialFactors
      cutoffTwoVacuumHeatFactors cutoffTwoVacuumLinkFactors
    refine Q'.eqv_trans _ _ _
      (listQProduct_append_eqv
        (fun factor : ScopedQFactor => factor.value source)
        (cutoffTwoExpectedLowerFaceIds.map fun faceId =>
          scopedTableFactor 3 [faceId] cutoffTwoExpectedHeatTable)
        (cutoffTwoExpectedActiveLinkFaceIds.map fun scope =>
          scopedTableFactor 3 scope
            (cutoffTwoMultiplicityQTable scope.length))) ?_
    rw [listQProduct_map, listQProduct_map]
    exact Q'.eqv_refl _
  have htables :
      listQProduct
          (fun faceId =>
            (scopedTableFactor 3 [faceId]
              cutoffTwoExpectedHeatTable).value source)
          cutoffTwoExpectedLowerFaceIds *
        listQProduct
          (fun scope =>
            (scopedTableFactor 3 scope
              (cutoffTwoMultiplicityQTable scope.length)).value source)
          cutoffTwoExpectedActiveLinkFaceIds ≈
      listQProduct heatValue cutoffTwoExpectedLowerFaceIds *
        listQProduct linkValue cutoffTwoExpectedActiveLinkFaceIds := by
    apply q_mul_congr
    · apply listQProduct_congr_eqv
      intro faceId hface
      exact cutoffTwoVacuumHeatTable_eqv_direct
        faceId hface source hsource
    · apply listQProduct_congr_eqv
      intro scope hscope
      exact cutoffTwoVacuumLinkTable_eqv_direct
        scope hscope source hsource
  have hphysical :
      listQProduct heatValue cutoffTwoExpectedLowerFaceIds *
          listQProduct linkValue cutoffTwoExpectedActiveLinkFaceIds ≈
        centralHalfAmplitudeFactorProduct
          cutoffTwoHalfCoupling 2 0 source zeroEdgeLabelling := by
    unfold centralHalfAmplitudeFactorProduct
    apply q_mul_congr
    · rw [cutoffTwoLowerFaceIds_checked]
      apply listQProduct_congr_eqv
      intro faceId hface
      exact cutoffTwoDirectHeat_eqv_physicalFace
        source hsource faceId hface
    · rw [← cutoffTwoActiveLinkFaceIds_checked]
      unfold cutoffTwoProductionActiveLinkFaceIds
      rw [listQProduct_map]
      apply listQProduct_congr_eqv
      intro link _hlink
      exact cutoffTwoDirectLink_eqv_physicalLink source hsource link
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _ _ _ htables
      (Q'.eqv_trans _ _ _ hphysical
        (Q'.eqv_symm
          (centralHalfAmplitude_eqv_factorProduct
            cutoffTwoHalfCoupling 2 0 source zeroEdgeLabelling))))

/-! ## 3. Exact full-carrier physical column -/

/-- Exact source-to-vacuum mass before the positive-row carrier filter. -/
def cutoffTwoVacuumFullColumnMass : Q' :=
  listQSum
    (fun source =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
        zeroEdgeLabelling)
    (centralHalfStates 2 0)

/-- The genuine complete cutoff-two lower-half source sum is the exact
rational certified by the sparse contraction. -/
theorem cutoffTwoVacuumFullColumnMass_eqv_expected :
    cutoffTwoVacuumFullColumnMass ≈ cutoffTwoVacuumExpectedScalar := by
  unfold cutoffTwoVacuumFullColumnMass centralHalfStates
  rw [cutoffTwoLowerFaceIds_checked]
  refine Q'.eqv_trans _
    (listQSum
      (scopedFactorProduct cutoffTwoVacuumInitialFactors)
      (boundedEdgeLabellings 2 cutoffTwoExpectedLowerFaceIds)) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact Q'.eqv_symm
      (cutoffTwoVacuumScopedFactorProduct_eqv_halfAmplitude
        source hsource)
  · refine Q'.eqv_trans _
      (scopedFactorPartitionSum 2
        cutoffTwoVacuumEliminationFaceOrder
        cutoffTwoVacuumInitialFactors) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_bounded_perm 2
          (scopedFactorProduct cutoffTwoVacuumInitialFactors)
          cutoffTwoVacuumEliminationFaceOrder_perm)
    · exact cutoffTwoVacuumFactorGraphPartitionSum_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnFullContraction

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnFullContraction.cutoffTwoVacuumLinkLocalEquations_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnFullContraction.cutoffTwoVacuumScopedFactorProduct_eqv_halfAmplitude
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnFullContraction.cutoffTwoVacuumFullColumnMass_eqv_expected
