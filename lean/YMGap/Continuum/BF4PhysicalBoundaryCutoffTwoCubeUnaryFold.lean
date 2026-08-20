/-
# Exact unary fold for the cutoff-two cube Gram integrand

For each fixed face, the genuine heat coefficient is multiplied by two
copies of the lower-cube support mask.  This module proves that their product
is exactly the unary table used by the sparse interface contraction:
`[1,0,3/256]` on the twelve active coordinates and `[1,0,0]` elsewhere.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFixedLinkBridge

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
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

private theorem listQProduct_pointwise_mul_local
    {Item : Type} (left right : Item → Q') : ∀ items,
    listQProduct (fun item => left item * right item) items ≈
      listQProduct left items * listQProduct right items
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | head :: tail => by
      simp only [listQProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (listQProduct_pointwise_mul_local left right tail)) ?_
      exact YMGap.Continuum.RingNormaliser.q_mul4_swap
        (left head) (right head)
        (listQProduct left tail) (listQProduct right tail)

private theorem listQProduct_pointwise_triple_local
    {Item : Type} (first second third : Item → Q') (items : List Item) :
    listQProduct
        (fun item => (first item * second item) * third item) items ≈
      (listQProduct first items * listQProduct second items) *
        listQProduct third items := by
  exact Q'.eqv_trans _ _ _
    (listQProduct_pointwise_mul_local
      (fun item => first item * second item) third items)
    (Q'.mul_eqv_congr_right _ _ _
      (listQProduct_pointwise_mul_local first second items))

/-! ## 1. One-face support and unary fold -/

def cutoffTwoCubeSupportUnaryTable (faceId : Nat) : List Q' :=
  if faceId ∈ cutoffTwoCubeActiveFixedFaceIds then
    [(1 : Q'), 0, 1]
  else
    [(1 : Q'), 0, 0]

def cutoffTwoCubeSupportValue
    (boundary : EdgeLabelling) (faceId : Nat) : Q' :=
  scopedTableValue 3 [faceId]
    (cutoffTwoCubeSupportUnaryTable faceId) boundary

def cutoffTwoFixedHeatValue
    (boundary : EdgeLabelling) (faceId : Nat) : Q' :=
  coeffW cutoffTwoHalfCoupling (boundary faceId)

theorem cutoffTwoCubeInterfaceUnary_eqv_heat_support_square
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0))
    (faceId : Nat) (hfaceId : faceId ∈ centralFixedFaceIds 0) :
    (scopedTableFactor 3 [faceId]
        (cutoffTwoCubeInterfaceUnaryTable faceId)).value boundary ≈
      (cutoffTwoFixedHeatValue boundary faceId *
        cutoffTwoCubeSupportValue boundary faceId) *
          cutoffTwoCubeSupportValue boundary faceId := by
  have hspin := (boundedEdgeLabellings_sound 2
    (centralFixedFaceIds 0) boundary hboundary).1 faceId hfaceId
  have hcases : boundary faceId = 0 ∨ boundary faceId = 1 ∨
      boundary faceId = 2 := by omega
  change scopedTableValue 3 [faceId]
      (cutoffTwoCubeInterfaceUnaryTable faceId) boundary ≈
    (coeffW cutoffTwoHalfCoupling (boundary faceId) *
      scopedTableValue 3 [faceId]
        (cutoffTwoCubeSupportUnaryTable faceId) boundary) *
      scopedTableValue 3 [faceId]
        (cutoffTwoCubeSupportUnaryTable faceId) boundary
  unfold scopedTableValue scopedTableIndex
  rcases hcases with hzero | hone | htwo
  · rw [hzero]
    by_cases hactive : faceId ∈ cutoffTwoCubeActiveFixedFaceIds
    · simp [cutoffTwoCubeInterfaceUnaryTable,
        cutoffTwoCubeSupportUnaryTable, cutoffTwoCubeSupportValue,
        cutoffTwoFixedHeatValue, scopedTableFactor, scopedTableValue,
        scopedTableIndex, hactive, hzero]
      rw [coeffW_zero]
      decide
    · simp [cutoffTwoCubeInterfaceUnaryTable,
        cutoffTwoCubeSupportUnaryTable, cutoffTwoCubeSupportValue,
        cutoffTwoFixedHeatValue, scopedTableFactor, scopedTableValue,
        scopedTableIndex, hactive, hzero]
      rw [coeffW_zero]
      decide
  · rw [hone]
    by_cases hactive : faceId ∈ cutoffTwoCubeActiveFixedFaceIds
    · simp [cutoffTwoCubeInterfaceUnaryTable,
        cutoffTwoCubeSupportUnaryTable, cutoffTwoCubeSupportValue,
        cutoffTwoFixedHeatValue, scopedTableFactor, scopedTableValue,
        scopedTableIndex, hactive, hone]
      decide
    · simp [cutoffTwoCubeInterfaceUnaryTable,
        cutoffTwoCubeSupportUnaryTable, cutoffTwoCubeSupportValue,
        cutoffTwoFixedHeatValue, scopedTableFactor, scopedTableValue,
        scopedTableIndex, hactive, hone]
      decide
  · rw [htwo]
    by_cases hactive : faceId ∈ cutoffTwoCubeActiveFixedFaceIds
    · simp [cutoffTwoCubeInterfaceUnaryTable,
        cutoffTwoCubeSupportUnaryTable, cutoffTwoCubeSupportValue,
        cutoffTwoFixedHeatValue, scopedTableFactor, scopedTableValue,
        scopedTableIndex, hactive, htwo]
      decide
    · simp [cutoffTwoCubeInterfaceUnaryTable,
        cutoffTwoCubeSupportUnaryTable, cutoffTwoCubeSupportValue,
        cutoffTwoFixedHeatValue, scopedTableFactor, scopedTableValue,
        scopedTableIndex, hactive, htwo]
      decide

/-! ## 2. The 48 lower-link masks reduce to 24 face masks -/

def cutoffTwoCubeSupportScopeTable (scope : List Nat) : List Q' :=
  match scope with
  | [] => [(1 : Q')]
  | faceId :: _ => cutoffTwoCubeSupportUnaryTable faceId

def cutoffTwoCubeSupportScopeFactor (scope : List Nat) : ScopedQFactor :=
  scopedTableFactor 3 scope (cutoffTwoCubeSupportScopeTable scope)

def cutoffTwoCubeSupportScopeValue
    (boundary : EdgeLabelling) (scope : List Nat) : Q' :=
  (cutoffTwoCubeSupportScopeFactor scope).value boundary

theorem cutoffTwoCubeBoundaryLinkFactors_eq_scopeMap :
    cutoffTwoCubeBoundaryLinkFactors =
      cutoffTwoCubeProductionFixedScopes.map
        cutoffTwoCubeSupportScopeFactor := by
  unfold cutoffTwoCubeBoundaryLinkFactors cutoffTwoCubeProductionFixedScopes
  rw [List.map_map]
  apply List.map_congr_left
  intro link _
  rfl

def cutoffTwoCubeExpectedSingletonFaceIds : List Nat :=
  [2, 4, 20, 40, 5, 11, 41, 13, 23, 29, 49, 14,
   50, 32, 22, 58, 59, 31, 67, 68, 38, 56, 47, 65]

theorem cutoffTwoCubeExpectedScopes_filter_nonempty :
    cutoffTwoCubeExpectedFixedScopes.filter
        (fun scope => !scope.isEmpty) =
      cutoffTwoCubeExpectedSingletonFaceIds.map
        (fun faceId => [faceId]) := by
  decide

theorem cutoffTwoCubeExpectedSingletonProduct_eqv
    (value : Nat → Q') :
    listQProduct value cutoffTwoCubeExpectedSingletonFaceIds ≈
      listQProduct value (centralFixedFaceIds 0) := by
  rw [cutoffTwoFixedFaceIds_checked]
  unfold cutoffTwoCubeExpectedSingletonFaceIds
    cutoffTwoExpectedFixedFaceIds
  simp only [listQProduct]
  show _ = _
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

private theorem listQProduct_filter_vacuum
    {Item : Type} (value : Item → Q') (keep : Item → Bool) :
    ∀ items,
      (∀ item, item ∈ items → keep item = false → value item ≈ 1) →
      listQProduct value items ≈
        listQProduct value (items.filter keep)
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hvacuum => by
      have htail := listQProduct_filter_vacuum value keep tail
        (fun item hitem =>
          hvacuum item (List.mem_cons_of_mem head hitem))
      by_cases hkeep : keep head = true
      · simp only [listQProduct, List.filter_cons_of_pos hkeep]
        exact Q'.mul_eqv_congr_left _ _ _ htail
      · have hfalse : keep head = false := by
          cases hvalue : keep head <;> simp_all
        simp only [listQProduct, List.filter_cons_of_neg hkeep]
        refine Q'.eqv_trans _
          ((1 : Q') * listQProduct value tail) _
          (q_mul_congr
            (hvacuum head List.mem_cons_self hfalse)
            (Q'.eqv_refl _)) ?_
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ htail)
          (Q'.one_mul_eqv _)

theorem cutoffTwoCubeBoundaryLinkProduct_eqv_supportProduct
    (boundary : EdgeLabelling) :
    scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors boundary ≈
      listQProduct (cutoffTwoCubeSupportValue boundary)
        (centralFixedFaceIds 0) := by
  unfold scopedFactorProduct
  rw [cutoffTwoCubeBoundaryLinkFactors_eq_scopeMap,
    listQProduct_map, cutoffTwoCubeFixedScopes_checked]
  refine Q'.eqv_trans _
    (listQProduct (cutoffTwoCubeSupportScopeValue boundary)
      (cutoffTwoCubeExpectedFixedScopes.filter
        (fun scope => !scope.isEmpty))) _ ?_ ?_
  · apply listQProduct_filter_vacuum
    intro scope _ hscope
    have hempty : scope = [] := by
      cases scope with
      | nil => rfl
      | cons head tail => simp at hscope
    subst scope
    exact Q'.eqv_refl 1
  rw [cutoffTwoCubeExpectedScopes_filter_nonempty]
  refine Q'.eqv_trans _
    (listQProduct (cutoffTwoCubeSupportValue boundary)
      cutoffTwoCubeExpectedSingletonFaceIds) _ ?_ ?_
  · exact Q'.eqv_of_eq (by
      rw [listQProduct_map]
      rfl)
  refine Q'.eqv_trans _
    (listQProduct (cutoffTwoCubeSupportValue boundary)
      (centralFixedFaceIds 0)) _
    (cutoffTwoCubeExpectedSingletonProduct_eqv _)
    (Q'.eqv_refl _)

/-! ## 3. Complete fixed-face fold -/

theorem centralBoundaryFixedFaceFactor_eqv_heatProduct
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    slabFaceFactorOn cutoffTwoHalfCoupling 2
        (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
          zeroEdgeLabelling)
        (centralFixedFaceIds 0) ≈
      listQProduct (cutoffTwoFixedHeatValue boundary)
        (centralFixedFaceIds 0) := by
  unfold slabFaceFactorOn
  rw [eliminateLinks_eq_listQProduct]
  apply listQProduct_congr_eqv
  intro faceId hfaceId
  have hparts := mem_centralFixedFaceIds.mp hfaceId
  have hspin := (boundedEdgeLabellings_sound 2
    (centralFixedFaceIds 0) boundary hboundary).1 faceId hfaceId
  rw [assembleReflectedSlabLabelling_fixed hparts.1 hparts.2,
    coeffAt_heatKernelPacket hspin]
  exact Q'.eqv_refl _

theorem cutoffTwoCubeFixedFaceAndSupport_eqv_unaryProduct
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈
      boundedEdgeLabellings 2 (centralFixedFaceIds 0)) :
    slabFaceFactorOn cutoffTwoHalfCoupling 2
        (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
          zeroEdgeLabelling)
        (centralFixedFaceIds 0) *
      (scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors boundary *
        scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors boundary) ≈
      scopedFactorProduct cutoffTwoCubeInterfaceUnaryFactors boundary := by
  let ids := centralFixedFaceIds 0
  let heat := cutoffTwoFixedHeatValue boundary
  let support := cutoffTwoCubeSupportValue boundary
  have hphysical :
      slabFaceFactorOn cutoffTwoHalfCoupling 2
          (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary
            zeroEdgeLabelling) ids ≈
        listQProduct heat ids :=
    centralBoundaryFixedFaceFactor_eqv_heatProduct boundary hboundary
  have hsupport :
      scopedFactorProduct cutoffTwoCubeBoundaryLinkFactors boundary ≈
        listQProduct support ids :=
    cutoffTwoCubeBoundaryLinkProduct_eqv_supportProduct boundary
  refine Q'.eqv_trans _
    (listQProduct heat ids *
      (listQProduct support ids * listQProduct support ids)) _
    (q_mul_congr hphysical (q_mul_congr hsupport hsupport)) ?_
  refine Q'.eqv_trans _
    ((listQProduct heat ids * listQProduct support ids) *
      listQProduct support ids) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (listQProduct (fun faceId =>
      (heat faceId * support faceId) * support faceId) ids) _
    (Q'.eqv_symm
      (listQProduct_pointwise_triple_local heat support support ids)) ?_
  unfold cutoffTwoCubeInterfaceUnaryFactors scopedFactorProduct
  rw [listQProduct_map]
  apply listQProduct_congr_eqv
  intro faceId hfaceId
  exact Q'.eqv_symm
    (cutoffTwoCubeInterfaceUnary_eqv_heat_support_square
      boundary hboundary faceId hfaceId)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold.cutoffTwoCubeInterfaceUnary_eqv_heat_support_square
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold.cutoffTwoCubeExpectedSingletonProduct_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold.cutoffTwoCubeBoundaryLinkProduct_eqv_supportProduct
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeUnaryFold.cutoffTwoCubeFixedFaceAndSupport_eqv_unaryProduct
