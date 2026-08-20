/-
# Exact cutoff-two cube fixed-interface contraction

The cube half-amplitude support leaves twelve fixed-interface coordinates in
the labels `0` or `2` and forces the other twelve to zero.  Multiplying two
copies of that support with the genuine fixed-interface heat factors and
fixed-link SU(2) multiplicities gives a 24-variable scoped factor graph.

A 16-process exact-arithmetic scout proposed a width-five elimination order.
Lean recomputes every arity-at-most-six local multiplicity table and every
intermediate bucket table.  The exact interface sum is

  79228171482694884378979459057 /
  79228162514264337593543950336.

This module certifies the finite factor contraction.  Its identification
with the genuine physical cube Gram diagonal is kept in a separate bridge so
the kernel can release the elimination state first.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryFactorGraph
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationTrace
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fixed-link scopes and tables -/

def cutoffTwoFixedIncidentFaceIds (link : Z4Link) : List Nat :=
  (slabIncidentPlaqIds 1 link).filter fun faceId =>
    decide (faceId ∈ centralFixedFaceIds 0)

def cutoffTwoProductionFixedLinkFaceIds : List (List Nat) :=
  (centralFixedLinks 0).map cutoffTwoFixedIncidentFaceIds

def cutoffTwoExpectedFixedLinkFaceIds : List (List Nat) :=
  [[2, 4, 5], [2, 38, 40, 41], [4, 20, 22, 23], [5, 11, 13, 14],
   [11, 41, 47, 49, 50], [13, 23, 29, 31, 32], [14],
   [20, 40, 56, 58, 59], [22], [29, 49, 59, 65, 67, 68],
   [31], [32], [38], [47], [50], [56], [58], [65], [67], [68]]

theorem cutoffTwoFixedLinkFaceIds_checked :
    cutoffTwoProductionFixedLinkFaceIds =
      cutoffTwoExpectedFixedLinkFaceIds := by
  decide

theorem cutoffTwoFixedLinkScopes_arity_le_six :
    cutoffTwoExpectedFixedLinkFaceIds.all
      (fun scope => decide (scope.length ≤ 6)) = true := by
  decide

/-- Literal arity-five and arity-six tables emitted by the exact producer.
The smaller arities reuse the independently checked cutoff-two tables. -/
def cutoffTwoExpectedMultiplicityTableFive : List Nat :=
  [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4, 0, 4, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 3, 0, 4, 0, 3, 0, 6]

def cutoffTwoExpectedMultiplicityTableSix : List Nat :=
  [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4, 0, 4, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 3, 0, 4, 0, 3, 0, 6, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3, 0, 5, 0, 3, 0, 6, 0, 3, 0, 3, 0, 6, 0, 6, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 3, 0, 3, 0, 6, 0, 6, 0, 2, 0, 4, 0, 6, 0, 4, 0, 9, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 3, 0, 3, 0, 6, 0, 6, 0, 2, 0, 4, 0, 6, 0, 4, 0, 9, 0, 2, 0, 2, 0, 4, 0, 4, 0, 2, 0, 4, 0, 6, 0, 4, 0, 9, 0, 4, 0, 4, 0, 9, 0, 9, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 3, 0, 4, 0, 3, 0, 6, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 2, 0, 3, 0, 2, 0, 4, 0, 3, 0, 3, 0, 6, 0, 6, 0, 2, 0, 4, 0, 6, 0, 4, 0, 9, 0, 2, 0, 2, 0, 4, 0, 4, 0, 2, 0, 4, 0, 6, 0, 4, 0, 9, 0, 4, 0, 4, 0, 9, 0, 9, 0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 0, 2, 0, 2, 0, 4, 0, 4, 0, 1, 0, 3, 0, 4, 0, 3, 0, 6, 0, 2, 0, 2, 0, 4, 0, 4, 0, 2, 0, 4, 0, 6, 0, 4, 0, 9, 0, 4, 0, 4, 0, 9, 0, 9, 0, 1, 0, 3, 0, 4, 0, 3, 0, 6, 0, 4, 0, 4, 0, 9, 0, 9, 0, 3, 0, 6, 0, 9, 0, 6, 0, 15]

def cutoffTwoExpectedMultiplicityTablesUpToSix : List (List Nat) :=
  cutoffTwoExpectedMultiplicityTables ++
    [cutoffTwoExpectedMultiplicityTableFive,
      cutoffTwoExpectedMultiplicityTableSix]

def cutoffTwoFixedMultiplicityQTable (arity : Nat) : List Q' :=
  (cutoffTwoExpectedMultiplicityTablesUpToSix.getD arity []).map Q'.ofNat

def cutoffTwoFixedLinkTableFactor (link : Z4Link) : ScopedQFactor :=
  let scope := cutoffTwoFixedIncidentFaceIds link
  scopedTableFactor 3 scope
    (cutoffTwoFixedMultiplicityQTable scope.length)

private theorem fixedBoundaryLinkLocality
    (link : Z4Link) (left right : EdgeLabelling)
    (hagree : ∀ id, id ∈ cutoffTwoFixedIncidentFaceIds link →
      left id = right id) :
    centralHalfLinkLocalFactor 2 0 zeroEdgeLabelling left link =
      centralHalfLinkLocalFactor 2 0 zeroEdgeLabelling right link := by
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

/-! ## 2. The complete interface graph -/

/-- Heat weight multiplied by the squared cube support mask.  On a selected
cube-edge coordinate the table is `[1, 0, 3/256]`; on every other coordinate
only the vacuum label survives. -/
def cutoffTwoCubeInterfaceUnaryTable (faceId : Nat) : List Q' :=
  if faceId ∈ cutoffTwoCubeActiveFixedFaceIds then
    [(1 : Q'), 0, Q'.mkPos 3 256 (by decide)]
  else
    [(1 : Q'), 0, 0]

def cutoffTwoCubeInterfaceUnaryFactors : List ScopedQFactor :=
  (centralFixedFaceIds 0).map fun faceId =>
    scopedTableFactor 3 [faceId]
      (cutoffTwoCubeInterfaceUnaryTable faceId)

def cutoffTwoCubeFixedLinkFactors : List ScopedQFactor :=
  (centralFixedLinks 0).map cutoffTwoFixedLinkTableFactor

/-- The folded 24 unary factors and the 20 genuine fixed-link factors. -/
def cutoffTwoCubeInterfaceFactors : List ScopedQFactor :=
  cutoffTwoCubeInterfaceUnaryFactors ++
    cutoffTwoCubeFixedLinkFactors

theorem cutoffTwoCubeInterfaceFactor_count :
    cutoffTwoCubeInterfaceFactors.length = 44 := by
  decide

/-- Width-five order proposed by the parallel exact scout, expressed in
production fixed-face identifiers. -/
def cutoffTwoCubeInterfaceEliminationOrder : List Nat :=
  [38, 22, 14, 5, 31, 32, 56, 58, 23, 40, 47, 50,
   13, 4, 41, 2, 11, 20, 65, 29, 59, 49, 68, 67]

def cutoffTwoExpectedFixedFaceIds : List Nat :=
  [2, 4, 5, 11, 13, 14, 20, 22, 23, 29, 31, 32,
   38, 40, 41, 47, 49, 50, 56, 58, 59, 65, 67, 68]

theorem cutoffTwoFixedFaceIds_checked :
    centralFixedFaceIds 0 = cutoffTwoExpectedFixedFaceIds := by
  decide

theorem cutoffTwoCubeInterfaceEliminationOrder_perm :
    cutoffTwoCubeInterfaceEliminationOrder.Perm
      (centralFixedFaceIds 0) := by
  rw [cutoffTwoFixedFaceIds_checked]
  unfold cutoffTwoCubeInterfaceEliminationOrder
    cutoffTwoExpectedFixedFaceIds
  refine (List.perm_middle (a := 2)
    (l₁ := [38, 22, 14, 5, 31, 32, 56, 58, 23, 40, 47, 50, 13, 4, 41])
    (l₂ := [11, 20, 65, 29, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 4)
    (l₁ := [38, 22, 14, 5, 31, 32, 56, 58, 23, 40, 47, 50, 13])
    (l₂ := [41, 11, 20, 65, 29, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 5) (l₁ := [38, 22, 14])
    (l₂ := [31, 32, 56, 58, 23, 40, 47, 50, 13, 41, 11, 20,
      65, 29, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 11)
    (l₁ := [38, 22, 14, 31, 32, 56, 58, 23, 40, 47, 50, 13, 41])
    (l₂ := [20, 65, 29, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 13)
    (l₁ := [38, 22, 14, 31, 32, 56, 58, 23, 40, 47, 50])
    (l₂ := [41, 20, 65, 29, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 14) (l₁ := [38, 22])
    (l₂ := [31, 32, 56, 58, 23, 40, 47, 50, 41, 20, 65, 29,
      59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 20)
    (l₁ := [38, 22, 31, 32, 56, 58, 23, 40, 47, 50, 41])
    (l₂ := [65, 29, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 22) (l₁ := [38])
    (l₂ := [31, 32, 56, 58, 23, 40, 47, 50, 41, 65, 29, 59,
      49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 23) (l₁ := [38, 31, 32, 56, 58])
    (l₂ := [40, 47, 50, 41, 65, 29, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 29)
    (l₁ := [38, 31, 32, 56, 58, 40, 47, 50, 41, 65])
    (l₂ := [59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 31) (l₁ := [38])
    (l₂ := [32, 56, 58, 40, 47, 50, 41, 65, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 32) (l₁ := [38])
    (l₂ := [56, 58, 40, 47, 50, 41, 65, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 38) (l₁ := [])
    (l₂ := [56, 58, 40, 47, 50, 41, 65, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 40) (l₁ := [56, 58])
    (l₂ := [47, 50, 41, 65, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 41) (l₁ := [56, 58, 47, 50])
    (l₂ := [65, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 47) (l₁ := [56, 58])
    (l₂ := [50, 65, 59, 49, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 49) (l₁ := [56, 58, 50, 65, 59])
    (l₂ := [68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 50) (l₁ := [56, 58])
    (l₂ := [65, 59, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 56) (l₁ := [])
    (l₂ := [58, 65, 59, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 58) (l₁ := [])
    (l₂ := [65, 59, 68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 59) (l₁ := [65])
    (l₂ := [68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 65) (l₁ := [])
    (l₂ := [68, 67])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 67) (l₁ := [68])
    (l₂ := [])).trans ?_
  apply List.Perm.cons
  refine (List.perm_middle (a := 68) (l₁ := [])
    (l₂ := [])).trans ?_
  apply List.Perm.cons
  exact List.Perm.nil

def cutoffTwoCubeExpectedInterfaceSum : Q' :=
  Q'.mkPos
    79228171482694884378979459057
    79228162514264337593543950336
    (by decide)

/-- Sparse result-table constructor used by the independently compiled
elimination-step shards. -/
def cutoffTwoCubeSparseDatum
    (scope : List Nat) (entries : List (Nat × Q')) :
    SparseEliminationDatum :=
  { scope := scope, nonzeroEntries := entries }

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction.cutoffTwoFixedLinkFaceIds_checked
