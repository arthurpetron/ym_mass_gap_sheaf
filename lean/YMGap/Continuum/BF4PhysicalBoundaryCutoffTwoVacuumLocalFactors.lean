/-
# Exact cutoff-two vacuum-column local factors

The external sparse contraction uses only three heat weights and the SU(2)
invariant-multiplicity tables of arity zero through four.  This file records
those finite tables and has Lean evaluate every entry from the production
definitions.  It also proves that deleting vacuum-labelled incident faces
from a production lower-link factor leaves exactly the active local factor.

Thus the Python producer may propose factor tables, but it is not trusted for
their values or for their connection to the BF4 amplitude.

This is a finite `K = 2`, half-extent-zero result at coupling `1/2`.  It makes
no cutoff-uniform, volume-uniform, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry
import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-- The fixed rational coupling used by the first positive-cutoff exact
contraction beyond the binary model. -/
def cutoffTwoHalfCoupling : Q' := Q'.mkPos 1 2 (by decide)

/-- The three exact heat weights proposed by the external producer. -/
def cutoffTwoExpectedHeatTable : List Q' :=
  [(1 : Q'), Q'.mkPos 1 4 (by decide), Q'.mkPos 3 256 (by decide)]

/-- Kernel evaluation of the three rational heat weights modulo the rational
setoid (the production numerator/denominator representation is not reduced). -/
theorem cutoffTwoHeatTable_checked :
    ((List.range 3).zip cutoffTwoExpectedHeatTable).all
      (fun entry => decide
        (coeffW cutoffTwoHalfCoupling entry.1 ≈ entry.2)) = true := by
  decide

theorem cutoffTwoHeatFactor_eqv_expected
    (spin : Nat) (hspin : spin < 3) :
    coeffW cutoffTwoHalfCoupling spin ≈
      cutoffTwoExpectedHeatTable.getD spin 0 := by
  have hcases : spin = 0 ∨ spin = 1 ∨ spin = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  all_goals decide

/-- Production local multiplicity on a short active spin list. -/
def cutoffTwoActiveMultiplicity (spins : List Nat) : Nat :=
  explicitValenceMultiplicity (linkAuxiliaryCutoff 2) spins.length
    (externalSpinsOfList spins)

/-- Literal arity-zero through arity-four tables, in `allSeqs 3 arity`
lexicographic order. -/
def cutoffTwoExpectedMultiplicityTables : List (List Nat) :=
  [[1],
   [1, 0, 0],
   [1, 0, 0, 0, 1, 0, 0, 0, 1],
   [1, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0,
    0, 0, 1, 0, 1, 0, 1, 0, 1],
   [1, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0,
    0, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 0, 1, 0, 2, 0, 1, 0, 2,
    0, 1, 0, 1, 0, 2, 0, 2, 0,
    0, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 2, 0, 2, 0,
    1, 0, 1, 0, 2, 0, 1, 0, 3]]

/-- Lean-computed arity-zero through arity-four tables. -/
def cutoffTwoComputedMultiplicityTables : List (List Nat) :=
  (List.range 5).map fun arity =>
    (allSeqs 3 arity).map cutoffTwoActiveMultiplicity

/-- Kernel evaluation of all 121 local SU(2) multiplicity entries. -/
theorem cutoffTwoMultiplicityTables_checked :
    cutoffTwoComputedMultiplicityTables =
      cutoffTwoExpectedMultiplicityTables := by
  decide

/-- The active spins of a production lower-link factor. -/
def cutoffTwoActiveSpins
    (physical : EdgeLabelling) (link : Z4Link) : List Nat :=
  (cutoffTwoActiveIncidentFaceIds link).map physical

/-- The full production incident-spin list. -/
def cutoffTwoIncidentSpins
    (physical : EdgeLabelling) (link : Z4Link) : List Nat :=
  (slabIncidentPlaqIds 1 link).map physical

/-- Removing incident vacuum labels is a zero extension, so the genuine
production multiplicity is exactly the checked active local factor. -/
theorem slabExplicitLinkMultiplicity_cutoffTwo_eq_active
    (physical : EdgeLabelling) (link : Z4Link)
    (hbounded : ∀ faceId, physical faceId ≤ 2)
    (hzero : ∀ faceId,
      faceId ∈ slabIncidentPlaqIds 1 link →
        faceId ∉ centralLowerFaceIds 0 → physical faceId = 0) :
    slabExplicitLinkMultiplicity 2 1 physical link =
      cutoffTwoActiveMultiplicity (cutoffTwoActiveSpins physical link) := by
  let active := cutoffTwoActiveSpins physical link
  let incident := cutoffTwoIncidentSpins physical link
  have hextension : ZeroExtension active incident := by
    unfold active cutoffTwoActiveSpins incident cutoffTwoIncidentSpins
    apply ZeroExtension.map_of_sublist physical List.filter_sublist
      (slabIncidentPlaqIds_nodup 1 link)
    intro faceId hface hnotActive
    apply hzero faceId hface
    intro hlower
    apply hnotActive
    exact List.mem_filter.mpr ⟨hface, by simp only [hlower, decide_true]⟩
  have hactiveLength : active.length ≤ 6 := by
    unfold active cutoffTwoActiveSpins cutoffTwoActiveIncidentFaceIds
    rw [List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _)
      (slabIncidentPlaqIds_length_le_six 1 link)
  have hincidentLength : incident.length ≤ 6 := by
    unfold incident cutoffTwoIncidentSpins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 link
  have hactiveBounded :
      SpinsBounded (linkAuxiliaryCutoff 2) active := by
    intro spin hspin
    unfold active cutoffTwoActiveSpins at hspin
    rcases List.mem_map.mp hspin with ⟨faceId, _hface, rfl⟩
    have := hbounded faceId
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  unfold slabExplicitLinkMultiplicity cutoffTwoActiveMultiplicity
  change
    explicitValenceMultiplicity (linkAuxiliaryCutoff 2) incident.length
        (externalSpinsOfList incident) =
      explicitValenceMultiplicity (linkAuxiliaryCutoff 2) active.length
        (externalSpinsOfList active)
  exact (explicitValenceMultiplicity_zeroExtension
    hextension hactiveLength hincidentLength hactiveBounded).symm

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHeatTable_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoMultiplicityTables_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.slabExplicitLinkMultiplicity_cutoffTwo_eq_active
