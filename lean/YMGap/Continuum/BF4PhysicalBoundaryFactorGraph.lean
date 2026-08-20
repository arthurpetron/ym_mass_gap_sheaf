/-
# Local factor graph for the physical BF4 half amplitude

This file rewrites the genuine finite BF4 half amplitude as a product of
one rational factor per lower face and one rational factor per lower link.
Each link factor reads only the plaquette identifiers incident to that link.
This is the local representation needed by a variable-elimination producer.

The identity is checked in Lean from the production definitions.  It does
not assert that a particular elimination order has small width, and it makes
no cutoff-uniform or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryVariableElimination
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.BF4PhysicalBoundaryFactorGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryVariableElimination
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- The unary heat-kernel factor attached to one lower-face identifier. -/
def centralHalfFaceLocalFactor
    (w : Q') (K half : Nat)
    (source boundary : EdgeLabelling) (id : Nat) : Q' :=
  coeffAt (heatKernelPacket K w)
    (assembleReflectedSlabLabelling
      half source boundary zeroEdgeLabelling id)

/-- The exact fusion multiplicity attached to one lower link, embedded as a
rational factor. -/
def centralHalfLinkLocalFactor
    (K half : Nat) (source boundary : EdgeLabelling)
    (link : Z4Link) : Q' :=
  Q'.ofNat
    (slabExplicitLinkMultiplicity K (centralExtent half)
      (assembleReflectedSlabLabelling
        half source boundary zeroEdgeLabelling)
      link)

/-- Executable local-factor presentation of one physical half amplitude. -/
def centralHalfAmplitudeFactorProduct
    (w : Q') (K half : Nat)
    (source boundary : EdgeLabelling) : Q' :=
  listQProduct
      (centralHalfFaceLocalFactor w K half source boundary)
      (centralLowerFaceIds half) *
    listQProduct
      (centralHalfLinkLocalFactor K half source boundary)
      (centralLowerLinks half)

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

/-- The production half amplitude is exactly the displayed local factor
graph.  No surrogate amplitude is introduced. -/
theorem centralHalfAmplitude_eqv_factorProduct
    (w : Q') (K half : Nat)
    (source boundary : EdgeLabelling) :
    centralHalfAmplitude w K half source boundary ≈
      centralHalfAmplitudeFactorProduct
        w K half source boundary := by
  unfold centralHalfAmplitude centralLowerFactor
    centralHalfAmplitudeFactorProduct
    centralHalfFaceLocalFactor centralHalfLinkLocalFactor
    slabFaceFactorOn slabLinkMultiplicityProductOn
  exact q_mul_congr
    (Q'.eqv_of_eq
      (eliminateLinks_eq_listQProduct
        (fun id =>
          coeffAt (heatKernelPacket K w)
            (assembleReflectedSlabLabelling
              half source boundary zeroEdgeLabelling id))
        (centralLowerFaceIds half)))
    (ofNat_natListProduct_eqv_listQProduct
      (slabExplicitLinkMultiplicity K (centralExtent half)
        (assembleReflectedSlabLabelling
          half source boundary zeroEdgeLabelling))
      (centralLowerLinks half))

private theorem listMap_congr_on {A B : Type}
    (left right : A → B) : ∀ items : List A,
    (∀ item, item ∈ items → left item = right item) →
      items.map left = items.map right
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [List.map_cons]
      rw [hagree head List.mem_cons_self,
        listMap_congr_on left right tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem))]

/-- A lower-link factor depends only on the face labels incident to that
link.  This is the formal finite-scope fact used to justify sparse factors. -/
theorem centralHalfLinkLocalFactor_eq_of_incident_eq
    (K half : Nat) (left right : EdgeLabelling) (link : Z4Link)
    (hagree : ∀ id,
      id ∈ slabIncidentPlaqIds (centralExtent half) link →
        left id = right id) :
    Q'.ofNat
        (slabExplicitLinkMultiplicity K (centralExtent half) left link) =
      Q'.ofNat
        (slabExplicitLinkMultiplicity K (centralExtent half) right link) := by
  unfold slabExplicitLinkMultiplicity
  rw [listMap_congr_on left right
    (slabIncidentPlaqIds (centralExtent half) link) hagree]

/-- Every local link scope contains at most six plaquette identifiers. -/
theorem centralHalfLinkLocalFactor_scope_length_le_six
    (half : Nat) (link : Z4Link) :
    (slabIncidentPlaqIds (centralExtent half) link).length ≤ 6 :=
  slabIncidentPlaqIds_length_le_six (centralExtent half) link

end YMGap.Continuum.BF4PhysicalBoundaryFactorGraph

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryFactorGraph.centralHalfAmplitude_eqv_factorProduct
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryFactorGraph.centralHalfLinkLocalFactor_eq_of_incident_eq
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryFactorGraph.centralHalfLinkLocalFactor_scope_length_le_six
