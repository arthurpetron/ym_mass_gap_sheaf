/-
# A duplicate-free connected surface gas at arbitrary spin cutoff

The duplicate-free physical Cartesian enumeration is mapped to its exact
spin-decorated maximal-component family.  Reconstruction makes this map
injective, so the resulting list is an honest finite gas domain.  Every gas
family is duplicate-free, physical, link-separated, nonempty componentwise,
and connected on the actual face-link adjacency.  Its family-activity sum is
exactly the arbitrary-cutoff finite-box spin-foam partition.
-/

import YMGap.Continuum.Z4AllSpinSurfaceComponentLabels
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup

namespace YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4AllSpinSurfaceComponentLabels
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Component support facts retained by spin decoration -/

def decoratedSurfaceComponents_allNonempty
    (n : Nat) (physical : EdgeLabelling) :
    AllNonempty (surfaceComponents n physical) :=
  graphComponents_allNonempty (faceLinkAdjacentB n)
    (excitedPlaquetteIds n physical)

theorem mem_excitedPlaquetteIds_decoratedComponentLabel_iff
    {n : Nat} {physical : EdgeLabelling} {component : List Nat}
    (hcomponent : component ∈ surfaceComponents n physical)
    (edge : Nat) :
    edge ∈ excitedPlaquetteIds n
        (decoratedComponentLabel physical component) ↔
      edge ∈ component := by
  constructor
  · intro hexcited
    have hpositive : 1 ≤ decoratedComponentLabel physical component edge := by
      have hp := (List.mem_filter.mp hexcited).2
      simpa only [decide_eq_true_eq] using hp
    by_cases hmem : edge ∈ component
    · exact hmem
    · rw [decoratedComponentLabel_eq_zero_of_not_mem hmem] at hpositive
      omega
  · intro hmem
    have hsupport : edge ∈ excitedPlaquetteIds n physical :=
      (surfaceComponents_cover n physical edge).2
        ⟨component, hcomponent, hmem⟩
    have hparts := List.mem_filter.mp hsupport
    have hpositive : 1 ≤ physical edge := by
      simpa only [decide_eq_true_eq] using hparts.2
    apply List.mem_filter.mpr
    constructor
    · exact surfaceComponent_subset_physicalFaceEdges hcomponent hmem
    · simp only [decide_eq_true_eq]
      rw [decoratedComponentLabel_eq_physical_of_mem hmem]
      exact hpositive

def DecoratedAllNonempty (n : Nat)
    (family : List EdgeLabelling) : Prop :=
  ∀ label, label ∈ family →
    ∃ edge, edge ∈ excitedPlaquetteIds n label

def DecoratedAllConnected (n : Nat)
    (family : List EdgeLabelling) : Prop :=
  ∀ label, label ∈ family → ∀ left right,
    left ∈ excitedPlaquetteIds n label →
    right ∈ excitedPlaquetteIds n label →
    Nonempty (ChainIn (faceLinkAdjacentB n)
      (excitedPlaquetteIds n label) left right)

theorem decoratedSurfaceComponentLabels_allNonempty
    (n : Nat) (physical : EdgeLabelling) :
    DecoratedAllNonempty n
      (decoratedSurfaceComponentLabels n physical) := by
  intro label hlabel
  unfold decoratedSurfaceComponentLabels at hlabel
  obtain ⟨component, hcomponent, rfl⟩ := List.mem_map.mp hlabel
  obtain ⟨edge, hedge⟩ :=
    decoratedSurfaceComponents_allNonempty n physical
      component hcomponent
  exact ⟨edge,
    (mem_excitedPlaquetteIds_decoratedComponentLabel_iff
      hcomponent edge).2 hedge⟩

theorem decoratedSurfaceComponentLabels_allConnected
    (n : Nat) (physical : EdgeLabelling) :
    DecoratedAllConnected n
      (decoratedSurfaceComponentLabels n physical) := by
  intro label hlabel
  unfold decoratedSurfaceComponentLabels at hlabel
  obtain ⟨component, hcomponent, rfl⟩ := List.mem_map.mp hlabel
  intro left right hleft hright
  have hleftComponent :=
    (mem_excitedPlaquetteIds_decoratedComponentLabel_iff
      hcomponent left).1 hleft
  have hrightComponent :=
    (mem_excitedPlaquetteIds_decoratedComponentLabel_iff
      hcomponent right).1 hright
  have hchain := surfaceComponents_allConnected n physical
    component hcomponent left right hleftComponent hrightComponent
  exact ⟨ChainIn.mono
      (fun point hpoint =>
        (mem_excitedPlaquetteIds_decoratedComponentLabel_iff
          hcomponent point).2 hpoint)
      hchain⟩

theorem decoratedSurfaceComponentLabels_nodup
    (n : Nat) (physical : EdgeLabelling) :
    (decoratedSurfaceComponentLabels n physical).Nodup := by
  unfold decoratedSurfaceComponentLabels
  apply CayleyPruferInjection.nodup_map_of_injOn
  · exact surfaceComponents_nodup n physical
  · intro left hleft right hright heq
    by_cases hlr : left = right
    · exact hlr
    · obtain ⟨edge, hedgeLeft⟩ :=
        decoratedSurfaceComponents_allNonempty n physical left hleft
      have hedgeRight : edge ∉ right :=
        surfaceComponents_distinctDisjoint n physical
          left hleft right hright hlr edge hedgeLeft
      have hpositive : 1 ≤ physical edge := by
        have hsupport : edge ∈ excitedPlaquetteIds n physical :=
          (surfaceComponents_cover n physical edge).2
            ⟨left, hleft, hedgeLeft⟩
        have hp := (List.mem_filter.mp hsupport).2
        simpa only [decide_eq_true_eq] using hp
      have hpoint := congrArg (fun label => label edge) heq
      change decoratedComponentLabel physical left edge =
        decoratedComponentLabel physical right edge at hpoint
      rw [decoratedComponentLabel_eq_physical_of_mem hedgeLeft,
        decoratedComponentLabel_eq_zero_of_not_mem hedgeRight]
        at hpoint
      omega

/-! ## 2. The duplicate-free gas domain -/

def canonicalDecoratedConnectedSurfaceGas (K n : Nat) :
    List (List EdgeLabelling) :=
  (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n))).map
    (decoratedSurfaceComponentLabels n)

theorem decoratedSurfaceComponentLabels_injective_on_bounded
    {K n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (hright : right ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (heq : decoratedSurfaceComponentLabels n left =
      decoratedSurfaceComponentLabels n right) :
    left = right := by
  have hleftUnion :=
    decoratedSurfaceComponentLabels_union_eq_physical hleft
  have hrightUnion :=
    decoratedSurfaceComponentLabels_union_eq_physical hright
  calc
    left = binaryUnionLabels
        (decoratedSurfaceComponentLabels n left) := hleftUnion.symm
    _ = binaryUnionLabels
        (decoratedSurfaceComponentLabels n right) := congrArg _ heq
    _ = right := hrightUnion

theorem canonicalDecoratedConnectedSurfaceGas_nodup
    (K n : Nat) :
    (canonicalDecoratedConnectedSurfaceGas K n).Nodup := by
  unfold canonicalDecoratedConnectedSurfaceGas
  apply CayleyPruferInjection.nodup_map_of_injOn
  · apply boundedEdgeLabellings_nodup
    simpa [physicalFaceEdges] using physicalFaceEdges_nodup n
  · intro left hleft right hright heq
    exact decoratedSurfaceComponentLabels_injective_on_bounded
      hleft hright heq

theorem mem_canonicalDecoratedConnectedSurfaceGas_iff
    {K n : Nat} {family : List EdgeLabelling} :
    family ∈ canonicalDecoratedConnectedSurfaceGas K n ↔
      ∃ physical,
        physical ∈ boundedEdgeLabellings K
          (List.range (plaquetteEdgeCount n)) ∧
        decoratedSurfaceComponentLabels n physical = family := by
  unfold canonicalDecoratedConnectedSurfaceGas
  exact List.mem_map

theorem canonicalDecoratedGasFamilyFacts
    {K n : Nat} {family : List EdgeLabelling}
    (hfamily : family ∈ canonicalDecoratedConnectedSurfaceGas K n) :
    family.Nodup ∧
      KPhysicalFamily K n family ∧
        LinkSeparatedFamily n family ∧
          DecoratedAllNonempty n family ∧
            DecoratedAllConnected n family := by
  obtain ⟨physical, hphysical, heq⟩ :=
    mem_canonicalDecoratedConnectedSurfaceGas_iff.mp hfamily
  rw [← heq]
  exact ⟨decoratedSurfaceComponentLabels_nodup n physical,
    decoratedSurfaceComponentLabels_kPhysicalFamily K n physical hphysical,
    decoratedSurfaceComponentLabels_linkSeparatedFamily n physical,
    decoratedSurfaceComponentLabels_allNonempty n physical,
    decoratedSurfaceComponentLabels_allConnected n physical⟩

/-! ## 3. Exact equality of the physical and decorated-gas partitions -/

def parametricKCanonicalDecoratedConnectedSurfaceGasPartition
    (w : Q') (K n : Nat) : Q' :=
  listQSum (parametricKPhysicalTermProduct w K n)
    (canonicalDecoratedConnectedSurfaceGas K n)

private theorem listQSum_map_local {A B : Type}
    (f : B → Q') (g : A → B) : ∀ xs : List A,
    listQSum f (xs.map g) = listQSum (fun x => f (g x)) xs
  | [] => rfl
  | _ :: xs => congrArg (fun tail => f (g _) + tail)
      (listQSum_map_local f g xs)

theorem parametricKDecoratedComponentProductPartition_eq_gas
    (w : Q') (K n : Nat) :
    parametricKCanonicalDecoratedComponentProductPartition w K n =
      parametricKCanonicalDecoratedConnectedSurfaceGasPartition w K n := by
  unfold parametricKCanonicalDecoratedComponentProductPartition
    parametricKCanonicalDecoratedConnectedSurfaceGasPartition
    canonicalDecoratedConnectedSurfaceGas
  rw [listQSum_map_local]

theorem parametricKPhysicalPartition_eq_decoratedConnectedSurfaceGas
    (w : Q') (K n : Nat) :
    parametricKPhysicalPartition w K n ≈
      parametricKCanonicalDecoratedConnectedSurfaceGasPartition w K n := by
  exact Q'.eqv_trans _ _ _
    (parametricKPhysicalPartition_eq_decoratedComponentProduct w K n)
    (Q'.eqv_of_eq
      (parametricKDecoratedComponentProductPartition_eq_gas w K n))

end YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas.decoratedSurfaceComponentLabels_nodup
#print axioms YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas.canonicalDecoratedConnectedSurfaceGas_nodup
#print axioms YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas.canonicalDecoratedGasFamilyFacts
#print axioms YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas.parametricKPhysicalPartition_eq_decoratedConnectedSurfaceGas
