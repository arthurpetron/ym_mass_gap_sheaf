/-
# Spin-decorated surface components at arbitrary cutoff

The support components used by the cutoff-one polymer gas depend only on
whether a plaquette label is zero.  Hence the same constructive component
engine applies at every spin cutoff.  Here each maximal component is labelled
by the restriction of the original physical spin labelling, rather than by a
binary indicator.

The restricted labels are physical, recursively link-separated, and their
pointwise union is exactly the original labelling.  Combining these geometric
facts with arbitrary-cutoff family factorization yields an exact decorated
connected-component product for every finite-box spin-foam term and partition.
-/

import YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
import YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

namespace YMGap.Continuum.Z4AllSpinSurfaceComponentLabels

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Spin-preserving restrictions and elementary union lemmas -/

def decoratedComponentLabel (physical : EdgeLabelling)
    (component : List Nat) : EdgeLabelling :=
  fun edge => if edge ∈ component then physical edge else 0

def decoratedSurfaceComponentLabels (n : Nat)
    (physical : EdgeLabelling) : List EdgeLabelling :=
  (surfaceComponents n physical).map (decoratedComponentLabel physical)

theorem decoratedComponentLabel_eq_physical_of_mem
    {physical : EdgeLabelling} {component : List Nat} {edge : Nat}
    (hmem : edge ∈ component) :
    decoratedComponentLabel physical component edge = physical edge := by
  simp [decoratedComponentLabel, hmem]

theorem decoratedComponentLabel_eq_zero_of_not_mem
    {physical : EdgeLabelling} {component : List Nat} {edge : Nat}
    (hmem : edge ∉ component) :
    decoratedComponentLabel physical component edge = 0 := by
  simp [decoratedComponentLabel, hmem]

theorem unionDecoratedLabels_eq_zero_of_not_mem
    (physical : EdgeLabelling) (edge : Nat) :
    ∀ components : List (List Nat),
      (∀ component, component ∈ components → edge ∉ component) →
      binaryUnionLabels
        (components.map (decoratedComponentLabel physical)) edge = 0
  | [], _ => rfl
  | head :: tail, hnone => by
      have hhead := hnone head List.mem_cons_self
      have htail : ∀ component, component ∈ tail → edge ∉ component :=
        fun component hcomponent =>
          hnone component (List.mem_cons_of_mem head hcomponent)
      have ih := unionDecoratedLabels_eq_zero_of_not_mem
        physical edge tail htail
      simp [binaryUnionLabels, binaryUnionLabel, decoratedComponentLabel,
        hhead, ih]

theorem exists_component_of_one_le_unionDecoratedLabels
    (physical : EdgeLabelling) (edge : Nat) :
    ∀ components : List (List Nat),
      1 ≤ binaryUnionLabels
        (components.map (decoratedComponentLabel physical)) edge →
      ∃ component, component ∈ components ∧ edge ∈ component
  | [], h => by
      simp [binaryUnionLabels, zeroEdgeLabelling] at h
  | head :: tail, h => by
      by_cases hhead : edge ∈ head
      · exact ⟨head, List.mem_cons_self, hhead⟩
      · have htail :
            1 ≤ binaryUnionLabels
              (tail.map (decoratedComponentLabel physical)) edge := by
          simpa [binaryUnionLabels, binaryUnionLabel,
            decoratedComponentLabel, hhead] using h
        obtain ⟨component, hcomponent, hedge⟩ :=
          exists_component_of_one_le_unionDecoratedLabels
            physical edge tail htail
        exact ⟨component, List.mem_cons_of_mem head hcomponent, hedge⟩

theorem unionDecoratedLabels_eq_physical_of_covered
    (physical : EdgeLabelling) (edge : Nat) :
    ∀ components : List (List Nat),
      components.Nodup → DistinctDisjoint components →
      (∃ component, component ∈ components ∧ edge ∈ component) →
      binaryUnionLabels
        (components.map (decoratedComponentLabel physical)) edge =
          physical edge
  | [], _, _, hexists => by
      obtain ⟨component, hcomponent, _⟩ := hexists
      exact absurd hcomponent List.not_mem_nil
  | head :: tail, hnodup, hdisjoint, hexists => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : edge ∈ head
      · have hnone : ∀ component, component ∈ tail → edge ∉ component := by
          intro component hcomponent hedge
          have hne : head ≠ component := by
            intro heq
            subst component
            exact hparts.1 hcomponent
          exact hdisjoint head List.mem_cons_self component
            (List.mem_cons_of_mem head hcomponent) hne edge hhead hedge
        have hzero := unionDecoratedLabels_eq_zero_of_not_mem
          physical edge tail hnone
        simp [binaryUnionLabels, binaryUnionLabel,
          decoratedComponentLabel, hhead, hzero]
      · obtain ⟨component, hcomponent, hedge⟩ := hexists
        have hcomponentTail : component ∈ tail := by
          rcases List.mem_cons.mp hcomponent with heq | htail
          · subst component
            exact absurd hedge hhead
          · exact htail
        have hdisjointTail : DistinctDisjoint tail := by
          intro left hleft right hright hne
          exact hdisjoint left (List.mem_cons_of_mem head hleft)
            right (List.mem_cons_of_mem head hright) hne
        have ih := unionDecoratedLabels_eq_physical_of_covered
          physical edge tail hparts.2 hdisjointTail
          ⟨component, hcomponentTail, hedge⟩
        simp [binaryUnionLabels, binaryUnionLabel,
          decoratedComponentLabel, hhead, ih]

/-! ## 2. Every decorated component is physical at the same cutoff -/

theorem decoratedComponentLabel_mem_bounded
    {K n : Nat} {physical : EdgeLabelling} {component : List Nat}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)))
    (hcomponent : component ∈ surfaceComponents n physical) :
    decoratedComponentLabel physical component ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n)) := by
  have hsound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) physical hphysical
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    by_cases hmem : edge ∈ component
    · rw [decoratedComponentLabel_eq_physical_of_mem hmem]
      exact hsound.1 edge hedge
    · rw [decoratedComponentLabel_eq_zero_of_not_mem hmem]
      omega
  · intro edge hedge
    rw [decoratedComponentLabel_eq_zero_of_not_mem]
    intro hmem
    have hin : edge ∈ physicalFaceEdges n :=
      surfaceComponent_subset_physicalFaceEdges hcomponent hmem
    exact hedge (by simpa [physicalFaceEdges] using hin)

theorem decoratedSurfaceComponentLabels_kPhysicalFamily
    (K n : Nat) (physical : EdgeLabelling)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    KPhysicalFamily K n (decoratedSurfaceComponentLabels n physical) := by
  intro label hlabel
  unfold decoratedSurfaceComponentLabels at hlabel
  obtain ⟨component, hcomponent, rfl⟩ := List.mem_map.mp hlabel
  exact decoratedComponentLabel_mem_bounded hphysical hcomponent

/-! ## 3. Actual-link separation of spin-decorated components -/

private theorem hasExcitedB_exists_local (label : EdgeLabelling) :
    ∀ edges, hasExcitedB label edges = true →
      ∃ edge, edge ∈ edges ∧ 1 ≤ label edge
  | [], h => by cases h
  | edge :: rest, h => by
      by_cases hexcited : 1 ≤ label edge
      · exact ⟨edge, List.mem_cons_self, hexcited⟩
      · have hrest : hasExcitedB label rest = true := by
          simpa [hasExcitedB, hexcited] using h
        obtain ⟨found, hmem, hfound⟩ :=
          hasExcitedB_exists_local label rest hrest
        exact ⟨found, List.mem_cons_of_mem edge hmem, hfound⟩

theorem decoratedComponent_faceDisjoint_union
    (n : Nat) (physical : EdgeLabelling)
    (head : List Nat) (tail : List (List Nat))
    (hdisjoint : ∀ component, component ∈ tail →
      SupportsDisjoint head component) :
    FaceDisjoint n (decoratedComponentLabel physical head)
      (binaryUnionLabels
        (tail.map (decoratedComponentLabel physical))) := by
  intro edge hedge
  by_cases hhead : edge ∈ head
  · right
    exact unionDecoratedLabels_eq_zero_of_not_mem physical edge tail
      (fun component hcomponent => hdisjoint component hcomponent edge hhead)
  · left
    exact decoratedComponentLabel_eq_zero_of_not_mem hhead

theorem decoratedComponent_linkSeparated_union
    (n : Nat) (physical : EdgeLabelling)
    (head : List Nat) (tail : List (List Nat))
    (hseparated : ∀ component, component ∈ tail →
      SupportsSeparated (faceLinkAdjacentB n) head component) :
    LinkSeparated n (decoratedComponentLabel physical head)
      (binaryUnionLabels
        (tail.map (decoratedComponentLabel physical))) := by
  intro indexed hindexed hboth
  have hlink : indexed.2 ∈ distinctBoxLinks n := enumerate_snd_mem hindexed
  obtain ⟨left, hleftIncident, hleftExcited⟩ :=
    hasExcitedB_exists_local _ _ hboth.1
  obtain ⟨right, hrightIncident, hrightExcited⟩ :=
    hasExcitedB_exists_local _ _ hboth.2
  have hleftMem : left ∈ head := by
    by_cases hmem : left ∈ head
    · exact hmem
    · rw [decoratedComponentLabel_eq_zero_of_not_mem hmem]
        at hleftExcited
      omega
  obtain ⟨component, hcomponent, hrightMem⟩ :=
    exists_component_of_one_le_unionDecoratedLabels
      physical right tail hrightExcited
  have htrue := faceLinkAdjacentB_true_of_link hlink
    hleftIncident hrightIncident
  have hfalse := hseparated component hcomponent left hleftMem
    right hrightMem
  rw [htrue] at hfalse
  cases hfalse

theorem decoratedComponentLabels_linkSeparatedFamily
    (n : Nat) (physical : EdgeLabelling) :
    ∀ components : List (List Nat),
      components.Nodup →
      DistinctDisjoint components →
      DistinctSeparated (faceLinkAdjacentB n) components →
      LinkSeparatedFamily n
        (components.map (decoratedComponentLabel physical))
  | [], _, _, _ => trivial
  | head :: tail, hnodup, hdisjoint, hseparated => by
      have hparts := List.nodup_cons.mp hnodup
      have hheadDisjoint : ∀ component, component ∈ tail →
          SupportsDisjoint head component := by
        intro component hcomponent
        have hne : head ≠ component := by
          intro heq
          subst component
          exact hparts.1 hcomponent
        exact hdisjoint head List.mem_cons_self component
          (List.mem_cons_of_mem head hcomponent) hne
      have hheadSeparated : ∀ component, component ∈ tail →
          SupportsSeparated (faceLinkAdjacentB n) head component := by
        intro component hcomponent
        have hne : head ≠ component := by
          intro heq
          subst component
          exact hparts.1 hcomponent
        exact hseparated head List.mem_cons_self component
          (List.mem_cons_of_mem head hcomponent) hne
      have htailDisjoint : DistinctDisjoint tail := by
        intro left hleft right hright hne
        exact hdisjoint left (List.mem_cons_of_mem head hleft)
          right (List.mem_cons_of_mem head hright) hne
      have htailSeparated :
          DistinctSeparated (faceLinkAdjacentB n) tail := by
        intro left hleft right hright hne
        exact hseparated left (List.mem_cons_of_mem head hleft)
          right (List.mem_cons_of_mem head hright) hne
      change
        FaceDisjoint n (decoratedComponentLabel physical head)
            (binaryUnionLabels
              (tail.map (decoratedComponentLabel physical))) ∧
          LinkSeparated n (decoratedComponentLabel physical head)
              (binaryUnionLabels
                (tail.map (decoratedComponentLabel physical))) ∧
            LinkSeparatedFamily n
              (tail.map (decoratedComponentLabel physical))
      exact ⟨decoratedComponent_faceDisjoint_union
          n physical head tail hheadDisjoint,
        decoratedComponent_linkSeparated_union
          n physical head tail hheadSeparated,
        decoratedComponentLabels_linkSeparatedFamily
          n physical tail hparts.2 htailDisjoint htailSeparated⟩

theorem decoratedSurfaceComponentLabels_linkSeparatedFamily
    (n : Nat) (physical : EdgeLabelling) :
    LinkSeparatedFamily n (decoratedSurfaceComponentLabels n physical) := by
  unfold decoratedSurfaceComponentLabels
  exact decoratedComponentLabels_linkSeparatedFamily
    n physical (surfaceComponents n physical)
    (surfaceComponents_nodup n physical)
    (surfaceComponents_distinctDisjoint n physical)
    (surfaceComponents_distinctSeparated n physical)

/-! ## 4. Exact reconstruction and exact all-spin factorization -/

theorem decoratedSurfaceComponentLabels_union_eq_physical
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    binaryUnionLabels (decoratedSurfaceComponentLabels n physical) =
      physical := by
  have hsound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) physical hphysical
  funext edge
  unfold decoratedSurfaceComponentLabels
  by_cases hedge : edge ∈ physicalFaceEdges n
  · by_cases hzero : physical edge = 0
    · have hnone : ∀ component,
          component ∈ surfaceComponents n physical → edge ∉ component := by
        intro component hcomponent hmem
        have hsupport : edge ∈ excitedPlaquetteIds n physical :=
          (surfaceComponents_cover n physical edge).2
            ⟨component, hcomponent, hmem⟩
        have hexcited : 1 ≤ physical edge := by
          have hp := (List.mem_filter.mp hsupport).2
          simpa only [decide_eq_true_eq] using hp
        omega
      rw [hzero]
      exact unionDecoratedLabels_eq_zero_of_not_mem
        physical edge (surfaceComponents n physical) hnone
    · have hpositive : 1 ≤ physical edge := by omega
      have hsupport : edge ∈ excitedPlaquetteIds n physical := by
        unfold excitedPlaquetteIds
        exact List.mem_filter.mpr ⟨hedge, by
          simp only [decide_eq_true_eq]
          exact hpositive⟩
      have hcovered := (surfaceComponents_cover n physical edge).1 hsupport
      exact unionDecoratedLabels_eq_physical_of_covered
        physical edge (surfaceComponents n physical)
        (surfaceComponents_nodup n physical)
        (surfaceComponents_distinctDisjoint n physical) hcovered
  · have hzero := hsound.2 edge (by
        simpa [physicalFaceEdges] using hedge)
    have hnone : ∀ component,
        component ∈ surfaceComponents n physical → edge ∉ component := by
      intro component hcomponent hmem
      exact hedge
        (surfaceComponent_subset_physicalFaceEdges hcomponent hmem)
    rw [hzero]
    exact unionDecoratedLabels_eq_zero_of_not_mem
      physical edge (surfaceComponents n physical) hnone

theorem parametricKPhysicalTerm_surfaceComponent_factor
    {w : Q'} {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalTerm w K n physical ≈
      parametricKPhysicalTermProduct w K n
        (decoratedSurfaceComponentLabels n physical) := by
  have hfactor := parametricKPhysicalTerm_unionLabels_factor w K n
    (decoratedSurfaceComponentLabels n physical)
    (decoratedSurfaceComponentLabels_kPhysicalFamily K n physical hphysical)
    (decoratedSurfaceComponentLabels_linkSeparatedFamily n physical)
  rw [decoratedSurfaceComponentLabels_union_eq_physical hphysical]
    at hfactor
  exact hfactor

def parametricKCanonicalDecoratedComponentProductPartition
    (w : Q') (K n : Nat) : Q' :=
  listQSum
    (fun physical => parametricKPhysicalTermProduct w K n
      (decoratedSurfaceComponentLabels n physical))
    (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n)))

private theorem listQSum_congr_mem_local {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | head :: tail, h =>
      Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_congr_mem_local tail
          (fun x hx => h x (List.mem_cons_of_mem head hx)))

theorem parametricKPhysicalPartition_eq_decoratedComponentProduct
    (w : Q') (K n : Nat) :
    parametricKPhysicalPartition w K n ≈
      parametricKCanonicalDecoratedComponentProductPartition w K n := by
  unfold parametricKPhysicalPartition
    parametricKCanonicalDecoratedComponentProductPartition
  apply listQSum_congr_mem_local
  intro physical hphysical
  exact parametricKPhysicalTerm_surfaceComponent_factor hphysical

end YMGap.Continuum.Z4AllSpinSurfaceComponentLabels

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4AllSpinSurfaceComponentLabels.decoratedSurfaceComponentLabels_kPhysicalFamily
#print axioms YMGap.Continuum.Z4AllSpinSurfaceComponentLabels.decoratedSurfaceComponentLabels_linkSeparatedFamily
#print axioms YMGap.Continuum.Z4AllSpinSurfaceComponentLabels.decoratedSurfaceComponentLabels_union_eq_physical
#print axioms YMGap.Continuum.Z4AllSpinSurfaceComponentLabels.parametricKPhysicalTerm_surfaceComponent_factor
#print axioms YMGap.Continuum.Z4AllSpinSurfaceComponentLabels.parametricKPhysicalPartition_eq_decoratedComponentProduct
