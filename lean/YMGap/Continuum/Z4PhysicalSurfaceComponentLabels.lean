/-
# Exact component labels and factorization of cutoff-one Z4 configurations

Each numerical face component is turned into its binary indicator labelling.
The component cover and disjointness theorems prove that the union of these
indicators is exactly the original cutoff-one physical labelling.  Actual
shared-link separation proves that the indicator family satisfies the
recursive separation interface of the finite-family multiplication theorem.

Consequently every cutoff-one finite-box spin-foam configuration has an exact
factorization into the weights of its constructively generated maximal
link-connected components.
-/

import YMGap.Continuum.Z4PhysicalSurfaceComponents

namespace YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Indicator labellings and their finite unions -/

def componentLabel (component : List Nat) : EdgeLabelling :=
  fun edge => if edge ∈ component then 1 else 0

def surfaceComponentLabels (n : Nat) (physical : EdgeLabelling) :
    List EdgeLabelling :=
  (surfaceComponents n physical).map componentLabel

theorem componentLabel_eq_one_iff {component : List Nat} {edge : Nat} :
    componentLabel component edge = 1 ↔ edge ∈ component := by
  unfold componentLabel
  by_cases hmem : edge ∈ component <;> simp [hmem]

theorem componentLabel_eq_zero_of_not_mem
    {component : List Nat} {edge : Nat} (hmem : edge ∉ component) :
    componentLabel component edge = 0 := by
  simp [componentLabel, hmem]

theorem binaryUnionComponentLabels_eq_zero_of_not_mem (edge : Nat) :
    ∀ components : List (List Nat),
      (∀ component, component ∈ components → edge ∉ component) →
      binaryUnionLabels (components.map componentLabel) edge = 0
  | [], _ => rfl
  | head :: tail, hnone => by
      have hhead := hnone head List.mem_cons_self
      have htail : ∀ component, component ∈ tail → edge ∉ component :=
        fun component hcomponent =>
          hnone component (List.mem_cons_of_mem head hcomponent)
      have ih := binaryUnionComponentLabels_eq_zero_of_not_mem edge tail htail
      simp [binaryUnionLabels, binaryUnionLabel, componentLabel, hhead, ih]

theorem exists_component_of_one_le_binaryUnionLabels (edge : Nat) :
    ∀ components : List (List Nat),
      1 ≤ binaryUnionLabels (components.map componentLabel) edge →
      ∃ component, component ∈ components ∧ edge ∈ component
  | [], h => by
      simp [binaryUnionLabels, zeroEdgeLabelling] at h
  | head :: tail, h => by
      by_cases hhead : edge ∈ head
      · exact ⟨head, List.mem_cons_self, hhead⟩
      · have htail :
            1 ≤ binaryUnionLabels (tail.map componentLabel) edge := by
          simpa [binaryUnionLabels, binaryUnionLabel, componentLabel, hhead]
            using h
        obtain ⟨component, hcomponent, hedge⟩ :=
          exists_component_of_one_le_binaryUnionLabels edge tail htail
        exact ⟨component, List.mem_cons_of_mem head hcomponent, hedge⟩

theorem binaryUnionComponentLabels_eq_one_of_covered (edge : Nat) :
    ∀ components : List (List Nat),
      components.Nodup → DistinctDisjoint components →
      (∃ component, component ∈ components ∧ edge ∈ component) →
      binaryUnionLabels (components.map componentLabel) edge = 1
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
        have hzero :=
          binaryUnionComponentLabels_eq_zero_of_not_mem edge tail hnone
        simp [binaryUnionLabels, binaryUnionLabel, componentLabel, hhead,
          hzero]
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
        have ih := binaryUnionComponentLabels_eq_one_of_covered edge tail
          hparts.2 hdisjointTail
          ⟨component, hcomponentTail, hedge⟩
        simp [binaryUnionLabels, binaryUnionLabel, componentLabel, hhead, ih]

/-! ## 2. Every component indicator is a physical cutoff-one labelling -/

theorem surfaceComponent_subset_physicalFaceEdges
    {n : Nat} {physical : EdgeLabelling} {component : List Nat}
    (hcomponent : component ∈ surfaceComponents n physical) :
    ∀ {edge}, edge ∈ component → edge ∈ physicalFaceEdges n := by
  intro edge hedge
  have hsupport : edge ∈ excitedPlaquetteIds n physical :=
    (surfaceComponents_cover n physical edge).2
      ⟨component, hcomponent, hedge⟩
  exact (List.mem_filter.mp hsupport).1

theorem componentLabel_mem_physical_of_subset
    {n : Nat} {component : List Nat}
    (hsubset : ∀ {edge}, edge ∈ component → edge ∈ physicalFaceEdges n) :
    componentLabel component ∈ explicitPhysicalLabellings 1 n := by
  unfold explicitPhysicalLabellings
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    unfold componentLabel
    by_cases hmem : edge ∈ component <;> simp [hmem]
  · intro edge hedge
    unfold componentLabel
    rw [if_neg]
    intro hmem
    exact hedge (hsubset hmem)

theorem surfaceComponentLabels_physicalFamily
    (n : Nat) (physical : EdgeLabelling) :
    PhysicalFamily n (surfaceComponentLabels n physical) := by
  intro label hlabel
  unfold surfaceComponentLabels at hlabel
  obtain ⟨component, hcomponent, rfl⟩ := List.mem_map.mp hlabel
  exact componentLabel_mem_physical_of_subset
    (surfaceComponent_subset_physicalFaceEdges hcomponent)

/-! ## 3. Actual-link separation of the indicator family -/

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

theorem componentLabel_faceDisjoint_union
    (n : Nat) (head : List Nat) (tail : List (List Nat))
    (hdisjoint : ∀ component, component ∈ tail →
      SupportsDisjoint head component) :
    FaceDisjoint n (componentLabel head)
      (binaryUnionLabels (tail.map componentLabel)) := by
  intro edge hedge
  by_cases hhead : edge ∈ head
  · right
    exact binaryUnionComponentLabels_eq_zero_of_not_mem edge tail
      (fun component hcomponent => hdisjoint component hcomponent edge hhead)
  · left
    exact componentLabel_eq_zero_of_not_mem hhead

theorem componentLabel_linkSeparated_union
    (n : Nat) (head : List Nat) (tail : List (List Nat))
    (hseparated : ∀ component, component ∈ tail →
      SupportsSeparated (faceLinkAdjacentB n) head component) :
    LinkSeparated n (componentLabel head)
      (binaryUnionLabels (tail.map componentLabel)) := by
  intro indexed hindexed hboth
  have hlink : indexed.2 ∈ distinctBoxLinks n := enumerate_snd_mem hindexed
  have hleftTouch :
      hasExcitedB (componentLabel head)
        (incidentPlaqIds n indexed.2) = true := hboth.1
  have hrightTouch :
      hasExcitedB (binaryUnionLabels (tail.map componentLabel))
        (incidentPlaqIds n indexed.2) = true := hboth.2
  obtain ⟨left, hleftIncident, hleftExcited⟩ :=
    hasExcitedB_exists_local _ _ hleftTouch
  obtain ⟨right, hrightIncident, hrightExcited⟩ :=
    hasExcitedB_exists_local _ _ hrightTouch
  have hleftMem : left ∈ head := by
    by_cases hmem : left ∈ head
    · exact hmem
    · rw [componentLabel_eq_zero_of_not_mem hmem] at hleftExcited
      omega
  obtain ⟨component, hcomponent, hrightMem⟩ :=
    exists_component_of_one_le_binaryUnionLabels right tail hrightExcited
  have htrue := faceLinkAdjacentB_true_of_link hlink
    hleftIncident hrightIncident
  have hfalse := hseparated component hcomponent left hleftMem
    right hrightMem
  rw [htrue] at hfalse
  cases hfalse

theorem componentLabels_linkSeparatedFamily (n : Nat) :
    ∀ components : List (List Nat),
      components.Nodup →
      DistinctDisjoint components →
      DistinctSeparated (faceLinkAdjacentB n) components →
      LinkSeparatedFamily n (components.map componentLabel)
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
        FaceDisjoint n (componentLabel head)
            (binaryUnionLabels (tail.map componentLabel)) ∧
          LinkSeparated n (componentLabel head)
              (binaryUnionLabels (tail.map componentLabel)) ∧
            LinkSeparatedFamily n (tail.map componentLabel)
      exact ⟨componentLabel_faceDisjoint_union n head tail hheadDisjoint,
        componentLabel_linkSeparated_union n head tail hheadSeparated,
        componentLabels_linkSeparatedFamily n tail hparts.2
          htailDisjoint htailSeparated⟩

theorem surfaceComponentLabels_linkSeparatedFamily
    (n : Nat) (physical : EdgeLabelling) :
    LinkSeparatedFamily n (surfaceComponentLabels n physical) := by
  unfold surfaceComponentLabels
  exact componentLabels_linkSeparatedFamily n (surfaceComponents n physical)
    (surfaceComponents_nodup n physical)
    (surfaceComponents_distinctDisjoint n physical)
    (surfaceComponents_distinctSeparated n physical)

/-! ## 4. Exact reconstruction and exact weight factorization -/

theorem surfaceComponentLabels_union_eq_physical
    {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    binaryUnionLabels (surfaceComponentLabels n physical) = physical := by
  have hsound := boundedEdgeLabellings_sound 1
    (physicalFaceEdges n) physical hphysical
  funext edge
  unfold surfaceComponentLabels
  by_cases hedge : edge ∈ physicalFaceEdges n
  · have hbinary : physical edge = 0 ∨ physical edge = 1 := by
      have := hsound.1 edge hedge
      omega
    rcases hbinary with hzero | hone
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
      exact binaryUnionComponentLabels_eq_zero_of_not_mem edge
        (surfaceComponents n physical) hnone
    · have hsupport : edge ∈ excitedPlaquetteIds n physical := by
        unfold excitedPlaquetteIds
        exact List.mem_filter.mpr ⟨hedge, by
          simp only [decide_eq_true_eq]
          omega⟩
      have hcovered := (surfaceComponents_cover n physical edge).1 hsupport
      rw [hone]
      exact binaryUnionComponentLabels_eq_one_of_covered edge
        (surfaceComponents n physical)
        (surfaceComponents_nodup n physical)
        (surfaceComponents_distinctDisjoint n physical) hcovered
  · have hzero := hsound.2 edge hedge
    have hnone : ∀ component,
        component ∈ surfaceComponents n physical → edge ∉ component := by
      intro component hcomponent hmem
      exact hedge (surfaceComponent_subset_physicalFaceEdges hcomponent hmem)
    rw [hzero]
    exact binaryUnionComponentLabels_eq_zero_of_not_mem edge
      (surfaceComponents n physical) hnone

theorem parametricLocalizedSpinFoamWeight_surfaceComponent_factor
    {w : Q'} {n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings 1 n) :
    parametricLocalizedSpinFoamWeight w n physical ≈
      parametricLocalizedWeightProduct w n
        (surfaceComponentLabels n physical) := by
  have hfactor := parametricLocalizedSpinFoamWeight_unionLabels_factor w n
    (surfaceComponentLabels n physical)
    (surfaceComponentLabels_physicalFamily n physical)
    (surfaceComponentLabels_linkSeparatedFamily n physical)
  rw [surfaceComponentLabels_union_eq_physical hphysical] at hfactor
  exact hfactor

def parametricCanonicalComponentProductPartition (w : Q') (n : Nat) : Q' :=
  listQSum
    (fun physical => parametricLocalizedWeightProduct w n
      (surfaceComponentLabels n physical))
    (explicitPhysicalLabellings 1 n)

private theorem listQSum_congr_mem_local {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | head :: tail, h =>
      Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_congr_mem_local tail
          (fun x hx => h x (List.mem_cons_of_mem head hx)))

theorem parametricLocalizedSpinFoamPartition_eq_componentProduct
    (w : Q') (n : Nat) :
    parametricLocalizedSpinFoamPartition w n ≈
      parametricCanonicalComponentProductPartition w n := by
  unfold parametricLocalizedSpinFoamPartition
    parametricCanonicalComponentProductPartition
  apply listQSum_congr_mem_local
  intro physical hphysical
  exact parametricLocalizedSpinFoamWeight_surfaceComponent_factor hphysical

end YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponentLabels.surfaceComponentLabels_physicalFamily
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponentLabels.surfaceComponentLabels_linkSeparatedFamily
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponentLabels.surfaceComponentLabels_union_eq_physical
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponentLabels.parametricLocalizedSpinFoamWeight_surfaceComponent_factor
#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponentLabels.parametricLocalizedSpinFoamPartition_eq_componentProduct
