/-
# The canonical connected-surface gas

The cutoff-one support sum is reorganized into a duplicate-free list of
families of connected face supports.  Every support inside a family is put in
the ambient physical-face order.  This removes both irrelevant orderings from
the component algorithm while retaining its Type-level connectivity witness.

Distinct members of every family are disjoint and share no physical link.
Thus this is the corrected surface-gas compatibility, stronger than the old
plaquette-only hard-core predicate.  The exact spin-foam partition is proved
equal to the resulting family-activity sum without a multiplicity factor.
-/

import YMGap.Continuum.Z4CutoffOneSupportBijection

namespace YMGap.Continuum.Z4CanonicalConnectedSurfaceGas

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def decodeMapMember {A B : Type} [DecidableEq B] (f : A → B) :
    ∀ (xs : List A) (value : B), value ∈ xs.map f →
      Σ' source : A, (source ∈ xs) ×' (f source = value)
  | [], value, hmem => absurd hmem List.not_mem_nil
  | head :: tail, value, hmem => by
      by_cases hhead : value = f head
      · exact ⟨head, List.mem_cons_self, hhead.symm⟩
      · have htail : value ∈ tail.map f :=
          (List.mem_cons.mp hmem).resolve_left hhead
        obtain ⟨source, hsource, heq⟩ :=
          decodeMapMember f tail value htail
        exact ⟨source, List.mem_cons_of_mem head hsource, heq⟩

def surfaceComponents_allNonemptyLocal
    (n : Nat) (physical : EdgeLabelling) :
    AllNonempty (surfaceComponents n physical) :=
  graphComponents_allNonempty (faceLinkAdjacentB n)
    (excitedPlaquetteIds n physical)

/-! ## 1. Canonical ordering of every component support -/

def canonicalFaceSupport (n : Nat) (component : List Nat) : List Nat :=
  (physicalFaceEdges n).filter (fun edge => decide (edge ∈ component))

theorem mem_canonicalFaceSupport_iff
    {n : Nat} {component : List Nat}
    (hsubset : ∀ {edge}, edge ∈ component → edge ∈ physicalFaceEdges n)
    (edge : Nat) :
    edge ∈ canonicalFaceSupport n component ↔ edge ∈ component := by
  unfold canonicalFaceSupport
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨hsubset h, h⟩

theorem componentLabel_canonicalFaceSupport
    {n : Nat} {component : List Nat}
    (hsubset : ∀ {edge}, edge ∈ component → edge ∈ physicalFaceEdges n) :
    componentLabel (canonicalFaceSupport n component) =
      componentLabel component := by
  funext edge
  unfold componentLabel
  have hiff := mem_canonicalFaceSupport_iff hsubset edge
  by_cases hmem : edge ∈ component
  · have hcanonical : edge ∈ canonicalFaceSupport n component := hiff.2 hmem
    simp [hmem, hcanonical]
  · have hcanonical : edge ∉ canonicalFaceSupport n component := by
      intro h
      exact hmem (hiff.1 h)
    simp [hmem, hcanonical]

theorem canonicalFaceSupport_mem_cutoffOneFaceSupports
    (n : Nat) (component : List Nat) :
    canonicalFaceSupport n component ∈ cutoffOneFaceSupports n := by
  unfold canonicalFaceSupport cutoffOneFaceSupports
  exact filter_mem_sublists _ _

/-! ## 2. Canonical connected families and their invariants -/

def canonicalSurfaceFamily (n : Nat) (support : List Nat) :
    List (List Nat) :=
  (surfaceComponents n (componentLabel support)).map
    (canonicalFaceSupport n)

theorem canonicalSurfaceFamily_labels_eq
    (n : Nat) (support : List Nat) :
    (canonicalSurfaceFamily n support).map componentLabel =
      surfaceComponentLabels n (componentLabel support) := by
  unfold canonicalSurfaceFamily surfaceComponentLabels
  rw [List.map_map]
  apply List.map_congr_left
  intro component hcomponent
  simp only [Function.comp_apply]
  exact componentLabel_canonicalFaceSupport
    (surfaceComponent_subset_physicalFaceEdges hcomponent)

def canonicalSurfaceFamily_allNonempty
    (n : Nat) (support : List Nat) :
    AllNonempty (canonicalSurfaceFamily n support) := by
  intro canonical hcanonical
  obtain ⟨component, hcomponent, hcanonicalEq⟩ :=
    decodeMapMember (canonicalFaceSupport n)
      (surfaceComponents n (componentLabel support)) canonical hcanonical
  rw [← hcanonicalEq]
  obtain ⟨point, hpoint⟩ :=
    surfaceComponents_allNonemptyLocal n (componentLabel support)
      component hcomponent
  refine ⟨point, ?_⟩
  exact (mem_canonicalFaceSupport_iff
    (surfaceComponent_subset_physicalFaceEdges hcomponent) point).2 hpoint

def canonicalSurfaceFamily_allConnected
    (n : Nat) (support : List Nat) :
    AllConnected (faceLinkAdjacentB n)
      (canonicalSurfaceFamily n support) := by
  intro canonical hcanonical
  obtain ⟨component, hcomponent, hcanonicalEq⟩ :=
    decodeMapMember (canonicalFaceSupport n)
      (surfaceComponents n (componentLabel support)) canonical hcanonical
  rw [← hcanonicalEq]
  have hsubset : ∀ {edge}, edge ∈ component → edge ∈ physicalFaceEdges n :=
    surfaceComponent_subset_physicalFaceEdges hcomponent
  intro left right hleft hright
  have hchain := surfaceComponents_allConnected n (componentLabel support)
    component hcomponent left right
    ((mem_canonicalFaceSupport_iff hsubset left).1 hleft)
    ((mem_canonicalFaceSupport_iff hsubset right).1 hright)
  exact ChainIn.mono
    (fun point hpoint =>
      (mem_canonicalFaceSupport_iff hsubset point).2 hpoint)
    hchain

theorem canonicalSurfaceFamily_distinctSeparated
    (n : Nat) (support : List Nat) :
    DistinctSeparated (faceLinkAdjacentB n)
      (canonicalSurfaceFamily n support) := by
  intro left hleft right hright hne
  obtain ⟨leftRaw, hleftRaw, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨rightRaw, hrightRaw, rfl⟩ := List.mem_map.mp hright
  have hrawNe : leftRaw ≠ rightRaw := by
    intro heq
    subst rightRaw
    exact hne rfl
  have hleftSubset : ∀ {edge}, edge ∈ leftRaw →
      edge ∈ physicalFaceEdges n :=
    surfaceComponent_subset_physicalFaceEdges hleftRaw
  have hrightSubset : ∀ {edge}, edge ∈ rightRaw →
      edge ∈ physicalFaceEdges n :=
    surfaceComponent_subset_physicalFaceEdges hrightRaw
  intro leftPoint hleftPoint rightPoint hrightPoint
  exact surfaceComponents_distinctSeparated n (componentLabel support)
    leftRaw hleftRaw rightRaw hrightRaw hrawNe
    leftPoint
      ((mem_canonicalFaceSupport_iff hleftSubset leftPoint).1 hleftPoint)
    rightPoint
      ((mem_canonicalFaceSupport_iff hrightSubset rightPoint).1 hrightPoint)

theorem canonicalSurfaceFamily_distinctDisjoint
    (n : Nat) (support : List Nat) :
    DistinctDisjoint (canonicalSurfaceFamily n support) := by
  intro left hleft right hright hne
  obtain ⟨leftRaw, hleftRaw, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨rightRaw, hrightRaw, rfl⟩ := List.mem_map.mp hright
  have hrawNe : leftRaw ≠ rightRaw := by
    intro heq
    subst rightRaw
    exact hne rfl
  have hleftSubset : ∀ {edge}, edge ∈ leftRaw →
      edge ∈ physicalFaceEdges n :=
    surfaceComponent_subset_physicalFaceEdges hleftRaw
  have hrightSubset : ∀ {edge}, edge ∈ rightRaw →
      edge ∈ physicalFaceEdges n :=
    surfaceComponent_subset_physicalFaceEdges hrightRaw
  intro point hpoint hpointRight
  exact surfaceComponents_distinctDisjoint n (componentLabel support)
    leftRaw hleftRaw rightRaw hrightRaw hrawNe point
    ((mem_canonicalFaceSupport_iff hleftSubset point).1 hpoint)
    ((mem_canonicalFaceSupport_iff hrightSubset point).1 hpointRight)

theorem canonicalSurfaceFamily_covers
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    Covers support (canonicalSurfaceFamily n support) := by
  intro edge
  have hexcited := excitedPlaquetteIds_componentLabel_eq_support hsupport
  constructor
  · intro hedge
    have hedgeExcited :
        edge ∈ excitedPlaquetteIds n (componentLabel support) := by
      rw [hexcited]
      exact hedge
    obtain ⟨component, hcomponent, hedgeComponent⟩ :=
      (surfaceComponents_cover n (componentLabel support) edge).1
        hedgeExcited
    refine ⟨canonicalFaceSupport n component, ?_, ?_⟩
    · unfold canonicalSurfaceFamily
      exact List.mem_map.mpr ⟨component, hcomponent, rfl⟩
    · exact (mem_canonicalFaceSupport_iff
        (surfaceComponent_subset_physicalFaceEdges hcomponent) edge).2
          hedgeComponent
  · rintro ⟨canonical, hcanonical, hedgeCanonical⟩
    unfold canonicalSurfaceFamily at hcanonical
    obtain ⟨component, hcomponent, hcanonicalEq⟩ :=
      List.mem_map.mp hcanonical
    subst canonical
    have hedgeComponent := (mem_canonicalFaceSupport_iff
      (surfaceComponent_subset_physicalFaceEdges hcomponent) edge).1
        hedgeCanonical
    have hedgeExcited :=
      (surfaceComponents_cover n (componentLabel support) edge).2
        ⟨component, hcomponent, hedgeComponent⟩
    rw [hexcited] at hedgeExcited
    exact hedgeExcited

theorem canonicalSurfaceFamily_nodup
    (n : Nat) (support : List Nat) :
    (canonicalSurfaceFamily n support).Nodup := by
  unfold canonicalSurfaceFamily
  apply nodup_map_of_injOn (canonicalFaceSupport n)
    (surfaceComponents n (componentLabel support))
    (surfaceComponents_nodup n (componentLabel support))
  intro left hleft right hright heq
  by_cases hne : left ≠ right
  · obtain ⟨point, hpoint⟩ :=
      surfaceComponents_allNonemptyLocal n (componentLabel support) left hleft
    have hleftSubset : ∀ {edge}, edge ∈ left →
        edge ∈ physicalFaceEdges n :=
      surfaceComponent_subset_physicalFaceEdges hleft
    have hrightSubset : ∀ {edge}, edge ∈ right →
        edge ∈ physicalFaceEdges n :=
      surfaceComponent_subset_physicalFaceEdges hright
    have hcanonicalPoint : point ∈ canonicalFaceSupport n left :=
      (mem_canonicalFaceSupport_iff hleftSubset point).2 hpoint
    rw [heq] at hcanonicalPoint
    have hpointRight : point ∈ right :=
      (mem_canonicalFaceSupport_iff hrightSubset point).1 hcanonicalPoint
    exact absurd hpointRight
      (surfaceComponents_distinctDisjoint n (componentLabel support)
        left hleft right hright hne point hpoint)
  · exact Decidable.byContradiction hne

theorem canonicalSurfaceFamily_members_are_faceSupports
    (n : Nat) (support : List Nat) :
    ∀ component, component ∈ canonicalSurfaceFamily n support →
      component ∈ cutoffOneFaceSupports n := by
  intro component hcomponent
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp hcomponent
  exact canonicalFaceSupport_mem_cutoffOneFaceSupports n raw

/-! ## 3. A duplicate-free finite gas domain -/

def canonicalConnectedSurfaceGas (n : Nat) : List (List (List Nat)) :=
  (cutoffOneFaceSupports n).map (canonicalSurfaceFamily n)

theorem canonicalConnectedSurfaceGas_nodup (n : Nat) :
    (canonicalConnectedSurfaceGas n).Nodup := by
  unfold canonicalConnectedSurfaceGas
  apply nodup_map_of_injOn (canonicalSurfaceFamily n)
    (cutoffOneFaceSupports n) (cutoffOneFaceSupports_nodup n)
  intro left hleft right hright heq
  apply sublists_eq_of_mem_iff (physicalFaceEdges n) left right
    (physicalFaceEdges_nodup n) hleft hright
  intro edge
  have hleftCover := canonicalSurfaceFamily_covers hleft
  have hrightCover := canonicalSurfaceFamily_covers hright
  rw [hleftCover edge, hrightCover edge, heq]

def canonicalConnectedSurfaceGas_correctedCompatibility
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalConnectedSurfaceGas n) :
    AllNonempty family ×'
      AllConnected (faceLinkAdjacentB n) family ×'
        DistinctDisjoint family ×'
          DistinctSeparated (faceLinkAdjacentB n) family := by
  obtain ⟨support, _, hfamilyEq⟩ :=
    decodeMapMember (canonicalSurfaceFamily n)
      (cutoffOneFaceSupports n) family hfamily
  rw [← hfamilyEq]
  exact ⟨canonicalSurfaceFamily_allNonempty n support,
    canonicalSurfaceFamily_allConnected n support,
    canonicalSurfaceFamily_distinctDisjoint n support,
    canonicalSurfaceFamily_distinctSeparated n support⟩

/-! ## 4. Exact family activities and the spin-foam partition -/

def canonicalSurfaceActivity (w : Q') (n : Nat)
    (support : List Nat) : Q' :=
  parametricLocalizedSpinFoamWeight w n (componentLabel support)

def canonicalSurfaceFamilyActivity (w : Q') (n : Nat) :
    List (List Nat) → Q'
  | [] => 1
  | component :: rest =>
      canonicalSurfaceActivity w n component *
        canonicalSurfaceFamilyActivity w n rest

theorem parametricLocalizedWeightProduct_componentLabels
    (w : Q') (n : Nat) : ∀ family : List (List Nat),
    parametricLocalizedWeightProduct w n (family.map componentLabel) =
      canonicalSurfaceFamilyActivity w n family
  | [] => rfl
  | component :: rest => by
      change canonicalSurfaceActivity w n component *
          parametricLocalizedWeightProduct w n (rest.map componentLabel) =
        canonicalSurfaceActivity w n component *
          canonicalSurfaceFamilyActivity w n rest
      rw [parametricLocalizedWeightProduct_componentLabels w n rest]

theorem supportGasTerm_eq_canonicalFamilyActivity
    (w : Q') (n : Nat) (support : List Nat) :
    parametricLocalizedWeightProduct w n
        (surfaceComponentLabels n (componentLabel support)) =
      canonicalSurfaceFamilyActivity w n
        (canonicalSurfaceFamily n support) := by
  rw [← canonicalSurfaceFamily_labels_eq,
    parametricLocalizedWeightProduct_componentLabels]

def parametricCanonicalConnectedSurfaceGasPartition
    (w : Q') (n : Nat) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity w n)
    (canonicalConnectedSurfaceGas n)

private theorem listQSum_map_local {A B : Type}
    (f : B → Q') (g : A → B) : ∀ xs : List A,
    listQSum f (xs.map g) = listQSum (fun x => f (g x)) xs
  | [] => rfl
  | _ :: xs => congrArg (fun tail => f (g _) + tail)
      (listQSum_map_local f g xs)

private theorem listQSum_congr_eq_local {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x = g x) →
      listQSum f xs = listQSum g xs
  | [], _ => rfl
  | head :: tail, h => by
      change f head + listQSum f tail = g head + listQSum g tail
      rw [h head List.mem_cons_self,
        listQSum_congr_eq_local tail
          (fun x hx => h x (List.mem_cons_of_mem head hx))]

theorem parametricCanonicalSupportGasPartition_eq_connectedSurfaceGas
    (w : Q') (n : Nat) :
    parametricCanonicalSupportGasPartition w n =
      parametricCanonicalConnectedSurfaceGasPartition w n := by
  unfold parametricCanonicalSupportGasPartition
    parametricCanonicalConnectedSurfaceGasPartition
    canonicalConnectedSurfaceGas
  rw [listQSum_map_local]
  apply listQSum_congr_eq_local
  intro support _
  exact supportGasTerm_eq_canonicalFamilyActivity w n support

theorem parametricLocalizedSpinFoamPartition_eq_connectedSurfaceGas
    (w : Q') (n : Nat) :
    parametricLocalizedSpinFoamPartition w n ≈
      parametricCanonicalConnectedSurfaceGasPartition w n := by
  exact Q'.eqv_trans _ _ _
    (parametricLocalizedSpinFoamPartition_eq_supportGas w n)
    (Q'.eqv_of_eq
      (parametricCanonicalSupportGasPartition_eq_connectedSurfaceGas w n))

/-! ## 5. Exact strong-coupling activity bounds on the gas -/

theorem canonicalSurfaceActivity_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (n : Nat) (support : List Nat) :
    (0 : Q') ≤ canonicalSurfaceActivity w n support := by
  unfold canonicalSurfaceActivity
  exact parametricLocalizedSpinFoamWeight_nonnegative hw n _

theorem canonicalSurfaceActivity_anchor_le_envelopePow
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    canonicalSurfaceActivity anchorCoupling n support ≤
      anchorPerFaceEnvelope ^ support.length := by
  unfold canonicalSurfaceActivity
  have hphysical :
      componentLabel support ∈ explicitPhysicalLabellings 1 n := by
    rw [explicitPhysicalLabellings_one_eq_supportIndicators]
    exact List.mem_map.mpr ⟨support, hsupport, rfl⟩
  have hbound :=
    parametricLocalizedSpinFoamWeight_anchor_le_envelopePow hphysical
  rw [excitedPlaquetteEntries_componentLabel_length hsupport] at hbound
  exact hbound

end YMGap.Continuum.Z4CanonicalConnectedSurfaceGas

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.canonicalSurfaceFamily_allConnected
#print axioms YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.canonicalSurfaceFamily_distinctSeparated
#print axioms YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.canonicalSurfaceFamily_covers
#print axioms YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.canonicalSurfaceFamily_nodup
#print axioms YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.canonicalConnectedSurfaceGas_nodup
#print axioms YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.canonicalConnectedSurfaceGas_correctedCompatibility
#print axioms YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.parametricLocalizedSpinFoamPartition_eq_connectedSurfaceGas
#print axioms YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.canonicalSurfaceActivity_anchor_le_envelopePow
