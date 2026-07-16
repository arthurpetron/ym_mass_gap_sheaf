/-
# The affine embedded cell as a literal restricted polymer gas

The exact uniformly shifted embedding is useful for a boundary comparison only
after its image has been characterized atom by atom.  This file supplies a
constructive inverse geometric encoding.  A target canonical root is in the
uniform-padding image exactly when every plaquette in its geometric support lies
in the translated source plaquette list.  Consequently a compatible target
family belongs to the embedded cell exactly when all of its roots pass this
translated-region test.

No choice is used: the inverse root is obtained by subtracting the known
nonnegative uniform padding and applying the canonical `geometricSupportIds`
encoder in the source box.
-/

import YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
import YMGap.Continuum.Z4ShiftedSubboxCarrierTail

namespace YMGap.Continuum.Z4UniformShiftEmbeddedRegion

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

/-! ## 1. Constructive inverse of a known nonnegative uniform padding -/

def uniformUnshiftVertex (padding : Nat) : Z4Vertex → Z4Vertex
  | (a, b, c, d) =>
      (a - padding, b - padding, c - padding, d - padding)

def uniformUnshiftPlaquette (padding : Nat) (plaquette : Z4Plaq) : Z4Plaq :=
  (uniformUnshiftVertex padding plaquette.1, plaquette.2)

theorem uniformUnshiftPlaquette_uniformShiftPlaquette
    (padding : Nat) (plaquette : Z4Plaq) :
    uniformUnshiftPlaquette padding (uniformShiftPlaquette padding plaquette) =
      plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp [uniformUnshiftPlaquette, uniformUnshiftVertex,
    uniformShiftPlaquette, uniformShiftVertex]

theorem uniformShiftPlaquette_uniformUnshiftPlaquette_of_mem
    {padding base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ uniformShiftedPlaquetteList padding base) :
    uniformShiftPlaquette padding (uniformUnshiftPlaquette padding plaquette) =
      plaquette := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq, uniformUnshiftPlaquette_uniformShiftPlaquette]

theorem uniformUnshiftPlaquette_mem_box_of_shifted
    {padding base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ uniformShiftedPlaquetteList padding base) :
    uniformUnshiftPlaquette padding plaquette ∈ boxPlaquettes base := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq, uniformUnshiftPlaquette_uniformShiftPlaquette]
  exact hsource

def uniformUnshiftAdjacentOfShifted
    {padding base : Nat} {left right : Z4Plaq}
    (hleft : left ∈ uniformShiftedPlaquetteList padding base)
    (hright : right ∈ uniformShiftedPlaquetteList padding base)
    (hadj : z4Chain.toLattice.Adjacent left right) :
    z4Chain.toLattice.Adjacent
      (uniformUnshiftPlaquette padding left)
      (uniformUnshiftPlaquette padding right) := by
  apply unshiftActualAdjacent padding
  rw [uniformShiftPlaquette_uniformUnshiftPlaquette_of_mem hleft,
    uniformShiftPlaquette_uniformUnshiftPlaquette_of_mem hright]
  exact hadj

def uniformUnshiftChainOnShifted
    (padding base : Nat) {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ uniformShiftedPlaquetteList padding base) :
    {first last : Z4Plaq} →
      (hfirst : first ∈ support) →
      ChainIn z4Chain.toLattice support first last →
      ChainIn z4Chain.toLattice
        (support.map (uniformUnshiftPlaquette padding))
        (uniformUnshiftPlaquette padding first)
        (uniformUnshiftPlaquette padding last)
  | _, _, _, .refl plaquette => .refl _
  | _, _, hfirst, .step adjacent hnext rest =>
      .step
        (uniformUnshiftAdjacentOfShifted
          (hsubset _ hfirst) (hsubset _ hnext) adjacent)
        (List.mem_map.mpr ⟨_, hnext, rfl⟩)
        (uniformUnshiftChainOnShifted padding base hsubset hnext rest)

def uniformUnshiftConnectedOnShifted
    (padding base : Nat) {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ uniformShiftedPlaquetteList padding base)
    (hconnected : connectedIn (L := z4Chain.toLattice) support) :
    connectedIn (L := z4Chain.toLattice)
      (support.map (uniformUnshiftPlaquette padding)) := by
  intro first last hfirst hlast
  obtain ⟨sourceFirst, hsourceFirst, hfirstEq⟩ :=
    decodeMapMember (uniformUnshiftPlaquette padding) support first hfirst
  obtain ⟨sourceLast, hsourceLast, hlastEq⟩ :=
    decodeMapMember (uniformUnshiftPlaquette padding) support last hlast
  rw [← hfirstEq, ← hlastEq]
  exact uniformUnshiftChainOnShifted padding base hsubset hsourceFirst
    (hconnected sourceFirst sourceLast hsourceFirst hsourceLast)

/-! ## 2. The inverse canonical root and exact round trip -/

def uniformUnshiftCanonicalRoot (padding base : Nat)
    (target : List Nat) : List Nat :=
  geometricSupportIds base
    ((geometricPolymer (uniformPaddedBase padding base) target).map
      (uniformUnshiftPlaquette padding))

def TargetRootInsideUniformShift (padding base : Nat)
    (target : List Nat) : Prop :=
  ∀ plaquette, plaquette ∈ geometricPolymer (uniformPaddedBase padding base) target →
    plaquette ∈ uniformShiftedPlaquetteList padding base

def targetRootInsideUniformShiftB (padding base : Nat)
    (target : List Nat) : Bool :=
  (geometricPolymer (uniformPaddedBase padding base) target).all
    (fun plaquette => decide
      (plaquette ∈ uniformShiftedPlaquetteList padding base))

theorem targetRootInsideUniformShiftB_true_iff
    (padding base : Nat) (target : List Nat) :
    targetRootInsideUniformShiftB padding base target = true ↔
      TargetRootInsideUniformShift padding base target := by
  unfold targetRootInsideUniformShiftB TargetRootInsideUniformShift
  rw [List.all_eq_true]
  simp only [decide_eq_true_eq]

theorem uniformUnshiftCanonicalRoot_sameSupport
    {padding base : Nat} {target : List Nat}
    (hinside : TargetRootInsideUniformShift padding base target) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer base
        (uniformUnshiftCanonicalRoot padding base target))
      ((geometricPolymer (uniformPaddedBase padding base) target).map
        (uniformUnshiftPlaquette padding)) := by
  unfold uniformUnshiftCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨targetPlaquette, htarget, heq⟩ :=
    List.mem_map.mp hplaquette
  rw [← heq]
  exact uniformUnshiftPlaquette_mem_box_of_shifted (hinside _ htarget)

def uniformUnshiftCanonicalRoot_nonempty
    {padding base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (uniformPaddedBase padding base))
    (hinside : TargetRootInsideUniformShift padding base target) :
    Σ' face : Nat, face ∈ uniformUnshiftCanonicalRoot padding base target := by
  obtain ⟨targetFace, htargetFace⟩ :=
    canonicalSurfacePolymers_allNonempty (uniformPaddedBase padding base) target htarget
  have htargetGeom : boxPlaquetteAt (uniformPaddedBase padding base) targetFace ∈
      geometricPolymer (uniformPaddedBase padding base) target :=
    List.mem_map.mpr ⟨targetFace, htargetFace, rfl⟩
  have hunshifted : uniformUnshiftPlaquette padding
        (boxPlaquetteAt (uniformPaddedBase padding base) targetFace) ∈
      (geometricPolymer (uniformPaddedBase padding base) target).map
        (uniformUnshiftPlaquette padding) :=
    List.mem_map.mpr
      ⟨boxPlaquetteAt (uniformPaddedBase padding base) targetFace, htargetGeom, rfl⟩
  have hsourceGeom :=
    (uniformUnshiftCanonicalRoot_sameSupport hinside).2 _ hunshifted
  obtain ⟨sourceFace, hsourceFace, _⟩ :=
    decodeMapMember (boxPlaquetteAt base)
      (uniformUnshiftCanonicalRoot padding base target)
      (uniformUnshiftPlaquette padding
        (boxPlaquetteAt (uniformPaddedBase padding base) targetFace)) hsourceGeom
  exact ⟨sourceFace, hsourceFace⟩

def uniformUnshiftCanonicalRoot_connected
    {padding base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (uniformPaddedBase padding base))
    (hinside : TargetRootInsideUniformShift padding base target) :
    InternallyConnected (faceLinkAdjacentB base)
      (uniformUnshiftCanonicalRoot padding base target) := by
  unfold uniformUnshiftCanonicalRoot
  apply geometricSupportIds_connected
  · intro plaquette hplaquette
    obtain ⟨targetPlaquette, htargetPlaquette, heq⟩ :=
      List.mem_map.mp hplaquette
    rw [← heq]
    exact uniformUnshiftPlaquette_mem_box_of_shifted
      (hinside _ htargetPlaquette)
  · apply uniformUnshiftConnectedOnShifted padding base hinside
    exact numericalConnectedToGeometric
      ((canonicalSurfacePolymers_allConnected (uniformPaddedBase padding base))
        target htarget)

theorem uniformUnshiftCanonicalRoot_canonical
    {padding base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (uniformPaddedBase padding base))
    (hinside : TargetRootInsideUniformShift padding base target) :
    uniformUnshiftCanonicalRoot padding base target ∈
      canonicalSurfacePolymers base :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports base _)
    (uniformUnshiftCanonicalRoot_nonempty htarget hinside)
    (uniformUnshiftCanonicalRoot_connected htarget hinside)

private theorem sameSupport_map_local
    {left right : List Z4Plaq} (mapP : Z4Plaq → Z4Plaq)
    (h : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map mapP) (right.map mapP) := by
  constructor
  · intro item hitem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hitem
    exact List.mem_map.mpr ⟨source, h.1 _ hsource, rfl⟩
  · intro item hitem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hitem
    exact List.mem_map.mpr ⟨source, h.2 _ hsource, rfl⟩

theorem uniformUnshiftCanonicalRoot_roundtrip
    {padding base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (uniformPaddedBase padding base))
    (hinside : TargetRootInsideUniformShift padding base target) :
    uniformShiftCanonicalRoot padding base
        (uniformUnshiftCanonicalRoot padding base target) = target := by
  let source := uniformUnshiftCanonicalRoot padding base target
  have hsource : source ∈ canonicalSurfacePolymers base :=
    uniformUnshiftCanonicalRoot_canonical htarget hinside
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    (uniformShiftCanonicalRoot_canonical hsource) htarget
  have hshift := uniformShiftCanonicalRoot_sameSupport
    (padding := padding) hsource
  have hunshift := uniformUnshiftCanonicalRoot_sameSupport hinside
  have hmapped := sameSupport_map_local (uniformShiftPlaquette padding) hunshift
  have hround : sameSupport (L := z4Chain.toLattice)
      (((geometricPolymer (uniformPaddedBase padding base) target).map
          (uniformUnshiftPlaquette padding)).map
        (uniformShiftPlaquette padding))
      (geometricPolymer (uniformPaddedBase padding base) target) := by
    constructor
    · intro plaquette hplaquette
      obtain ⟨unshifted, hunshifted, heq⟩ :=
        List.mem_map.mp hplaquette
      obtain ⟨original, horiginal, hunshiftEq⟩ :=
        List.mem_map.mp hunshifted
      subst unshifted
      rw [uniformShiftPlaquette_uniformUnshiftPlaquette_of_mem
        (hinside _ horiginal)] at heq
      rw [← heq]
      exact horiginal
    · intro plaquette hplaquette
      apply List.mem_map.mpr
      refine ⟨uniformUnshiftPlaquette padding plaquette, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨plaquette, hplaquette, rfl⟩
      · exact uniformShiftPlaquette_uniformUnshiftPlaquette_of_mem
          (hinside _ hplaquette)
  exact sameSupport_trans hshift
    (sameSupport_trans hmapped hround)

/-! ## 3. Atomwise image characterization -/

def uniformShiftCanonicalRoots (padding base : Nat) : List (List Nat) :=
  (canonicalSurfacePolymers base).map
    (uniformShiftCanonicalRoot padding base)

theorem uniformShiftCanonicalRoots_nodup (padding base : Nat) :
    (uniformShiftCanonicalRoots padding base).Nodup := by
  unfold uniformShiftCanonicalRoots
  apply nodup_map_of_injOn (uniformShiftCanonicalRoot padding base)
    (canonicalSurfacePolymers base)
    (canonicalSurfacePolymers_nodup base)
  intro left hleft right hright heq
  exact uniformShiftCanonicalRoot_injective_on_canonical hleft hright heq

theorem targetRootInside_uniformShiftCanonicalRoot
    {padding base : Nat} {source : List Nat}
    (hsource : source ∈ canonicalSurfacePolymers base) :
    TargetRootInsideUniformShift padding base
      (uniformShiftCanonicalRoot padding base source) := by
  intro plaquette hplaquette
  have hmapped := (uniformShiftCanonicalRoot_sameSupport hsource).1
    _ hplaquette
  obtain ⟨sourcePlaquette, hsourcePlaquette, heq⟩ :=
    List.mem_map.mp hmapped
  rw [← heq]
  unfold uniformShiftedPlaquetteList
  apply List.mem_map.mpr
  exact ⟨sourcePlaquette,
    geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hsource)
      sourcePlaquette hsourcePlaquette, rfl⟩

theorem mem_uniformShiftCanonicalRoots_iff
    {padding base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (uniformPaddedBase padding base)) :
    target ∈ uniformShiftCanonicalRoots padding base ↔
      TargetRootInsideUniformShift padding base target := by
  constructor
  · intro htargetImage
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htargetImage
    rw [← heq]
    exact targetRootInside_uniformShiftCanonicalRoot hsource
  · intro hinside
    apply List.mem_map.mpr
    exact ⟨uniformUnshiftCanonicalRoot padding base target,
      uniformUnshiftCanonicalRoot_canonical htarget hinside,
      uniformUnshiftCanonicalRoot_roundtrip htarget hinside⟩

theorem targetRootInsideUniformShiftB_eq_memberB
    {padding base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (uniformPaddedBase padding base)) :
    targetRootInsideUniformShiftB padding base target =
      memberB (uniformShiftCanonicalRoots padding base) target := by
  apply Bool.eq_iff_iff.mpr
  rw [targetRootInsideUniformShiftB_true_iff,
    memberB_eq_true_iff, ← mem_uniformShiftCanonicalRoots_iff htarget]

/-! ## 4. Compatible-family image characterization -/

def uniformUnshiftFamily (padding base : Nat)
    (targetFamily : List (List Nat)) : List (List Nat) :=
  (canonicalSurfacePolymers base).filter
    (fun source => decide
      (uniformShiftCanonicalRoot padding base source ∈ targetFamily))

theorem mem_uniformUnshiftFamily_iff
    (padding base : Nat) (targetFamily : List (List Nat))
    (source : List Nat) :
    source ∈ uniformUnshiftFamily padding base targetFamily ↔
      source ∈ canonicalSurfacePolymers base ∧
        uniformShiftCanonicalRoot padding base source ∈ targetFamily := by
  unfold uniformUnshiftFamily
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem uniformShiftFamily_uniformUnshift_mem_iff
    {padding base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (hallInside : ∀ target, target ∈ targetFamily →
      TargetRootInsideUniformShift padding base target)
    (target : List Nat) :
    target ∈ uniformShiftFamily padding base
        (uniformUnshiftFamily padding base targetFamily) ↔
      target ∈ targetFamily := by
  constructor
  · intro htargetShift
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htargetShift
    exact heq ▸ (mem_uniformUnshiftFamily_iff
      padding base targetFamily source).1 hsource |>.2
  · intro htargetMem
    have htargetCanonical :=
      compatibleAmbientFamily_member_ambient htarget htargetMem
    have hinside := hallInside target htargetMem
    let source := uniformUnshiftCanonicalRoot padding base target
    have hsourceCanonical : source ∈ canonicalSurfacePolymers base :=
      uniformUnshiftCanonicalRoot_canonical htargetCanonical hinside
    have hround : uniformShiftCanonicalRoot padding base source = target :=
      uniformUnshiftCanonicalRoot_roundtrip htargetCanonical hinside
    apply List.mem_map.mpr
    refine ⟨source, (mem_uniformUnshiftFamily_iff
      padding base targetFamily source).2 ?_, hround⟩
    exact ⟨hsourceCanonical, by simpa only [hround] using htargetMem⟩

theorem uniformUnshiftFamily_nodup (padding base : Nat)
    (targetFamily : List (List Nat)) :
    (uniformUnshiftFamily padding base targetFamily).Nodup := by
  unfold uniformUnshiftFamily
  exact List.filter_sublist.nodup
    (canonicalSurfacePolymers_nodup base)

theorem uniformUnshiftFamily_mem_compatible
    {padding base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base)) :
    uniformUnshiftFamily padding base targetFamily ∈
      canonicalCompatibleAmbientFamilies base := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  refine ⟨filter_mem_sublists _ _, ?_⟩
  rw [← genericFamilyCompatibleB_eq_canonical]
  apply familyCompatibleB_of_pairwise
    (canonicalPolymerCompatibleB base)
    (uniformUnshiftFamily_nodup padding base targetFamily)
  intro left hleft right hright hne
  have hleftParts := (mem_uniformUnshiftFamily_iff
    padding base targetFamily left).1 hleft
  have hrightParts := (mem_uniformUnshiftFamily_iff
    padding base targetFamily right).1 hright
  have hshiftNe : uniformShiftCanonicalRoot padding base left ≠
      uniformShiftCanonicalRoot padding base right := by
    intro heq
    exact hne (uniformShiftCanonicalRoot_injective_on_canonical
      hleftParts.1 hrightParts.1 heq)
  have htargetInvariants := compatibleAmbientFamily_invariants htarget
  have hdisjoint := htargetInvariants.1
      (uniformShiftCanonicalRoot padding base left) hleftParts.2
      (uniformShiftCanonicalRoot padding base right) hrightParts.2 hshiftNe
  have hseparated := htargetInvariants.2
      (uniformShiftCanonicalRoot padding base left) hleftParts.2
      (uniformShiftCanonicalRoot padding base right) hrightParts.2 hshiftNe
  unfold canonicalPolymerCompatibleB
  apply List.all_eq_true.mpr
  intro leftFace hleftFace
  apply List.all_eq_true.mpr
  intro rightFace hrightFace
  have hleftTarget := uniformShiftRootMemberTarget
    (padding := padding)
    (canonicalSurfacePolymer_mem_faceSupports hleftParts.1) hleftFace
  have hrightTarget := uniformShiftRootMemberTarget
    (padding := padding)
    (canonicalSurfacePolymer_mem_faceSupports hrightParts.1) hrightFace
  obtain ⟨leftTarget, hleftTargetMem, hleftEq⟩ := hleftTarget
  obtain ⟨rightTarget, hrightTargetMem, hrightEq⟩ := hrightTarget
  have hfaceNe : leftFace ≠ rightFace := by
    intro heq
    subst rightFace
    have htargetEq : leftTarget = rightTarget :=
      boxPlaquetteAt_injective_on_physical
        (mem_of_mem_sublists (physicalFaceEdges (uniformPaddedBase padding base))
          (uniformShiftCanonicalRoot padding base left)
          (canonicalSurfacePolymer_mem_faceSupports
            (uniformShiftCanonicalRoot_canonical hleftParts.1))
          leftTarget hleftTargetMem)
        (mem_of_mem_sublists (physicalFaceEdges (uniformPaddedBase padding base))
          (uniformShiftCanonicalRoot padding base right)
          (canonicalSurfacePolymer_mem_faceSupports
            (uniformShiftCanonicalRoot_canonical hrightParts.1))
          rightTarget hrightTargetMem)
        (hleftEq.symm.trans hrightEq)
    subst rightTarget
    exact hdisjoint leftTarget hleftTargetMem hrightTargetMem
  have hnotAdjacent : faceLinkAdjacentB base leftFace rightFace = false := by
    cases hadj : faceLinkAdjacentB base leftFace rightFace with
    | false => rfl
    | true =>
        have hadjActual := actualAdjacentOfFaceLinkAdjacent
          (n := base) (left := leftFace) (right := rightFace) hadj
        have hadjShifted := uniformShiftAdjacent padding hadjActual
        have hadjTarget : faceLinkAdjacentB (uniformPaddedBase padding base)
            leftTarget rightTarget = true :=
          faceLinkAdjacentB_true_of_actualAdjacent
            (mem_of_mem_sublists (physicalFaceEdges (uniformPaddedBase padding base))
              (uniformShiftCanonicalRoot padding base left)
              (canonicalSurfacePolymer_mem_faceSupports
                (uniformShiftCanonicalRoot_canonical hleftParts.1))
              leftTarget hleftTargetMem)
            (mem_of_mem_sublists (physicalFaceEdges (uniformPaddedBase padding base))
              (uniformShiftCanonicalRoot padding base right)
              (canonicalSurfacePolymer_mem_faceSupports
                (uniformShiftCanonicalRoot_canonical hrightParts.1))
              rightTarget hrightTargetMem)
            (by simpa only [hleftEq, hrightEq] using hadjShifted)
        have hfalse := hseparated leftTarget hleftTargetMem
          rightTarget hrightTargetMem
        rw [hfalse] at hadjTarget
        cases hadjTarget
  simp only [hfaceNe, decide_false, Bool.not_false,
    hnotAdjacent, Bool.true_and]

theorem embeddedUniformShiftFamily_uniformUnshift_eq
    {padding base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (hallInside : ∀ target, target ∈ targetFamily →
      TargetRootInsideUniformShift padding base target) :
    embeddedUniformShiftFamily padding base
        (uniformUnshiftFamily padding base targetFamily) = targetFamily := by
  apply sublists_eq_of_mem_iff (canonicalSurfacePolymers (uniformPaddedBase padding base))
    _ _ (canonicalSurfacePolymers_nodup (uniformPaddedBase padding base))
    (compatibleAmbientFamily_sublist
      (embeddedUniformShiftFamily_mem_compatible
        (uniformUnshiftFamily_mem_compatible htarget)))
    (compatibleAmbientFamily_sublist htarget)
  intro target
  rw [mem_embeddedUniformShiftFamily_iff
    (uniformUnshiftFamily_mem_compatible htarget)]
  constructor
  · rintro ⟨source, hsource, rfl⟩
    exact (mem_uniformUnshiftFamily_iff
      padding base targetFamily source).1 hsource |>.2
  · intro htargetMem
    have htargetCanonical :=
      compatibleAmbientFamily_member_ambient htarget htargetMem
    let source := uniformUnshiftCanonicalRoot padding base target
    have hsourceCanonical : source ∈ canonicalSurfacePolymers base :=
      uniformUnshiftCanonicalRoot_canonical htargetCanonical
        (hallInside target htargetMem)
    have hround : uniformShiftCanonicalRoot padding base source = target :=
      uniformUnshiftCanonicalRoot_roundtrip htargetCanonical
        (hallInside target htargetMem)
    exact ⟨source,
      (mem_uniformUnshiftFamily_iff padding base targetFamily source).2
        ⟨hsourceCanonical, by simpa only [hround] using htargetMem⟩,
      hround.symm⟩

theorem mem_uniformShiftEmbeddedCompatibleFamilies_iff_all_inside
    {padding base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base)) :
    targetFamily ∈ uniformShiftEmbeddedCompatibleFamilies padding base ↔
      ∀ target, target ∈ targetFamily →
        TargetRootInsideUniformShift padding base target := by
  constructor
  · intro himage target htargetMem
    obtain ⟨sourceFamily, hsourceFamily, heq⟩ :=
      List.mem_map.mp himage
    rw [← heq] at htargetMem
    obtain ⟨source, hsource, htargetEq⟩ :=
      (mem_embeddedUniformShiftFamily_iff hsourceFamily target).1
        htargetMem
    rw [htargetEq]
    exact targetRootInside_uniformShiftCanonicalRoot
      (compatibleAmbientFamily_member_ambient hsourceFamily hsource)
  · intro hallInside
    apply List.mem_map.mpr
    exact ⟨uniformUnshiftFamily padding base targetFamily,
      uniformUnshiftFamily_mem_compatible htarget,
      embeddedUniformShiftFamily_uniformUnshift_eq htarget hallInside⟩

theorem mem_uniformShiftEmbeddedTargetFamilies_iff
    {padding base : Nat} {targetFamily : List (List Nat)} :
    targetFamily ∈ uniformShiftEmbeddedTargetFamilies padding base ↔
      targetFamily ∈
          canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) ∧
        targetFamily.all
          (targetRootInsideUniformShiftB padding base) = true := by
  unfold uniformShiftEmbeddedTargetFamilies
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · intro hparts
    refine ⟨hparts.1, ?_⟩
    rw [List.all_eq_true]
    intro target htarget
    apply (targetRootInsideUniformShiftB_true_iff padding base target).2
    exact (mem_uniformShiftEmbeddedCompatibleFamilies_iff_all_inside
      hparts.1).1 hparts.2 target htarget
  · intro hparts
    refine ⟨hparts.1, ?_⟩
    apply (mem_uniformShiftEmbeddedCompatibleFamilies_iff_all_inside
      hparts.1).2
    intro target htarget
    exact (targetRootInsideUniformShiftB_true_iff padding base target).1
      (List.all_eq_true.mp hparts.2 target htarget)

#print axioms uniformUnshiftAdjacentOfShifted
#print axioms uniformUnshiftConnectedOnShifted
#print axioms uniformUnshiftCanonicalRoot_canonical
#print axioms uniformUnshiftCanonicalRoot_roundtrip
#print axioms mem_uniformShiftCanonicalRoots_iff
#print axioms uniformUnshiftFamily_mem_compatible
#print axioms embeddedUniformShiftFamily_uniformUnshift_eq
#print axioms mem_uniformShiftEmbeddedCompatibleFamilies_iff_all_inside
#print axioms mem_uniformShiftEmbeddedTargetFamilies_iff

end YMGap.Continuum.Z4UniformShiftEmbeddedRegion
