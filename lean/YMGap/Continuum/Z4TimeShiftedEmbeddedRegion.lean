/-
# The affine embedded cell as a literal restricted polymer gas

The exact time-shifted embedding is useful for a boundary comparison only
after its image has been characterized atom by atom.  This file supplies a
constructive inverse geometric encoding.  A target canonical root is in the
time-shift image exactly when every plaquette in its geometric support lies
in the translated source plaquette list.  Consequently a compatible target
family belongs to the embedded cell exactly when all of its roots pass this
translated-region test.

No choice is used: the inverse root is obtained by subtracting the known
nonnegative time shift and applying the canonical `geometricSupportIds`
encoder in the source box.
-/

import YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
import YMGap.Continuum.Z4ShiftedSubboxCarrierTail

namespace YMGap.Continuum.Z4TimeShiftedEmbeddedRegion

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
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport

/-! ## 1. Constructive inverse of a known nonnegative time shift -/

def timeUnshiftVertex (shift : Nat) : Z4Vertex → Z4Vertex
  | (a, b, c, d) => (a, b, c, d - shift)

def timeUnshiftPlaquette (shift : Nat) (plaquette : Z4Plaq) : Z4Plaq :=
  (timeUnshiftVertex shift plaquette.1, plaquette.2)

theorem timeUnshiftPlaquette_timeShiftPlaquette
    (shift : Nat) (plaquette : Z4Plaq) :
    timeUnshiftPlaquette shift (timeShiftPlaquette shift plaquette) =
      plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp [timeUnshiftPlaquette, timeUnshiftVertex,
    timeShiftPlaquette, timeShiftVertex]

theorem timeShiftPlaquette_timeUnshiftPlaquette_of_mem
    {shift base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ timeShiftedPlaquetteList shift base) :
    timeShiftPlaquette shift (timeUnshiftPlaquette shift plaquette) =
      plaquette := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq, timeUnshiftPlaquette_timeShiftPlaquette]

theorem timeUnshiftPlaquette_mem_box_of_shifted
    {shift base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ timeShiftedPlaquetteList shift base) :
    timeUnshiftPlaquette shift plaquette ∈ boxPlaquettes base := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq, timeUnshiftPlaquette_timeShiftPlaquette]
  exact hsource

def timeUnshiftAdjacentOfShifted
    {shift base : Nat} {left right : Z4Plaq}
    (hleft : left ∈ timeShiftedPlaquetteList shift base)
    (hright : right ∈ timeShiftedPlaquetteList shift base)
    (hadj : z4Chain.toLattice.Adjacent left right) :
    z4Chain.toLattice.Adjacent
      (timeUnshiftPlaquette shift left)
      (timeUnshiftPlaquette shift right) := by
  apply unshiftActualAdjacent shift
  rw [timeShiftPlaquette_timeUnshiftPlaquette_of_mem hleft,
    timeShiftPlaquette_timeUnshiftPlaquette_of_mem hright]
  exact hadj

def timeUnshiftChainOnShifted
    (shift base : Nat) {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ timeShiftedPlaquetteList shift base) :
    {first last : Z4Plaq} →
      (hfirst : first ∈ support) →
      ChainIn z4Chain.toLattice support first last →
      ChainIn z4Chain.toLattice
        (support.map (timeUnshiftPlaquette shift))
        (timeUnshiftPlaquette shift first)
        (timeUnshiftPlaquette shift last)
  | _, _, _, .refl plaquette => .refl _
  | _, _, hfirst, .step adjacent hnext rest =>
      .step
        (timeUnshiftAdjacentOfShifted
          (hsubset _ hfirst) (hsubset _ hnext) adjacent)
        (List.mem_map.mpr ⟨_, hnext, rfl⟩)
        (timeUnshiftChainOnShifted shift base hsubset hnext rest)

def timeUnshiftConnectedOnShifted
    (shift base : Nat) {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ timeShiftedPlaquetteList shift base)
    (hconnected : connectedIn (L := z4Chain.toLattice) support) :
    connectedIn (L := z4Chain.toLattice)
      (support.map (timeUnshiftPlaquette shift)) := by
  intro first last hfirst hlast
  obtain ⟨sourceFirst, hsourceFirst, hfirstEq⟩ :=
    decodeMapMember (timeUnshiftPlaquette shift) support first hfirst
  obtain ⟨sourceLast, hsourceLast, hlastEq⟩ :=
    decodeMapMember (timeUnshiftPlaquette shift) support last hlast
  rw [← hfirstEq, ← hlastEq]
  exact timeUnshiftChainOnShifted shift base hsubset hsourceFirst
    (hconnected sourceFirst sourceLast hsourceFirst hsourceLast)

/-! ## 2. The inverse canonical root and exact round trip -/

def timeUnshiftCanonicalRoot (shift base : Nat)
    (target : List Nat) : List Nat :=
  geometricSupportIds base
    ((geometricPolymer (base + shift) target).map
      (timeUnshiftPlaquette shift))

def TargetRootInsideTimeShift (shift base : Nat)
    (target : List Nat) : Prop :=
  ∀ plaquette, plaquette ∈ geometricPolymer (base + shift) target →
    plaquette ∈ timeShiftedPlaquetteList shift base

def targetRootInsideTimeShiftB (shift base : Nat)
    (target : List Nat) : Bool :=
  (geometricPolymer (base + shift) target).all
    (fun plaquette => decide
      (plaquette ∈ timeShiftedPlaquetteList shift base))

theorem targetRootInsideTimeShiftB_true_iff
    (shift base : Nat) (target : List Nat) :
    targetRootInsideTimeShiftB shift base target = true ↔
      TargetRootInsideTimeShift shift base target := by
  unfold targetRootInsideTimeShiftB TargetRootInsideTimeShift
  rw [List.all_eq_true]
  simp only [decide_eq_true_eq]

theorem timeUnshiftCanonicalRoot_sameSupport
    {shift base : Nat} {target : List Nat}
    (hinside : TargetRootInsideTimeShift shift base target) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer base
        (timeUnshiftCanonicalRoot shift base target))
      ((geometricPolymer (base + shift) target).map
        (timeUnshiftPlaquette shift)) := by
  unfold timeUnshiftCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨targetPlaquette, htarget, heq⟩ :=
    List.mem_map.mp hplaquette
  rw [← heq]
  exact timeUnshiftPlaquette_mem_box_of_shifted (hinside _ htarget)

def timeUnshiftCanonicalRoot_nonempty
    {shift base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (base + shift))
    (hinside : TargetRootInsideTimeShift shift base target) :
    Σ' face : Nat, face ∈ timeUnshiftCanonicalRoot shift base target := by
  obtain ⟨targetFace, htargetFace⟩ :=
    canonicalSurfacePolymers_allNonempty (base + shift) target htarget
  have htargetGeom : boxPlaquetteAt (base + shift) targetFace ∈
      geometricPolymer (base + shift) target :=
    List.mem_map.mpr ⟨targetFace, htargetFace, rfl⟩
  have hunshifted : timeUnshiftPlaquette shift
        (boxPlaquetteAt (base + shift) targetFace) ∈
      (geometricPolymer (base + shift) target).map
        (timeUnshiftPlaquette shift) :=
    List.mem_map.mpr
      ⟨boxPlaquetteAt (base + shift) targetFace, htargetGeom, rfl⟩
  have hsourceGeom :=
    (timeUnshiftCanonicalRoot_sameSupport hinside).2 _ hunshifted
  obtain ⟨sourceFace, hsourceFace, _⟩ :=
    decodeMapMember (boxPlaquetteAt base)
      (timeUnshiftCanonicalRoot shift base target)
      (timeUnshiftPlaquette shift
        (boxPlaquetteAt (base + shift) targetFace)) hsourceGeom
  exact ⟨sourceFace, hsourceFace⟩

def timeUnshiftCanonicalRoot_connected
    {shift base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (base + shift))
    (hinside : TargetRootInsideTimeShift shift base target) :
    InternallyConnected (faceLinkAdjacentB base)
      (timeUnshiftCanonicalRoot shift base target) := by
  unfold timeUnshiftCanonicalRoot
  apply geometricSupportIds_connected
  · intro plaquette hplaquette
    obtain ⟨targetPlaquette, htargetPlaquette, heq⟩ :=
      List.mem_map.mp hplaquette
    rw [← heq]
    exact timeUnshiftPlaquette_mem_box_of_shifted
      (hinside _ htargetPlaquette)
  · apply timeUnshiftConnectedOnShifted shift base hinside
    exact numericalConnectedToGeometric
      ((canonicalSurfacePolymers_allConnected (base + shift))
        target htarget)

theorem timeUnshiftCanonicalRoot_canonical
    {shift base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (base + shift))
    (hinside : TargetRootInsideTimeShift shift base target) :
    timeUnshiftCanonicalRoot shift base target ∈
      canonicalSurfacePolymers base :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports base _)
    (timeUnshiftCanonicalRoot_nonempty htarget hinside)
    (timeUnshiftCanonicalRoot_connected htarget hinside)

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

theorem timeUnshiftCanonicalRoot_roundtrip
    {shift base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (base + shift))
    (hinside : TargetRootInsideTimeShift shift base target) :
    timeShiftCanonicalRoot shift base
        (timeUnshiftCanonicalRoot shift base target) = target := by
  let source := timeUnshiftCanonicalRoot shift base target
  have hsource : source ∈ canonicalSurfacePolymers base :=
    timeUnshiftCanonicalRoot_canonical htarget hinside
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    (timeShiftCanonicalRoot_canonical hsource) htarget
  have hshift := timeShiftCanonicalRoot_sameSupport
    (shift := shift) hsource
  have hunshift := timeUnshiftCanonicalRoot_sameSupport hinside
  have hmapped := sameSupport_map_local (timeShiftPlaquette shift) hunshift
  have hround : sameSupport (L := z4Chain.toLattice)
      (((geometricPolymer (base + shift) target).map
          (timeUnshiftPlaquette shift)).map
        (timeShiftPlaquette shift))
      (geometricPolymer (base + shift) target) := by
    constructor
    · intro plaquette hplaquette
      obtain ⟨unshifted, hunshifted, heq⟩ :=
        List.mem_map.mp hplaquette
      obtain ⟨original, horiginal, hunshiftEq⟩ :=
        List.mem_map.mp hunshifted
      subst unshifted
      rw [timeShiftPlaquette_timeUnshiftPlaquette_of_mem
        (hinside _ horiginal)] at heq
      rw [← heq]
      exact horiginal
    · intro plaquette hplaquette
      apply List.mem_map.mpr
      refine ⟨timeUnshiftPlaquette shift plaquette, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨plaquette, hplaquette, rfl⟩
      · exact timeShiftPlaquette_timeUnshiftPlaquette_of_mem
          (hinside _ hplaquette)
  exact sameSupport_trans hshift
    (sameSupport_trans hmapped hround)

/-! ## 3. Atomwise image characterization -/

def timeShiftCanonicalRoots (shift base : Nat) : List (List Nat) :=
  (canonicalSurfacePolymers base).map
    (timeShiftCanonicalRoot shift base)

theorem timeShiftCanonicalRoots_nodup (shift base : Nat) :
    (timeShiftCanonicalRoots shift base).Nodup := by
  unfold timeShiftCanonicalRoots
  apply nodup_map_of_injOn (timeShiftCanonicalRoot shift base)
    (canonicalSurfacePolymers base)
    (canonicalSurfacePolymers_nodup base)
  intro left hleft right hright heq
  exact timeShiftCanonicalRoot_injective_on_canonical hleft hright heq

theorem targetRootInside_timeShiftCanonicalRoot
    {shift base : Nat} {source : List Nat}
    (hsource : source ∈ canonicalSurfacePolymers base) :
    TargetRootInsideTimeShift shift base
      (timeShiftCanonicalRoot shift base source) := by
  intro plaquette hplaquette
  have hmapped := (timeShiftCanonicalRoot_sameSupport hsource).1
    _ hplaquette
  obtain ⟨sourcePlaquette, hsourcePlaquette, heq⟩ :=
    List.mem_map.mp hmapped
  rw [← heq]
  unfold timeShiftedPlaquetteList
  apply List.mem_map.mpr
  exact ⟨sourcePlaquette,
    geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hsource)
      sourcePlaquette hsourcePlaquette, rfl⟩

theorem mem_timeShiftCanonicalRoots_iff
    {shift base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (base + shift)) :
    target ∈ timeShiftCanonicalRoots shift base ↔
      TargetRootInsideTimeShift shift base target := by
  constructor
  · intro htargetImage
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htargetImage
    rw [← heq]
    exact targetRootInside_timeShiftCanonicalRoot hsource
  · intro hinside
    apply List.mem_map.mpr
    exact ⟨timeUnshiftCanonicalRoot shift base target,
      timeUnshiftCanonicalRoot_canonical htarget hinside,
      timeUnshiftCanonicalRoot_roundtrip htarget hinside⟩

theorem targetRootInsideTimeShiftB_eq_memberB
    {shift base : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers (base + shift)) :
    targetRootInsideTimeShiftB shift base target =
      memberB (timeShiftCanonicalRoots shift base) target := by
  apply Bool.eq_iff_iff.mpr
  rw [targetRootInsideTimeShiftB_true_iff,
    memberB_eq_true_iff, ← mem_timeShiftCanonicalRoots_iff htarget]

/-! ## 4. Compatible-family image characterization -/

def timeUnshiftFamily (shift base : Nat)
    (targetFamily : List (List Nat)) : List (List Nat) :=
  (canonicalSurfacePolymers base).filter
    (fun source => decide
      (timeShiftCanonicalRoot shift base source ∈ targetFamily))

theorem mem_timeUnshiftFamily_iff
    (shift base : Nat) (targetFamily : List (List Nat))
    (source : List Nat) :
    source ∈ timeUnshiftFamily shift base targetFamily ↔
      source ∈ canonicalSurfacePolymers base ∧
        timeShiftCanonicalRoot shift base source ∈ targetFamily := by
  unfold timeUnshiftFamily
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem timeShiftFamily_timeUnshift_mem_iff
    {shift base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      canonicalCompatibleAmbientFamilies (base + shift))
    (hallInside : ∀ target, target ∈ targetFamily →
      TargetRootInsideTimeShift shift base target)
    (target : List Nat) :
    target ∈ timeShiftFamily shift base
        (timeUnshiftFamily shift base targetFamily) ↔
      target ∈ targetFamily := by
  constructor
  · intro htargetShift
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htargetShift
    exact heq ▸ (mem_timeUnshiftFamily_iff
      shift base targetFamily source).1 hsource |>.2
  · intro htargetMem
    have htargetCanonical :=
      compatibleAmbientFamily_member_ambient htarget htargetMem
    have hinside := hallInside target htargetMem
    let source := timeUnshiftCanonicalRoot shift base target
    have hsourceCanonical : source ∈ canonicalSurfacePolymers base :=
      timeUnshiftCanonicalRoot_canonical htargetCanonical hinside
    have hround : timeShiftCanonicalRoot shift base source = target :=
      timeUnshiftCanonicalRoot_roundtrip htargetCanonical hinside
    apply List.mem_map.mpr
    refine ⟨source, (mem_timeUnshiftFamily_iff
      shift base targetFamily source).2 ?_, hround⟩
    exact ⟨hsourceCanonical, by simpa only [hround] using htargetMem⟩

theorem timeUnshiftFamily_nodup (shift base : Nat)
    (targetFamily : List (List Nat)) :
    (timeUnshiftFamily shift base targetFamily).Nodup := by
  unfold timeUnshiftFamily
  exact List.filter_sublist.nodup
    (canonicalSurfacePolymers_nodup base)

theorem timeUnshiftFamily_mem_compatible
    {shift base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      canonicalCompatibleAmbientFamilies (base + shift)) :
    timeUnshiftFamily shift base targetFamily ∈
      canonicalCompatibleAmbientFamilies base := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  refine ⟨filter_mem_sublists _ _, ?_⟩
  rw [← genericFamilyCompatibleB_eq_canonical]
  apply familyCompatibleB_of_pairwise
    (canonicalPolymerCompatibleB base)
    (timeUnshiftFamily_nodup shift base targetFamily)
  intro left hleft right hright hne
  have hleftParts := (mem_timeUnshiftFamily_iff
    shift base targetFamily left).1 hleft
  have hrightParts := (mem_timeUnshiftFamily_iff
    shift base targetFamily right).1 hright
  have hshiftNe : timeShiftCanonicalRoot shift base left ≠
      timeShiftCanonicalRoot shift base right := by
    intro heq
    exact hne (timeShiftCanonicalRoot_injective_on_canonical
      hleftParts.1 hrightParts.1 heq)
  have htargetInvariants := compatibleAmbientFamily_invariants htarget
  have hdisjoint := htargetInvariants.1
      (timeShiftCanonicalRoot shift base left) hleftParts.2
      (timeShiftCanonicalRoot shift base right) hrightParts.2 hshiftNe
  have hseparated := htargetInvariants.2
      (timeShiftCanonicalRoot shift base left) hleftParts.2
      (timeShiftCanonicalRoot shift base right) hrightParts.2 hshiftNe
  unfold canonicalPolymerCompatibleB
  apply List.all_eq_true.mpr
  intro leftFace hleftFace
  apply List.all_eq_true.mpr
  intro rightFace hrightFace
  have hleftTarget := timeShiftRootMemberTarget
    (shift := shift)
    (canonicalSurfacePolymer_mem_faceSupports hleftParts.1) hleftFace
  have hrightTarget := timeShiftRootMemberTarget
    (shift := shift)
    (canonicalSurfacePolymer_mem_faceSupports hrightParts.1) hrightFace
  obtain ⟨leftTarget, hleftTargetMem, hleftEq⟩ := hleftTarget
  obtain ⟨rightTarget, hrightTargetMem, hrightEq⟩ := hrightTarget
  have hfaceNe : leftFace ≠ rightFace := by
    intro heq
    subst rightFace
    have htargetEq : leftTarget = rightTarget :=
      boxPlaquetteAt_injective_on_physical
        (mem_of_mem_sublists (physicalFaceEdges (base + shift))
          (timeShiftCanonicalRoot shift base left)
          (canonicalSurfacePolymer_mem_faceSupports
            (timeShiftCanonicalRoot_canonical hleftParts.1))
          leftTarget hleftTargetMem)
        (mem_of_mem_sublists (physicalFaceEdges (base + shift))
          (timeShiftCanonicalRoot shift base right)
          (canonicalSurfacePolymer_mem_faceSupports
            (timeShiftCanonicalRoot_canonical hrightParts.1))
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
        have hadjShifted := timeShiftAdjacent shift hadjActual
        have hadjTarget : faceLinkAdjacentB (base + shift)
            leftTarget rightTarget = true :=
          faceLinkAdjacentB_true_of_actualAdjacent
            (mem_of_mem_sublists (physicalFaceEdges (base + shift))
              (timeShiftCanonicalRoot shift base left)
              (canonicalSurfacePolymer_mem_faceSupports
                (timeShiftCanonicalRoot_canonical hleftParts.1))
              leftTarget hleftTargetMem)
            (mem_of_mem_sublists (physicalFaceEdges (base + shift))
              (timeShiftCanonicalRoot shift base right)
              (canonicalSurfacePolymer_mem_faceSupports
                (timeShiftCanonicalRoot_canonical hrightParts.1))
              rightTarget hrightTargetMem)
            (by simpa only [hleftEq, hrightEq] using hadjShifted)
        have hfalse := hseparated leftTarget hleftTargetMem
          rightTarget hrightTargetMem
        rw [hfalse] at hadjTarget
        cases hadjTarget
  simp only [hfaceNe, decide_false, Bool.not_false,
    hnotAdjacent, Bool.true_and]

theorem embeddedTimeShiftFamily_timeUnshift_eq
    {shift base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      canonicalCompatibleAmbientFamilies (base + shift))
    (hallInside : ∀ target, target ∈ targetFamily →
      TargetRootInsideTimeShift shift base target) :
    embeddedTimeShiftFamily shift base
        (timeUnshiftFamily shift base targetFamily) = targetFamily := by
  apply sublists_eq_of_mem_iff (canonicalSurfacePolymers (base + shift))
    _ _ (canonicalSurfacePolymers_nodup (base + shift))
    (compatibleAmbientFamily_sublist
      (embeddedTimeShiftFamily_mem_compatible
        (timeUnshiftFamily_mem_compatible htarget)))
    (compatibleAmbientFamily_sublist htarget)
  intro target
  rw [mem_embeddedTimeShiftFamily_iff
    (timeUnshiftFamily_mem_compatible htarget)]
  constructor
  · rintro ⟨source, hsource, rfl⟩
    exact (mem_timeUnshiftFamily_iff
      shift base targetFamily source).1 hsource |>.2
  · intro htargetMem
    have htargetCanonical :=
      compatibleAmbientFamily_member_ambient htarget htargetMem
    let source := timeUnshiftCanonicalRoot shift base target
    have hsourceCanonical : source ∈ canonicalSurfacePolymers base :=
      timeUnshiftCanonicalRoot_canonical htargetCanonical
        (hallInside target htargetMem)
    have hround : timeShiftCanonicalRoot shift base source = target :=
      timeUnshiftCanonicalRoot_roundtrip htargetCanonical
        (hallInside target htargetMem)
    exact ⟨source,
      (mem_timeUnshiftFamily_iff shift base targetFamily source).2
        ⟨hsourceCanonical, by simpa only [hround] using htargetMem⟩,
      hround.symm⟩

theorem mem_timeShiftEmbeddedCompatibleFamilies_iff_all_inside
    {shift base : Nat} {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈
      canonicalCompatibleAmbientFamilies (base + shift)) :
    targetFamily ∈ timeShiftEmbeddedCompatibleFamilies shift base ↔
      ∀ target, target ∈ targetFamily →
        TargetRootInsideTimeShift shift base target := by
  constructor
  · intro himage target htargetMem
    obtain ⟨sourceFamily, hsourceFamily, heq⟩ :=
      List.mem_map.mp himage
    rw [← heq] at htargetMem
    obtain ⟨source, hsource, htargetEq⟩ :=
      (mem_embeddedTimeShiftFamily_iff hsourceFamily target).1
        htargetMem
    rw [htargetEq]
    exact targetRootInside_timeShiftCanonicalRoot
      (compatibleAmbientFamily_member_ambient hsourceFamily hsource)
  · intro hallInside
    apply List.mem_map.mpr
    exact ⟨timeUnshiftFamily shift base targetFamily,
      timeUnshiftFamily_mem_compatible htarget,
      embeddedTimeShiftFamily_timeUnshift_eq htarget hallInside⟩

theorem mem_timeShiftEmbeddedTargetFamilies_iff
    {shift base : Nat} {targetFamily : List (List Nat)} :
    targetFamily ∈ timeShiftEmbeddedTargetFamilies shift base ↔
      targetFamily ∈
          canonicalCompatibleAmbientFamilies (base + shift) ∧
        targetFamily.all
          (targetRootInsideTimeShiftB shift base) = true := by
  unfold timeShiftEmbeddedTargetFamilies
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · intro hparts
    refine ⟨hparts.1, ?_⟩
    rw [List.all_eq_true]
    intro target htarget
    apply (targetRootInsideTimeShiftB_true_iff shift base target).2
    exact (mem_timeShiftEmbeddedCompatibleFamilies_iff_all_inside
      hparts.1).1 hparts.2 target htarget
  · intro hparts
    refine ⟨hparts.1, ?_⟩
    apply (mem_timeShiftEmbeddedCompatibleFamilies_iff_all_inside
      hparts.1).2
    intro target htarget
    exact (targetRootInsideTimeShiftB_true_iff shift base target).1
      (List.all_eq_true.mp hparts.2 target htarget)

#print axioms timeUnshiftAdjacentOfShifted
#print axioms timeUnshiftConnectedOnShifted
#print axioms timeUnshiftCanonicalRoot_canonical
#print axioms timeUnshiftCanonicalRoot_roundtrip
#print axioms mem_timeShiftCanonicalRoots_iff
#print axioms timeUnshiftFamily_mem_compatible
#print axioms embeddedTimeShiftFamily_timeUnshift_eq
#print axioms mem_timeShiftEmbeddedCompatibleFamilies_iff_all_inside
#print axioms mem_timeShiftEmbeddedTargetFamilies_iff

end YMGap.Continuum.Z4TimeShiftedEmbeddedRegion
