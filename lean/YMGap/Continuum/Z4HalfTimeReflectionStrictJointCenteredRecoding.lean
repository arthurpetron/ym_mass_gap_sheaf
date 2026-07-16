/-
# Fixed centered recoding of the strict reflected joint chart

At stage zero the strict upper and reflected lower roots lie strictly inside
the adjacent odd centered box.  Re-encoding them there produces one fixed
canonical source chart.  Subsequent centered stages are uniform translations
of this fixed chart because translation by `stage` commutes with reflection
when the reflection extent grows by `2 * stage`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
import YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
open YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Shrinking the strict stage-zero roots into the odd source box -/

def strictJointCenteredSourceBase (base : Nat) : Nat :=
  centeredBoxBase (strictQueryBase base)

/-- Re-encode an even stage-zero root in the adjacent odd centered box. -/
def strictJointCenteredReencodeRoot
    (base : Nat) (root : List Nat) : List Nat :=
  geometricSupportIds (strictJointCenteredSourceBase base)
    (geometricPolymer (centralAmbient (strictQueryBase base)) root)

theorem centralStrictUpper_stageZero_geometric_mem_sourceBox
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈
      geometricPolymer (centralAmbient (strictQueryBase base))
        (centralStrictUpperCanonicalRoot
          (strictQueryBase base) base root)) :
    plaquette ∈ boxPlaquettes (strictJointCenteredSourceBase base) := by
  have hshifted :=
    (centralFaceQueryCanonicalRoot_sameSupport
      (Nat.le_refl (strictQueryBase base))
      (strictQuerySourceRoot_canonical hroot)).1 _ hplaquette
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hshifted
  rw [← hsourceEq]
  exact uniformShiftPlaquette_mem_centeredBase_of_le
    (Nat.le_refl (strictQueryBase base))
    (geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports
        (strictQuerySourceRoot_canonical hroot)) source hsource)

private theorem reflected_strictUpper_mem_centeredBox
    {radius : Nat} {plaquette : Z4Plaq}
    (hbox : plaquette ∈ boxPlaquettes (centeredBoxBase radius))
    (htime : radius + 3 ≤ plaquette.1.2.2.2)
    (hadmissible : plaquetteTimeAdmissible
      (centralExtent radius) plaquette) :
    timeReflectPlaquette (centralExtent radius) plaquette ∈
      boxPlaquettes (centeredBoxBase radius) := by
  have hcoordinates := (mem_boxPlaquettes plaquette
    (centeredBoxBase radius)).1 hbox
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  change a < centeredBoxBase radius ∧
    b < centeredBoxBase radius ∧
    c < centeredBoxBase radius ∧
    d < centeredBoxBase radius at hcoordinates
  change radius + 3 ≤ d at htime
  have hbasePos : 0 < centeredBoxBase radius := by
    unfold centeredBoxBase
    omega
  have hdPos : 0 < d := by omega
  have hspatial :
      centralExtent radius - d < centeredBoxBase radius := by
    change centeredBoxBase radius - d < centeredBoxBase radius
    exact Nat.sub_lt hbasePos hdPos
  have htemporal :
      centralExtent radius - (d + 1) < centeredBoxBase radius := by
    change centeredBoxBase radius - (d + 1) < centeredBoxBase radius
    exact Nat.sub_lt hbasePos (Nat.zero_lt_succ d)
  apply (mem_boxPlaquettes _ _).2
  cases plane <;>
    simp only [timeReflectPlaquette]
  all_goals
    first
    | exact ⟨hcoordinates.1, hcoordinates.2.1,
        hcoordinates.2.2.1, hspatial⟩
    | exact ⟨hcoordinates.1, hcoordinates.2.1,
        hcoordinates.2.2.1, htemporal⟩

/-- If the reflection extent grows by two lattice units per centered stage,
uniform translation by one unit per stage commutes with reflection.  The
admissibility hypothesis is exactly what turns the truncated natural
subtractions into the intended affine identities. -/
theorem uniformShift_timeReflectPlaquette_centralExtent
    {radius stage : Nat} {plaquette : Z4Plaq}
    (hadmissible : plaquetteTimeAdmissible
      (centralExtent radius) plaquette) :
    uniformShiftPlaquette stage
        (timeReflectPlaquette (centralExtent radius) plaquette) =
      timeReflectPlaquette (centralExtent (radius + stage))
        (uniformShiftPlaquette stage plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;>
    simp [plaquetteTimeAdmissible, centralExtent,
      timeReflectPlaquette, uniformShiftPlaquette,
      uniformShiftVertex] at hadmissible ⊢ <;>
    omega

private theorem sameSupport_map
    {left right : List Z4Plaq} (reindex : Z4Plaq → Z4Plaq)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map reindex) (right.map reindex) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.2 source hsource, rfl⟩

private theorem sameSupport_map_uniformShift
    {left right : List Z4Plaq} (stage : Nat)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map (uniformShiftPlaquette stage))
      (right.map (uniformShiftPlaquette stage)) :=
  sameSupport_map (uniformShiftPlaquette stage) hsupport

private theorem sameSupport_right_eq
    {left right target : List Z4Plaq}
    (hsupport : sameSupport (L := z4Chain.toLattice) left right)
    (heq : right = target) :
    sameSupport (L := z4Chain.toLattice) left target := by
  cases heq
  exact hsupport

theorem strictJointCenteredReencodeRoot_sameSupport
    {base : Nat} {root : List Nat}
    (hbox : ∀ plaquette, plaquette ∈
      geometricPolymer (centralAmbient (strictQueryBase base)) root →
        plaquette ∈ boxPlaquettes (strictJointCenteredSourceBase base)) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (strictJointCenteredSourceBase base)
        (strictJointCenteredReencodeRoot base root))
      (geometricPolymer (centralAmbient (strictQueryBase base)) root) := by
  unfold strictJointCenteredReencodeRoot
  exact geometricSupportIds_sameSupport hbox

theorem centralStrictLower_stageZero_geometric_mem_sourceBox
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈
      geometricPolymer (centralAmbient (strictQueryBase base))
        (centralStrictLowerCanonicalRoot
          (strictQueryBase base) base root)) :
    plaquette ∈ boxPlaquettes (strictJointCenteredSourceBase base) := by
  have hupperCanonical := centralStrictUpperCanonicalRoot_canonical
    (Nat.le_refl (strictQueryBase base)) hroot
  have hupperSupported := centralStrictUpperCanonicalRoot_supported
    (Nat.le_refl (strictQueryBase base)) hroot
  have hmapped :=
    (centralReflectedCanonicalRoot_sameSupport hupperSupported).1
      plaquette hplaquette
  obtain ⟨upperPlaquette, hupperPlaquette, hreflectedEq⟩ :=
    List.mem_map.mp hmapped
  obtain ⟨upperFace, hupperFace, hupperEq⟩ :=
    List.mem_map.mp hupperPlaquette
  have hupperBox := centralStrictUpper_stageZero_geometric_mem_sourceBox
    hroot hupperPlaquette
  have htime := centralStrictUpperCanonicalRoot_time_ge
    (Nat.le_refl (strictQueryBase base)) hroot hupperFace
  rw [hupperEq] at htime
  have hadmissible :=
    (mem_boundaryCompleteSlabPlaquettes _ _).1
      (canonicalPolymerSlabSupported_face
        hupperSupported hupperFace) |>.2
  rw [hupperEq] at hadmissible
  rw [← hreflectedEq]
  exact reflected_strictUpper_mem_centeredBox
    hupperBox htime hadmissible

theorem strictJointCenteredReencodeRoot_canonical
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers
      (centralAmbient (strictQueryBase base)))
    (hbox : ∀ plaquette, plaquette ∈
      geometricPolymer (centralAmbient (strictQueryBase base)) root →
        plaquette ∈ boxPlaquettes (strictJointCenteredSourceBase base)) :
    strictJointCenteredReencodeRoot base root ∈
      canonicalSurfacePolymers (strictJointCenteredSourceBase base) := by
  have hsame : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (strictJointCenteredSourceBase base)
        (strictJointCenteredReencodeRoot base root))
      (geometricPolymer (centralAmbient (strictQueryBase base)) root) := by
    exact strictJointCenteredReencodeRoot_sameSupport hbox
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · unfold strictJointCenteredReencodeRoot
    exact geometricSupportIds_mem_cutoffOneFaceSupports _ _
  · obtain ⟨sourceFace, hsourceFace⟩ :=
      canonicalSurfacePolymers_allNonempty
        (centralAmbient (strictQueryBase base)) root hroot
    have hsourceGeom :
        boxPlaquetteAt (centralAmbient (strictQueryBase base)) sourceFace ∈
          geometricPolymer (centralAmbient (strictQueryBase base)) root :=
      List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
    have hencodedGeom := hsame.2 _ hsourceGeom
    obtain ⟨targetFace, htargetFace, _⟩ :=
      decodeMapMember (boxPlaquetteAt (strictJointCenteredSourceBase base))
        (strictJointCenteredReencodeRoot base root) _ hencodedGeom
    exact ⟨targetFace, htargetFace⟩
  · unfold strictJointCenteredReencodeRoot
    apply geometricSupportIds_connected hbox
    exact numericalConnectedToGeometric
      ((canonicalSurfacePolymers_allConnected
        (centralAmbient (strictQueryBase base))) root hroot)

def centralStrictLowerCenteredSourceRoot
    (base : Nat) (root : List Nat) : List Nat :=
  strictJointCenteredReencodeRoot base
    (centralStrictLowerCanonicalRoot (strictQueryBase base) base root)

def centralStrictUpperCenteredSourceRoot
    (base : Nat) (root : List Nat) : List Nat :=
  strictJointCenteredReencodeRoot base
    (centralStrictUpperCanonicalRoot (strictQueryBase base) base root)

theorem centralStrictLowerCenteredSourceRoot_canonical
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCenteredSourceRoot base root ∈
      canonicalSurfacePolymers (strictJointCenteredSourceBase base) := by
  exact strictJointCenteredReencodeRoot_canonical
    (centralStrictLowerCanonicalRoot_canonical
      (Nat.le_refl (strictQueryBase base)) hroot)
    (fun plaquette hplaquette =>
      centralStrictLower_stageZero_geometric_mem_sourceBox
        (plaquette := plaquette) hroot hplaquette)

theorem centralStrictUpperCenteredSourceRoot_canonical
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictUpperCenteredSourceRoot base root ∈
      canonicalSurfacePolymers (strictJointCenteredSourceBase base) := by
  exact strictJointCenteredReencodeRoot_canonical
    (centralStrictUpperCanonicalRoot_canonical
      (Nat.le_refl (strictQueryBase base)) hroot)
    (fun plaquette hplaquette =>
      centralStrictUpper_stageZero_geometric_mem_sourceBox
        (plaquette := plaquette) hroot hplaquette)

def centralStrictJointCenteredSourceRoots
    (base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  roots.map (centralStrictLowerCenteredSourceRoot base) ++
    roots.map (centralStrictUpperCenteredSourceRoot base)

@[simp] theorem centralStrictJointCenteredSourceRoots_length
    (base : Nat) (roots : List (List Nat)) :
    (centralStrictJointCenteredSourceRoots base roots).length =
      roots.length + roots.length := by
  simp [centralStrictJointCenteredSourceRoots]

theorem centralStrictJointCenteredSourceRoots_canonical
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centralStrictJointCenteredSourceRoots base roots →
      target ∈ canonicalSurfacePolymers
        (strictJointCenteredSourceBase base) := by
  intro target htarget
  have hparts := List.mem_append.mp htarget
  cases hparts with
  | inl hlower =>
      obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp hlower
      rw [← htargetEq]
      exact centralStrictLowerCenteredSourceRoot_canonical
        (hroots source hsource)
  | inr hupper =>
      obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp hupper
      rw [← htargetEq]
      exact centralStrictUpperCenteredSourceRoot_canonical
        (hroots source hsource)

/-! ## 2. Uniformly translated centered stages -/

theorem strictJointCenteredStageBase_eq
    (base stage : Nat) :
    uniformPaddedBase stage (strictJointCenteredSourceBase base) =
      centeredBoxBase (strictQueryBase base + stage) := by
  unfold strictJointCenteredSourceBase uniformPaddedBase centeredBoxBase
  omega

def centralStrictLowerCenteredStageRoot
    (base stage : Nat) (root : List Nat) : List Nat :=
  uniformShiftCanonicalRoot stage (strictJointCenteredSourceBase base)
    (centralStrictLowerCenteredSourceRoot base root)

def centralStrictUpperCenteredStageRoot
    (base stage : Nat) (root : List Nat) : List Nat :=
  uniformShiftCanonicalRoot stage (strictJointCenteredSourceBase base)
    (centralStrictUpperCenteredSourceRoot base root)

def centralStrictJointCenteredStageRoots
    (base stage : Nat) (roots : List (List Nat)) : List (List Nat) :=
  (centralStrictJointCenteredSourceRoots base roots).map
    (uniformShiftCanonicalRoot stage
      (strictJointCenteredSourceBase base))

@[simp] theorem centralStrictJointCenteredStageRoots_length
    (base stage : Nat) (roots : List (List Nat)) :
    (centralStrictJointCenteredStageRoots base stage roots).length =
      roots.length + roots.length := by
  simp [centralStrictJointCenteredStageRoots]

theorem centralStrictJointCenteredStageRoots_canonical
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈
        centralStrictJointCenteredStageRoots base stage roots →
      target ∈ canonicalSurfacePolymers
        (centeredBoxBase (strictQueryBase base + stage)) := by
  intro target htarget
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq]
  have hcanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage)
    (centralStrictJointCenteredSourceRoots_canonical hroots source hsource)
  rw [strictJointCenteredStageBase_eq] at hcanonical
  exact hcanonical

theorem centralStrictJointCenteredStageRoots_split
    (base stage : Nat) (roots : List (List Nat)) :
    centralStrictJointCenteredStageRoots base stage roots =
      roots.map (centralStrictLowerCenteredStageRoot base stage) ++
        roots.map (centralStrictUpperCenteredStageRoot base stage) := by
  unfold centralStrictJointCenteredStageRoots
    centralStrictJointCenteredSourceRoots
    centralStrictLowerCenteredStageRoot
    centralStrictUpperCenteredStageRoot
  rw [List.map_append, List.map_map, List.map_map]
  rfl

/-! ## 3. Exact transport of the upper centered stage -/

theorem centralStrictUpperCenteredSourceRoot_sameSupport
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (strictJointCenteredSourceBase base)
        (centralStrictUpperCenteredSourceRoot base root))
      (geometricPolymer (centralAmbient (strictQueryBase base))
        (centralStrictUpperCanonicalRoot
          (strictQueryBase base) base root)) := by
  unfold centralStrictUpperCenteredSourceRoot
  exact strictJointCenteredReencodeRoot_sameSupport
    (fun plaquette hplaquette =>
      centralStrictUpper_stageZero_geometric_mem_sourceBox
        (plaquette := plaquette) hroot hplaquette)

theorem centralStrictLowerCenteredSourceRoot_sameSupport
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (strictJointCenteredSourceBase base)
        (centralStrictLowerCenteredSourceRoot base root))
      (geometricPolymer (centralAmbient (strictQueryBase base))
        (centralStrictLowerCanonicalRoot
          (strictQueryBase base) base root)) := by
  unfold centralStrictLowerCenteredSourceRoot
  exact strictJointCenteredReencodeRoot_sameSupport
    (fun plaquette hplaquette =>
      centralStrictLower_stageZero_geometric_mem_sourceBox
        (plaquette := plaquette) hroot hplaquette)

theorem centralStrictUpperCanonicalRoot_eq_transport_centeredStage
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictUpperCanonicalRoot
        (strictQueryBase base + stage) base root =
      transportPolymer
        (centeredBoxBase (strictQueryBase base + stage))
        (centralAmbient (strictQueryBase base + stage))
        (centralStrictUpperCenteredStageRoot base stage root) := by
  have hsourceCanonical :=
    centralStrictUpperCenteredSourceRoot_canonical hroot
  have hstageCanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage) hsourceCanonical
  rw [strictJointCenteredStageBase_eq] at hstageCanonical
  have hdirectCanonical := centralStrictUpperCanonicalRoot_canonical
    (Nat.le_add_right (strictQueryBase base) stage) hroot
  have hle : centeredBoxBase (strictQueryBase base + stage) ≤
      centralAmbient (strictQueryBase base + stage) := by
    rw [centralAmbient_eq_centeredBoxBase_add_one]
    omega
  have htransportCanonical :=
    transportPolymer_mem_canonicalSurfacePolymers hle hstageCanonical
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    hdirectCanonical htransportCanonical
  have hdirectSupport := centralFaceQueryCanonicalRoot_sameSupport
    (Nat.le_add_right (strictQueryBase base) stage)
    (strictQuerySourceRoot_canonical hroot)
  have hsourceSupport :=
    centralStrictUpperCenteredSourceRoot_sameSupport hroot
  have hzeroSupport := centralFaceQueryCanonicalRoot_sameSupport
    (Nat.le_refl (strictQueryBase base))
    (strictQuerySourceRoot_canonical hroot)
  have hsourceToZeroCommon :=
    sameSupport_trans hsourceSupport hzeroSupport
  have hmapped := sameSupport_map_uniformShift stage hsourceToZeroCommon
  have hmapEq :
      ((geometricPolymer (strictQueryBase base)
          (strictQuerySourceRoot base root)).map
          (uniformShiftPlaquette (strictQueryBase base))).map
          (uniformShiftPlaquette stage) =
        (geometricPolymer (strictQueryBase base)
          (strictQuerySourceRoot base root)).map
          (uniformShiftPlaquette (strictQueryBase base + stage)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro plaquette _
    simp only [Function.comp_apply]
    exact uniformShiftPlaquette_comp
      (strictQueryBase base) stage plaquette
  have hmappedCommon := sameSupport_right_eq hmapped hmapEq
  have hstageSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := stage) hsourceCanonical
  rw [strictJointCenteredStageBase_eq] at hstageSupport
  have hstageToCommon := sameSupport_trans hstageSupport hmappedCommon
  have hdirectToStage := sameSupport_trans hdirectSupport
    (sameSupport_symm hstageToCommon)
  exact sameSupport_trans hdirectToStage
    (transportPolymer_sameSupport hle
      (canonicalSurfacePolymer_mem_faceSupports hstageCanonical))

/-! ## 4. Reflection covariance and transport of the lower stage -/

theorem centralStrictLowerCanonicalRoot_eq_transport_centeredStage
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCanonicalRoot
        (strictQueryBase base + stage) base root =
      transportPolymer
        (centeredBoxBase (strictQueryBase base + stage))
        (centralAmbient (strictQueryBase base + stage))
        (centralStrictLowerCenteredStageRoot base stage root) := by
  have hsourceCanonical :=
    centralStrictLowerCenteredSourceRoot_canonical hroot
  have hstageCanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage) hsourceCanonical
  rw [strictJointCenteredStageBase_eq] at hstageCanonical
  have hbaseStage : strictQueryBase base ≤
      strictQueryBase base + stage :=
    Nat.le_add_right (strictQueryBase base) stage
  have hdirectCanonical := centralStrictLowerCanonicalRoot_canonical
    hbaseStage hroot
  have hle : centeredBoxBase (strictQueryBase base + stage) ≤
      centralAmbient (strictQueryBase base + stage) := by
    rw [centralAmbient_eq_centeredBoxBase_add_one]
    omega
  have htransportCanonical :=
    transportPolymer_mem_canonicalSurfacePolymers hle hstageCanonical
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    hdirectCanonical htransportCanonical

  have hzeroUpperSupported := centralStrictUpperCanonicalRoot_supported
    (Nat.le_refl (strictQueryBase base)) hroot
  have hstageUpperSupported := centralStrictUpperCanonicalRoot_supported
    hbaseStage hroot
  have hzeroLowerReflected :=
    centralReflectedCanonicalRoot_sameSupport hzeroUpperSupported
  have hstageLowerReflected :=
    centralReflectedCanonicalRoot_sameSupport hstageUpperSupported
  have hsourceLower :=
    centralStrictLowerCenteredSourceRoot_sameSupport hroot
  have hsourceToZeroReflected :=
    sameSupport_trans hsourceLower hzeroLowerReflected
  have hsourceMapped := sameSupport_map_uniformShift stage
    hsourceToZeroReflected

  have hzeroAdmissible : ∀ plaquette,
      plaquette ∈ geometricPolymer
          (centralAmbient (strictQueryBase base))
          (centralStrictUpperCanonicalRoot
            (strictQueryBase base) base root) →
        plaquetteTimeAdmissible
          (centralExtent (strictQueryBase base)) plaquette := by
    intro plaquette hplaquette
    obtain ⟨face, hface, hplaquetteEq⟩ := List.mem_map.mp hplaquette
    rw [← hplaquetteEq]
    exact (mem_boundaryCompleteSlabPlaquettes _ _).1
      (canonicalPolymerSlabSupported_face
        hzeroUpperSupported hface) |>.2
  have hreflectShiftEq :
      ((geometricPolymer (centralAmbient (strictQueryBase base))
          (centralStrictUpperCanonicalRoot
            (strictQueryBase base) base root)).map
          (timeReflectPlaquette
            (centralExtent (strictQueryBase base)))).map
          (uniformShiftPlaquette stage) =
        ((geometricPolymer (centralAmbient (strictQueryBase base))
          (centralStrictUpperCanonicalRoot
            (strictQueryBase base) base root)).map
          (uniformShiftPlaquette stage)).map
          (timeReflectPlaquette
            (centralExtent (strictQueryBase base + stage))) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro plaquette hplaquette
    simp only [Function.comp_apply]
    exact uniformShift_timeReflectPlaquette_centralExtent
      (hzeroAdmissible plaquette hplaquette)
  have hsourceToReflectedCommon :=
    sameSupport_right_eq hsourceMapped hreflectShiftEq

  have hzeroUpperSupport := centralFaceQueryCanonicalRoot_sameSupport
    (Nat.le_refl (strictQueryBase base))
    (strictQuerySourceRoot_canonical hroot)
  have hstageUpperSupport := centralFaceQueryCanonicalRoot_sameSupport
    hbaseStage (strictQuerySourceRoot_canonical hroot)
  have hzeroUpperMapped := sameSupport_map_uniformShift stage
    hzeroUpperSupport
  have hupperMapEq :
      ((geometricPolymer (strictQueryBase base)
          (strictQuerySourceRoot base root)).map
          (uniformShiftPlaquette (strictQueryBase base))).map
          (uniformShiftPlaquette stage) =
        (geometricPolymer (strictQueryBase base)
          (strictQuerySourceRoot base root)).map
          (uniformShiftPlaquette (strictQueryBase base + stage)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro plaquette _
    simp only [Function.comp_apply]
    exact uniformShiftPlaquette_comp
      (strictQueryBase base) stage plaquette
  have hzeroUpperToCommon := sameSupport_right_eq
    hzeroUpperMapped hupperMapEq
  have hstageUpperToZeroShift := sameSupport_trans hstageUpperSupport
    (sameSupport_symm hzeroUpperToCommon)
  have hreflectedStageUpperToCommon := sameSupport_map
    (timeReflectPlaquette
      (centralExtent (strictQueryBase base + stage)))
    hstageUpperToZeroShift
  have hdirectLowerToCommon := sameSupport_trans hstageLowerReflected
    hreflectedStageUpperToCommon

  have hstageRootSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := stage) hsourceCanonical
  rw [strictJointCenteredStageBase_eq] at hstageRootSupport
  have hstageRootToCommon := sameSupport_trans hstageRootSupport
    hsourceToReflectedCommon
  have hdirectToStage := sameSupport_trans hdirectLowerToCommon
    (sameSupport_symm hstageRootToCommon)
  exact sameSupport_trans hdirectToStage
    (transportPolymer_sameSupport hle
      (canonicalSurfacePolymer_mem_faceSupports hstageCanonical))

/-! ## 5. The complete joint root list is one transported odd-box chart -/

theorem centralStrictJointCylinderRoots_eq_transported_centeredStage
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centralStrictJointCylinderRoots
        (strictQueryBase base + stage) base roots =
      transportedCylinderRoots
        (centeredBoxBase (strictQueryBase base + stage))
        (centralAmbient (strictQueryBase base + stage))
        (centralStrictJointCenteredStageRoots base stage roots) := by
  rw [centralStrictJointCenteredStageRoots_split]
  unfold centralStrictJointCylinderRoots
    centralStrictLowerCylinderRoots
    centralStrictUpperCylinderRoots
    centralStrictLowerCenteredStageRoot
    centralStrictUpperCenteredStageRoot
    transportedCylinderRoots
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact centralStrictLowerCanonicalRoot_eq_transport_centeredStage
      (hroots root hroot)
  · apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact centralStrictUpperCanonicalRoot_eq_transport_centeredStage
      (hroots root hroot)

/-! ## 6. A stage-growing protected core in the odd box -/

def strictJointCenteredInner (base stage : Nat) : Nat :=
  strictJointCenteredSourceBase base + stage

theorem strictJointCenteredInner_add_distance
    (base stage : Nat) :
    strictJointCenteredInner base stage + stage =
      centeredBoxBase (strictQueryBase base + stage) := by
  unfold strictJointCenteredInner strictJointCenteredSourceBase
    centeredBoxBase
  omega

theorem uniformShiftPlaquette_mem_oneSidedPaddedBox
    {base stage : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    uniformShiftPlaquette stage plaquette ∈
      boxPlaquettes (base + stage) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rw [mem_boxPlaquettes] at hplaquette ⊢
  change a < base ∧ b < base ∧ c < base ∧ d < base
    at hplaquette
  simp only [uniformShiftPlaquette, uniformShiftVertex]
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem centralStrictJointCenteredStageRoots_inside_originBox
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈
        centralStrictJointCenteredStageRoots base stage roots →
      PolymerInsideBox (strictJointCenteredInner base stage)
        (centeredBoxBase (strictQueryBase base + stage)) target := by
  intro target htarget plaquette hplaquette
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq] at hplaquette
  have hsourceCanonical :=
    centralStrictJointCenteredSourceRoots_canonical hroots source hsource
  have hsupport := uniformShiftCanonicalRoot_sameSupport
    (padding := stage) hsourceCanonical
  rw [strictJointCenteredStageBase_eq] at hsupport
  have hmapped := hsupport.1 plaquette hplaquette
  obtain ⟨sourcePlaquette, hsourcePlaquette, hplaquetteEq⟩ :=
    List.mem_map.mp hmapped
  rw [← hplaquetteEq]
  unfold strictJointCenteredInner
  exact uniformShiftPlaquette_mem_oneSidedPaddedBox
    (geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
      sourcePlaquette hsourcePlaquette)

/-! ## 7. Adjacent odd/even comparison for the complete joint event -/

theorem strictJointCenteredStageBase_le_centralAmbient
    (base stage : Nat) :
    centeredBoxBase (strictQueryBase base + stage) ≤
      centralAmbient (strictQueryBase base + stage) := by
  rw [centralAmbient_eq_centeredBoxBase_add_one]
  omega

theorem centralStrictJointSlabEvent_eq_transportedCenteredStage
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let hsmall := strictJointCenteredStageBase_le_centralAmbient
      base stage
    let hstageRoots :=
      centralStrictJointCenteredStageRoots_canonical
        (stage := stage) hroots
    slabMarkedCylinderEvent
        (centralStrictJointCanonicalAtoms
          (strictQueryBase base + stage) base roots
          (Nat.le_add_right (strictQueryBase base) stage) hroots)
        predicate =
      markedCylinderEvent
        (transportedCanonicalCylinderAtoms hsmall
          (centralStrictJointCenteredStageRoots base stage roots)
          hstageRoots)
        predicate := by
  dsimp only
  unfold slabMarkedCylinderEvent markedCylinderEvent
  apply congrArg (fun rawRoots => cylinderEvent rawRoots predicate)
  calc
    (centralStrictJointCanonicalAtoms
        (strictQueryBase base + stage) base roots
        (Nat.le_add_right (strictQueryBase base) stage) hroots).map
          Subtype.val =
        centralStrictJointCylinderRoots
          (strictQueryBase base + stage) base roots :=
      centralStrictJointCanonicalAtoms_values
        (strictQueryBase base + stage) base roots
        (Nat.le_add_right (strictQueryBase base) stage) hroots
    _ = transportedCylinderRoots
          (centeredBoxBase (strictQueryBase base + stage))
          (centralAmbient (strictQueryBase base + stage))
          (centralStrictJointCenteredStageRoots base stage roots) :=
      centralStrictJointCylinderRoots_eq_transported_centeredStage hroots
    _ = (transportedCanonicalCylinderAtoms
          (strictJointCenteredStageBase_le_centralAmbient base stage)
          (centralStrictJointCenteredStageRoots base stage roots)
          (centralStrictJointCenteredStageRoots_canonical
            (stage := stage) hroots)).map Subtype.val :=
      (transportedCanonicalCylinderAtoms_values
        (strictJointCenteredStageBase_le_centralAmbient base stage)
        (centralStrictJointCenteredStageRoots base stage roots)
        (centralStrictJointCenteredStageRoots_canonical
          (stage := stage) hroots)).symm

theorem couplingParametricKCompatibleStrictJoint_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centralAmbient (strictQueryBase base + stage))
            (slabMarkedCylinderEvent
              (centralStrictJointCanonicalAtoms
                (strictQueryBase base + stage) base roots
                (Nat.le_add_right (strictQueryBase base) stage) hroots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase base + stage))
            (sourceCylinderEvent
              (centralStrictJointCenteredStageRoots base stage roots)
              predicate)) ≤
      spinSummedCylinderBoundaryEpsilon
        (roots.length + roots.length) stage := by
  let hsmall := strictJointCenteredStageBase_le_centralAmbient
    base stage
  let stageRoots := centralStrictJointCenteredStageRoots
    base stage roots
  let hstageRoots : ∀ root, root ∈ stageRoots →
      root ∈ canonicalSurfacePolymers
        (centeredBoxBase (strictQueryBase base + stage)) :=
    centralStrictJointCenteredStageRoots_canonical hroots
  have hbound :=
    couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
      hcoupling hle cutoff hsmall stageRoots hstageRoots predicate
      (centralStrictJointCenteredStageRoots_inside_originBox hroots)
      (strictJointCenteredInner_add_distance base stage)
  have hevent := centralStrictJointSlabEvent_eq_transportedCenteredStage
    (stage := stage) hroots predicate
  have hlength : stageRoots.length =
      roots.length + roots.length := by
    simpa only [stageRoots] using
      (centralStrictJointCenteredStageRoots_length base stage roots)
  rw [← hevent] at hbound
  simpa only [stageRoots, hlength] using hbound

theorem couplingPhysicalStrictJoint_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (centralAmbient (strictQueryBase base + stage))
            (slabMarkedCylinderEvent
              (centralStrictJointCanonicalAtoms
                (strictQueryBase base + stage) base roots
                (Nat.le_add_right (strictQueryBase base) stage) hroots)
              predicate) -
          couplingKFamilyEventProbability coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase base + stage))
            (sourceCylinderEvent
              (centralStrictJointCenteredStageRoots base stage roots)
              predicate)) ≤
      spinSummedCylinderBoundaryEpsilon
        (roots.length + roots.length) stage := by
  let largeEvent := slabMarkedCylinderEvent
    (centralStrictJointCanonicalAtoms
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots)
    predicate
  let smallEvent := sourceCylinderEvent
    (centralStrictJointCenteredStageRoots base stage roots) predicate
  have hbridge := couplingPhysicalAdjacentDifference_eqv_compatible
    (large := centralAmbient (strictQueryBase base + stage))
    (small := centeredBoxBase (strictQueryBase base + stage))
    hcoupling cutoff largeEvent smallEvent
  have hcompatible :=
    couplingParametricKCompatibleStrictJoint_cross_centered_abs_sub_le
      (stage := stage) hcoupling hle cutoff hroots predicate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hbridge))
    (by simpa only [largeEvent, smallEvent] using hcompatible)

#print axioms centralStrictUpper_stageZero_geometric_mem_sourceBox
#print axioms centralStrictLower_stageZero_geometric_mem_sourceBox
#print axioms strictJointCenteredReencodeRoot_canonical
#print axioms centralStrictLowerCenteredSourceRoot_canonical
#print axioms centralStrictUpperCenteredSourceRoot_canonical
#print axioms centralStrictJointCenteredSourceRoots_canonical
#print axioms uniformShift_timeReflectPlaquette_centralExtent
#print axioms strictJointCenteredReencodeRoot_sameSupport
#print axioms centralStrictJointCenteredStageRoots_canonical
#print axioms centralStrictJointCenteredStageRoots_split
#print axioms centralStrictUpperCenteredSourceRoot_sameSupport
#print axioms centralStrictLowerCenteredSourceRoot_sameSupport
#print axioms centralStrictUpperCanonicalRoot_eq_transport_centeredStage
#print axioms centralStrictLowerCanonicalRoot_eq_transport_centeredStage
#print axioms centralStrictJointCylinderRoots_eq_transported_centeredStage
#print axioms centralStrictJointCenteredStageRoots_inside_originBox
#print axioms centralStrictJointSlabEvent_eq_transportedCenteredStage
#print axioms couplingParametricKCompatibleStrictJoint_cross_centered_abs_sub_le
#print axioms couplingPhysicalStrictJoint_cross_centered_abs_sub_le

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
