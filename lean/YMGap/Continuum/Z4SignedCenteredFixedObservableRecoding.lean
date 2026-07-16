/-
# Fixed signed observables in a receding centered exhaustion

A canonical root in a finite corner box determines an absolute signed local
support.  At centered radius `base + stage`, the same support is represented
by adding that radius in all four natural coordinates and canonically
re-encoding the translated plaquettes.  This file proves that the signed
support is independent of the stage and that two stages are related by one
uniform affine shift.

The geometry also supplies the protected core needed by a receding-boundary
estimate: the radius-`base + earlier` cell embeds symmetrically in the
radius-`base + later` cell, while every plaquette of the fixed root lies in a
core of side `2 * base + 1` at distance `earlier` from the embedded boundary.
No probability comparison is asserted here.
-/

import YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
import YMGap.Continuum.Z4ShiftedSubboxCarrierTail
import YMGap.Continuum.Z4UniformShiftPhysicalTransport

namespace YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

/-! ## 1. Uniform affine translation in natural coordinates -/

def uniformNatLower (offset : Nat) : Z4Vertex :=
  (offset, offset, offset, offset)

theorem uniformShiftPlaquette_eq_offsetNatPlaquette
    (offset : Nat) (plaquette : Z4Plaq) :
    uniformShiftPlaquette offset plaquette =
      offsetNatPlaquette offset plaquette := rfl

theorem uniformShiftPlaquette_comp
    (first second : Nat) (plaquette : Z4Plaq) :
    uniformShiftPlaquette second
        (uniformShiftPlaquette first plaquette) =
      uniformShiftPlaquette (first + second) plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp [uniformShiftPlaquette, uniformShiftVertex, Nat.add_assoc]

theorem uniformShiftPlaquette_mem_centeredBase_of_le
    {base radius : Nat} {plaquette : Z4Plaq}
    (hbase : base ≤ radius)
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    uniformShiftPlaquette radius plaquette ∈
      boxPlaquettes (centeredBoxBase radius) := by
  rw [uniformShiftPlaquette_eq_offsetNatPlaquette]
  exact offsetNatPlaquette_mem_centeredBase
    (boxPlaquettes_mono hbase hplaquette)

/-! ## 2. Canonical re-encoding of one fixed absolute root -/

def centeredOffsetCanonicalRoot
    (radius base : Nat) (root : List Nat) : List Nat :=
  geometricSupportIds (centeredBoxBase radius)
    ((geometricPolymer base root).map (uniformShiftPlaquette radius))

theorem centeredOffsetCanonicalRoot_sameSupport
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centeredBoxBase radius)
        (centeredOffsetCanonicalRoot radius base root))
      ((geometricPolymer base root).map
        (uniformShiftPlaquette radius)) := by
  unfold centeredOffsetCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  exact uniformShiftPlaquette_mem_centeredBase_of_le hbase
    (geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)

def centeredOffsetCanonicalRoot_nonempty
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    Σ' face : Nat,
      face ∈ centeredOffsetCanonicalRoot radius base root := by
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty base root hroot
  have hsource : boxPlaquetteAt base sourceFace ∈
      geometricPolymer base root :=
    List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
  have hoffset :
      uniformShiftPlaquette radius (boxPlaquetteAt base sourceFace) ∈
        (geometricPolymer base root).map
          (uniformShiftPlaquette radius) :=
    List.mem_map.mpr ⟨_, hsource, rfl⟩
  have hencoded :=
    (centeredOffsetCanonicalRoot_sameSupport hbase hroot).2 _ hoffset
  obtain ⟨targetFace, htargetFace, _⟩ :=
    decodeMapMember (boxPlaquetteAt (centeredBoxBase radius))
      (centeredOffsetCanonicalRoot radius base root)
      (uniformShiftPlaquette radius (boxPlaquetteAt base sourceFace))
      hencoded
  exact ⟨targetFace, htargetFace⟩

def centeredOffsetCanonicalRoot_connected
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    InternallyConnected (faceLinkAdjacentB (centeredBoxBase radius))
      (centeredOffsetCanonicalRoot radius base root) := by
  unfold centeredOffsetCanonicalRoot
  apply geometricSupportIds_connected
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact uniformShiftPlaquette_mem_centeredBase_of_le hbase
      (geometricPolymer_subset_box
        (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)
  · exact uniformShiftConnected radius
      (numericalConnectedToGeometric
        ((canonicalSurfacePolymers_allConnected base) root hroot))

theorem centeredOffsetCanonicalRoot_canonical
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centeredOffsetCanonicalRoot radius base root ∈
      canonicalSurfacePolymers (centeredBoxBase radius) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports
      (centeredBoxBase radius)
      ((geometricPolymer base root).map (uniformShiftPlaquette radius)))
    (centeredOffsetCanonicalRoot_nonempty hbase hroot)
    (centeredOffsetCanonicalRoot_connected hbase hroot)

def centeredOffsetCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) :
    List (List Nat) :=
  roots.map (centeredOffsetCanonicalRoot radius base)

theorem centeredOffsetCylinderRoots_length
    (radius base : Nat) (roots : List (List Nat)) :
    (centeredOffsetCylinderRoots radius base roots).length = roots.length := by
  simp [centeredOffsetCylinderRoots]

theorem centeredOffsetCylinderRoots_canonical
    {radius base : Nat} (hbase : base ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centeredOffsetCylinderRoots radius base roots →
      target ∈ canonicalSurfacePolymers (centeredBoxBase radius) := by
  intro target htarget
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
  exact centeredOffsetCanonicalRoot_canonical hbase
    (hroots source hsource)

/-! ## 3. Independence of the absolute signed support -/

theorem centeredOffsetCanonicalRoot_signedSupport
    {radius base : Nat} (hbase : base ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    ∀ plaquette : SignedZ4Plaq,
      plaquette ∈
          (geometricPolymer (centeredBoxBase radius)
              (centeredOffsetCanonicalRoot radius base root)).map
            (natPlaquetteToCenteredSigned radius) ↔
        plaquette ∈ signedCanonicalRootSupport base root := by
  intro plaquette
  have hsupport := centeredOffsetCanonicalRoot_sameSupport hbase hroot
  constructor
  · intro hplaquette
    obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hplaquette
    have hoffset := hsupport.1 target htarget
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hoffset
    unfold signedCanonicalRootSupport
    rw [uniformShiftPlaquette_eq_offsetNatPlaquette,
      natPlaquetteToCenteredSigned_offset]
    exact List.mem_map.mpr ⟨source, hsource, rfl⟩
  · intro hplaquette
    unfold signedCanonicalRootSupport at hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    have hoffset : uniformShiftPlaquette radius source ∈
        (geometricPolymer base root).map
          (uniformShiftPlaquette radius) :=
      List.mem_map.mpr ⟨source, hsource, rfl⟩
    have htarget := hsupport.2 _ hoffset
    obtain ⟨target, htarget, htargetEq⟩ :=
      decodeMapMember (boxPlaquetteAt (centeredBoxBase radius))
        (centeredOffsetCanonicalRoot radius base root)
        (uniformShiftPlaquette radius source) htarget
    apply List.mem_map.mpr
    refine ⟨boxPlaquetteAt (centeredBoxBase radius) target,
      List.mem_map.mpr ⟨target, htarget, rfl⟩, ?_⟩
    rw [htargetEq, uniformShiftPlaquette_eq_offsetNatPlaquette,
      natPlaquetteToCenteredSigned_offset]

/-! ## 4. Exact stage-to-stage support transport and protected core -/

private theorem sameSupport_map_uniformShift
    {left right : List Z4Plaq} (offset : Nat)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map (uniformShiftPlaquette offset))
      (right.map (uniformShiftPlaquette offset)) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr ⟨source, hsupport.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr ⟨source, hsupport.2 source hsource, rfl⟩

private theorem sameSupport_right_eq
    {left right target : List Z4Plaq}
    (hsupport : sameSupport (L := z4Chain.toLattice) left right)
    (heq : right = target) :
    sameSupport (L := z4Chain.toLattice) left target := by
  cases heq
  exact hsupport

theorem centeredOffsetCanonicalRoot_stage_transport
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centeredBoxBase (base + later))
        (centeredOffsetCanonicalRoot (base + later) base root))
      ((geometricPolymer (centeredBoxBase (base + earlier))
          (centeredOffsetCanonicalRoot (base + earlier) base root)).map
        (uniformShiftPlaquette (later - earlier))) := by
  have hbaseEarlier : base ≤ base + earlier := Nat.le_add_right _ _
  have hbaseLater : base ≤ base + later := Nat.le_add_right _ _
  have hearlier :=
    centeredOffsetCanonicalRoot_sameSupport hbaseEarlier hroot
  have hlater :=
    centeredOffsetCanonicalRoot_sameSupport hbaseLater hroot
  have hmapped := sameSupport_map_uniformShift
    (later - earlier) hearlier
  have hoffsetEq :
      ((geometricPolymer base root).map
          (uniformShiftPlaquette (base + earlier))).map
          (uniformShiftPlaquette (later - earlier)) =
        (geometricPolymer base root).map
          (uniformShiftPlaquette (base + later)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro plaquette _
    simp only [Function.comp_apply]
    rw [uniformShiftPlaquette_comp]
    apply congrArg (fun offset => uniformShiftPlaquette offset plaquette)
    omega
  exact sameSupport_trans hlater
    (sameSupport_symm (sameSupport_right_eq hmapped hoffsetEq))

theorem uniformPaddedBase_centeredBoxBase
    (base stage : Nat) :
    uniformPaddedBase stage (centeredBoxBase base) =
      centeredBoxBase (base + stage) := by
  unfold uniformPaddedBase centeredBoxBase
  omega

/-- The direct fixed-support re-encoding is exactly the canonical uniform
shift of the radius-`base` representation.  This is the stagewise identity
needed to feed the physical uniform-shift transport without changing the
observable. -/
theorem centeredOffsetCanonicalRoot_eq_uniformShift_from_centeredBase
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centeredOffsetCanonicalRoot (base + stage) base root =
      uniformShiftCanonicalRoot stage (centeredBoxBase base)
        (centeredOffsetCanonicalRoot base base root) := by
  have hbaseRoot : centeredOffsetCanonicalRoot base base root ∈
      canonicalSurfacePolymers (centeredBoxBase base) :=
    centeredOffsetCanonicalRoot_canonical (Nat.le_refl base) hroot
  have hleft : centeredOffsetCanonicalRoot (base + stage) base root ∈
      canonicalSurfacePolymers (centeredBoxBase (base + stage)) :=
    centeredOffsetCanonicalRoot_canonical
      (Nat.le_add_right base stage) hroot
  have hright := uniformShiftCanonicalRoot_canonical
    (padding := stage) hbaseRoot
  rw [uniformPaddedBase_centeredBoxBase] at hright
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have hstageSupport := centeredOffsetCanonicalRoot_stage_transport
    (base := base) (earlier := 0) (later := stage)
    (Nat.zero_le stage) hroot
  simp only [Nat.sub_zero, Nat.add_zero] at hstageSupport
  have hrightSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := stage) hbaseRoot
  rw [uniformPaddedBase_centeredBoxBase] at hrightSupport
  exact sameSupport_trans hstageSupport (sameSupport_symm hrightSupport)

theorem centeredOffsetCylinderRoots_eq_uniformShift_from_centeredBase
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centeredOffsetCylinderRoots (base + stage) base roots =
      (centeredOffsetCylinderRoots base base roots).map
        (uniformShiftCanonicalRoot stage (centeredBoxBase base)) := by
  unfold centeredOffsetCylinderRoots
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact centeredOffsetCanonicalRoot_eq_uniformShift_from_centeredBase
    (hroots root hroot)

theorem centeredOffsetPlaquette_inside_receding_core
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    insideShiftedBoxB
        (addUniform (uniformNatLower (later - earlier)) earlier)
        (centeredBoxBase base)
        (uniformShiftPlaquette (base + later) plaquette) = true := by
  apply (insideShiftedBoxB_true_iff _ _ _).2
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rw [mem_boxPlaquettes] at hplaquette
  change a < base ∧ b < base ∧ c < base ∧ d < base at hplaquette
  simp only [addUniform, uniformNatLower, uniformShiftPlaquette,
    uniformShiftVertex, cPlaq, vComp, centeredBoxBase]
  exact ⟨by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

theorem centeredOffsetCanonicalRoot_inside_receding_core
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {targetFace : Nat}
    (htargetFace : targetFace ∈
      centeredOffsetCanonicalRoot (base + later) base root) :
    insideShiftedBoxB
        (addUniform (uniformNatLower (later - earlier)) earlier)
        (centeredBoxBase base)
        (boxPlaquetteAt (centeredBoxBase (base + later)) targetFace) =
      true := by
  have htargetPlaquette :
      boxPlaquetteAt (centeredBoxBase (base + later)) targetFace ∈
        geometricPolymer (centeredBoxBase (base + later))
          (centeredOffsetCanonicalRoot (base + later) base root) :=
    List.mem_map.mpr ⟨targetFace, htargetFace, rfl⟩
  have hsupport := centeredOffsetCanonicalRoot_sameSupport
    (Nat.le_add_right base later) hroot
  have hoffset := hsupport.1 _ htargetPlaquette
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hoffset
  rw [← hsourceEq]
  exact centeredOffsetPlaquette_inside_receding_core hstage
    (geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)

theorem centeredBoxBase_stage_side
    (base stage : Nat) :
    centeredBoxBase base + stage + stage =
      centeredBoxBase (base + stage) := by
  unfold centeredBoxBase
  omega

#print axioms uniformShiftPlaquette_comp
#print axioms centeredOffsetCanonicalRoot_canonical
#print axioms centeredOffsetCylinderRoots_canonical
#print axioms centeredOffsetCanonicalRoot_signedSupport
#print axioms centeredOffsetCanonicalRoot_stage_transport
#print axioms centeredOffsetCanonicalRoot_eq_uniformShift_from_centeredBase
#print axioms centeredOffsetCylinderRoots_eq_uniformShift_from_centeredBase
#print axioms centeredOffsetPlaquette_inside_receding_core
#print axioms centeredOffsetCanonicalRoot_inside_receding_core
#print axioms centeredBoxBase_stage_side

end YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
