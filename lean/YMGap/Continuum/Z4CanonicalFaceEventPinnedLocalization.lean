/-
# Localizing the size-truncated pinned face cylinder

The pinned-size tail replaces the complete occupied-face event by polymers of
bounded size, but the resulting root list is still written in the coordinates
of each finite box.  This file supplies the geometric localization compiler:
a connected target polymer pinned in a protected core and smaller than the
core margin cannot leave the uniformly shifted source box.  The constructive
inverse of uniform translation then recovers one canonical source root whose
forward image is the target root.

The proof is the contrapositive of the existing shifted-boundary size floor.
It introduces no new counting constant.  It does not yet identify the full
truncated face predicate with one fixed coefficient function; that subsequent
step also needs a persistent, explicitly indexed central face.
-/

import YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
import YMGap.Continuum.Z4UniformShiftEmbeddedRegion

namespace YMGap.Continuum.Z4CanonicalFaceEventPinnedLocalization

set_option autoImplicit false

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4UniformShiftEmbeddedRegion
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

/-! ## 1. The translated source box as an exact shifted coordinate box -/

def uniformLower (padding : Nat) : Z4Vertex :=
  (padding, padding, padding, padding)

theorem vComp_uniformLower (padding : Nat) (direction : Dir4) :
    vComp (uniformLower padding) direction = padding := by
  cases direction <;> rfl

theorem uniformShiftPlaquette_insideShiftedBoxB
    {padding base : Nat} {source : Z4Plaq}
    (hsource : source ∈ boxPlaquettes base) :
    insideShiftedBoxB (uniformLower padding) base
      (uniformShiftPlaquette padding source) = true := by
  rw [insideShiftedBoxB_true_iff]
  rw [mem_boxPlaquettes] at hsource
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  change a < base ∧ b < base ∧ c < base ∧ d < base at hsource
  rcases hsource with ⟨ha, hb, hc, hd⟩
  simp only [uniformLower, uniformShiftPlaquette, uniformShiftVertex,
    cPlaq, vComp]
  exact ⟨by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

theorem insideShiftedBoxB_source
    {padding base : Nat} {plaquette : Z4Plaq}
    (hinside : insideShiftedBoxB
      (uniformLower padding) base plaquette = true) :
    ∃ source, source ∈ boxPlaquettes base ∧
      uniformShiftPlaquette padding source = plaquette := by
  rw [insideShiftedBoxB_true_iff] at hinside
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [uniformLower, cPlaq, vComp] at hinside
  rcases hinside with ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
  refine ⟨((a - padding, b - padding, c - padding, d - padding), plane),
    ?_, ?_⟩
  · rw [mem_boxPlaquettes]
    simp only
    exact ⟨by omega, by omega, by omega, by omega⟩
  · simp only [uniformShiftPlaquette, uniformShiftVertex, Prod.mk.injEq]
    rw [Nat.sub_add_cancel ha0, Nat.sub_add_cancel hb0,
      Nat.sub_add_cancel hc0, Nat.sub_add_cancel hd0]
    exact ⟨⟨rfl, rfl, rfl, rfl⟩, True.intro⟩

/-- Every plaquette in the literal translated list lies in the corresponding
half-open shifted coordinate box. -/
theorem mem_uniformShiftedPlaquetteList_implies_insideShiftedBoxB
    {padding base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ uniformShiftedPlaquetteList padding base) :
    insideShiftedBoxB (uniformLower padding) base plaquette = true := by
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq]
  exact uniformShiftPlaquette_insideShiftedBoxB hsource

/-- Conversely, the coordinate inequalities construct the explicit unshifted
source plaquette. -/
theorem insideShiftedBoxB_implies_mem_uniformShiftedPlaquetteList
    {padding base : Nat} {plaquette : Z4Plaq}
    (hinside : insideShiftedBoxB
      (uniformLower padding) base plaquette = true) :
    plaquette ∈ uniformShiftedPlaquetteList padding base := by
  obtain ⟨source, hsource, heq⟩ := insideShiftedBoxB_source hinside
  unfold uniformShiftedPlaquetteList
  apply List.mem_map.mpr
  exact ⟨source, hsource, heq⟩

/-- Membership in the literal translated plaquette list is exactly membership
in the half-open shifted coordinate box. -/
theorem mem_uniformShiftedPlaquetteList_iff_insideShiftedBoxB
    (padding base : Nat) (plaquette : Z4Plaq) :
    plaquette ∈ uniformShiftedPlaquetteList padding base ↔
      insideShiftedBoxB (uniformLower padding) base plaquette = true :=
  ⟨mem_uniformShiftedPlaquetteList_implies_insideShiftedBoxB,
    insideShiftedBoxB_implies_mem_uniformShiftedPlaquetteList⟩

/-- The Boolean shifted-box exit test is the exact complement of membership
in the translated source plaquette list. -/
theorem outsideShiftedBoxB_true_iff_not_mem_uniformShiftedPlaquetteList
    (padding base : Nat) (plaquette : Z4Plaq) :
    outsideShiftedBoxB (uniformLower padding) base plaquette = true ↔
      plaquette ∉ uniformShiftedPlaquetteList padding base := by
  rw [mem_uniformShiftedPlaquetteList_iff_insideShiftedBoxB]
  rw [outsideShiftedBoxB_true_iff, insideShiftedBoxB_true_iff]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [uniformLower, cPlaq, vComp]
  constructor
  · intro hout hinside
    rcases hinside with ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
    rcases hout with h0lo | h0hi | h1lo | h1hi |
      h2lo | h2hi | h3lo | h3hi <;> omega
  · intro hnotInside
    by_cases ha0 : padding ≤ a
    · by_cases ha1 : a < padding + base
      · by_cases hb0 : padding ≤ b
        · by_cases hb1 : b < padding + base
          · by_cases hc0 : padding ≤ c
            · by_cases hc1 : c < padding + base
              · by_cases hd0 : padding ≤ d
                · by_cases hd1 : d < padding + base
                  · exfalso
                    exact hnotInside
                      ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
                  · exact Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (by omega)))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inl (by omega)))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl (by omega))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl (by omega)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)

/-! ## 2. Small pinned target roots lie in the fixed affine image -/

/-- A target root pinned in the protected core and strictly smaller than the
shifted-boundary floor lies entirely in the uniformly shifted source box. -/
theorem smallPinnedCanonicalRoot_inside_uniformShift
    {padding inner distance targetFace : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers
      (uniformPaddedBase padding (inner + distance + distance)))
    (hpinned : targetFace ∈ target)
    (hcore : insideShiftedBoxB
      (addUniform (uniformLower padding) distance) inner
      (boxPlaquetteAt
        (uniformPaddedBase padding (inner + distance + distance))
        targetFace) = true)
    (hsmall : target.length < distance + 2) :
    TargetRootInsideUniformShift padding
      (inner + distance + distance) target := by
  intro plaquette hplaquette
  by_cases hinside : plaquette ∈ uniformShiftedPlaquetteList padding
      (inner + distance + distance)
  · exact hinside
  · have hexit : outsideShiftedBoxB (uniformLower padding)
        (inner + distance + distance) plaquette = true :=
      (outsideShiftedBoxB_true_iff_not_mem_uniformShiftedPlaquetteList
        padding (inner + distance + distance) plaquette).2 hinside
    have hfloor := canonicalSurfacePolymer_shifted_boundary_floor
      htarget hpinned hcore hplaquette hexit
    omega

/-- Consequently every such small target root occurs in the explicit image
of the fixed finite source-root list. -/
theorem smallPinnedCanonicalRoot_mem_uniformShiftCanonicalRoots
    {padding inner distance targetFace : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers
      (uniformPaddedBase padding (inner + distance + distance)))
    (hpinned : targetFace ∈ target)
    (hcore : insideShiftedBoxB
      (addUniform (uniformLower padding) distance) inner
      (boxPlaquetteAt
        (uniformPaddedBase padding (inner + distance + distance))
        targetFace) = true)
    (hsmall : target.length < distance + 2) :
    target ∈ uniformShiftCanonicalRoots padding
      (inner + distance + distance) := by
  exact (mem_uniformShiftCanonicalRoots_iff htarget).2
    (smallPinnedCanonicalRoot_inside_uniformShift
      htarget hpinned hcore hsmall)

/-- Constructive source-root recovery packages the canonical witness and its
exact forward round trip. -/
def smallPinnedCanonicalRootSource
    {padding inner distance targetFace : Nat} {target : List Nat}
    (htarget : target ∈ canonicalSurfacePolymers
      (uniformPaddedBase padding (inner + distance + distance)))
    (hpinned : targetFace ∈ target)
    (hcore : insideShiftedBoxB
      (addUniform (uniformLower padding) distance) inner
      (boxPlaquetteAt
        (uniformPaddedBase padding (inner + distance + distance))
        targetFace) = true)
    (hsmall : target.length < distance + 2) :
    Σ' source : List Nat,
      (source ∈ canonicalSurfacePolymers
          (inner + distance + distance)) ×'
        (uniformShiftCanonicalRoot padding
          (inner + distance + distance) source = target) := by
  let hinside := smallPinnedCanonicalRoot_inside_uniformShift
    htarget hpinned hcore hsmall
  exact ⟨uniformUnshiftCanonicalRoot padding
      (inner + distance + distance) target,
    uniformUnshiftCanonicalRoot_canonical htarget hinside,
    uniformUnshiftCanonicalRoot_roundtrip htarget hinside⟩

#print axioms mem_uniformShiftedPlaquetteList_iff_insideShiftedBoxB
#print axioms outsideShiftedBoxB_true_iff_not_mem_uniformShiftedPlaquetteList
#print axioms smallPinnedCanonicalRoot_inside_uniformShift
#print axioms smallPinnedCanonicalRoot_mem_uniformShiftCanonicalRoots
#print axioms smallPinnedCanonicalRootSource

end YMGap.Continuum.Z4CanonicalFaceEventPinnedLocalization
