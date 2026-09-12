/-
# Selection in the complete original interface at every odd extent

The actual central fixed-face list is noduplicated structurally. Removing
one selected face permutes its full character product without deleting any
other factor. The exposed-link theorem therefore annihilates the ORIGINAL
complete interface above an explicit insertion-dependent degree bound.

This supplies all-extent cutoff selection. Resummation and a common
cutoff-limit carrier are not asserted by this file.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection

namespace YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

def fixedFaces (half : Nat) : List Z4Plaq :=
  (centralFixedFaceIds half).map (slabPlaquetteAt (centralExtent half))

theorem fixedFaces_physical {half : Nat} {face : Z4Plaq} (hf : face ∈ fixedFaces half) :
    face ∈ boundaryCompleteSlabPlaquettes (centralExtent half) ∧ plaquetteHalfSide half face = .fixed := by
  obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hf
  exact ⟨slabPlaquetteAt_mem (mem_centralFixedFaceIds.mp hi).1, (mem_centralFixedFaceIds.mp hi).2⟩

theorem fixedFaces_nodup (half : Nat) : (fixedFaces half).Nodup := by
  apply nodup_map_of_injOn _ _ (fixedFaceIds_nodup half)
  intro a ha b hb he
  have hh := congrArg (fun face => (boundaryCompleteSlabPlaquettes (centralExtent half)).idxOf face) he
  dsimp only at hh
  rw [idxOf_slabPlaquetteAt (mem_centralFixedFaceIds.mp ha).1,
    idxOf_slabPlaquetteAt (mem_centralFixedFaceIds.mp hb).1] at hh
  exact hh

private theorem erase_perm (target : Z4Plaq) : ∀ {faces : List Z4Plaq},
    target ∈ faces → faces.Perm (target :: eraseFixedFace target faces)
  | [], h => False.elim (List.not_mem_nil h)
  | head :: tail, h => by
    by_cases heq : head = target
    · subst head
      simp only [eraseFixedFace, decide_true, ↓reduceIte]
      exact List.Perm.refl _
    · have ht : target ∈ tail := (List.mem_cons.mp h).resolve_left (fun h => heq h.symm)
      simp only [eraseFixedFace, decide_eq_false heq, Bool.false_eq_true, ↓reduceIte]
      exact (List.Perm.cons head (erase_perm target ht)).trans
        (List.Perm.swap target head (eraseFixedFace target tail))

/-- The literal full product of every central crossing-face character. -/
def interfaceCharacters (half : Nat) (boundary : EdgeLabelling) : RatPoly :=
  faceProduct (centralExtent half) boundary (fixedFaces half)

theorem interfaceCharacters_insert_zero {half : Nat} {selected : Z4Plaq}
    (hf : selected ∈ fixedFaces half) (boundary : EdgeLabelling) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hs : selectedFaceBound (fixedFaces_physical hf).1 p <
      boundary ((boundaryCompleteSlabPlaquettes (centralExtent half)).idxOf selected)) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul p (interfaceCharacters half boundary)) ≈ 0 := by
  have he := erase_perm selected hf
  have hn := (List.nodup_cons.mp (he.nodup (fixedFaces_nodup half))).1
  have ho : ∀ face, face ∈ eraseFixedFace selected (fixedFaces half) →
      face ∈ boundaryCompleteSlabPlaquettes (centralExtent half) ∧
        plaquetteHalfSide half face = .fixed ∧ face ≠ selected := by
    intro face hh
    have hfull := he.mem_iff.mpr (List.mem_cons_of_mem selected hh)
    have hfacts := fixedFaces_physical hfull
    exact ⟨hfacts.1, hfacts.2, fun h => hn (h ▸ hh)⟩
  refine Q'.eqv_trans _ _ _ (quaternionHaar_factorFold_perm _
    (correctedSlabPlaquetteSpinFactor (centralExtent half) boundary) he p) ?_
  change quaternionHaar _ (polyMul p (polyMul _ _)) ≈ 0
  have hcomm := (RatPolyCoeffEqv.mul_comm p
    (correctedSlabPlaquetteSpinFactor (centralExtent half) boundary selected)).mul_right
    (faceProduct (centralExtent half) boundary (eraseFixedFace selected (fixedFaces half)))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc _ _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ hcomm) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc _ _ _ _) ?_
  exact crossing_faces_product_zero (fixedFaces_physical hf).1 (fixedFaces_physical hf).2
    boundary _ ho p hp hs

/-- The maximum over the actual finite crossing-face carrier is data. -/
def interfaceBound (half : Nat) (p : RatPoly) : Nat :=
  ((fixedFaces half).attach.map (fun face => selectedFaceBound (fixedFaces_physical face.property).1 p)).foldr Nat.max 0

private theorem mem_le_max : ∀ (xs : List Nat) (n : Nat), n ∈ xs → n ≤ xs.foldr Nat.max 0
  | [], _, h => False.elim (List.not_mem_nil h)
  | a :: xs, n, h => by
    rcases List.mem_cons.mp h with rfl | hn
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (mem_le_max xs n hn) (Nat.le_max_right _ _)

theorem interfaceBound_spec (half : Nat) (p : RatPoly) {face : Z4Plaq} (hf : face ∈ fixedFaces half) :
    selectedFaceBound (fixedFaces_physical hf).1 p ≤ interfaceBound half p :=
  mem_le_max _ _ (List.mem_map.mpr ⟨⟨face, hf⟩, List.mem_attach _ _, rfl⟩)

/-- An above-bound spin on ANY actual fixed face annihilates the full interface. -/
theorem interfaceCharacters_above_bound_zero {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (boundary : EdgeLabelling) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hs : interfaceBound half p < boundary id) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul p (interfaceCharacters half boundary)) ≈ 0 := by
  have hf : slabPlaquetteAt (centralExtent half) id ∈ fixedFaces half := List.mem_map.mpr ⟨id, hi, rfl⟩
  apply interfaceCharacters_insert_zero hf boundary p hp
  rw [idxOf_slabPlaquetteAt (mem_centralFixedFaceIds.mp hi).1]
  exact Nat.lt_of_le_of_lt (interfaceBound_spec half p hf) hs

end YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection.fixedFaces
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection.fixedFaces_physical
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection.fixedFaces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection.interfaceCharacters
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection.interfaceCharacters_insert_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection.interfaceBound
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection.interfaceBound_spec
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection.interfaceCharacters_above_bound_zero
