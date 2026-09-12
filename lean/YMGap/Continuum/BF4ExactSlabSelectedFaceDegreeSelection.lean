/-
# Degree selection with all other physical interface faces retained

For a fixed supported insertion P, a selected original fixed-face character
vanishes under the SAME 116-link Haar integral when its spin exceeds the
degree of P in that face's exposed link. The other twenty-three characters
are retained at arbitrary spins: their degree in that link is zero.

The degree bound is computed after the two already-proved physical block
involutions. Full support is checked before using their Haar invariance or
the canonical-word prefix identity. This is exact algebraic selection, not
a spectral estimate or a thermodynamic/continuum limit.
-/

import YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection

namespace YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

private theorem headDegreeBound_le (bound : Nat) : ∀ p : RatPoly,
    (∀ t, t ∈ p → quaternionBlockDegree t.1 0 ≤ bound) → headDegreeBound p ≤ bound
  | [], _ => Nat.zero_le _
  | t :: p, h => Nat.max_le.mpr ⟨h t List.mem_cons_self,
      headDegreeBound_le bound p (fun s hs => h s (List.mem_cons_of_mem t hs))⟩

/-- Arbitrarily large degrees in other links do not enlarge this bound. -/
theorem headDegreeBound_mul_independent (p q : RatPoly)
    (hq : HasQuaternionBlockDegree 0 0 q) :
    headDegreeBound (polyMul p q) ≤ headDegreeBound p := by
  apply headDegreeBound_le
  intro t ht
  obtain ⟨s, hs, hmap⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, heq⟩ := List.mem_map.mp hmap
  rw [← heq]
  have hm : quaternionBlockDegree (monoMul s.1 r.1) 0 =
      quaternionBlockDegree s.1 0 + quaternionBlockDegree r.1 0 := by
    unfold quaternionBlockDegree
    rw [SU2QuaternionRatPolyDifferential.exponentAt_monoMul,
      SU2QuaternionRatPolyDifferential.exponentAt_monoMul,
      SU2QuaternionRatPolyDifferential.exponentAt_monoMul,
      SU2QuaternionRatPolyDifferential.exponentAt_monoMul]
    omega
  rw [hm, hq r hr, Nat.add_zero]
  exact headDegreeBound_spec p s hs

theorem doubleReindex_mul (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (p q : RatPoly) :
    exactFixedFaceDoubleReindex face hface (polyMul p q) =
      polyMul (exactFixedFaceDoubleReindex face hface p)
        (exactFixedFaceDoubleReindex face hface q) := by
  unfold exactFixedFaceDoubleReindex
  rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul]

theorem doubleReindex_supported (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (p : RatPoly) : SupportedQuaternionBlocks 116 (exactFixedFaceDoubleReindex face hface p) :=
  reindexQuaternionPolynomial_supported (exactFixedFaceTailBlockInvolution face hface) _

/-- The support premise prevents truncation from being mistaken for a
change of variables on a larger carrier. -/
theorem doubleReindex_haar (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 116 p) :
    quaternionHaar 116 (exactFixedFaceDoubleReindex face hface p) ≈ quaternionHaar 116 p :=
  Q'.eqv_trans _ _ _
    (quaternionHaar_reindex (exactFixedFaceTailBlockInvolution face hface) _
      (reindexQuaternionPolynomial_supported (exactFixedFaceHeadBlockInvolution face hface) p))
    (quaternionHaar_reindex (exactFixedFaceHeadBlockInvolution face hface) p hp)

/-- Explicit bound depending only on the fixed insertion, not other labels. -/
def selectedFaceDegreeBound (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (p : RatPoly) : Nat := headDegreeBound (exactFixedFaceDoubleReindex face hface p)

theorem selectedProduct_supported (boundary : EdgeLabelling) (face : Z4Plaq) :
    SupportedQuaternionBlocks 116 (exactFixedFaceSelectedProduct boundary face) := by
  rw [← correctedSlabLinks_extent_one_length]
  exact supported_polyMul (correctedSlabPlaquetteSpinFactor_support 1 boundary face)
    (correctedSlabSpinNetworkFaces_support 1 boundary (exactFixedFaceOtherFaces face))

/-- Canonical-word replacement remains valid WITH the unchanged insertion. -/
theorem selectedProduct_insert_haar_eq_canonical (boundary : EdgeLabelling)
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 116 p) :
    quaternionHaar 116 (polyMul p (exactFixedFaceSelectedProduct boundary face)) ≈
      quaternionHaar 116 (polyMul (exactFixedFaceDoubleReindex face hface p)
        (exactFixedFaceCanonicalSelectedProduct boundary face hface)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (doubleReindex_haar face hface _
    (supported_polyMul hp (selectedProduct_supported boundary face)))) ?_
  rw [doubleReindex_mul]
  exact quaternionHaar_prefixPolynomialEqv 116
    ((QuaternionPrefixPolynomialEqv.refl 116 _).mul
      (exactFixedFaceDoublyReindexedSelectedProduct_prefix boundary hface))
    (supported_polyMul (doubleReindex_supported face hface p)
      (exactFixedFaceDoublyReindexedSelectedProduct_supported boundary hface))
    (supported_polyMul (doubleReindex_supported face hface p)
      (exactFixedFaceCanonicalSelectedProduct_supported boundary hface))

/-- The selected spin may be arbitrarily large; the other twenty-three
spins are unrestricted and do not appear in the degree bound. -/
theorem selectedProduct_insert_haar_zero (boundary : EdgeLabelling)
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 116 p)
    (hs : selectedFaceDegreeBound face hface p <
      boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face)) :
    quaternionHaar 116 (polyMul p (exactFixedFaceSelectedProduct boundary face)) ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (selectedProduct_insert_haar_eq_canonical boundary face hface p hp) ?_
  unfold exactFixedFaceCanonicalSelectedProduct
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_middle_comm 116 _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc 116 _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm 116 _ _) ?_
  apply exposedCharacter_haar_zero false false true true
  exact Nat.lt_of_le_of_lt (headDegreeBound_mul_independent _ _
    (exactFixedFaceDoublyReindexedOther_headDegree_zero boundary hface)) hs

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

/-- Literal selected-face extraction, now under an arbitrary insertion. -/
theorem interior_insert_haar_eq_selected (boundary : EdgeLabelling)
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces) (p : RatPoly) :
    quaternionHaar 116 (polyMul p (exactCorrectedSlabInteriorInsertion boundary)) ≈
      quaternionHaar 116 (polyMul p (exactFixedFaceSelectedProduct boundary face)) :=
  quaternionHaar_factorFold_perm 116 (fun other => correctedSlabPlaquetteSpinFactor 1 boundary other)
    (erase_perm face hface) p

/-- Selection in the ORIGINAL full twenty-four-face interface, not a
surrogate kernel or an uninserted vacuum identity. -/
theorem interior_insert_haar_zero (boundary : EdgeLabelling)
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 116 p)
    (hs : selectedFaceDegreeBound face hface p <
      boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face)) :
    quaternionHaar 116 (polyMul p (exactCorrectedSlabInteriorInsertion boundary)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (interior_insert_haar_eq_selected boundary face hface p)
    (selectedProduct_insert_haar_zero boundary face hface p hp hs)

end YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection

#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.headDegreeBound_mul_independent
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.doubleReindex_mul
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.doubleReindex_supported
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.doubleReindex_haar
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.selectedFaceDegreeBound
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.selectedProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.selectedProduct_insert_haar_eq_canonical
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.selectedProduct_insert_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.interior_insert_haar_eq_selected
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceDegreeSelection.interior_insert_haar_zero
