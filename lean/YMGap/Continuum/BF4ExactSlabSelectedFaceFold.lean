/-
# Exact selected-face extraction from the BF4 fixed-plane fold

This module extracts one selected plaquette character from the literal
twenty-four-factor fixed-plane insertion.  The remaining twenty-three factors
are proved to have degree zero in the selected exposed quaternion, and this
degree statement is transported through the explicit head-swap involution.

The extraction is performed only under the exact product-Haar functional,
where factor permutations have already been proved constructively.  No
expanded normalization of the full slab polynomial is required.
-/

import YMGap.Continuum.BF4ExactSlabSelectedFaceDegree
import YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
import YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport

namespace YMGap.Continuum.BF4ExactSlabSelectedFaceFold

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSelectedFaceDegree
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- Constructive first-occurrence erasure specialized to the physical face
type.  Its proofs below avoid the classical choice dependency carried by the
generic library theorem `List.perm_cons_erase`. -/
def eraseFixedFace (target : Z4Plaq) : List Z4Plaq → List Z4Plaq
  | [] => []
  | head :: tail =>
      if decide (head = target) then tail
      else head :: eraseFixedFace target tail

private theorem eraseFixedFace_perm_cons
    (target : Z4Plaq) : ∀ {faces : List Z4Plaq},
    target ∈ faces → faces.Perm (target :: eraseFixedFace target faces)
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      cases hdec : decide (head = target) with
      | true =>
        have heq : head = target := of_decide_eq_true hdec
        subst head
        unfold eraseFixedFace
        rw [hdec]
        rw [if_pos rfl]
      | false =>
        have hne : head ≠ target := by
          intro heq
          have htrue : decide (head = target) = true := decide_eq_true heq
          rw [htrue] at hdec
          exact Bool.noConfusion hdec
        have htail : target ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left (fun heq => hne heq.symm)
        unfold eraseFixedFace
        rw [hdec]
        exact (List.Perm.cons head
          (eraseFixedFace_perm_cons target htail)).trans
            (List.Perm.swap target head (eraseFixedFace target tail))

private theorem mem_of_mem_eraseFixedFace
    (target : Z4Plaq) : ∀ {faces : List Z4Plaq} {face : Z4Plaq},
    face ∈ eraseFixedFace target faces → face ∈ faces
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, face, hmem => by
      cases hdec : decide (head = target) with
      | true =>
        unfold eraseFixedFace at hmem
        rw [hdec] at hmem
        exact List.mem_cons_of_mem head hmem
      | false =>
        unfold eraseFixedFace at hmem
        rw [hdec] at hmem
        rcases List.mem_cons.mp hmem with heq | htail
        · exact List.mem_cons.mpr (Or.inl heq)
        · exact List.mem_cons_of_mem head
            (mem_of_mem_eraseFixedFace target htail)

private theorem not_mem_eraseFixedFace_of_nodup
    (target : Z4Plaq) : ∀ {faces : List Z4Plaq},
    faces.Nodup → target ∉ eraseFixedFace target faces
  | [], _ => List.not_mem_nil
  | head :: tail, hnodup => by
      rw [List.nodup_cons] at hnodup
      cases hdec : decide (head = target) with
      | true =>
        have heq : head = target := of_decide_eq_true hdec
        subst head
        unfold eraseFixedFace
        rw [hdec]
        exact hnodup.1
      | false =>
        have hne : head ≠ target := by
          intro heq
          have htrue : decide (head = target) = true := decide_eq_true heq
          rw [htrue] at hdec
          exact Bool.noConfusion hdec
        unfold eraseFixedFace
        rw [hdec]
        intro hmem
        rcases List.mem_cons.mp hmem with heq | htail
        · exact hne heq.symm
        · exact (not_mem_eraseFixedFace_of_nodup target hnodup.2) htail

/-- The literal residual list after deleting the selected fixed face. -/
def exactFixedFaceOtherFaces (face : Z4Plaq) : List Z4Plaq :=
  eraseFixedFace face exactCorrectedSlabFixedFaces

/-- The product of the other twenty-three fixed-face character factors. -/
def exactFixedFaceOtherInsertion
    (boundary : EdgeLabelling) (face : Z4Plaq) : RatPoly :=
  (exactFixedFaceOtherFaces face).foldr
    (fun other total =>
      polyMul
        (correctedSlabPlaquetteSpinFactor 1 boundary other)
        total)
    polyOne

/-- The finite fixed-face list has no repetitions. -/
theorem exactCorrectedSlabFixedFaces_nodup :
    exactCorrectedSlabFixedFaces.Nodup := by
  decide

private theorem quaternionHaar_polyMul_one_left
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks (polyMul polyOne polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact Q'.eqv_trans _
    (quaternionHaar blocks (polyMul polynomial polyOne)) _
    (quaternionHaar_polyMul_comm blocks polyOne polynomial)
    (quaternionHaar_polyMul_one_right blocks polynomial)

/-- **Exact selected-face fold extraction.**  Under the literal 116-block
Haar functional, the twenty-four-face fold equals the selected character
times the fold obtained by erasing that face. -/
theorem exactInteriorHaar_eq_selectedFace_mul_other
    (boundary : EdgeLabelling) (face : Z4Plaq)
    (hface : face ∈ exactCorrectedSlabFixedFaces) :
    quaternionHaar 116
        (exactCorrectedSlabInteriorInsertion boundary) ≈
      quaternionHaar 116
        (polyMul
          (correctedSlabPlaquetteSpinFactor 1 boundary face)
          (exactFixedFaceOtherInsertion boundary face)) := by
  let factor : Z4Plaq → RatPoly := fun other =>
    correctedSlabPlaquetteSpinFactor 1 boundary other
  have hperm :
      exactCorrectedSlabFixedFaces.Perm
        (face :: eraseFixedFace face exactCorrectedSlabFixedFaces) :=
    eraseFixedFace_perm_cons face hface
  have hfold := quaternionHaar_factorFold_perm
    116 factor hperm polyOne
  unfold exactCorrectedSlabInteriorInsertion
  refine Q'.eqv_trans _
    (quaternionHaar 116
      (polyMul polyOne
        (exactCorrectedSlabFixedFaces.foldr
          (fun other total => polyMul (factor other) total)
          polyOne))) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_one_left 116 _)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 116
      (polyMul polyOne
        ((face :: eraseFixedFace face exactCorrectedSlabFixedFaces).foldr
          (fun other total => polyMul (factor other) total)
          polyOne))) _
    hfold ?_
  simp only [List.foldr]
  exact quaternionHaar_polyMul_one_left 116 _

/-- A character of a scalar of block degree zero still has block degree zero
at every spin. -/
theorem characterPolynomial_blockDegree_zero
    {block : Nat} {scalar : RatPoly}
    (hscalar : HasQuaternionBlockDegree block 0 scalar) :
    ∀ spin,
      HasQuaternionBlockDegree block 0
        (characterPolynomial scalar spin)
  | 0 => hasQuaternionBlockDegree_one block
  | 1 => hscalar.smul 2
  | spin + 2 => by
      apply HasQuaternionBlockDegree.add
      · exact HasQuaternionBlockDegree.relabel (by omega)
          ((hscalar.smul 2).mul
            (characterPolynomial_blockDegree_zero hscalar (spin + 1)))
      · exact (characterPolynomial_blockDegree_zero hscalar spin).smul (-1)

/-- Every non-selected fixed-face character is independent of the selected
face's exposed quaternion block. -/
theorem otherFaceSpinFactor_blockDegree_zero
    (boundary : EdgeLabelling) {selected other : Z4Plaq}
    (hselected : selected ∈ exactCorrectedSlabFixedFaces)
    (hother : other ∈ exactCorrectedSlabFixedFaces)
    (hne : other ≠ selected) :
    HasQuaternionBlockDegree (exactFixedFaceExposedBlock selected) 0
      (correctedSlabPlaquetteSpinFactor 1 boundary other) := by
  unfold correctedSlabPlaquetteSpinFactor
  apply characterPolynomial_blockDegree_zero
  exact otherFaceScalar_degree_zero hselected hother hne

private theorem otherFaceFold_blockDegree_zero
    (boundary : EdgeLabelling) {selected : Z4Plaq}
    (hselected : selected ∈ exactCorrectedSlabFixedFaces) :
    ∀ faces : List Z4Plaq,
      (∀ other, other ∈ faces →
        other ∈ exactCorrectedSlabFixedFaces) →
      selected ∉ faces →
      HasQuaternionBlockDegree (exactFixedFaceExposedBlock selected) 0
        (faces.foldr
          (fun other total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor 1 boundary other)
              total)
          polyOne)
  | [], _, _ => hasQuaternionBlockDegree_one _
  | other :: rest, hfaces, hnotmem => by
      simp only [List.foldr]
      have hother : other ∈ exactCorrectedSlabFixedFaces :=
        hfaces other List.mem_cons_self
      have hne : other ≠ selected := by
        intro heq
        apply hnotmem
        simp [heq]
      have hrestNot : selected ∉ rest := by
        intro hmem
        exact hnotmem (List.mem_cons_of_mem other hmem)
      exact HasQuaternionBlockDegree.relabel (by omega)
        ((otherFaceSpinFactor_blockDegree_zero
            boundary hselected hother hne).mul
          (otherFaceFold_blockDegree_zero
            boundary hselected rest
            (fun item hitem =>
              hfaces item (List.mem_cons_of_mem other hitem))
            hrestNot))

/-- The erased twenty-three-face fold is independent of the selected exposed
block before reindexing. -/
theorem exactFixedFaceOtherInsertion_blockDegree_zero
    (boundary : EdgeLabelling) (face : Z4Plaq)
    (hface : face ∈ exactCorrectedSlabFixedFaces) :
    HasQuaternionBlockDegree (exactFixedFaceExposedBlock face) 0
      (exactFixedFaceOtherInsertion boundary face) := by
  unfold exactFixedFaceOtherInsertion exactFixedFaceOtherFaces
  apply otherFaceFold_blockDegree_zero boundary hface
  · intro other hother
    exact mem_of_mem_eraseFixedFace face hother
  · exact not_mem_eraseFixedFace_of_nodup face
      exactCorrectedSlabFixedFaces_nodup

/-- Exact block degree is transported contravariantly by an explicit block
involution.  A target block reads the source block named by `map`. -/
theorem blockDegree_reindex
    {blocks source target degree : Nat}
    (permutation : QuaternionBlockInvolution blocks)
    (htarget : target < blocks)
    (hmap : permutation.map target = source)
    {polynomial : RatPoly}
    (hdegree : HasQuaternionBlockDegree source degree polynomial) :
    HasQuaternionBlockDegree target degree
      (reindexQuaternionPolynomial permutation polynomial) := by
  intro term hterm
  unfold reindexQuaternionPolynomial at hterm
  obtain ⟨original, horiginal, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq]
  have horiginalDegree := hdegree original horiginal
  unfold quaternionBlockDegree at horiginalDegree ⊢
  rw [exponentAt_reindexQuaternionExponents permutation original.1
        (by omega),
    exponentAt_reindexQuaternionExponents permutation original.1
        (by omega),
    exponentAt_reindexQuaternionExponents permutation original.1
        (by omega),
    exponentAt_reindexQuaternionExponents permutation original.1
        (by omega)]
  have hd0 : (4 * target) / 4 = target := by omega
  have hm0 : (4 * target) % 4 = 0 := by omega
  have hd1 : (4 * target + 1) / 4 = target := by omega
  have hm1 : (4 * target + 1) % 4 = 1 := by omega
  have hd2 : (4 * target + 2) / 4 = target := by omega
  have hm2 : (4 * target + 2) % 4 = 2 := by omega
  have hd3 : (4 * target + 3) / 4 = target := by omega
  have hm3 : (4 * target + 3) % 4 = 3 := by omega
  rw [hd0, hm0, hd1, hm1, hd2, hm2, hd3, hm3, hmap]
  simpa only [Nat.add_zero] using horiginalDegree

/-- After the canonical selected-block swap, the other twenty-three face
factors are genuinely independent of the Gaussian/Haar head block. -/
theorem reindexedExactFixedFaceOtherInsertion_headDegree_zero
    (boundary : EdgeLabelling) (face : Z4Plaq)
    (hface : face ∈ exactCorrectedSlabFixedFaces) :
    HasQuaternionBlockDegree 0 0
      (reindexQuaternionPolynomial
        (headSwapBlockInvolution 116
          (exactFixedFaceExposedBlock face)
          (exactFixedFaceExposedBlock_lt hface))
        (exactFixedFaceOtherInsertion boundary face)) := by
  apply blockDegree_reindex
    (headSwapBlockInvolution 116
      (exactFixedFaceExposedBlock face)
      (exactFixedFaceExposedBlock_lt hface))
    (by omega)
    (headSwapBlockInvolution_map_zero 116
      (exactFixedFaceExposedBlock face)
      (exactFixedFaceExposedBlock_lt hface))
  exact exactFixedFaceOtherInsertion_blockDegree_zero boundary face hface

/-! ## The exact three-transposition tail permutation -/

/-- The four quaternion blocks, in the literal oriented plaquette-word
order, occupied by one fixed face. -/
def exactFixedFaceWordBlocks (face : Z4Plaq) : List Nat :=
  (orientedPlaquetteBoundary face).map (fun entry =>
    (boundaryCompleteSlabLinks 1).idxOf entry.link)

/-- The four inversion bits in the same literal word order. -/
def exactFixedFaceWordOrientations (face : Z4Plaq) : List Bool :=
  (orientedPlaquetteBoundary face).map (fun entry => entry.reverse)

/-- Source block for canonical tail slot `slot + 1`.  Only slots `0,1,2`
are used below; the total fallback makes the definition computational. -/
def exactFixedFaceTailSource (face : Z4Plaq) (slot : Nat) : Nat :=
  (exactFixedFaceWordBlocks face).getD (slot + 1) 0

/-- Swap canonical tail blocks `1,2,3` with the selected word's three
non-head blocks.  The finite geometry theorem below proves that these are
three disjoint transpositions on every physical fixed face. -/
def exactFixedFaceTailBlockMap (face : Z4Plaq) (block : Nat) : Nat :=
  let source1 := exactFixedFaceTailSource face 0
  let source2 := exactFixedFaceTailSource face 1
  let source3 := exactFixedFaceTailSource face 2
  if block = 1 then source1
  else if block = source1 then 1
  else if block = 2 then source2
  else if block = source2 then 2
  else if block = 3 then source3
  else if block = source3 then 3
  else block

private def exactFixedFaceTailGeometryCheck : Bool :=
  exactCorrectedSlabFixedFaces.all (fun face =>
    decide (
      exactFixedFaceWordBlocks face =
        [exactFixedFaceExposedBlock face,
          exactFixedFaceTailSource face 0,
          exactFixedFaceTailSource face 1,
          exactFixedFaceTailSource face 2] ∧
      exactFixedFaceWordOrientations face =
        [false, false, true, true] ∧
      List.Nodup
        [0, 1, exactFixedFaceTailSource face 0,
          2, exactFixedFaceTailSource face 1,
          3, exactFixedFaceTailSource face 2]))

private theorem exactFixedFaceTailGeometry_check :
    exactFixedFaceTailGeometryCheck = true := by
  decide

/-- Exact selected-face word audit.  It records both the link order and the
orientation pattern, and proves that the three required swaps are disjoint. -/
theorem exactFixedFaceTailGeometry
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    exactFixedFaceWordBlocks face =
        [exactFixedFaceExposedBlock face,
          exactFixedFaceTailSource face 0,
          exactFixedFaceTailSource face 1,
          exactFixedFaceTailSource face 2] ∧
      exactFixedFaceWordOrientations face =
        [false, false, true, true] ∧
      List.Nodup
        [0, 1, exactFixedFaceTailSource face 0,
          2, exactFixedFaceTailSource face 1,
          3, exactFixedFaceTailSource face 2] := by
  have hrow := List.all_eq_true.mp
    exactFixedFaceTailGeometry_check face hface
  exact of_decide_eq_true hrow

private def exactFixedFaceTailPermutationCheck : Bool :=
  exactCorrectedSlabFixedFaces.all (fun face =>
    (List.range 116).all (fun block =>
      decide (
        exactFixedFaceTailBlockMap face block < 116 ∧
        exactFixedFaceTailBlockMap face
          (exactFixedFaceTailBlockMap face block) = block)))

private theorem exactFixedFaceTailPermutation_check :
    exactFixedFaceTailPermutationCheck = true := by
  decide

theorem exactFixedFaceTailBlockMap_lt
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces)
    {block : Nat} (hblock : block < 116) :
    exactFixedFaceTailBlockMap face block < 116 := by
  have hrow := List.all_eq_true.mp
    exactFixedFaceTailPermutation_check face hface
  have hentry := List.all_eq_true.mp hrow block
    (List.mem_range.mpr hblock)
  exact (of_decide_eq_true hentry).1

theorem exactFixedFaceTailBlockMap_involutive
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces)
    {block : Nat} (hblock : block < 116) :
    exactFixedFaceTailBlockMap face
      (exactFixedFaceTailBlockMap face block) = block := by
  have hrow := List.all_eq_true.mp
    exactFixedFaceTailPermutation_check face hface
  have hentry := List.all_eq_true.mp hrow block
    (List.mem_range.mpr hblock)
  exact (of_decide_eq_true hentry).2

private def exactFixedFaceTailBlockImagesCheck : Bool :=
  exactCorrectedSlabFixedFaces.all (fun face =>
    decide (
      exactFixedFaceTailBlockMap face 0 = 0 ∧
      exactFixedFaceTailBlockMap face 1 =
          exactFixedFaceTailSource face 0 ∧
      exactFixedFaceTailBlockMap face 2 =
          exactFixedFaceTailSource face 1 ∧
      exactFixedFaceTailBlockMap face 3 =
          exactFixedFaceTailSource face 2))

private theorem exactFixedFaceTailBlockImages_check :
    exactFixedFaceTailBlockImagesCheck = true := by
  decide

/-- The three-pair map fixes the selected head and sends canonical tail
slots `1,2,3` to the three literal tail sources. -/
theorem exactFixedFaceTailBlockMap_first_four
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    exactFixedFaceTailBlockMap face 0 = 0 ∧
      exactFixedFaceTailBlockMap face 1 =
          exactFixedFaceTailSource face 0 ∧
      exactFixedFaceTailBlockMap face 2 =
          exactFixedFaceTailSource face 1 ∧
      exactFixedFaceTailBlockMap face 3 =
          exactFixedFaceTailSource face 2 := by
  have hrow := List.all_eq_true.mp
    exactFixedFaceTailBlockImages_check face hface
  exact of_decide_eq_true hrow

/-- The physical tail permutation as constructive Haar change-of-variable
data.  No finite equivalence or choice operation is hidden in this object. -/
def exactFixedFaceTailBlockInvolution
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces) :
    QuaternionBlockInvolution 116 where
  map := exactFixedFaceTailBlockMap face
  map_lt := fun _ hblock =>
    exactFixedFaceTailBlockMap_lt hface hblock
  involutive := fun _ hblock =>
    exactFixedFaceTailBlockMap_involutive hface hblock

/-- Compose the tail permutation with the prior head swap.  This reports
which original slab block is read by each new block. -/
def exactFixedFaceCombinedBlockMap (face : Z4Plaq) (block : Nat) : Nat :=
  headSwapBlockMap (exactFixedFaceExposedBlock face)
    (exactFixedFaceTailBlockMap face block)

private def exactFixedFaceCombinedBlockCheck : Bool :=
  exactCorrectedSlabFixedFaces.all (fun face =>
    decide (
      exactFixedFaceCombinedBlockMap face 0 =
          exactFixedFaceExposedBlock face ∧
      exactFixedFaceCombinedBlockMap face 1 =
          exactFixedFaceTailSource face 0 ∧
      exactFixedFaceCombinedBlockMap face 2 =
          exactFixedFaceTailSource face 1 ∧
      exactFixedFaceCombinedBlockMap face 3 =
          exactFixedFaceTailSource face 2))

private theorem exactFixedFaceCombinedBlock_check :
    exactFixedFaceCombinedBlockCheck = true := by
  decide

/-- **Exact tail-permutation certificate.**  After the exposed-link head
swap and the three disjoint tail swaps, new blocks `0,1,2,3` read precisely
the selected face's four old blocks in oriented word order. -/
theorem exactFixedFaceCombinedBlockMap_first_four
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    exactFixedFaceCombinedBlockMap face 0 =
        exactFixedFaceExposedBlock face ∧
      exactFixedFaceCombinedBlockMap face 1 =
        exactFixedFaceTailSource face 0 ∧
      exactFixedFaceCombinedBlockMap face 2 =
        exactFixedFaceTailSource face 1 ∧
      exactFixedFaceCombinedBlockMap face 3 =
        exactFixedFaceTailSource face 2 := by
  have hrow := List.all_eq_true.mp
    exactFixedFaceCombinedBlock_check face hface
  exact of_decide_eq_true hrow

end YMGap.Continuum.BF4ExactSlabSelectedFaceFold

#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceFold.exactInteriorHaar_eq_selectedFace_mul_other
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceFold.exactFixedFaceOtherInsertion_blockDegree_zero
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceFold.blockDegree_reindex
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceFold.reindexedExactFixedFaceOtherInsertion_headDegree_zero
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceFold.exactFixedFaceTailGeometry
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceFold.exactFixedFaceTailBlockMap_involutive
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceFold.exactFixedFaceTailBlockMap_first_four
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceFold.exactFixedFaceCombinedBlockMap_first_four
