/-
# Selected-link Haar reduction for the exact BF4 vacuum coefficient

This module moves the canonical exposed link of a nontrivial fixed face to
the first quaternion block and applies the constructive polynomial Fubini
theorem.  It identifies the exact remaining positivity atom as a literal
115-block Haar value of a polynomial-valued one-link integral.

No abstract kernel, measure, or positivity field is introduced.
-/

import YMGap.Continuum.BF4ExactSlabVacuumReflection
import YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction
import YMGap.Continuum.SU2QuaternionHaarHeadFubini

namespace YMGap.Continuum.BF4ExactSlabVacuumSelectedHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The block number of the canonical exposed link of a fixed face. -/
def exactFixedFaceExposedBlock (face : Z4Plaq) : Nat :=
  (boundaryCompleteSlabLinks 1).idxOf
    (exactFixedFaceExposedLink face)

theorem exactFixedFaceExposedBlock_lt
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    exactFixedFaceExposedBlock face < 116 := by
  unfold exactFixedFaceExposedBlock
  rw [← correctedSlabLinks_extent_one_length]
  exact List.idxOf_lt_length_of_mem
    (exactFixedFaceExposedLink_spec hface).2.1

/-- Reindex the exposed link to block zero and integrate precisely that
`S^3` variable.  The output is a rational polynomial in the remaining 115
quaternion blocks. -/
def exactFixedFaceSelectedPartialInsertion
    (boundary : EdgeLabelling) (face : Z4Plaq)
    (hface : face ∈ exactCorrectedSlabFixedFaces) : RatPoly :=
  partialHaarHead
    (reindexQuaternionPolynomial
      (headSwapBlockInvolution 116
        (exactFixedFaceExposedBlock face)
        (exactFixedFaceExposedBlock_lt hface))
      (exactCorrectedSlabInteriorInsertion boundary))

/-- The original 116-link Haar coefficient is exactly the remaining
115-link Haar functional applied after selected-link partial integration. -/
theorem exactInteriorHaar_eq_selectedPartial
    (boundary : EdgeLabelling) (face : Z4Plaq)
    (hface : face ∈ exactCorrectedSlabFixedFaces) :
    quaternionHaar 116
        (exactCorrectedSlabInteriorInsertion boundary) ≈
      quaternionHaar 115
        (exactFixedFaceSelectedPartialInsertion boundary face hface) := by
  have hsupport :
      SupportedQuaternionBlocks 116
        (exactCorrectedSlabInteriorInsertion boundary) := by
    simpa [correctedSlabLinks_extent_one_length] using
      (exactCorrectedSlabInteriorInsertion_supported boundary)
  exact quaternionHaar_eq_partialHaar_selected 115
    (exactFixedFaceExposedBlock face)
    (exactFixedFaceExposedBlock_lt hface)
    (exactCorrectedSlabInteriorInsertion boundary)
    hsupport

/-- The genuinely conditional, polynomial Peter--Weyl target after Fubini.
Unlike the earlier statement, this proposition visibly performs the selected
one-link integration before asking the remaining 115-link Haar functional to
vanish. -/
def ExactFixedFaceSelectedPartialOrthogonality : Prop :=
  ∀ (boundary : EdgeLabelling) (face : Z4Plaq)
      (hface : face ∈ exactCorrectedSlabFixedFaces),
    boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face) ≠ 0 →
      quaternionHaar 115
          (exactFixedFaceSelectedPartialInsertion boundary face hface) ≈
        0

/-! ## The unconditional odd-spin half of the Peter--Weyl atom -/

/-- Syntactic parity of one quaternion block throughout a polynomial. -/
def HasQuaternionBlockParity
    (block parity : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    quaternionBlockDegree term.1 block % 2 = parity % 2

/-- Exact degree in one quaternion block.  This stronger carrier is retained
for the even-spin solid-harmonic continuation; parity is its immediate
corollary. -/
def HasQuaternionBlockDegree
    (block degree : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    quaternionBlockDegree term.1 block = degree

private theorem blockDegree_monoMul
    (left right : List Nat) (block : Nat) :
    quaternionBlockDegree (monoMul left right) block =
      quaternionBlockDegree left block +
        quaternionBlockDegree right block := by
  unfold quaternionBlockDegree
  rw [exponentAt_monoMul, exponentAt_monoMul,
    exponentAt_monoMul, exponentAt_monoMul]
  omega

private theorem blockParity_one (block : Nat) :
    HasQuaternionBlockParity block 0 polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp [quaternionBlockDegree, exponentAt]

private theorem blockParity_add
    {block parity : Nat} {left right : RatPoly}
    (hleft : HasQuaternionBlockParity block parity left)
    (hright : HasQuaternionBlockParity block parity right) :
    HasQuaternionBlockParity block parity (polyAdd left right) := by
  intro term hterm
  rcases List.mem_append.mp hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem blockParity_smul
    {block parity : Nat} {polynomial : RatPoly}
    (scale : Q')
    (hsupport : HasQuaternionBlockParity block parity polynomial) :
    HasQuaternionBlockParity block parity
      (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq]
  exact hsupport source hsource

private theorem blockParity_mul
    {block leftParity rightParity : Nat}
    {left right : RatPoly}
    (hleft : HasQuaternionBlockParity block leftParity left)
    (hright : HasQuaternionBlockParity block rightParity right) :
    HasQuaternionBlockParity block (leftParity + rightParity)
      (polyMul left right) := by
  intro term hterm
  obtain ⟨source, hsource, htargetTerm⟩ :=
    List.mem_flatMap.mp hterm
  obtain ⟨target, htarget, htermEq⟩ :=
    List.mem_map.mp htargetTerm
  rw [← htermEq, blockDegree_monoMul]
  calc
    (quaternionBlockDegree source.1 block +
          quaternionBlockDegree target.1 block) % 2 =
        (quaternionBlockDegree source.1 block % 2 +
          quaternionBlockDegree target.1 block % 2) % 2 := by
            exact Nat.add_mod _ _ _
    _ = (leftParity % 2 + rightParity % 2) % 2 := by
          rw [hleft source hsource, hright target htarget]
    _ = (leftParity + rightParity) % 2 := by
          exact (Nat.add_mod _ _ _).symm

private theorem blockParity_relabel
    {block first second : Nat} {polynomial : RatPoly}
    (hsame : first % 2 = second % 2)
    (hparity : HasQuaternionBlockParity block first polynomial) :
    HasQuaternionBlockParity block second polynomial := by
  intro term hterm
  rw [← hsame]
  exact hparity term hterm

/-- A character of an odd block-linear scalar has the parity of its spin. -/
private theorem characterPolynomial_blockParity_of_odd
    {block : Nat} {scalar : RatPoly}
    (hscalar : HasQuaternionBlockParity block 1 scalar) :
    ∀ spin,
      HasQuaternionBlockParity block (spin % 2)
        (characterPolynomial scalar spin)
  | 0 => blockParity_one block
  | 1 => blockParity_smul 2 hscalar
  | spin + 2 => by
      apply blockParity_add
      · exact blockParity_relabel (by omega)
          (blockParity_mul
            (blockParity_smul 2 hscalar)
            (characterPolynomial_blockParity_of_odd hscalar (spin + 1)))
      · exact blockParity_relabel (by omega)
          (blockParity_smul (-1)
            (characterPolynomial_blockParity_of_odd hscalar spin))

/-- An even block scalar produces an even character at every spin. -/
private theorem characterPolynomial_blockParity_of_even
    {block : Nat} {scalar : RatPoly}
    (hscalar : HasQuaternionBlockParity block 0 scalar) :
    ∀ spin,
      HasQuaternionBlockParity block 0
        (characterPolynomial scalar spin)
  | 0 => blockParity_one block
  | 1 => blockParity_smul 2 hscalar
  | spin + 2 => by
      exact blockParity_add
        (blockParity_mul
          (blockParity_smul 2 hscalar)
          (characterPolynomial_blockParity_of_even hscalar (spin + 1)))
        (blockParity_smul (-1)
          (characterPolynomial_blockParity_of_even hscalar spin))

private def polynomialBlockDegreeCheck
    (block degree : Nat) (polynomial : RatPoly) : Bool :=
  polynomial.all fun term =>
    decide (quaternionBlockDegree term.1 block = degree)

private def fixedFaceScalarDegreeRowCheck (face : Z4Plaq) : Bool :=
  let block := exactFixedFaceExposedBlock face
  polynomialBlockDegreeCheck block 1
      (correctedSlabPlaquettePolynomial 1 face).scalar &&
    exactCorrectedSlabFixedFaces.all fun other =>
      if decide (other = face) then true
      else polynomialBlockDegreeCheck block 0
        (correctedSlabPlaquettePolynomial 1 other).scalar

private def fixedFaceScalarDegreeCheck : Bool :=
  exactCorrectedSlabFixedFaces.all fixedFaceScalarDegreeRowCheck

private def fixedFaceDegreeEntry (offset : Nat) : Z4Plaq :=
  exactCorrectedSlabFixedFaces.getD offset fallbackPlaquette

private theorem fixedFaceDegree_entries :
    exactCorrectedSlabFixedFaces =
      [fixedFaceDegreeEntry 0, fixedFaceDegreeEntry 1,
       fixedFaceDegreeEntry 2, fixedFaceDegreeEntry 3,
       fixedFaceDegreeEntry 4, fixedFaceDegreeEntry 5,
       fixedFaceDegreeEntry 6, fixedFaceDegreeEntry 7,
       fixedFaceDegreeEntry 8, fixedFaceDegreeEntry 9,
       fixedFaceDegreeEntry 10, fixedFaceDegreeEntry 11,
       fixedFaceDegreeEntry 12, fixedFaceDegreeEntry 13,
       fixedFaceDegreeEntry 14, fixedFaceDegreeEntry 15,
       fixedFaceDegreeEntry 16, fixedFaceDegreeEntry 17,
       fixedFaceDegreeEntry 18, fixedFaceDegreeEntry 19,
       fixedFaceDegreeEntry 20, fixedFaceDegreeEntry 21,
       fixedFaceDegreeEntry 22, fixedFaceDegreeEntry 23] := by
  decide

private theorem fixedFaceDegree_row0 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 0) = true := by decide
private theorem fixedFaceDegree_row1 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 1) = true := by decide
private theorem fixedFaceDegree_row2 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 2) = true := by decide
private theorem fixedFaceDegree_row3 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 3) = true := by decide
private theorem fixedFaceDegree_row4 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 4) = true := by decide
private theorem fixedFaceDegree_row5 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 5) = true := by decide
private theorem fixedFaceDegree_row6 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 6) = true := by decide
private theorem fixedFaceDegree_row7 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 7) = true := by decide
private theorem fixedFaceDegree_row8 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 8) = true := by decide
private theorem fixedFaceDegree_row9 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 9) = true := by decide
private theorem fixedFaceDegree_row10 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 10) = true := by decide
private theorem fixedFaceDegree_row11 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 11) = true := by decide
private theorem fixedFaceDegree_row12 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 12) = true := by decide
private theorem fixedFaceDegree_row13 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 13) = true := by decide
private theorem fixedFaceDegree_row14 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 14) = true := by decide
private theorem fixedFaceDegree_row15 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 15) = true := by decide
private theorem fixedFaceDegree_row16 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 16) = true := by decide
private theorem fixedFaceDegree_row17 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 17) = true := by decide
private theorem fixedFaceDegree_row18 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 18) = true := by decide
private theorem fixedFaceDegree_row19 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 19) = true := by decide
private theorem fixedFaceDegree_row20 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 20) = true := by decide
private theorem fixedFaceDegree_row21 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 21) = true := by decide
private theorem fixedFaceDegree_row22 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 22) = true := by decide
private theorem fixedFaceDegree_row23 :
    fixedFaceScalarDegreeRowCheck (fixedFaceDegreeEntry 23) = true := by decide

/-- Literal incidence audit: the selected face is exactly linear in its
exposed block, and every other fixed face is independent of that block. -/
private theorem fixedFaceScalarDegree_check :
    fixedFaceScalarDegreeCheck = true := by
  unfold fixedFaceScalarDegreeCheck
  rw [fixedFaceDegree_entries]
  simp only [List.all_cons, List.all_nil,
    fixedFaceDegree_row0, fixedFaceDegree_row1,
    fixedFaceDegree_row2, fixedFaceDegree_row3,
    fixedFaceDegree_row4, fixedFaceDegree_row5,
    fixedFaceDegree_row6, fixedFaceDegree_row7,
    fixedFaceDegree_row8, fixedFaceDegree_row9,
    fixedFaceDegree_row10, fixedFaceDegree_row11,
    fixedFaceDegree_row12, fixedFaceDegree_row13,
    fixedFaceDegree_row14, fixedFaceDegree_row15,
    fixedFaceDegree_row16, fixedFaceDegree_row17,
    fixedFaceDegree_row18, fixedFaceDegree_row19,
    fixedFaceDegree_row20, fixedFaceDegree_row21,
    fixedFaceDegree_row22, fixedFaceDegree_row23,
    Bool.and_self]

theorem ownFaceScalar_degree_one
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    HasQuaternionBlockDegree (exactFixedFaceExposedBlock face) 1
      (correctedSlabPlaquettePolynomial 1 face).scalar := by
  have hentry := List.all_eq_true.mp fixedFaceScalarDegree_check face hface
  unfold fixedFaceScalarDegreeRowCheck at hentry
  unfold polynomialBlockDegreeCheck at hentry
  rw [Bool.and_eq_true] at hentry
  intro term hterm
  exact of_decide_eq_true (List.all_eq_true.mp hentry.1 term hterm)

theorem otherFaceScalar_degree_zero
    {face other : Z4Plaq}
    (hface : face ∈ exactCorrectedSlabFixedFaces)
    (hother : other ∈ exactCorrectedSlabFixedFaces)
    (hne : other ≠ face) :
    HasQuaternionBlockDegree (exactFixedFaceExposedBlock face) 0
      (correctedSlabPlaquettePolynomial 1 other).scalar := by
  have hentry := List.all_eq_true.mp fixedFaceScalarDegree_check face hface
  unfold fixedFaceScalarDegreeRowCheck at hentry
  rw [Bool.and_eq_true] at hentry
  have hotherEntry := List.all_eq_true.mp hentry.2 other hother
  simp [hne] at hotherEntry
  unfold polynomialBlockDegreeCheck at hotherEntry
  intro term hterm
  exact of_decide_eq_true (List.all_eq_true.mp hotherEntry term hterm)

private theorem ownFaceScalar_odd
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    HasQuaternionBlockParity (exactFixedFaceExposedBlock face) 1
      (correctedSlabPlaquettePolynomial 1 face).scalar := by
  intro term hterm
  rw [ownFaceScalar_degree_one hface term hterm]

private theorem otherFaceScalar_even
    {face other : Z4Plaq}
    (hface : face ∈ exactCorrectedSlabFixedFaces)
    (hother : other ∈ exactCorrectedSlabFixedFaces)
    (hne : other ≠ face) :
    HasQuaternionBlockParity (exactFixedFaceExposedBlock face) 0
      (correctedSlabPlaquettePolynomial 1 other).scalar := by
  intro term hterm
  rw [otherFaceScalar_degree_zero hface hother hne term hterm]

private theorem fixedFaces_nodup : exactCorrectedSlabFixedFaces.Nodup := by
  decide

private theorem interiorInsertion_blockParity
    (boundary : EdgeLabelling) {selected : Z4Plaq}
    (hselected : selected ∈ exactCorrectedSlabFixedFaces) :
    HasQuaternionBlockParity (exactFixedFaceExposedBlock selected)
      (boundary ((boundaryCompleteSlabPlaquettes 1).idxOf selected) % 2)
      (exactCorrectedSlabInteriorInsertion boundary) := by
  unfold exactCorrectedSlabInteriorInsertion
  have evenFold : ∀ (faces : List Z4Plaq),
      selected ∉ faces →
      (∀ other, other ∈ faces →
        other ∈ exactCorrectedSlabFixedFaces) →
      HasQuaternionBlockParity (exactFixedFaceExposedBlock selected) 0
        (faces.foldr
          (fun face total =>
            polyMul (correctedSlabPlaquetteSpinFactor 1 boundary face) total)
          polyOne) := by
    intro faces hnotmem hfaces
    induction faces with
    | nil => exact blockParity_one _
    | cons head tail induction =>
        simp only [List.foldr]
        have hheadNe : head ≠ selected := by
          intro heq
          apply hnotmem
          simp [heq]
        have htailNot : selected ∉ tail := by
          intro hmem
          exact hnotmem (List.mem_cons_of_mem head hmem)
        exact blockParity_mul
          (characterPolynomial_blockParity_of_even
            (otherFaceScalar_even hselected
              (hfaces head List.mem_cons_self) hheadNe)
            (boundary ((boundaryCompleteSlabPlaquettes 1).idxOf head)))
          (induction htailNot
            (fun other hother =>
              hfaces other (List.mem_cons_of_mem head hother)))
  have go : ∀ (faces : List Z4Plaq),
      faces.Nodup →
      selected ∈ faces →
      (∀ other, other ∈ faces → other ∈ exactCorrectedSlabFixedFaces) →
      HasQuaternionBlockParity (exactFixedFaceExposedBlock selected)
        (boundary ((boundaryCompleteSlabPlaquettes 1).idxOf selected) % 2)
        (faces.foldr
          (fun face total =>
            polyMul (correctedSlabPlaquetteSpinFactor 1 boundary face) total)
          polyOne) := by
    intro faces hnodup hmem hfaces
    induction faces with
    | nil => simp at hmem
    | cons head tail induction =>
        simp only [List.foldr]
        have hparts := List.nodup_cons.mp hnodup
        rcases List.mem_cons.mp hmem with heq | htail
        · subst head
          apply blockParity_relabel
            (first :=
              boundary
                ((boundaryCompleteSlabPlaquettes 1).idxOf selected) % 2 + 0)
            (by omega)
          apply blockParity_mul
          · exact characterPolynomial_blockParity_of_odd
              (ownFaceScalar_odd hselected)
              (boundary
                ((boundaryCompleteSlabPlaquettes 1).idxOf selected))
          · exact evenFold tail hparts.1
              (fun other hother =>
                hfaces other (List.mem_cons_of_mem selected hother))
        · apply blockParity_relabel
            (first :=
              0 + boundary
                ((boundaryCompleteSlabPlaquettes 1).idxOf selected) % 2)
            (by omega)
          apply blockParity_mul
          · exact characterPolynomial_blockParity_of_even
              (otherFaceScalar_even hselected
                (hfaces head List.mem_cons_self)
                (fun h => hparts.1 (by simpa [h] using htail)))
              (boundary ((boundaryCompleteSlabPlaquettes 1).idxOf head))
          · exact induction hparts.2 htail
              (fun other hother =>
                hfaces other (List.mem_cons_of_mem head hother))
  exact go exactCorrectedSlabFixedFaces fixedFaces_nodup hselected
    (fun _ h => h)

private theorem headDegree_reindex_selected
    (monomial : List Nat) (selected : Nat) (hselected : selected < 116) :
    headQuaternionDegree
        (reindexQuaternionExponents
          (headSwapBlockInvolution 116 selected hselected) monomial) =
      quaternionBlockDegree monomial selected := by
  unfold headQuaternionDegree quaternionBlockDegree
  rw [exponentAt_reindexQuaternionExponents,
    exponentAt_reindexQuaternionExponents,
    exponentAt_reindexQuaternionExponents,
    exponentAt_reindexQuaternionExponents]
  all_goals try omega
  simp [headSwapBlockInvolution_map_zero]

/-- Odd fixed-face labels are already killed unconditionally by the exact
selected-link partial Haar integral. -/
theorem selectedPartial_orthogonality_of_odd_label
    (boundary : EdgeLabelling) (face : Z4Plaq)
    (hface : face ∈ exactCorrectedSlabFixedFaces)
    (hodd :
      boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face) % 2 = 1) :
    quaternionHaar 115
        (exactFixedFaceSelectedPartialInsertion boundary face hface) ≈ 0 := by
  apply quaternionHaar_partialHaarHead_eq_zero_of_odd
  intro term hterm
  unfold reindexQuaternionPolynomial at hterm
  obtain ⟨source, hsource, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq,
    headDegree_reindex_selected source.1
      (exactFixedFaceExposedBlock face)
      (exactFixedFaceExposedBlock_lt hface)]
  have hparity := interiorInsertion_blockParity boundary hface source hsource
  rw [hparity]
  omega

/-- At cutoff one every non-vacuum interface label is the odd fundamental
label.  Hence the selected-link theorem already annihilates every non-vacuum
vacuum--vacuum summand, without waiting for the even-spin harmonic bridge. -/
theorem exactVacuumNontrivialHaarTermsVanish_cutoff_one :
    ExactVacuumNontrivialHaarTermsVanish 1 := by
  intro boundary hboundary hnonvacuum
  obtain ⟨face, hface, hlabel, hspec⟩ :=
    nonvacuumBoundary_has_exposed_nontrivial_face
      hboundary hnonvacuum
  have hsound := boundedEdgeLabellings_sound 1
    (centralFixedFaceIds 0) boundary hboundary
  obtain ⟨id, hid, hfaceImage⟩ := List.mem_map.mp hface
  have hidPhysical : id ∈ slabPhysicalFaceEdges 1 :=
    (mem_centralFixedFaceIds.mp hid).1
  have hidx :
      (boundaryCompleteSlabPlaquettes 1).idxOf face = id := by
    have hphysicalIdx := idxOf_slabPlaquetteAt_one hidPhysical
    rw [hfaceImage] at hphysicalIdx
    exact hphysicalIdx
  rw [hidx] at hlabel
  have hlt : boundary id < 2 := hsound.1 id hid
  have hone : boundary id = 1 := by omega
  have hodd :
      boundary
          ((boundaryCompleteSlabPlaquettes 1).idxOf face) % 2 = 1 := by
    rw [hidx, hone]
  exact Q'.eqv_trans _ _ _
    (exactCorrectedSlabVacuumBoundaryHaarCoefficient_eq_interior boundary)
    (Q'.eqv_trans _ _ _
      (exactInteriorHaar_eq_selectedPartial boundary face hface)
      (selectedPartial_orthogonality_of_odd_label
        boundary face hface hodd))

/-- Selected-link partial orthogonality inhabits the exact fixed-face
conditional Haar statement consumed by vacuum positivity. -/
theorem fixedFaceConditionalHaarOrthogonality_of_selectedPartial
    (orthogonality : ExactFixedFaceSelectedPartialOrthogonality) :
    ExactFixedFaceConditionalHaarOrthogonality := by
  intro boundary face hface hnontrivial
  rw [correctedSlabLinks_extent_one_length]
  exact Q'.eqv_trans _ _ _
    (exactInteriorHaar_eq_selectedPartial boundary face hface)
    (orthogonality boundary face hface hnontrivial)

end YMGap.Continuum.BF4ExactSlabVacuumSelectedHaar

#print axioms YMGap.Continuum.BF4ExactSlabVacuumSelectedHaar.exactFixedFaceExposedBlock_lt
#print axioms YMGap.Continuum.BF4ExactSlabVacuumSelectedHaar.exactInteriorHaar_eq_selectedPartial
#print axioms YMGap.Continuum.BF4ExactSlabVacuumSelectedHaar.fixedFaceConditionalHaarOrthogonality_of_selectedPartial
