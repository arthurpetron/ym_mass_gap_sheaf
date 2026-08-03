/-
# Canonical four-word form of the exact selected BF4 face

The selected physical plaquette initially occupies four arbitrary blocks of
the 116-link slab carrier.  The exposed-block swap followed by the explicit
three-transposition tail permutation sends those blocks, in oriented word
order, to `0,1,2,3`.  This file proves that fact structurally on polynomial
quaternions.  In particular it never expands a 116-block character.
-/

import YMGap.Continuum.BF4ExactSlabSelectedFaceFold
import YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction

namespace YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSelectedFaceDegree
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Componentwise prefix equivalence -/

/-- Prefix equivalence of all four coordinates of two polynomial
quaternions. -/
structure QuaternionPrefixPolyQuaternionEqv
    (blocks : Nat) (left right : PolyQuaternion) : Prop where
  scalar : QuaternionPrefixPolynomialEqv blocks left.scalar right.scalar
  iPart : QuaternionPrefixPolynomialEqv blocks left.iPart right.iPart
  jPart : QuaternionPrefixPolynomialEqv blocks left.jPart right.jPart
  kPart : QuaternionPrefixPolynomialEqv blocks left.kPart right.kPart

namespace QuaternionPrefixPolyQuaternionEqv

theorem refl (blocks : Nat) (quaternion : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks quaternion quaternion :=
  ⟨QuaternionPrefixPolynomialEqv.refl blocks quaternion.scalar,
    QuaternionPrefixPolynomialEqv.refl blocks quaternion.iPart,
    QuaternionPrefixPolynomialEqv.refl blocks quaternion.jPart,
    QuaternionPrefixPolynomialEqv.refl blocks quaternion.kPart⟩

theorem trans {blocks : Nat} {left middle right : PolyQuaternion}
    (hleft : QuaternionPrefixPolyQuaternionEqv blocks left middle)
    (hright : QuaternionPrefixPolyQuaternionEqv blocks middle right) :
    QuaternionPrefixPolyQuaternionEqv blocks left right :=
  ⟨hleft.scalar.trans hright.scalar,
    hleft.iPart.trans hright.iPart,
    hleft.jPart.trans hright.jPart,
    hleft.kPart.trans hright.kPart⟩

theorem conj {blocks : Nat} {left right : PolyQuaternion}
    (heqv : QuaternionPrefixPolyQuaternionEqv blocks left right) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (PolyQuaternion.conj left) (PolyQuaternion.conj right) :=
  ⟨heqv.scalar, heqv.iPart.neg, heqv.jPart.neg, heqv.kPart.neg⟩

theorem mul {blocks : Nat}
    {left left' right right' : PolyQuaternion}
    (hleft : QuaternionPrefixPolyQuaternionEqv blocks left left')
    (hright : QuaternionPrefixPolyQuaternionEqv blocks right right') :
    QuaternionPrefixPolyQuaternionEqv blocks
      (PolyQuaternion.mul left right)
      (PolyQuaternion.mul left' right') := by
  constructor
  · exact (hleft.scalar.mul hright.scalar).append
      (((hleft.iPart.mul hright.iPart).append
        ((hleft.jPart.mul hright.jPart).append
          (hleft.kPart.mul hright.kPart))).neg)
  · exact (hleft.scalar.mul hright.iPart).append
      ((hleft.iPart.mul hright.scalar).append
        ((hleft.jPart.mul hright.kPart).append
          ((hleft.kPart.mul hright.jPart).neg)))
  · exact (hleft.scalar.mul hright.jPart).append
      ((hleft.jPart.mul hright.scalar).append
        ((hleft.kPart.mul hright.iPart).append
          ((hleft.iPart.mul hright.kPart).neg)))
  · exact (hleft.scalar.mul hright.kPart).append
      ((hleft.kPart.mul hright.scalar).append
        ((hleft.iPart.mul hright.jPart).append
          ((hleft.jPart.mul hright.iPart).neg)))

end QuaternionPrefixPolyQuaternionEqv

/-! ## 2. Structural transport of coordinate quaternions -/

/-- Reindex all four coordinate polynomials of a polynomial quaternion. -/
def reindexPolyQuaternion
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (quaternion : PolyQuaternion) : PolyQuaternion where
  scalar := reindexQuaternionPolynomial permutation quaternion.scalar
  iPart := reindexQuaternionPolynomial permutation quaternion.iPart
  jPart := reindexQuaternionPolynomial permutation quaternion.jPart
  kPart := reindexQuaternionPolynomial permutation quaternion.kPart

theorem reindexPolyQuaternion_conj
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (quaternion : PolyQuaternion) :
    reindexPolyQuaternion permutation (PolyQuaternion.conj quaternion) =
      PolyQuaternion.conj (reindexPolyQuaternion permutation quaternion) := by
  cases quaternion
  simp [reindexPolyQuaternion, PolyQuaternion.conj,
    reindexQuaternionPolynomial_neg]

theorem reindexPolyQuaternion_mul
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (left right : PolyQuaternion) :
    reindexPolyQuaternion permutation (PolyQuaternion.mul left right) =
      PolyQuaternion.mul
        (reindexPolyQuaternion permutation left)
        (reindexPolyQuaternion permutation right) := by
  cases left
  cases right
  simp [reindexPolyQuaternion, PolyQuaternion.mul,
    reindexQuaternionPolynomial_add,
    reindexQuaternionPolynomial_mul,
    reindexQuaternionPolynomial_neg]

/-- One coordinate variable transported through two block involutions. -/
theorem reindexTwice_polyVar_prefix
    {blocks target source component : Nat}
    (first second : QuaternionBlockInvolution blocks)
    (htarget : target < blocks) (hcomponent : component < 4)
    (hmap : first.map (second.map target) = source) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial second
        (reindexQuaternionPolynomial first
          (polyVar (4 * source + component))))
      (polyVar (4 * target + component)) := by
  change QuaternionPrefixPolynomialEqv blocks
    [(_, 1)] [(YMGap.Continuum.RingNormaliser.varMono
      (4 * target + component), 1)]
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro coordinate hcoordinate
      rw [exponentAt_reindexQuaternionExponents second _ hcoordinate]
      have hblock : coordinate / 4 < blocks := by omega
      have hsecondBlock : second.map (coordinate / 4) < blocks :=
        second.map_lt (coordinate / 4) hblock
      rw [exponentAt_reindexQuaternionExponents first _ (by omega),
        exponentAt_varMono, exponentAt_varMono]
      have hcomponentCoordinate : coordinate % 4 < 4 :=
        Nat.mod_lt coordinate (by omega)
      have hsecondDiv :
          (4 * second.map (coordinate / 4) + coordinate % 4) / 4 =
            second.map (coordinate / 4) := by omega
      have hsecondMod :
          (4 * second.map (coordinate / 4) + coordinate % 4) % 4 =
            coordinate % 4 := by omega
      rw [hsecondDiv, hsecondMod]
      by_cases heq :
          4 * first.map (second.map (coordinate / 4)) + coordinate % 4 =
            4 * source + component
      · rw [if_pos heq]
        have hmapped :
            first.map (second.map (coordinate / 4)) = source := by omega
        have hfirstInject := first.injective_on
          hsecondBlock
          (second.map_lt target htarget)
          (left := second.map (coordinate / 4))
          (right := second.map target)
        have hsecondMapped : second.map (coordinate / 4) = second.map target :=
          hfirstInject (hmapped.trans hmap.symm)
        have hsourceBlock : coordinate / 4 = target :=
          second.injective_on hblock htarget hsecondMapped
        have hcoordinateDecomp :
            4 * (coordinate / 4) + coordinate % 4 = coordinate := by omega
        have hcomponentEq : coordinate % 4 = component := by omega
        rw [if_pos]
        omega
      · rw [if_neg heq]
        rw [if_neg]
        intro hcoordinateEq
        subst coordinate
        have hdiv : (4 * target + component) / 4 = target := by omega
        have hmod : (4 * target + component) % 4 = component := by omega
        rw [hdiv, hmod, hmap] at heq
        exact heq rfl
  · exact .nil

/-- The four coordinate variables of one quaternion transport together. -/
theorem reindexTwice_coordinateVariable_prefix
    {blocks target source : Nat}
    (first second : QuaternionBlockInvolution blocks)
    (htarget : target < blocks)
    (hmap : first.map (second.map target) = source) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (reindexPolyQuaternion second
      (reindexPolyQuaternion first
          (PolyQuaternion.coordinateVariable source)))
      (PolyQuaternion.coordinateVariable target) := by
  exact ⟨
    by simpa [reindexPolyQuaternion, PolyQuaternion.coordinateVariable] using
      (reindexTwice_polyVar_prefix
        (target := target) (source := source) (component := 0)
        first second htarget (by omega) hmap),
    by simpa [reindexPolyQuaternion, PolyQuaternion.coordinateVariable] using
      (reindexTwice_polyVar_prefix
        (target := target) (source := source) (component := 1)
        first second htarget (by omega) hmap),
    by simpa [reindexPolyQuaternion, PolyQuaternion.coordinateVariable] using
      (reindexTwice_polyVar_prefix
        (target := target) (source := source) (component := 2)
        first second htarget (by omega) hmap),
    by simpa [reindexPolyQuaternion, PolyQuaternion.coordinateVariable] using
      (reindexTwice_polyVar_prefix
        (target := target) (source := source) (component := 3)
        first second htarget (by omega) hmap)⟩

/-- Orientation reversal is preserved by the two coordinate reindexings. -/
theorem reindexTwice_orientedCoordinateQuaternion_prefix
    {blocks target source : Nat}
    (first second : QuaternionBlockInvolution blocks)
    (htarget : target < blocks)
    (hmap : first.map (second.map target) = source)
    (reverse : Bool) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (reindexPolyQuaternion second
        (reindexPolyQuaternion first
          (orientedCoordinateQuaternion source reverse)))
      (orientedCoordinateQuaternion target reverse) := by
  cases reverse with
  | false =>
      exact reindexTwice_coordinateVariable_prefix
        first second htarget hmap
  | true =>
      rw [show orientedCoordinateQuaternion source true =
          PolyQuaternion.conj (PolyQuaternion.coordinateVariable source) by
            rfl,
        show orientedCoordinateQuaternion target true =
          PolyQuaternion.conj (PolyQuaternion.coordinateVariable target) by
            rfl,
        reindexPolyQuaternion_conj,
        reindexPolyQuaternion_conj]
      exact (reindexTwice_coordinateVariable_prefix
        first second htarget hmap).conj

/-! ## 3. The literal physical selected word -/

/-- The head transposition used before the tail permutation. -/
def exactFixedFaceHeadBlockInvolution
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces) :
    QuaternionBlockInvolution 116 :=
  headSwapBlockInvolution 116
    (exactFixedFaceExposedBlock face)
    (exactFixedFaceExposedBlock_lt hface)

/-- Apply the exposed-head swap and then the three tail transpositions. -/
def exactFixedFaceDoubleReindex
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (polynomial : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial
    (exactFixedFaceTailBlockInvolution face hface)
    (reindexQuaternionPolynomial
      (exactFixedFaceHeadBlockInvolution face hface) polynomial)

/-- Componentwise version of `exactFixedFaceDoubleReindex`. -/
def exactFixedFaceDoubleReindexQuaternion
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces)
    (quaternion : PolyQuaternion) : PolyQuaternion :=
  reindexPolyQuaternion
    (exactFixedFaceTailBlockInvolution face hface)
    (reindexPolyQuaternion
      (exactFixedFaceHeadBlockInvolution face hface) quaternion)

private theorem fixedFace_mem_complete
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    face ∈ boundaryCompleteSlabPlaquettes 1 := by
  have hpartition : face ∈ exactCorrectedSlabPartitionedFaces := by
    unfold exactCorrectedSlabPartitionedFaces
    simp [hface]
  exact (List.Perm.mem_iff
    exactCorrectedSlabPartitionedFaces_perm).mp hpartition

private theorem orientedCorrectedLink_eq_coordinate
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces)
    {entry : OrientedBF4Link}
    (hentry : entry ∈ orientedPlaquetteBoundary face) :
    orientedCorrectedSlabLinkPolynomial 1 entry =
      orientedCoordinateQuaternion
        ((boundaryCompleteSlabLinks 1).idxOf entry.link)
        entry.reverse := by
  have hlink := orientedPlaquetteBoundary_link_mem_slab
    (fixedFace_mem_complete hface) hentry
  unfold orientedCorrectedSlabLinkPolynomial
  rw [correctedSlabLinkPolynomial_of_mem hlink]
  cases entry.reverse <;> rfl

/-- The physical selected plaquette is the left fold of its four literal
coordinate quaternions, with no fallback link variables. -/
theorem correctedSlabPlaquettePolynomial_eq_coordinateFold
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    correctedSlabPlaquettePolynomial 1 face =
      (orientedPlaquetteBoundary face).foldl
        (fun total entry => PolyQuaternion.mul total
          (orientedCoordinateQuaternion
            ((boundaryCompleteSlabLinks 1).idxOf entry.link)
            entry.reverse))
        PolyQuaternion.one := by
  unfold correctedSlabPlaquettePolynomial
  have go : ∀ (entries : List OrientedBF4Link)
      (initial : PolyQuaternion),
      (∀ entry, entry ∈ entries →
        entry ∈ orientedPlaquetteBoundary face) →
      entries.foldl
          (fun total entry => PolyQuaternion.mul total
            (orientedCorrectedSlabLinkPolynomial 1 entry)) initial =
        entries.foldl
          (fun total entry => PolyQuaternion.mul total
            (orientedCoordinateQuaternion
              ((boundaryCompleteSlabLinks 1).idxOf entry.link)
              entry.reverse)) initial := by
    intro entries
    induction entries with
    | nil => intro initial _; rfl
    | cons entry rest induction =>
        intro initial hentries
        simp only [List.foldl_cons]
        rw [orientedCorrectedLink_eq_coordinate hface
          (hentries entry List.mem_cons_self)]
        exact induction _ (fun item hitem =>
          hentries item (List.mem_cons_of_mem entry hitem))
  exact go (orientedPlaquetteBoundary face) PolyQuaternion.one
    (fun _ hentry => hentry)

/-- Compact source-block/orientation descriptor of the physical word. -/
def exactFixedFaceWordDescriptor (face : Z4Plaq) : List (Nat × Bool) :=
  (orientedPlaquetteBoundary face).map (fun entry =>
    ((boundaryCompleteSlabLinks 1).idxOf entry.link, entry.reverse))

private def exactFixedFaceWordDescriptorCheck : Bool :=
  exactCorrectedSlabFixedFaces.all (fun face =>
    decide (exactFixedFaceWordDescriptor face =
      [(exactFixedFaceExposedBlock face, false),
        (exactFixedFaceTailSource face 0, false),
        (exactFixedFaceTailSource face 1, true),
        (exactFixedFaceTailSource face 2, true)]))

private theorem exactFixedFaceWordDescriptor_check :
    exactFixedFaceWordDescriptorCheck = true := by
  decide

/-- The exact physical selected word has orientation pattern
`false,false,true,true`, in the four sources named by the combined map. -/
theorem exactFixedFaceWordDescriptor_eq
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    exactFixedFaceWordDescriptor face =
      [(exactFixedFaceExposedBlock face, false),
        (exactFixedFaceTailSource face 0, false),
        (exactFixedFaceTailSource face 1, true),
        (exactFixedFaceTailSource face 2, true)] := by
  have hrow := List.all_eq_true.mp
    exactFixedFaceWordDescriptor_check face hface
  exact of_decide_eq_true hrow

private theorem coordinateFold_eq_descriptorFold
    (entries : List OrientedBF4Link) (initial : PolyQuaternion) :
    entries.foldl
        (fun total entry => PolyQuaternion.mul total
          (orientedCoordinateQuaternion
            ((boundaryCompleteSlabLinks 1).idxOf entry.link)
            entry.reverse)) initial =
      (entries.map (fun entry =>
        ((boundaryCompleteSlabLinks 1).idxOf entry.link,
          entry.reverse))).foldl
        (fun total descriptor => PolyQuaternion.mul total
          (orientedCoordinateQuaternion descriptor.1 descriptor.2))
        initial := by
  induction entries generalizing initial with
  | nil => rfl
  | cons entry rest induction =>
      simp only [List.foldl_cons, List.map_cons]
      exact induction _

/-- Literal four-factor coordinate form of the selected plaquette. -/
theorem correctedSlabPlaquettePolynomial_eq_physicalFourFold
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    correctedSlabPlaquettePolynomial 1 face =
      PolyQuaternion.mul
        (PolyQuaternion.mul
          (PolyQuaternion.mul
            (PolyQuaternion.mul PolyQuaternion.one
              (orientedCoordinateQuaternion
                (exactFixedFaceExposedBlock face) false))
            (orientedCoordinateQuaternion
              (exactFixedFaceTailSource face 0) false))
          (orientedCoordinateQuaternion
            (exactFixedFaceTailSource face 1) true))
        (orientedCoordinateQuaternion
          (exactFixedFaceTailSource face 2) true) := by
  rw [correctedSlabPlaquettePolynomial_eq_coordinateFold hface,
    coordinateFold_eq_descriptorFold,
    show (orientedPlaquetteBoundary face).map (fun entry =>
        ((boundaryCompleteSlabLinks 1).idxOf entry.link, entry.reverse)) =
      exactFixedFaceWordDescriptor face by rfl,
    exactFixedFaceWordDescriptor_eq hface]
  rfl

/-! ## 4. Prefix removal of the fold's leading unit -/

private theorem polyOne_mul_prefix
    {blocks : Nat} : ∀ polynomial : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (polyMul polyOne polynomial) polynomial
  | [] => .nil
  | term :: rest => by
      unfold polyMul List.flatMap
      simp only [polyOne, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil]
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact Q'.one_mul_eqv term.2
        · intro coordinate _
          simp [RingNormaliser.monoMul, exponentAt]
      · simpa [polyMul, polyOne] using
          (polyOne_mul_prefix (blocks := blocks) rest)

private theorem polyQuaternion_one_mul_prefix
    {blocks : Nat} (quaternion : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (PolyQuaternion.mul PolyQuaternion.one quaternion) quaternion := by
  constructor
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using
      (polyOne_mul_prefix (blocks := blocks) quaternion.scalar)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using
      (polyOne_mul_prefix (blocks := blocks) quaternion.iPart)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using
      (polyOne_mul_prefix (blocks := blocks) quaternion.jPart)
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using
      (polyOne_mul_prefix (blocks := blocks) quaternion.kPart)

private theorem reindexTwice_polyOne_prefix
    {blocks : Nat} (first second : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial second
        (reindexQuaternionPolynomial first polyOne)) polyOne := by
  change QuaternionPrefixPolynomialEqv blocks
    [(_, 1)] [([], 1)]
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro coordinate hcoordinate
      rw [exponentAt_reindexQuaternionExponents second _ hcoordinate]
      have hblock : coordinate / 4 < blocks := by omega
      have hmapped : second.map (coordinate / 4) < blocks :=
        second.map_lt _ hblock
      rw [exponentAt_reindexQuaternionExponents first _ (by omega)]
      simp [exponentAt]
  · exact .nil

private theorem reindexTwice_polyQuaternionOne_prefix
    {blocks : Nat} (first second : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (reindexPolyQuaternion second
        (reindexPolyQuaternion first PolyQuaternion.one))
      PolyQuaternion.one := by
  constructor
  · simpa [reindexPolyQuaternion, PolyQuaternion.one] using
      reindexTwice_polyOne_prefix first second
  all_goals
    change QuaternionPrefixPolynomialEqv blocks [] []
    exact .nil

/-! ## 5. Canonical scalar and character bridges -/

namespace QuaternionPrefixPolynomialEqv

/-- Applying the same block involution to both sides preserves prefix
equivalence. -/
theorem reindex
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv blocks left right) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial permutation left)
      (reindexQuaternionPolynomial permutation right) := by
  induction heqv with
  | nil => exact .nil
  | cons hterm hrest induction =>
      unfold reindexQuaternionPolynomial List.map
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact hterm.coefficient
        · intro coordinate hcoordinate
          rw [exponentAt_reindexQuaternionExponents permutation _ hcoordinate,
            exponentAt_reindexQuaternionExponents permutation _ hcoordinate]
          have hblock : coordinate / 4 < blocks := by omega
          have hmapped : permutation.map (coordinate / 4) < blocks :=
            permutation.map_lt _ hblock
          exact hterm.exponent
            (4 * permutation.map (coordinate / 4) + coordinate % 4)
            (by omega)
      · exact induction

end QuaternionPrefixPolynomialEqv

/-- **Structural selected-face canonicalization.**  The scalar of the
doubly reindexed physical plaquette is prefix-equivalent on all 116 blocks
to the scalar of the canonical exposed four-word. -/
theorem exactFixedFaceDoublyReindexedSelectedQuaternion_prefix
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    QuaternionPrefixPolyQuaternionEqv 116
      (exactFixedFaceDoubleReindexQuaternion face hface
        (correctedSlabPlaquettePolynomial 1 face))
      (exposedFourWord false false true true) := by
  let head := exactFixedFaceHeadBlockInvolution face hface
  let tail := exactFixedFaceTailBlockInvolution face hface
  have himages := exactFixedFaceCombinedBlockMap_first_four hface
  have hmap0 : head.map (tail.map 0) = exactFixedFaceExposedBlock face := by
    simpa [head, tail, exactFixedFaceHeadBlockInvolution,
      exactFixedFaceTailBlockInvolution,
      exactFixedFaceCombinedBlockMap, headSwapBlockInvolution] using
      himages.1
  have hmap1 :
      head.map (tail.map 1) = exactFixedFaceTailSource face 0 := by
    simpa [head, tail, exactFixedFaceHeadBlockInvolution,
      exactFixedFaceTailBlockInvolution,
      exactFixedFaceCombinedBlockMap, headSwapBlockInvolution] using
      himages.2.1
  have hmap2 :
      head.map (tail.map 2) = exactFixedFaceTailSource face 1 := by
    simpa [head, tail, exactFixedFaceHeadBlockInvolution,
      exactFixedFaceTailBlockInvolution,
      exactFixedFaceCombinedBlockMap, headSwapBlockInvolution] using
      himages.2.2.1
  have hmap3 :
      head.map (tail.map 3) = exactFixedFaceTailSource face 2 := by
    simpa [head, tail, exactFixedFaceHeadBlockInvolution,
      exactFixedFaceTailBlockInvolution,
      exactFixedFaceCombinedBlockMap, headSwapBlockInvolution] using
      himages.2.2.2
  have hone := reindexTwice_polyQuaternionOne_prefix head tail
  have h0 := reindexTwice_orientedCoordinateQuaternion_prefix
    head tail (target := 0) (source := exactFixedFaceExposedBlock face)
      (by omega) hmap0 false
  have h1 := reindexTwice_orientedCoordinateQuaternion_prefix
    head tail (target := 1) (source := exactFixedFaceTailSource face 0)
      (by omega) hmap1 false
  have h2 := reindexTwice_orientedCoordinateQuaternion_prefix
    head tail (target := 2) (source := exactFixedFaceTailSource face 1)
      (by omega) hmap2 true
  have h3 := reindexTwice_orientedCoordinateQuaternion_prefix
    head tail (target := 3) (source := exactFixedFaceTailSource face 2)
      (by omega) hmap3 true
  have hfold := (((hone.mul h0).mul h1).mul h2).mul h3
  have hdrop := (((polyQuaternion_one_mul_prefix
      (blocks := 116) (orientedCoordinateQuaternion 0 false)).mul
      (QuaternionPrefixPolyQuaternionEqv.refl 116
        (orientedCoordinateQuaternion 1 false))).mul
      (QuaternionPrefixPolyQuaternionEqv.refl 116
        (orientedCoordinateQuaternion 2 true))).mul
      (QuaternionPrefixPolyQuaternionEqv.refl 116
        (orientedCoordinateQuaternion 3 true))
  rw [correctedSlabPlaquettePolynomial_eq_physicalFourFold hface]
  unfold exactFixedFaceDoubleReindexQuaternion
  simp only [reindexPolyQuaternion_mul]
  exact hfold.trans (by
    simpa [exposedFourWord] using hdrop)

/-- Scalar projection of the structural four-word theorem requested by the
selected-face Haar argument. -/
theorem exactFixedFaceDoublyReindexedSelectedScalar_prefix
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    QuaternionPrefixPolynomialEqv 116
      (exactFixedFaceDoubleReindex face hface
        (correctedSlabPlaquettePolynomial 1 face).scalar)
      (exposedFourWord false false true true).scalar := by
  simpa [exactFixedFaceDoubleReindex,
    exactFixedFaceDoubleReindexQuaternion, reindexPolyQuaternion] using
    (exactFixedFaceDoublyReindexedSelectedQuaternion_prefix hface).scalar

/-- Two successive reindexings of a character are the character of the
twice-reindexed scalar, modulo harmless zero padding. -/
theorem reindexTwice_character_prefix
    {blocks : Nat} (first second : QuaternionBlockInvolution blocks)
    (scalar : RatPoly) (spin : Nat) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial second
        (reindexQuaternionPolynomial first
          (characterPolynomial scalar spin)))
      (characterPolynomial
        (reindexQuaternionPolynomial second
          (reindexQuaternionPolynomial first scalar)) spin) := by
  exact QuaternionPrefixPolynomialEqv.trans
    (YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.QuaternionPrefixPolynomialEqv.reindex second
        (reindexQuaternionPolynomial_character_prefix first scalar spin))
    (reindexQuaternionPolynomial_character_prefix second
      (reindexQuaternionPolynomial first scalar) spin)

/-- The all-spin physical selected-face factor becomes the canonical
`false,false,true,true` character after the two physical block changes. -/
theorem exactFixedFaceDoublyReindexedSelectedCharacter_prefix
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq}
    (hface : face ∈ exactCorrectedSlabFixedFaces) :
    QuaternionPrefixPolynomialEqv 116
      (exactFixedFaceDoubleReindex face hface
        (correctedSlabPlaquetteSpinFactor 1 boundary face))
      (characterPolynomial
        (exposedFourWord false false true true).scalar
        (boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face))) := by
  unfold correctedSlabPlaquetteSpinFactor
  exact QuaternionPrefixPolynomialEqv.trans
    (reindexTwice_character_prefix
      (exactFixedFaceHeadBlockInvolution face hface)
      (exactFixedFaceTailBlockInvolution face hface)
      (correctedSlabPlaquettePolynomial 1 face).scalar
      (boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face)))
    ((exactFixedFaceDoublyReindexedSelectedScalar_prefix hface).character _)

/-! ## 6. Even and odd Haar annihilation on the same canonical carrier -/

/-- The other twenty-three physical faces remain independent of the head
after both physical block changes. -/
theorem exactFixedFaceDoublyReindexedOther_headDegree_zero
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    HasQuaternionBlockDegree 0 0
      (exactFixedFaceDoubleReindex face hface
        (exactFixedFaceOtherInsertion boundary face)) := by
  have htailZero :
      (exactFixedFaceTailBlockInvolution face hface).map 0 = 0 := by
    simpa [exactFixedFaceTailBlockInvolution] using
      (exactFixedFaceTailBlockMap_first_four hface).1
  unfold exactFixedFaceDoubleReindex
  apply blockDegree_reindex
    (exactFixedFaceTailBlockInvolution face hface)
    (by omega)
    htailZero
  exact reindexedExactFixedFaceOtherInsertion_headDegree_zero
    boundary face hface

/-- Full doubly reindexed selected-times-residual product, before replacing
the selected character by its canonical four-word form. -/
def exactFixedFaceDoublyReindexedSelectedProduct
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces) :
    RatPoly :=
  exactFixedFaceDoubleReindex face hface
    (polyMul
      (correctedSlabPlaquetteSpinFactor 1 boundary face)
      (exactFixedFaceOtherInsertion boundary face))

/-- Canonical selected-character times the same doubly reindexed
twenty-three-face coefficient. -/
def exactFixedFaceCanonicalSelectedProduct
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (face : Z4Plaq) (hface : face ∈ exactCorrectedSlabFixedFaces) :
    RatPoly :=
  polyMul
    (characterPolynomial
      (exposedFourWord false false true true).scalar
      (boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face)))
    (exactFixedFaceDoubleReindex face hface
      (exactFixedFaceOtherInsertion boundary face))

/-- The structural scalar bridge, lifted through `characterPolynomial` and
then through multiplication by all twenty-three retained face factors. -/
theorem exactFixedFaceDoublyReindexedSelectedProduct_prefix
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    QuaternionPrefixPolynomialEqv 116
      (exactFixedFaceDoublyReindexedSelectedProduct boundary face hface)
      (exactFixedFaceCanonicalSelectedProduct boundary face hface) := by
  unfold exactFixedFaceDoublyReindexedSelectedProduct
    exactFixedFaceCanonicalSelectedProduct exactFixedFaceDoubleReindex
  rw [reindexQuaternionPolynomial_mul,
    reindexQuaternionPolynomial_mul]
  exact (exactFixedFaceDoublyReindexedSelectedCharacter_prefix
    boundary hface).mul
      (QuaternionPrefixPolynomialEqv.refl 116 _)

/-- Parity, rather than exact homogeneity, is the correct carrier for odd
ordinary characters. -/
def HasHeadQuaternionParity (parity : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    headQuaternionDegree term.1 % 2 = parity % 2

private theorem headDegree_monoMul
    (left right : List Nat) :
    headQuaternionDegree (monoMul left right) =
      headQuaternionDegree left + headQuaternionDegree right := by
  unfold headQuaternionDegree
  rw [exponentAt_monoMul, exponentAt_monoMul,
    exponentAt_monoMul, exponentAt_monoMul]
  omega

private theorem headParity_one :
    HasHeadQuaternionParity 0 polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp [headQuaternionDegree, exponentAt]

private theorem headParity_add
    {parity : Nat} {left right : RatPoly}
    (hleft : HasHeadQuaternionParity parity left)
    (hright : HasHeadQuaternionParity parity right) :
    HasHeadQuaternionParity parity (polyAdd left right) := by
  intro term hterm
  rcases List.mem_append.mp hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem headParity_smul
    {parity : Nat} {polynomial : RatPoly} (scale : Q')
    (hparity : HasHeadQuaternionParity parity polynomial) :
    HasHeadQuaternionParity parity (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq]
  exact hparity source hsource

private theorem headParity_mul
    {leftParity rightParity : Nat} {left right : RatPoly}
    (hleft : HasHeadQuaternionParity leftParity left)
    (hright : HasHeadQuaternionParity rightParity right) :
    HasHeadQuaternionParity (leftParity + rightParity)
      (polyMul left right) := by
  intro term hterm
  obtain ⟨source, hsource, htargetTerm⟩ :=
    List.mem_flatMap.mp hterm
  obtain ⟨target, htarget, htermEq⟩ :=
    List.mem_map.mp htargetTerm
  rw [← htermEq, headDegree_monoMul]
  calc
    (headQuaternionDegree source.1 + headQuaternionDegree target.1) % 2 =
        (headQuaternionDegree source.1 % 2 +
          headQuaternionDegree target.1 % 2) % 2 := Nat.add_mod _ _ _
    _ = (leftParity % 2 + rightParity % 2) % 2 := by
      rw [hleft source hsource, hright target htarget]
    _ = (leftParity + rightParity) % 2 := (Nat.add_mod _ _ _).symm

private theorem headParity_relabel
    {first second : Nat} {polynomial : RatPoly}
    (hsame : first % 2 = second % 2)
    (hparity : HasHeadQuaternionParity first polynomial) :
    HasHeadQuaternionParity second polynomial := by
  intro term hterm
  rw [← hsame]
  exact hparity term hterm

private theorem characterPolynomial_headParity
    {scalar : RatPoly}
    (hscalar : HasHeadQuaternionParity 1 scalar) : ∀ spin,
    HasHeadQuaternionParity (spin % 2)
      (characterPolynomial scalar spin)
  | 0 => headParity_one
  | 1 => headParity_smul 2 hscalar
  | spin + 2 => by
      apply headParity_add
      · exact headParity_relabel (by omega)
          (headParity_mul
            (headParity_smul 2 hscalar)
            (characterPolynomial_headParity hscalar (spin + 1)))
      · exact headParity_relabel (by omega)
          (headParity_smul (-1)
            (characterPolynomial_headParity hscalar spin))

private theorem headParity_of_blockDegree
    {degree : Nat} {polynomial : RatPoly}
    (hdegree : HasQuaternionBlockDegree 0 degree polynomial) :
    HasHeadQuaternionParity degree polynomial := by
  intro term hterm
  have h := hdegree term hterm
  unfold quaternionBlockDegree at h
  unfold headQuaternionDegree
  simpa using congrArg (fun value => value % 2) h

/-- Existing odd-head Fubini annihilation applied to the canonical physical
four-word with an arbitrary head-independent multiplier. -/
theorem exposedOddCharacter_mul_blockDegree_zero_quaternionHaar_zero
    (spin : Nat) (hodd : spin % 2 = 1)
    (multiplier : RatPoly)
    (hindependent : HasQuaternionBlockDegree 0 0 multiplier) :
    quaternionHaar 116
      (polyMul
        (characterPolynomial
          (exposedFourWord false false true true).scalar spin)
        multiplier) ≈ 0 := by
  let polynomial := polyMul
    (characterPolynomial
      (exposedFourWord false false true true).scalar spin)
    multiplier
  have hscalar : HasHeadQuaternionParity 1
      (exposedFourWord false false true true).scalar :=
    headParity_of_blockDegree
      (exposedFourWord_scalar_blockDegree
        false false true true 0 (by omega))
  have hparity : HasHeadQuaternionParity 1 polynomial := by
    apply headParity_relabel (first := spin % 2 + 0) (by omega)
    exact headParity_mul
      (characterPolynomial_headParity hscalar spin)
      (headParity_of_blockDegree hindependent)
  have hheadOdd : HeadQuaternionOdd polynomial := by
    intro term hterm
    exact hparity term hterm
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_partialHaarHead 115 polynomial))
    (quaternionHaar_partialHaarHead_eq_zero_of_odd
      115 polynomial hheadOdd)

/-- The existing positive-even solid-zonal/Haar theorem, now instantiated
on the exact doubly reindexed BF4 residual coefficient. -/
theorem exactFixedFaceCanonicalSelectedProduct_even_zero
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces)
    (k : Nat) (hpositive : 0 < k)
    (hspin :
      boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 2 * k) :
    quaternionHaar 116
      (exactFixedFaceCanonicalSelectedProduct boundary face hface) ≈ 0 := by
  unfold exactFixedFaceCanonicalSelectedProduct
  rw [hspin]
  exact exposedEvenCharacter_mul_blockDegree_zero_quaternionHaar_zero
    false false true true k hpositive _
    (exactFixedFaceDoublyReindexedOther_headDegree_zero boundary hface)

/-- The existing odd-head/Fubini theorem on the same exact canonical BF4
product. -/
theorem exactFixedFaceCanonicalSelectedProduct_odd_zero
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces)
    (hodd :
      boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face) % 2 = 1) :
    quaternionHaar 116
      (exactFixedFaceCanonicalSelectedProduct boundary face hface) ≈ 0 := by
  exact exposedOddCharacter_mul_blockDegree_zero_quaternionHaar_zero
    _ hodd _
    (exactFixedFaceDoublyReindexedOther_headDegree_zero boundary hface)

/-! ## 7. Supported Haar transport back to the physical polynomial -/

private theorem supported_polyZero (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyZero := by
  intro term hterm
  simp [polyZero] at hterm

private theorem supported_polyOne (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp

private theorem supported_polyVar
    {blocks coordinate : Nat} (hcoordinate : coordinate < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar coordinate) := by
  intro term hterm
  simp only [polyVar, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp [RingNormaliser.varMono]
  omega

private theorem supported_polyAdd
    {blocks : Nat} {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks blocks left)
    (hright : SupportedQuaternionBlocks blocks right) :
    SupportedQuaternionBlocks blocks (polyAdd left right) := by
  intro term hterm
  rcases List.mem_append.mp hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem supported_polyNeg
    {blocks : Nat} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polyNeg polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact hsupport source hsource

private theorem supported_polySmul
    {blocks : Nat} {scale : Q'} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact hsupport source hsource

private structure SupportedPolyQuaternion
    (blocks : Nat) (quaternion : PolyQuaternion) : Prop where
  scalar : SupportedQuaternionBlocks blocks quaternion.scalar
  iPart : SupportedQuaternionBlocks blocks quaternion.iPart
  jPart : SupportedQuaternionBlocks blocks quaternion.jPart
  kPart : SupportedQuaternionBlocks blocks quaternion.kPart

private theorem supportedPolyQuaternion_one (blocks : Nat) :
    SupportedPolyQuaternion blocks PolyQuaternion.one :=
  ⟨supported_polyOne blocks, supported_polyZero blocks,
    supported_polyZero blocks, supported_polyZero blocks⟩

private theorem supportedPolyQuaternion_coordinateVariable
    {blocks block : Nat} (hblock : block < blocks) :
    SupportedPolyQuaternion blocks
      (PolyQuaternion.coordinateVariable block) := by
  constructor <;> apply supported_polyVar <;> omega

private theorem supportedPolyQuaternion_conj
    {blocks : Nat} {quaternion : PolyQuaternion}
    (hsupport : SupportedPolyQuaternion blocks quaternion) :
    SupportedPolyQuaternion blocks (PolyQuaternion.conj quaternion) :=
  ⟨hsupport.scalar, supported_polyNeg hsupport.iPart,
    supported_polyNeg hsupport.jPart, supported_polyNeg hsupport.kPart⟩

private theorem supportedPolyQuaternion_mul
    {blocks : Nat} {left right : PolyQuaternion}
    (hleft : SupportedPolyQuaternion blocks left)
    (hright : SupportedPolyQuaternion blocks right) :
    SupportedPolyQuaternion blocks (PolyQuaternion.mul left right) := by
  constructor
  · exact supported_polyAdd
      (supported_polyMul hleft.scalar hright.scalar)
      (supported_polyNeg (supported_polyAdd
        (supported_polyMul hleft.iPart hright.iPart)
        (supported_polyAdd
          (supported_polyMul hleft.jPart hright.jPart)
          (supported_polyMul hleft.kPart hright.kPart))))
  · exact supported_polyAdd
      (supported_polyMul hleft.scalar hright.iPart)
      (supported_polyAdd
        (supported_polyMul hleft.iPart hright.scalar)
        (supported_polyAdd
          (supported_polyMul hleft.jPart hright.kPart)
          (supported_polyNeg
            (supported_polyMul hleft.kPart hright.jPart))))
  · exact supported_polyAdd
      (supported_polyMul hleft.scalar hright.jPart)
      (supported_polyAdd
        (supported_polyMul hleft.jPart hright.scalar)
        (supported_polyAdd
          (supported_polyMul hleft.kPart hright.iPart)
          (supported_polyNeg
            (supported_polyMul hleft.iPart hright.kPart))))
  · exact supported_polyAdd
      (supported_polyMul hleft.scalar hright.kPart)
      (supported_polyAdd
        (supported_polyMul hleft.kPart hright.scalar)
        (supported_polyAdd
          (supported_polyMul hleft.iPart hright.jPart)
          (supported_polyNeg
            (supported_polyMul hleft.jPart hright.iPart))))

private theorem orientedCoordinateQuaternion_supported
    {blocks block : Nat} (hblock : block < blocks) (reverse : Bool) :
    SupportedPolyQuaternion blocks
      (orientedCoordinateQuaternion block reverse) := by
  cases reverse with
  | false =>
      simpa [orientedCoordinateQuaternion] using
        (supportedPolyQuaternion_coordinateVariable hblock)
  | true =>
      simpa [orientedCoordinateQuaternion] using
        (supportedPolyQuaternion_conj
          (supportedPolyQuaternion_coordinateVariable hblock))

private theorem exposedFourWord_supported_116 :
    SupportedPolyQuaternion 116
      (exposedFourWord false false true true) :=
  supportedPolyQuaternion_mul
    (supportedPolyQuaternion_mul
      (supportedPolyQuaternion_mul
        (orientedCoordinateQuaternion_supported
          (blocks := 116) (block := 0) (by omega) false)
        (orientedCoordinateQuaternion_supported
          (blocks := 116) (block := 1) (by omega) false))
      (orientedCoordinateQuaternion_supported
        (blocks := 116) (block := 2) (by omega) true))
    (orientedCoordinateQuaternion_supported
      (blocks := 116) (block := 3) (by omega) true)

private theorem characterPolynomial_supported
    {blocks : Nat} {scalar : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks scalar) : ∀ spin,
    SupportedQuaternionBlocks blocks (characterPolynomial scalar spin)
  | 0 => supported_polyOne blocks
  | 1 => supported_polySmul hsupport
  | spin + 2 =>
      supported_polyAdd
        (supported_polyMul (supported_polySmul hsupport)
          (characterPolynomial_supported hsupport (spin + 1)))
        (supported_polySmul
          (characterPolynomial_supported hsupport spin))

/-- Any reindexed polynomial is syntactically supported on exactly the
declared padded carrier. -/
theorem reindexQuaternionPolynomial_supported
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks blocks
      (reindexQuaternionPolynomial permutation polynomial) := by
  intro term hterm
  unfold reindexQuaternionPolynomial at hterm
  obtain ⟨source, _, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq, reindexQuaternionExponents_length]
  exact Nat.le_refl _

private theorem doublyReindexed_supported
    {blocks : Nat} (first second : QuaternionBlockInvolution blocks)
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks blocks
      (reindexQuaternionPolynomial second
        (reindexQuaternionPolynomial first polynomial)) :=
  reindexQuaternionPolynomial_supported second _

theorem exactFixedFaceDoublyReindexedSelectedProduct_supported
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    SupportedQuaternionBlocks 116
      (exactFixedFaceDoublyReindexedSelectedProduct boundary face hface) := by
  unfold exactFixedFaceDoublyReindexedSelectedProduct
    exactFixedFaceDoubleReindex
  exact doublyReindexed_supported _ _ _

theorem exactFixedFaceCanonicalSelectedProduct_supported
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    SupportedQuaternionBlocks 116
      (exactFixedFaceCanonicalSelectedProduct boundary face hface) := by
  unfold exactFixedFaceCanonicalSelectedProduct exactFixedFaceDoubleReindex
  exact supported_polyMul
    (characterPolynomial_supported exposedFourWord_supported_116.scalar _)
    (doublyReindexed_supported _ _ _)

/-- Prefix equivalence is now promoted to exact equality under normalized
116-fold Haar integration. -/
theorem exactFixedFaceDoublyReindexedSelectedProduct_haar_eq_canonical
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    quaternionHaar 116
        (exactFixedFaceDoublyReindexedSelectedProduct boundary face hface) ≈
      quaternionHaar 116
        (exactFixedFaceCanonicalSelectedProduct boundary face hface) :=
  quaternionHaar_prefixPolynomialEqv 116
    (exactFixedFaceDoublyReindexedSelectedProduct_prefix boundary hface)
    (exactFixedFaceDoublyReindexedSelectedProduct_supported boundary hface)
    (exactFixedFaceCanonicalSelectedProduct_supported boundary hface)

/-- Every positive physical selected label is killed on the doubly
reindexed carrier.  The proof explicitly splits into the existing odd-head
and positive-even solid-zonal annihilation theorems. -/
theorem exactFixedFaceDoublyReindexedSelectedProduct_zero_of_nonzero_label
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces)
    (hpositive :
      0 < boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face)) :
    quaternionHaar 116
      (exactFixedFaceDoublyReindexedSelectedProduct boundary face hface) ≈
        0 := by
  refine Q'.eqv_trans _ _ _
    (exactFixedFaceDoublyReindexedSelectedProduct_haar_eq_canonical
      boundary hface) ?_
  let spin := boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face)
  by_cases hodd : spin % 2 = 1
  · exact exactFixedFaceCanonicalSelectedProduct_odd_zero
      boundary hface hodd
  · have hmodLt : spin % 2 < 2 := Nat.mod_lt _ (by omega)
    have heven : spin % 2 = 0 := by omega
    let k := spin / 2
    have hdecomp := Nat.mod_add_div spin 2
    have hspin : spin = 2 * k := by
      dsimp [k]
      omega
    have hk : 0 < k := by omega
    exact exactFixedFaceCanonicalSelectedProduct_even_zero
      boundary hface k hk (by simpa [spin] using hspin)

/-! ## 8. Return through both Haar changes of variables -/

private theorem correctedSlabLinkPolynomial_supported
    (extent : Nat) (link : Z4Link) :
    SupportedPolyQuaternion
      (boundaryCompleteSlabLinks extent).length
      (correctedSlabLinkPolynomial extent link) := by
  by_cases hlink : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hlink]
    exact supportedPolyQuaternion_coordinateVariable
      (List.idxOf_lt_length_of_mem hlink)
  · rw [correctedSlabLinkPolynomial_of_not_mem hlink]
    exact supportedPolyQuaternion_one _

private theorem orientedCorrectedSlabLinkPolynomial_supported
    (extent : Nat) (entry : OrientedBF4Link) :
    SupportedPolyQuaternion
      (boundaryCompleteSlabLinks extent).length
      (orientedCorrectedSlabLinkPolynomial extent entry) := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · exact supportedPolyQuaternion_conj
      (correctedSlabLinkPolynomial_supported extent entry.link)
  · exact correctedSlabLinkPolynomial_supported extent entry.link

private theorem correctedSlabPlaquetteFold_supported
    (extent : Nat) : ∀ (entries : List OrientedBF4Link)
      (total : PolyQuaternion),
    SupportedPolyQuaternion
        (boundaryCompleteSlabLinks extent).length total →
    SupportedPolyQuaternion
      (boundaryCompleteSlabLinks extent).length
      (entries.foldl
        (fun current entry => PolyQuaternion.mul current
          (orientedCorrectedSlabLinkPolynomial extent entry)) total)
  | [], _, htotal => htotal
  | entry :: rest, total, htotal => by
      simp only [List.foldl_cons]
      exact correctedSlabPlaquetteFold_supported extent rest _
        (supportedPolyQuaternion_mul htotal
          (orientedCorrectedSlabLinkPolynomial_supported extent entry))

private theorem correctedSlabPlaquettePolynomial_supported
    (extent : Nat) (face : Z4Plaq) :
    SupportedPolyQuaternion
      (boundaryCompleteSlabLinks extent).length
      (correctedSlabPlaquettePolynomial extent face) := by
  unfold correctedSlabPlaquettePolynomial
  exact correctedSlabPlaquetteFold_supported extent
    (orientedPlaquetteBoundary face) PolyQuaternion.one
    (supportedPolyQuaternion_one _)

private theorem correctedSlabPlaquetteSpinFactor_supported
    (extent : Nat)
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (face : Z4Plaq) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length
      (correctedSlabPlaquetteSpinFactor extent boundary face) := by
  unfold correctedSlabPlaquetteSpinFactor
  exact characterPolynomial_supported
    (correctedSlabPlaquettePolynomial_supported extent face).scalar _

private theorem correctedSlabFaceFold_supported
    (extent : Nat)
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    ∀ faces : List Z4Plaq,
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length
      (faces.foldr
        (fun face total => polyMul
          (correctedSlabPlaquetteSpinFactor extent boundary face) total)
        polyOne)
  | [] => supported_polyOne _
  | face :: rest => supported_polyMul
      (correctedSlabPlaquetteSpinFactor_supported extent boundary face)
      (correctedSlabFaceFold_supported extent boundary rest)

/-- Selected physical character times the literal other-23-face fold before
either block permutation. -/
def exactFixedFaceSelectedProduct
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (face : Z4Plaq) : RatPoly :=
  polyMul
    (correctedSlabPlaquetteSpinFactor 1 boundary face)
    (exactFixedFaceOtherInsertion boundary face)

private theorem exactFixedFaceSelectedProduct_supported
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (face : Z4Plaq) :
    SupportedQuaternionBlocks 116
      (exactFixedFaceSelectedProduct boundary face) := by
  rw [← correctedSlabLinks_extent_one_length]
  unfold exactFixedFaceSelectedProduct exactFixedFaceOtherInsertion
  exact supported_polyMul
    (correctedSlabPlaquetteSpinFactor_supported 1 boundary face)
    (correctedSlabFaceFold_supported 1 boundary _)

/-- Both explicit block involutions preserve the exact physical Haar value. -/
theorem exactFixedFaceSelectedProduct_haar_eq_doublyReindexed
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    quaternionHaar 116 (exactFixedFaceSelectedProduct boundary face) ≈
      quaternionHaar 116
        (exactFixedFaceDoublyReindexedSelectedProduct boundary face hface) := by
  let head := exactFixedFaceHeadBlockInvolution face hface
  let tail := exactFixedFaceTailBlockInvolution face hface
  let polynomial := exactFixedFaceSelectedProduct boundary face
  have hhead := quaternionHaar_reindex head polynomial
    (exactFixedFaceSelectedProduct_supported boundary face)
  have htail := quaternionHaar_reindex tail
    (reindexQuaternionPolynomial head polynomial)
    (reindexQuaternionPolynomial_supported head polynomial)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ htail hhead)

/-- The actual selected physical factorization has zero exact Haar value for
every nonzero selected spin. -/
theorem exactFixedFaceSelectedProduct_zero_of_nonzero_label
    (boundary :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces)
    (hpositive :
      0 < boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face)) :
    quaternionHaar 116 (exactFixedFaceSelectedProduct boundary face) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (exactFixedFaceSelectedProduct_haar_eq_doublyReindexed boundary hface)
    (exactFixedFaceDoublyReindexedSelectedProduct_zero_of_nonzero_label
      boundary hface hpositive)

/-- **The fixed-face conditional Peter--Weyl gate is inhabited.** -/
theorem exactFixedFaceConditionalHaarOrthogonality :
    ExactFixedFaceConditionalHaarOrthogonality := by
  intro boundary face hface hnonzero
  rw [correctedSlabLinks_extent_one_length]
  exact Q'.eqv_trans _ _ _
    (exactInteriorHaar_eq_selectedFace_mul_other boundary face hface)
    (exactFixedFaceSelectedProduct_zero_of_nonzero_label
      boundary hface (Nat.pos_of_ne_zero hnonzero))

/-- Consequently every non-vacuum vacuum-boundary term vanishes at every
finite label cutoff. -/
theorem exactVacuumNontrivialHaarTermsVanish_all_cutoffs
    (cutoff : Nat) : ExactVacuumNontrivialHaarTermsVanish cutoff :=
  exactVacuumNontrivialHaarTermsVanish_of_fixedFaceOrthogonality
    exactFixedFaceConditionalHaarOrthogonality cutoff

end YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.reindexTwice_polyVar_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.reindexTwice_orientedCoordinateQuaternion_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.exactFixedFaceDoublyReindexedSelectedScalar_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.exactFixedFaceDoublyReindexedSelectedCharacter_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.exactFixedFaceCanonicalSelectedProduct_even_zero
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.exactFixedFaceCanonicalSelectedProduct_odd_zero
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.exactFixedFaceConditionalHaarOrthogonality
#print axioms YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord.exactVacuumNontrivialHaarTermsVanish_all_cutoffs
