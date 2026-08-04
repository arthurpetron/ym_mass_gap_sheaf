/-
# Structural polynomial semantics for the BF4 surface forest gauge

This module supplies the non-expanding algebraic layer between the checked
oriented-edge words and the exact quaternion Haar carrier.  It proves that an
arbitrary certified block-swap chain transports every coordinate quaternion
to the coordinate named by its checked source map.  It also packages the
unit-sphere radius relation with the arbitrary left insertion strength needed
for cancellation inside a factor network.

These lemmas deliberately avoid canonical expansion of a selected surface.

## Axiom gate

Finite induction and the existing constructive sphere-ideal theorem only.
No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics
import YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
import YMGap.Continuum.SU2QuaternionSolidZonalCharacter

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## One block involution on coordinate quaternions -/

/-- One coordinate variable transported through one block involution. -/
theorem reindex_polyVar_prefix
    {blocks target source component : Nat}
    (permutation : QuaternionBlockInvolution blocks)
    (htarget : target < blocks) (hcomponent : component < 4)
    (hmap : permutation.map target = source) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial permutation
        (polyVar (4 * source + component)))
      (polyVar (4 * target + component)) := by
  change QuaternionPrefixPolynomialEqv blocks
    [(_, 1)] [(YMGap.Continuum.RingNormaliser.varMono
      (4 * target + component), 1)]
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro coordinate hcoordinate
      rw [exponentAt_reindexQuaternionExponents permutation _ hcoordinate,
        exponentAt_varMono, exponentAt_varMono]
      have hblock : coordinate / 4 < blocks := by omega
      have hcomponentCoordinate : coordinate % 4 < 4 :=
        Nat.mod_lt coordinate (by omega)
      by_cases heq :
          4 * permutation.map (coordinate / 4) + coordinate % 4 =
            4 * source + component
      · rw [if_pos heq]
        have hmapped : permutation.map (coordinate / 4) = source := by
          omega
        have hsourceBlock : coordinate / 4 = target :=
          permutation.injective_on hblock htarget
            (hmapped.trans hmap.symm)
        have hcoordinateDecomp :
            4 * (coordinate / 4) + coordinate % 4 = coordinate := by
          omega
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

/-- The four coordinates of one quaternion transport together through one
block involution. -/
theorem reindex_coordinateVariable_prefix
    {blocks target source : Nat}
    (permutation : QuaternionBlockInvolution blocks)
    (htarget : target < blocks)
    (hmap : permutation.map target = source) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (reindexPolyQuaternion permutation
        (PolyQuaternion.coordinateVariable source))
      (PolyQuaternion.coordinateVariable target) := by
  exact ⟨
    by simpa [reindexPolyQuaternion, PolyQuaternion.coordinateVariable] using
      (reindex_polyVar_prefix
        (target := target) (source := source) (component := 0)
        permutation htarget (by omega) hmap),
    by simpa [reindexPolyQuaternion, PolyQuaternion.coordinateVariable] using
      (reindex_polyVar_prefix
        (target := target) (source := source) (component := 1)
        permutation htarget (by omega) hmap),
    by simpa [reindexPolyQuaternion, PolyQuaternion.coordinateVariable] using
      (reindex_polyVar_prefix
        (target := target) (source := source) (component := 2)
        permutation htarget (by omega) hmap),
    by simpa [reindexPolyQuaternion, PolyQuaternion.coordinateVariable] using
      (reindex_polyVar_prefix
        (target := target) (source := source) (component := 3)
        permutation htarget (by omega) hmap)⟩

theorem reindex_polyOne_prefix
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial permutation polyOne) polyOne := by
  change QuaternionPrefixPolynomialEqv blocks [(_, 1)] [([], 1)]
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro coordinate hcoordinate
      rw [exponentAt_reindexQuaternionExponents permutation _ hcoordinate]
      simp [exponentAt]
  · exact .nil

theorem reindex_polyQuaternionOne_prefix
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (reindexPolyQuaternion permutation PolyQuaternion.one)
      PolyQuaternion.one := by
  constructor
  · simpa [reindexPolyQuaternion, PolyQuaternion.one] using
      reindex_polyOne_prefix permutation
  all_goals
    change QuaternionPrefixPolynomialEqv blocks [] []
    exact .nil

/-- Prefix equivalence is stable under a common block involution. -/
theorem reindex_prefix_polyQuaternion
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    {left right : PolyQuaternion}
    (heqv : QuaternionPrefixPolyQuaternionEqv blocks left right) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (reindexPolyQuaternion permutation left)
      (reindexPolyQuaternion permutation right) :=
  ⟨QuaternionPrefixPolynomialEqv.reindex permutation heqv.scalar,
    QuaternionPrefixPolynomialEqv.reindex permutation heqv.iPart,
    QuaternionPrefixPolynomialEqv.reindex permutation heqv.jPart,
    QuaternionPrefixPolynomialEqv.reindex permutation heqv.kPart⟩

/-! ## Arbitrary block-swap chains -/

/-- Componentwise action of an arbitrary block-swap chain. -/
def applyQuaternionBlockSwapChainQuaternion
    {blocks : Nat} :
    List (QuaternionBlockInvolution blocks) → PolyQuaternion → PolyQuaternion
  | [], quaternion => quaternion
  | swap :: rest, quaternion =>
      applyQuaternionBlockSwapChainQuaternion rest
        (reindexPolyQuaternion swap quaternion)

theorem applyQuaternionBlockSwapChainQuaternion_conj
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      (quaternion : PolyQuaternion),
      applyQuaternionBlockSwapChainQuaternion swaps
          (PolyQuaternion.conj quaternion) =
        PolyQuaternion.conj
          (applyQuaternionBlockSwapChainQuaternion swaps quaternion)
  | [], _ => rfl
  | swap :: rest, quaternion => by
      simp only [applyQuaternionBlockSwapChainQuaternion,
        reindexPolyQuaternion_conj]
      exact applyQuaternionBlockSwapChainQuaternion_conj rest
        (reindexPolyQuaternion swap quaternion)

theorem applyQuaternionBlockSwapChainQuaternion_mul
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      (left right : PolyQuaternion),
      applyQuaternionBlockSwapChainQuaternion swaps
          (PolyQuaternion.mul left right) =
        PolyQuaternion.mul
          (applyQuaternionBlockSwapChainQuaternion swaps left)
          (applyQuaternionBlockSwapChainQuaternion swaps right)
  | [], _, _ => rfl
  | swap :: rest, left, right => by
      simp only [applyQuaternionBlockSwapChainQuaternion,
        reindexPolyQuaternion_mul]
      exact applyQuaternionBlockSwapChainQuaternion_mul rest
        (reindexPolyQuaternion swap left)
        (reindexPolyQuaternion swap right)

theorem applyQuaternionBlockSwapChainQuaternion_prefix
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      {left right : PolyQuaternion},
      QuaternionPrefixPolyQuaternionEqv blocks left right →
      QuaternionPrefixPolyQuaternionEqv blocks
        (applyQuaternionBlockSwapChainQuaternion swaps left)
        (applyQuaternionBlockSwapChainQuaternion swaps right)
  | [], _, _, heqv => heqv
  | swap :: rest, _, _, heqv =>
      applyQuaternionBlockSwapChainQuaternion_prefix rest
        (reindex_prefix_polyQuaternion swap heqv)

theorem applyQuaternionBlockSwapChainQuaternion_one_prefix
    {blocks : Nat} :
    ∀ swaps : List (QuaternionBlockInvolution blocks),
      QuaternionPrefixPolyQuaternionEqv blocks
        (applyQuaternionBlockSwapChainQuaternion swaps PolyQuaternion.one)
        PolyQuaternion.one
  | [] => QuaternionPrefixPolyQuaternionEqv.refl blocks PolyQuaternion.one
  | swap :: rest =>
      QuaternionPrefixPolyQuaternionEqv.trans
        (applyQuaternionBlockSwapChainQuaternion_prefix rest
          (reindex_polyQuaternionOne_prefix swap))
        (applyQuaternionBlockSwapChainQuaternion_one_prefix rest)

/-- Polynomial prefix equivalence is stable under a complete block-swap
chain. -/
theorem applyQuaternionBlockSwapChain_prefix
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      {left right : RatPoly},
      QuaternionPrefixPolynomialEqv blocks left right →
      QuaternionPrefixPolynomialEqv blocks
        (applyQuaternionBlockSwapChain swaps left)
        (applyQuaternionBlockSwapChain swaps right)
  | [], _, _, heqv => heqv
  | swap :: rest, _, _, heqv =>
      applyQuaternionBlockSwapChain_prefix rest
        (QuaternionPrefixPolynomialEqv.reindex swap heqv)

/-- The production block-swap chain commutes with the complete character
recursion up to harmless prefix padding. -/
theorem applyQuaternionBlockSwapChain_character_prefix
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      (scalar : RatPoly) (spin : Nat),
      QuaternionPrefixPolynomialEqv blocks
        (applyQuaternionBlockSwapChain swaps
          (characterPolynomial scalar spin))
        (characterPolynomial
          (applyQuaternionBlockSwapChain swaps scalar) spin)
  | [], scalar, spin =>
      QuaternionPrefixPolynomialEqv.refl blocks
        (characterPolynomial scalar spin)
  | swap :: rest, scalar, spin => by
      exact QuaternionPrefixPolynomialEqv.trans
        (applyQuaternionBlockSwapChain_prefix rest
          (reindexQuaternionPolynomial_character_prefix swap scalar spin))
        (applyQuaternionBlockSwapChain_character_prefix rest
          (reindexQuaternionPolynomial swap scalar) spin)

/-- The checked source map is the exact coordinate action of the whole
block-swap chain. -/
theorem applyQuaternionBlockSwapChain_coordinateVariable_prefix
    {blocks target source : Nat}
    (swaps : List (QuaternionBlockInvolution blocks))
    (htarget : target < blocks)
    (hmap : quaternionBlockSwapChainSource swaps target = source) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (applyQuaternionBlockSwapChainQuaternion swaps
        (PolyQuaternion.coordinateVariable source))
      (PolyQuaternion.coordinateVariable target) := by
  induction swaps generalizing source with
  | nil =>
      have hsource : target = source := by
        simpa [quaternionBlockSwapChainSource] using hmap
      subst source
      exact QuaternionPrefixPolyQuaternionEqv.refl blocks
        (PolyQuaternion.coordinateVariable target)
  | cons swap rest induction =>
      let middle := quaternionBlockSwapChainSource rest target
      have hmiddle : middle < blocks :=
        quaternionBlockSwapChainSource_lt rest htarget
      have hfirstMap : swap.map middle = source := by
        simpa [middle, quaternionBlockSwapChainSource] using hmap
      have hfirst := reindex_coordinateVariable_prefix
        swap hmiddle hfirstMap
      have hrest := induction (source := middle) rfl
      exact QuaternionPrefixPolyQuaternionEqv.trans
        (applyQuaternionBlockSwapChainQuaternion_prefix rest hfirst)
        hrest

/-- Orientation reversal is preserved by the full block-swap chain. -/
theorem applyQuaternionBlockSwapChain_orientedCoordinate_prefix
    {blocks target source : Nat}
    (swaps : List (QuaternionBlockInvolution blocks))
    (htarget : target < blocks)
    (hmap : quaternionBlockSwapChainSource swaps target = source)
    (reverse : Bool) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (applyQuaternionBlockSwapChainQuaternion swaps
        (orientedCoordinateQuaternion source reverse))
      (orientedCoordinateQuaternion target reverse) := by
  cases reverse with
  | false =>
      exact applyQuaternionBlockSwapChain_coordinateVariable_prefix
        swaps htarget hmap
  | true =>
      rw [show orientedCoordinateQuaternion source true =
          PolyQuaternion.conj (PolyQuaternion.coordinateVariable source) by
            rfl,
        show orientedCoordinateQuaternion target true =
          PolyQuaternion.conj (PolyQuaternion.coordinateVariable target) by
            rfl,
        applyQuaternionBlockSwapChainQuaternion_conj]
      exact (applyQuaternionBlockSwapChain_coordinateVariable_prefix
        swaps htarget hmap).conj

/-- Scalar projection of the componentwise chain agrees definitionally with
the production polynomial chain. -/
theorem applyQuaternionBlockSwapChainQuaternion_scalar
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      (quaternion : PolyQuaternion),
      (applyQuaternionBlockSwapChainQuaternion swaps quaternion).scalar =
        applyQuaternionBlockSwapChain swaps quaternion.scalar
  | [], _ => rfl
  | swap :: rest, quaternion => by
      simpa [applyQuaternionBlockSwapChainQuaternion,
        applyQuaternionBlockSwapChain, reindexPolyQuaternion] using
        applyQuaternionBlockSwapChainQuaternion_scalar rest
          (reindexPolyQuaternion swap quaternion)

/-- A whole oriented coordinate fold transports through a swap chain without
expanding any Hamilton product. -/
theorem applyQuaternionBlockSwapChain_orientedFold_prefix
    {blocks : Nat}
    (swaps : List (QuaternionBlockInvolution blocks))
    (entries : List OrientedBF4Link)
    (source target : OrientedBF4Link → Nat)
    (hentry : ∀ entry, entry ∈ entries →
      target entry < blocks ∧
        quaternionBlockSwapChainSource swaps (target entry) = source entry) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (applyQuaternionBlockSwapChainQuaternion swaps
        (entries.foldl
          (fun total entry => PolyQuaternion.mul total
            (orientedCoordinateQuaternion (source entry) entry.reverse))
          PolyQuaternion.one))
      ((entries.map fun entry => (target entry, entry.reverse)).foldl
        (fun total entry => PolyQuaternion.mul total
          (orientedCoordinateQuaternion entry.1 entry.2))
        PolyQuaternion.one) := by
  have go : ∀ (remaining : List OrientedBF4Link)
      (sourceInitial targetInitial : PolyQuaternion),
      QuaternionPrefixPolyQuaternionEqv blocks
        (applyQuaternionBlockSwapChainQuaternion swaps sourceInitial)
        targetInitial →
      (∀ entry, entry ∈ remaining →
        target entry < blocks ∧
          quaternionBlockSwapChainSource swaps (target entry) =
            source entry) →
      QuaternionPrefixPolyQuaternionEqv blocks
        (applyQuaternionBlockSwapChainQuaternion swaps
          (remaining.foldl
            (fun total entry => PolyQuaternion.mul total
              (orientedCoordinateQuaternion (source entry) entry.reverse))
            sourceInitial))
        ((remaining.map fun entry => (target entry, entry.reverse)).foldl
          (fun total entry => PolyQuaternion.mul total
            (orientedCoordinateQuaternion entry.1 entry.2))
          targetInitial) := by
    intro remaining
    induction remaining with
    | nil =>
        intro sourceInitial targetInitial hinitial _
        simpa using hinitial
    | cons entry rest induction =>
        intro sourceInitial targetInitial hinitial hremaining
        simp only [List.foldl_cons, List.map_cons]
        apply induction
        · rw [applyQuaternionBlockSwapChainQuaternion_mul]
          exact hinitial.mul
            (applyQuaternionBlockSwapChain_orientedCoordinate_prefix
              swaps
              (hremaining entry List.mem_cons_self).1
              (hremaining entry List.mem_cons_self).2
              entry.reverse)
        · intro other hother
          exact hremaining other (List.mem_cons_of_mem entry hother)
  exact go entries PolyQuaternion.one PolyQuaternion.one
    (applyQuaternionBlockSwapChainQuaternion_one_prefix swaps) hentry

/-! ## The literal 24-face source/target table -/

private def fallbackSurfacePlaq :
    YMGap.Continuum.ClusterCount4DProgress.Z4Plaq :=
  ((0, 0, 0, 0), .p01)

/-- The literal slab face carrying one compact four-cube face id. -/
def surfaceSlabFace (faceId : Nat) :
    YMGap.Continuum.ClusterCount4DProgress.Z4Plaq :=
  (boundaryCompleteSlabPlaquettes 1).getD
    (activeHypercubeSlabFaceIds.getD faceId 0) fallbackSurfacePlaq

/-- Raw 116-link source block of one oriented literal boundary entry. -/
def surfaceEntryRawBlock (entry : OrientedBF4Link) : Nat :=
  (boundaryCompleteSlabLinks 1).idxOf entry.link

/-- Active 32-link target occupied by one oriented literal boundary entry. -/
def surfaceEntryActiveTarget (entry : OrientedBF4Link) : Nat :=
  bf4SurfaceActiveRawBlocks.idxOf (surfaceEntryRawBlock entry)

/-- The literal boundary word written directly in active target blocks. -/
def surfaceActiveTargetFaceWord (faceId : Nat) : List (Nat × Bool) :=
  (orientedPlaquetteBoundary (surfaceSlabFace faceId)).map fun entry =>
    (surfaceEntryActiveTarget entry, entry.reverse)

/-- Simultaneously check literal face membership, every swap-chain
source/target pair, and agreement with the compact primal-edge word. -/
def surfaceActiveFaceGeometryCheck : Bool :=
  (List.range 24).all fun faceId =>
    let face := surfaceSlabFace faceId
    decide (face ∈ boundaryCompleteSlabPlaquettes 1) &&
      ((orientedPlaquetteBoundary face).all fun entry =>
        decide (surfaceEntryActiveTarget entry < 32) &&
          decide
            (quaternionBlockSwapChainSource
                bf4SurfaceActiveCarrierSteps
                (surfaceEntryActiveTarget entry) =
              surfaceEntryRawBlock entry)) &&
      decide
        (surfaceActiveTargetFaceWord faceId =
          (hypercubeFaceWords.getD faceId []).map fun entry =>
            (surfaceActiveBlock entry.1, entry.2))

theorem surfaceActiveFaceGeometryCheck_true :
    surfaceActiveFaceGeometryCheck = true := by
  decide

/-- Structured form of the complete 24-face geometry certificate. -/
theorem surfaceActiveFaceGeometry
    (faceId : Nat) (hfaceId : faceId < 24) :
    surfaceSlabFace faceId ∈ boundaryCompleteSlabPlaquettes 1 ∧
      (∀ entry, entry ∈ orientedPlaquetteBoundary (surfaceSlabFace faceId) →
        surfaceEntryActiveTarget entry < 32 ∧
          quaternionBlockSwapChainSource
              bf4SurfaceActiveCarrierSteps
              (surfaceEntryActiveTarget entry) =
            surfaceEntryRawBlock entry) ∧
      surfaceActiveTargetFaceWord faceId =
        (hypercubeFaceWords.getD faceId []).map fun entry =>
          (surfaceActiveBlock entry.1, entry.2) := by
  have hrow := List.all_eq_true.mp
    surfaceActiveFaceGeometryCheck_true faceId
      (List.mem_range.mpr hfaceId)
  have hparts :
      (surfaceSlabFace faceId ∈ boundaryCompleteSlabPlaquettes 1 ∧
        ∀ entry, entry ∈
            orientedPlaquetteBoundary (surfaceSlabFace faceId) →
          surfaceEntryActiveTarget entry < 32 ∧
            quaternionBlockSwapChainSource
                bf4SurfaceActiveCarrierSteps
                (surfaceEntryActiveTarget entry) =
              surfaceEntryRawBlock entry) ∧
        surfaceActiveTargetFaceWord faceId =
          (hypercubeFaceWords.getD faceId []).map fun entry =>
            (surfaceActiveBlock entry.1, entry.2) := by
    simpa [surfaceActiveFaceGeometryCheck] using hrow
  exact ⟨hparts.1.1, hparts.1.2, hparts.2⟩

/-- Every literal slab plaquette is the fold of its genuine coordinate
quaternions; no fixed-face restriction or fallback variable is needed. -/
theorem correctedSlabPlaquettePolynomial_eq_coordinateFold_of_mem
    {face : YMGap.Continuum.ClusterCount4DProgress.Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    correctedSlabPlaquettePolynomial 1 face =
      (orientedPlaquetteBoundary face).foldl
        (fun total entry => PolyQuaternion.mul total
          (orientedCoordinateQuaternion
            (surfaceEntryRawBlock entry) entry.reverse))
        PolyQuaternion.one := by
  unfold correctedSlabPlaquettePolynomial
  have horiented : ∀ entry : OrientedBF4Link,
      entry ∈ orientedPlaquetteBoundary face →
      orientedCorrectedSlabLinkPolynomial 1 entry =
        orientedCoordinateQuaternion
          (surfaceEntryRawBlock entry) entry.reverse := by
    intro entry hentry
    have hlink := orientedPlaquetteBoundary_link_mem_slab hface hentry
    unfold orientedCorrectedSlabLinkPolynomial surfaceEntryRawBlock
    rw [correctedSlabLinkPolynomial_of_mem hlink]
    cases entry.reverse <;> rfl
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
              (surfaceEntryRawBlock entry) entry.reverse)) initial := by
    intro entries
    induction entries with
    | nil => intro initial _; rfl
    | cons entry rest induction =>
        intro initial hentries
        simp only [List.foldl_cons]
        rw [horiented entry (hentries entry List.mem_cons_self)]
        exact induction _ (fun item hitem =>
          hentries item (List.mem_cons_of_mem entry hitem))
  exact go (orientedPlaquetteBoundary face) PolyQuaternion.one
    (fun _ hentry => hentry)

/-! ## The physical 116-block face becomes the compact active word -/

/-- The complete checked swap chain sends the genuine quaternion polynomial
of any one of the 24 surface faces to its compact active-block word.  This is
the structural replacement for expanding the Hamilton products. -/
theorem reindexedSurfaceSlabFaceQuaternion_prefix
    (faceId : Nat) (hfaceId : faceId < 24) :
    QuaternionPrefixPolyQuaternionEqv 116
      (applyQuaternionBlockSwapChainQuaternion
        bf4SurfaceActiveCarrierSteps
        (correctedSlabPlaquettePolynomial 1 (surfaceSlabFace faceId)))
      (compactOrientedQuaternionWord
        ((hypercubeFaceWords.getD faceId []).map fun entry =>
          (surfaceActiveBlock entry.1, entry.2))) := by
  have hgeometry := surfaceActiveFaceGeometry faceId hfaceId
  rw [correctedSlabPlaquettePolynomial_eq_coordinateFold_of_mem
    hgeometry.1]
  have hfold := applyQuaternionBlockSwapChain_orientedFold_prefix
    bf4SurfaceActiveCarrierSteps
    (orientedPlaquetteBoundary (surfaceSlabFace faceId))
    surfaceEntryRawBlock surfaceEntryActiveTarget (fun entry hentry =>
      ⟨by
          have hactive := (hgeometry.2.1 entry hentry).1
          omega,
        (hgeometry.2.1 entry hentry).2⟩)
  have hword :
      QuaternionPrefixPolyQuaternionEqv 116
        (applyQuaternionBlockSwapChainQuaternion
          bf4SurfaceActiveCarrierSteps
          ((orientedPlaquetteBoundary (surfaceSlabFace faceId)).foldl
            (fun total entry => PolyQuaternion.mul total
              (orientedCoordinateQuaternion
                (surfaceEntryRawBlock entry) entry.reverse))
            PolyQuaternion.one))
        (compactOrientedQuaternionWord
          (surfaceActiveTargetFaceWord faceId)) := by
    simpa [surfaceActiveTargetFaceWord,
      compactOrientedQuaternionWord] using hfold
  rw [hgeometry.2.2] at hword
  exact hword

/-- Scalar projection of the preceding quaternion statement, stated using
the exact production reindexer. -/
theorem reindexedSurfaceSlabFaceScalar_prefix
    (faceId : Nat) (hfaceId : faceId < 24) :
    QuaternionPrefixPolynomialEqv 116
      (reindexBF4SurfaceActiveCarrier
        (correctedSlabPlaquettePolynomial
          1 (surfaceSlabFace faceId)).scalar)
      (compactOrientedQuaternionWord
        ((hypercubeFaceWords.getD faceId []).map fun entry =>
          (surfaceActiveBlock entry.1, entry.2))).scalar := by
  have hscalar :=
    (reindexedSurfaceSlabFaceQuaternion_prefix faceId hfaceId).scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hscalar
  simpa [reindexBF4SurfaceActiveCarrier] using hscalar

/-! ## Constructive deletion of the 84 inactive blocks -/

private theorem exponentAt_take_of_lt_semantics (monomial : List Nat) :
    ∀ count coordinate : Nat, coordinate < count →
      exponentAt (monomial.take count) coordinate =
        exponentAt monomial coordinate
  | 0, _, hcoordinate => by omega
  | count + 1, 0, _ => by
      cases monomial <;> simp [exponentAt]
  | count + 1, coordinate + 1, hcoordinate => by
      cases monomial with
      | nil => simp [exponentAt]
      | cons _ rest =>
          simp only [List.take_succ_cons]
          change exponentAt (rest.take count) coordinate =
            exponentAt rest coordinate
          exact exponentAt_take_of_lt_semantics rest count coordinate
            (by omega)

/-- Prefix equivalence on a larger quaternion carrier survives deleting the
same inactive tail on both sides. -/
theorem trimQuaternionPolynomial_prefix_equiv
    {large active : Nat} (hactive : active ≤ large)
    {left right : RatPoly}
    (heqv : QuaternionPrefixPolynomialEqv large left right) :
    QuaternionPrefixPolynomialEqv active
      (trimQuaternionPolynomial active left)
      (trimQuaternionPolynomial active right) := by
  induction heqv with
  | nil => exact .nil
  | @cons leftTerm rightTerm leftRest rightRest hterm hrest induction =>
      unfold trimQuaternionPolynomial
      simp only [List.map_cons]
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact hterm.coefficient
        · intro coordinate hcoordinate
          calc
            exponentAt (leftTerm.1.take (4 * active)) coordinate =
                exponentAt leftTerm.1 coordinate :=
              exponentAt_take_of_lt_semantics _ _ _ hcoordinate
            _ = exponentAt rightTerm.1 coordinate :=
              hterm.exponent coordinate (by omega)
            _ = exponentAt (rightTerm.1.take (4 * active)) coordinate :=
              (exponentAt_take_of_lt_semantics _ _ _ hcoordinate).symm
      · exact induction

/-- Trimming a polynomial does not change its declared active prefix.  This
requires no tail-support premise, so it remains valid under arbitrary zero
padding conventions. -/
theorem trimQuaternionPolynomial_prefix_self
    (blocks : Nat) : ∀ polynomial : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (trimQuaternionPolynomial blocks polynomial) polynomial
  | [] => .nil
  | term :: rest => by
      unfold trimQuaternionPolynomial
      simp only [List.map_cons]
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact Q'.eqv_refl _
        · intro coordinate hcoordinate
          exact exponentAt_take_of_lt_semantics _ _ _ hcoordinate
      · exact trimQuaternionPolynomial_prefix_self blocks rest

/-- The production 32-block scalar face factor is the compact active face
word on the exact prefix consumed by the active Haar evaluator. -/
theorem activeSurfaceSlabFaceScalar_prefix
    (faceId : Nat) (hfaceId : faceId < 24) :
    QuaternionPrefixPolynomialEqv 32
      (trimQuaternionPolynomial 32
        (reindexBF4SurfaceActiveCarrier
          (correctedSlabPlaquettePolynomial
            1 (surfaceSlabFace faceId)).scalar))
      (compactOrientedQuaternionWord
        ((hypercubeFaceWords.getD faceId []).map fun entry =>
          (surfaceActiveBlock entry.1, entry.2))).scalar := by
  exact QuaternionPrefixPolynomialEqv.trans
    (trimQuaternionPolynomial_prefix_equiv (by omega)
      (reindexedSurfaceSlabFaceScalar_prefix faceId hfaceId))
    (trimQuaternionPolynomial_prefix_self 32 _)

/-! ## The genuine selected spin-one face factor -/

/-- The reindexed physical fundamental character is the fundamental
character of the compact active word, before inactive-tail deletion. -/
theorem reindexedSurfaceSlabFaceFundamentalFactor_prefix
    (faceId : Nat) (hfaceId : faceId < 24) :
    QuaternionPrefixPolynomialEqv 116
      (reindexBF4SurfaceActiveCarrier
        (characterPolynomial
          (correctedSlabPlaquettePolynomial
            1 (surfaceSlabFace faceId)).scalar 1))
      (compactFundamentalWordFactor
        ((hypercubeFaceWords.getD faceId []).map fun entry =>
          (surfaceActiveBlock entry.1, entry.2))) := by
  unfold reindexBF4SurfaceActiveCarrier compactFundamentalWordFactor
  exact QuaternionPrefixPolynomialEqv.trans
    (applyQuaternionBlockSwapChain_character_prefix
      bf4SurfaceActiveCarrierSteps
      (correctedSlabPlaquettePolynomial
        1 (surfaceSlabFace faceId)).scalar 1)
    ((reindexedSurfaceSlabFaceScalar_prefix faceId hfaceId).character 1)

/-- The exact 32-block production factor of a selected physical face is the
compact spin-one word factor consumed by the forest-gauge network. -/
theorem activeSurfaceSlabFaceFundamentalFactor_prefix
    (faceId : Nat) (hfaceId : faceId < 24) :
    QuaternionPrefixPolynomialEqv 32
      (trimQuaternionPolynomial 32
        (reindexBF4SurfaceActiveCarrier
          (characterPolynomial
            (correctedSlabPlaquettePolynomial
              1 (surfaceSlabFace faceId)).scalar 1)))
      (compactFundamentalWordFactor
        ((hypercubeFaceWords.getD faceId []).map fun entry =>
          (surfaceActiveBlock entry.1, entry.2))) := by
  exact QuaternionPrefixPolynomialEqv.trans
    (trimQuaternionPolynomial_prefix_equiv (by omega)
      (reindexedSurfaceSlabFaceFundamentalFactor_prefix faceId hfaceId))
    (trimQuaternionPolynomial_prefix_self 32 _)

/-- Same theorem stated for the literal corrected-slab spin-factor API. -/
theorem activeSelectedSurfaceSlabFaceFactor_prefix
    (faceLabel :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (faceId : Nat) (hfaceId : faceId < 24)
    (hselected :
      faceLabel
        ((boundaryCompleteSlabPlaquettes 1).idxOf
          (surfaceSlabFace faceId)) = 1) :
    QuaternionPrefixPolynomialEqv 32
      (trimQuaternionPolynomial 32
        (reindexBF4SurfaceActiveCarrier
          (correctedSlabPlaquetteSpinFactor
            1 faceLabel (surfaceSlabFace faceId))))
      (compactFundamentalWordFactor
        ((hypercubeFaceWords.getD faceId []).map fun entry =>
          (surfaceActiveBlock entry.1, entry.2))) := by
  unfold correctedSlabPlaquetteSpinFactor
  rw [hselected]
  exact activeSurfaceSlabFaceFundamentalFactor_prefix faceId hfaceId

/-! ## The complete selected physical factor network -/

/-- Compact active-word factors before the maximal-forest substitution. -/
def activeSurfaceSelectedWordFactors (mask : Nat) : List RatPoly :=
  (surfaceSelectedCompactFaceIds mask).map fun faceId =>
    compactFundamentalWordFactor
      ((hypercubeFaceWords.getD faceId []).map fun entry =>
        (surfaceActiveBlock entry.1, entry.2))

/-- Simultaneously certify the order of selected literal slab faces, the
compact face bound, and the spin-one label used by every selected factor. -/
def selectedSurfaceLiteralFaceGeometryCheck : Bool :=
  binarySurfaceMasks.all fun mask =>
    decide
      (embeddedSurfaceSelectedFaces mask =
        (surfaceSelectedCompactFaceIds mask).map surfaceSlabFace) &&
      (surfaceSelectedCompactFaceIds mask).all fun faceId =>
        decide (faceId < 24) &&
          decide
            (embeddedSurfaceLabelling mask
              ((boundaryCompleteSlabPlaquettes 1).idxOf
                (surfaceSlabFace faceId)) = 1)

theorem selectedSurfaceLiteralFaceGeometryCheck_true :
    selectedSurfaceLiteralFaceGeometryCheck = true := by
  decide

/-- Structured selected-face geometry for any certified surface mask. -/
theorem selectedSurfaceLiteralFaceGeometry
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    embeddedSurfaceSelectedFaces mask =
        (surfaceSelectedCompactFaceIds mask).map surfaceSlabFace ∧
      ∀ faceId, faceId ∈ surfaceSelectedCompactFaceIds mask →
        faceId < 24 ∧
          embeddedSurfaceLabelling mask
            ((boundaryCompleteSlabPlaquettes 1).idxOf
              (surfaceSlabFace faceId)) = 1 := by
  have hrow := List.all_eq_true.mp
    selectedSurfaceLiteralFaceGeometryCheck_true mask hmask
  simpa [selectedSurfaceLiteralFaceGeometryCheck] using hrow

/-- The product of every actual trimmed physical spin factor is prefix
equivalent to the product of the corresponding compact active words. -/
theorem embeddedSurfaceSelectedActiveFactorProduct_prefix
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    QuaternionPrefixPolynomialEqv 32
      (factorProduct (embeddedSurfaceSelectedActiveFactors mask))
      (factorProduct (activeSurfaceSelectedWordFactors mask)) := by
  have hgeometry := selectedSurfaceLiteralFaceGeometry mask hmask
  unfold embeddedSurfaceSelectedActiveFactors
    activeSurfaceSelectedWordFactors
  rw [hgeometry.1, List.map_map]
  have go : ∀ ids : List Nat,
      (∀ faceId, faceId ∈ ids →
        faceId ∈ surfaceSelectedCompactFaceIds mask) →
      QuaternionPrefixPolynomialEqv 32
        (factorProduct (ids.map fun faceId =>
          trimQuaternionPolynomial 32
            (reindexBF4SurfaceActiveCarrier
              (correctedSlabPlaquetteSpinFactor 1
                (embeddedSurfaceLabelling mask)
                (surfaceSlabFace faceId)))))
        (factorProduct (ids.map fun faceId =>
          compactFundamentalWordFactor
            ((hypercubeFaceWords.getD faceId []).map fun entry =>
              (surfaceActiveBlock entry.1, entry.2)))) := by
    intro ids
    induction ids with
    | nil =>
        intro _
        exact QuaternionPrefixPolynomialEqv.refl 32 polyOne
    | cons faceId rest induction =>
        intro hids
        simp only [List.map_cons, factorProduct]
        exact QuaternionPrefixPolynomialEqv.mul
          (activeSelectedSurfaceSlabFaceFactor_prefix
            (embeddedSurfaceLabelling mask) faceId
            (hgeometry.2 faceId
              (hids faceId List.mem_cons_self)).1
            (hgeometry.2 faceId
              (hids faceId List.mem_cons_self)).2)
          (induction (fun other hother =>
            hids other (List.mem_cons_of_mem faceId hother)))
  exact go (surfaceSelectedCompactFaceIds mask)
    (fun _ hface => hface)

/-! ## The unit-sphere cancellation carrier -/

/-- A single retained quaternion radius is the polynomial unit with the
arbitrary-insertion strength required to cancel an inverse pair inside a
larger face network. -/
theorem quaternionRadiusPolynomial_carrier_one
    {blocks block : Nat} (hblock : block < blocks) :
    HaarCarrierEqv blocks
      (quaternionRadiusPolynomial block) polyOne := by
  intro insertion
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_mul_radius blocks block hblock insertion)
    (Q'.eqv_symm
      (quaternionHaar_polyMul_one_right blocks insertion))

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.reindex_coordinateVariable_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.applyQuaternionBlockSwapChain_coordinateVariable_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.applyQuaternionBlockSwapChain_character_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.applyQuaternionBlockSwapChain_orientedCoordinate_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.surfaceActiveFaceGeometry
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.correctedSlabPlaquettePolynomial_eq_coordinateFold_of_mem
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.reindexedSurfaceSlabFaceQuaternion_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.reindexedSurfaceSlabFaceScalar_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.trimQuaternionPolynomial_prefix_equiv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.activeSurfaceSlabFaceScalar_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.activeSelectedSurfaceSlabFaceFactor_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.selectedSurfaceLiteralFaceGeometry
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.embeddedSurfaceSelectedActiveFactorProduct_prefix
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics.quaternionRadiusPolynomial_carrier_one
