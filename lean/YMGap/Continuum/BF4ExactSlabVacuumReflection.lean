/-
# Exact corrected-slab vacuum reflection

This module begins the two load-bearing normalization proofs for the literal
corrected BF4 slab: time-reflection symmetry of its signed Haar coefficient
and strict positivity of its vacuum--vacuum reflected partition.

The first finite datum is the exact involution of the quaternion blocks.
Every block is one link in `boundaryCompleteSlabLinks`; reflecting the link
and searching the same nodup list gives a constructive numerical
permutation.  This is the block permutation to which product-Haar invariance
applies.  Positive time links additionally require quaternion conjugation;
that coordinate-sign layer is kept separate.

No symmetry or positivity claim about the full slab kernel is introduced by
structure field here.  The theorems below are literal geometry and are the
input to the subsequent polynomial and Gram identities.

## Axiom gate

Finite lists and exact rational polynomial Haar moments only.  No
`Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
import YMGap.Continuum.BF4GroupedGramChoiKernel
import YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
import YMGap.Continuum.SU2QuaternionHaarRingNormalizer
import YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck0
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck1
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck2
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck3
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck4
import YMGap.Continuum.BF4ExactSlabVacuumReflectionCheck5

namespace YMGap.Continuum.BF4ExactSlabVacuumReflection

set_option maxRecDepth 100000
set_option maxHeartbeats 100000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GroupedGramChoiKernel
open YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => YMGap.Constructive.Q'.eqv

/-! ## 1. Constructive reflection of the literal slab-link blocks -/

private abbrev SlabLink :=
  YMGap.Continuum.ClusterCount4DProgress.Z4Link

private abbrev SlabFace :=
  YMGap.Continuum.ClusterCount4DProgress.Z4Plaq

private abbrev SlabFaceLabelling :=
  YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling

private def correctedSlabFallbackLink : SlabLink :=
  ((0, 0, 0, 0),
    YMGap.Continuum.ClusterCount4DProgress.Dir4.x0)

/-- The physical quaternion-block range of the corrected slab. -/
def correctedSlabLinkBlocks (extent : Nat) : List Nat :=
  List.range (boundaryCompleteSlabLinks extent).length

/-- Recover the link occupying one quaternion block.  The fallback is never
used on `correctedSlabLinkBlocks`. -/
def correctedSlabLinkAt (extent block : Nat) : SlabLink :=
  (boundaryCompleteSlabLinks extent).getD block
    correctedSlabFallbackLink

theorem correctedSlabLinkBlock_lt
    {extent block : Nat}
    (hblock : block ∈ correctedSlabLinkBlocks extent) :
    block < (boundaryCompleteSlabLinks extent).length := by
  exact List.mem_range.mp hblock

theorem correctedSlabLinkAt_mem
    {extent block : Nat}
    (hblock : block ∈ correctedSlabLinkBlocks extent) :
    correctedSlabLinkAt extent block ∈
      boundaryCompleteSlabLinks extent := by
  have hlt := correctedSlabLinkBlock_lt hblock
  have hmem :
      (boundaryCompleteSlabLinks extent)[block] ∈
        boundaryCompleteSlabLinks extent :=
    List.getElem_mem hlt
  have hget := List.getElem_eq_getD
    (l := boundaryCompleteSlabLinks extent)
    (i := block) (h := hlt) correctedSlabFallbackLink
  rw [hget] at hmem
  exact hmem

/-- Numerical block occupied by the reflected physical link. -/
def correctedSlabLinkReflectBlock (extent block : Nat) : Nat :=
  listIndexOf
    (timeReflectLink extent (correctedSlabLinkAt extent block))
    (boundaryCompleteSlabLinks extent)

theorem correctedSlabLinkReflectBlock_physical
    {extent block : Nat}
    (hblock : block ∈ correctedSlabLinkBlocks extent) :
    correctedSlabLinkReflectBlock extent block ∈
      correctedSlabLinkBlocks extent := by
  unfold correctedSlabLinkBlocks correctedSlabLinkReflectBlock
  apply List.mem_range.mpr
  apply listIndexOf_lt_of_mem
  exact timeReflectLink_mem_boundaryCompleteSlabLinks
    (correctedSlabLinkAt_mem hblock)

/-- Looking up the reflected block returns exactly the reflected link. -/
theorem correctedSlabLinkAt_reflectBlock
    {extent block : Nat}
    (hblock : block ∈ correctedSlabLinkBlocks extent) :
    correctedSlabLinkAt extent
        (correctedSlabLinkReflectBlock extent block) =
      timeReflectLink extent (correctedSlabLinkAt extent block) := by
  unfold correctedSlabLinkAt correctedSlabLinkReflectBlock
  exact getD_listIndexOf_of_mem
    correctedSlabFallbackLink
    (timeReflectLink extent
      ((boundaryCompleteSlabLinks extent).getD block
        correctedSlabFallbackLink))
    (boundaryCompleteSlabLinks extent)
    (timeReflectLink_mem_boundaryCompleteSlabLinks
      (correctedSlabLinkAt_mem hblock))

/-- Distinct physical blocks contain distinct links. -/
theorem correctedSlabLinkAt_injective_on_physical
    {extent left right : Nat}
    (hleft : left ∈ correctedSlabLinkBlocks extent)
    (hright : right ∈ correctedSlabLinkBlocks extent)
    (heq : correctedSlabLinkAt extent left =
      correctedSlabLinkAt extent right) :
    left = right := by
  have hleftLt := correctedSlabLinkBlock_lt hleft
  have hrightLt := correctedSlabLinkBlock_lt hright
  apply List.getElem?_inj hleftLt
    (boundaryCompleteSlabLinks_nodup extent)
  rw [List.getElem?_eq_getElem hleftLt,
    List.getElem?_eq_getElem hrightLt]
  have hleftGet := List.getElem_eq_getD
    (l := boundaryCompleteSlabLinks extent)
    (i := left) (h := hleftLt) correctedSlabFallbackLink
  have hrightGet := List.getElem_eq_getD
    (l := boundaryCompleteSlabLinks extent)
    (i := right) (h := hrightLt) correctedSlabFallbackLink
  change some ((boundaryCompleteSlabLinks extent)[left]) =
    some ((boundaryCompleteSlabLinks extent)[right])
  congr 1
  rw [hleftGet, hrightGet]
  exact heq

/-- The numerical block reflection is an involution on the entire physical
link range. -/
theorem correctedSlabLinkReflectBlock_involutive
    {extent block : Nat}
    (hblock : block ∈ correctedSlabLinkBlocks extent) :
    correctedSlabLinkReflectBlock extent
        (correctedSlabLinkReflectBlock extent block) = block := by
  have hreflected := correctedSlabLinkReflectBlock_physical hblock
  apply correctedSlabLinkAt_injective_on_physical
    (correctedSlabLinkReflectBlock_physical hreflected) hblock
  rw [correctedSlabLinkAt_reflectBlock hreflected,
    correctedSlabLinkAt_reflectBlock hblock]
  exact timeReflectLink_involutive extent
    (correctedSlabLinkAt extent block)
    (linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks
      (correctedSlabLinkAt_mem hblock))

/-- The literal slab-link reflection packaged as the exact block involution
required by the arbitrary product-Haar change-of-variables theorem. -/
def correctedSlabQuaternionBlockInvolution
    (extent : Nat) :
    QuaternionBlockInvolution
      (boundaryCompleteSlabLinks extent).length where
  map := correctedSlabLinkReflectBlock extent
  map_lt := by
    intro block hblock
    exact List.mem_range.mp
      (correctedSlabLinkReflectBlock_physical
        (List.mem_range.mpr hblock))
  involutive := by
    intro block hblock
    exact correctedSlabLinkReflectBlock_involutive
      (List.mem_range.mpr hblock)

/-! ## 2. The orientation-correct polynomial change of variables -/

/-- Time reflection preserves the coordinate direction of a positively
oriented link.  Its geometric orientation reversal in direction `x3` is
represented separately by quaternion conjugation. -/
theorem timeReflectLink_direction
    (extent : Nat) (link : SlabLink) :
    (timeReflectLink extent link).2 = link.2 := by
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := link
  cases direction <;> rfl

/-- Select precisely the three vector coordinates of every positive
time-link quaternion. -/
def correctedSlabTimeVectorCoordinate
    (extent coordinate : Nat) : Bool :=
  decide
    ((correctedSlabLinkAt extent (coordinate / 4)).2 =
        YMGap.Continuum.ClusterCount4DProgress.Dir4.x3 ∧
      coordinate % 4 ≠ 0)

/-- Literal pullback of a slab polynomial by time reflection: permute link
blocks and conjugate every positive time-link quaternion. -/
def reflectCorrectedSlabPolynomial
    (extent : Nat) (polynomial : RatPoly) : RatPoly :=
  signSelectedPolynomial
    (4 * (boundaryCompleteSlabLinks extent).length)
    (correctedSlabTimeVectorCoordinate extent)
    (reindexQuaternionPolynomial
      (correctedSlabQuaternionBlockInvolution extent)
      polynomial)

/-- The proof-facing block-involution pullback is definitionally the same
executable pullback used by the finite covariance checker. -/
private theorem reflectCorrectedSlabPolynomial_eq_finite
    (extent : Nat) (polynomial : RatPoly) :
    reflectCorrectedSlabPolynomial extent polynomial =
      YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.reflectPolynomial
        extent polynomial := by
  unfold reflectCorrectedSlabPolynomial
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.reflectPolynomial
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.reindexPolynomial
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.reindexExponents
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.timeVectorCoordinate
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.reflectBlock
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.linkAt
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.fallbackLink
    correctedSlabTimeVectorCoordinate correctedSlabLinkAt
    correctedSlabFallbackLink reindexQuaternionPolynomial
    reindexQuaternionExponents
  rfl

/-- Exact normalized product Haar is invariant under the full slab change
of variables, including time-link inversion. -/
theorem quaternionHaar_reflectCorrectedSlabPolynomial
    (extent : Nat) (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length polynomial) :
    quaternionHaar
        (boundaryCompleteSlabLinks extent).length
        (reflectCorrectedSlabPolynomial extent polynomial) ≈
      quaternionHaar
        (boundaryCompleteSlabLinks extent).length polynomial := by
  unfold reflectCorrectedSlabPolynomial
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_signSelected
      (boundaryCompleteSlabLinks extent).length
      (correctedSlabTimeVectorCoordinate extent)
      (reindexQuaternionPolynomial
        (correctedSlabQuaternionBlockInvolution extent)
        polynomial))
    (quaternionHaar_reindex
      (correctedSlabQuaternionBlockInvolution extent)
      polynomial hsupport)

theorem reflectCorrectedSlabPolynomial_add
    (extent : Nat) (left right : RatPoly) :
    reflectCorrectedSlabPolynomial extent (polyAdd left right) =
      polyAdd
        (reflectCorrectedSlabPolynomial extent left)
        (reflectCorrectedSlabPolynomial extent right) := by
  unfold reflectCorrectedSlabPolynomial
  rw [reindexQuaternionPolynomial_add,
    signSelectedPolynomial_add]

theorem reflectCorrectedSlabPolynomial_neg
    (extent : Nat) (polynomial : RatPoly) :
    reflectCorrectedSlabPolynomial extent (polyNeg polynomial) =
      polyNeg (reflectCorrectedSlabPolynomial extent polynomial) := by
  unfold reflectCorrectedSlabPolynomial
  rw [reindexQuaternionPolynomial_neg,
    signSelectedPolynomial_neg]

theorem reflectCorrectedSlabPolynomial_mul_prefix
    (extent : Nat) (left right : RatPoly) :
    QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks extent).length
      (reflectCorrectedSlabPolynomial extent (polyMul left right))
      (polyMul
        (reflectCorrectedSlabPolynomial extent left)
        (reflectCorrectedSlabPolynomial extent right)) := by
  unfold reflectCorrectedSlabPolynomial
  rw [reindexQuaternionPolynomial_mul]
  exact signSelectedPolynomial_mul_prefix
    (boundaryCompleteSlabLinks extent).length
    (correctedSlabTimeVectorCoordinate extent) _ _

theorem reflectCorrectedSlabPolynomial_smul_prefix
    (extent : Nat) (scale : Q') (polynomial : RatPoly) :
    QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks extent).length
      (reflectCorrectedSlabPolynomial extent
        (polySmul scale polynomial))
      (polySmul scale
        (reflectCorrectedSlabPolynomial extent polynomial)) := by
  unfold reflectCorrectedSlabPolynomial
  rw [reindexQuaternionPolynomial_smul]
  exact signSelectedPolynomial_smul_prefix
    (boundaryCompleteSlabLinks extent).length
    (correctedSlabTimeVectorCoordinate extent)
    scale _

/-- The full orientation-correct slab pullback carries every Peter--Weyl
character to the character of the pulled-back scalar polynomial. -/
theorem reflectCorrectedSlabPolynomial_character_prefix
    (extent : Nat) (scalar : RatPoly) (spin : Nat) :
    QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks extent).length
      (reflectCorrectedSlabPolynomial extent
        (characterPolynomial scalar spin))
      (characterPolynomial
        (reflectCorrectedSlabPolynomial extent scalar) spin) := by
  unfold reflectCorrectedSlabPolynomial
  exact QuaternionPrefixPolynomialEqv.trans
    (QuaternionPrefixPolynomialEqv.signSelected
      (correctedSlabTimeVectorCoordinate extent)
      (reindexQuaternionPolynomial_character_prefix
        (correctedSlabQuaternionBlockInvolution extent)
        scalar spin))
    (signSelectedPolynomial_character_prefix
      (boundaryCompleteSlabLinks extent).length
      (correctedSlabTimeVectorCoordinate extent)
      (reindexQuaternionPolynomial
        (correctedSlabQuaternionBlockInvolution extent) scalar)
      spin)

/-! ## 3. Exact six-plane plaquette covariance at extent one -/

private def sparseExponentCodeAux : Nat → List Nat → List Nat
  | _, [] => []
  | coordinate, exponent :: rest =>
      if exponent = 0 then
        sparseExponentCodeAux (coordinate + 1) rest
      else
        coordinate :: exponent ::
          sparseExponentCodeAux (coordinate + 1) rest

/-- A compact, collision-free-on-support coordinate/exponent code.  Every
plaquette monomial has degree at most four, so this replaces a 464-entry
dense key by at most eight naturals before ring normalization. -/
private def sparseExponentCode (monomial : List Nat) : List Nat :=
  sparseExponentCodeAux 0 monomial

private def sparseExponentAt : List Nat → Nat → Nat
  | coordinate :: exponent :: rest, target =>
      if coordinate = target then exponent
      else sparseExponentAt rest target
  | _, _ => 0

private theorem sparseExponentAt_codeAux :
    ∀ (monomial : List Nat) (offset target : Nat),
      sparseExponentAt
          (sparseExponentCodeAux offset monomial) target =
        if target < offset then 0
        else exponentAt monomial (target - offset)
  | [], offset, target => by
      simp [sparseExponentCodeAux, sparseExponentAt, exponentAt]
  | exponent :: rest, offset, target => by
      unfold sparseExponentCodeAux
      by_cases hexponent : exponent = 0
      · rw [if_pos hexponent,
          sparseExponentAt_codeAux rest (offset + 1) target]
        by_cases hlt : target < offset
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt]
          by_cases heq : target = offset
          · subst target
            rw [if_pos (by omega)]
            simp [exponentAt, hexponent]
          · rw [if_neg (by omega)]
            have hshift :
                target - offset =
                  (target - (offset + 1)) + 1 := by
              omega
            rw [hshift]
            simp [exponentAt]
      · rw [if_neg hexponent]
        unfold sparseExponentAt
        by_cases heq : offset = target
        · subst target
          rw [if_pos rfl, if_neg (by omega)]
          simp [exponentAt]
        · rw [if_neg heq,
            sparseExponentAt_codeAux rest (offset + 1) target]
          by_cases hlt : target < offset
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
            have hshift :
                target - offset =
                  (target - (offset + 1)) + 1 := by
              omega
            rw [hshift]
            simp [exponentAt]

private theorem sparseExponentAt_code
    (monomial : List Nat) (target : Nat) :
    sparseExponentAt (sparseExponentCode monomial) target =
      exponentAt monomial target := by
  unfold sparseExponentCode
  rw [sparseExponentAt_codeAux]
  simp

private def expandSparseExponentCode
    (coordinates : Nat) (code : List Nat) : List Nat :=
  List.ofFn fun coordinate : Fin coordinates =>
    sparseExponentAt code coordinate.val

private theorem expandSparseExponentCode_code
    {coordinates : Nat} {monomial : List Nat}
    (hlength : monomial.length = coordinates) :
    expandSparseExponentCode coordinates
        (sparseExponentCode monomial) = monomial := by
  apply natList_eq_of_length_getD
  · rw [hlength]
    exact List.length_ofFn
  · intro coordinate hcoordinate
    have hexpand :
        coordinate <
          (expandSparseExponentCode coordinates
            (sparseExponentCode monomial)).length := by
      exact hcoordinate
    rw [← List.getElem_eq_getD
        (l := expandSparseExponentCode coordinates
          (sparseExponentCode monomial))
        (i := coordinate) (h := hexpand) 0]
    unfold expandSparseExponentCode
    rw [List.getElem_ofFn, sparseExponentAt_code]
    rfl

private theorem canonicalQuaternionMonomial_exponentAt_supported_local
    (blocks : Nat) :
    ∀ (monomial : List Nat),
      monomial.length ≤ 4 * blocks →
      ∀ index,
        exponentAt
            (canonicalQuaternionMonomial blocks monomial) index =
          exponentAt monomial index := by
  induction blocks with
  | zero =>
      intro monomial hlength index
      have hnil : monomial = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      subst monomial
      simp [canonicalQuaternionMonomial, exponentAt]
  | succ blocks induction =>
      intro monomial hlength index
      cases index with
      | zero => simp [canonicalQuaternionMonomial, exponentAt]
      | succ index =>
          cases index with
          | zero => simp [canonicalQuaternionMonomial, exponentAt]
          | succ index =>
              cases index with
              | zero => simp [canonicalQuaternionMonomial, exponentAt]
              | succ index =>
                  cases index with
                  | zero => simp [canonicalQuaternionMonomial, exponentAt]
                  | succ index =>
                      change
                        exponentAt
                            (canonicalQuaternionMonomial blocks
                              (monomial.drop 4)) index =
                          exponentAt monomial (index + 4)
                      have hdropLength :
                          (monomial.drop 4).length ≤ 4 * blocks := by
                        simp only [List.length_drop]
                        omega
                      refine Eq.trans
                        (induction (monomial.drop 4)
                          hdropLength index) ?_
                      rw [exponentAt_drop monomial 4 index]
                      congr 1
                      omega

private theorem expandSparseExponentCode_code_canonical
    (blocks : Nat) (monomial : List Nat)
    (hsupport : monomial.length ≤ 4 * blocks) :
    expandSparseExponentCode (4 * blocks)
        (sparseExponentCode monomial) =
      canonicalQuaternionMonomial blocks monomial := by
  apply natList_eq_of_length_getD
  · rw [canonicalQuaternionMonomial_length]
    exact List.length_ofFn
  · intro coordinate hcoordinate
    have hlt : coordinate < 4 * blocks := by
      simpa only [expandSparseExponentCode, List.length_ofFn] using hcoordinate
    change
      exponentAt
          (expandSparseExponentCode (4 * blocks)
            (sparseExponentCode monomial)) coordinate =
        exponentAt
          (canonicalQuaternionMonomial blocks monomial) coordinate
    unfold exponentAt expandSparseExponentCode
    rw [← List.getElem_eq_getD
        (l := List.ofFn fun coordinate : Fin (4 * blocks) =>
          sparseExponentAt (sparseExponentCode monomial) coordinate.val)
        (i := coordinate) (h := by
          rw [List.length_ofFn]
          exact hlt) 0,
      List.getElem_ofFn, sparseExponentAt_code]
    exact
      (canonicalQuaternionMonomial_exponentAt_supported_local
        blocks monomial hsupport coordinate).symm

private def sparsePolynomialRaw (polynomial : RatPoly) : RawPoly :=
  polynomial.map fun term =>
    (sparseExponentCode term.1, term.2.num)

private def ratPolynomialIntegral (polynomial : RatPoly) : Bool :=
  polynomial.all fun term => term.2.denPred == 0

private theorem sparseExponentCodeAux_eq_finite :
    ∀ (offset : Nat) (monomial : List Nat),
      sparseExponentCodeAux offset monomial =
        YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.sparseCodeAux
          offset monomial
  | _, [] => rfl
  | offset, exponent :: rest => by
      unfold sparseExponentCodeAux
        YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.sparseCodeAux
      split
      · exact sparseExponentCodeAux_eq_finite (offset + 1) rest
      · rw [sparseExponentCodeAux_eq_finite (offset + 1) rest]

private theorem sparseExponentCode_eq_finite (monomial : List Nat) :
    sparseExponentCode monomial =
      YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.sparseCode
        monomial := by
  unfold sparseExponentCode
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.sparseCode
  exact sparseExponentCodeAux_eq_finite 0 monomial

private theorem sparsePolynomialRaw_eq_finite (polynomial : RatPoly) :
    sparsePolynomialRaw polynomial =
      YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.sparseRaw
        polynomial := by
  unfold sparsePolynomialRaw
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.sparseRaw
  apply List.map_congr_left
  intro term hterm
  rw [sparseExponentCode_eq_finite]

private theorem ratPolynomialIntegral_eq_finite (polynomial : RatPoly) :
    ratPolynomialIntegral polynomial =
      YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.integralCoefficients
        polynomial := by
  rfl

private theorem mappedRawToRatPoly_sparsePolynomialRaw_eq
    (coordinates : Nat) :
    ∀ polynomial : RatPoly,
      ratPolynomialIntegral polynomial = true →
      (∀ term, term ∈ polynomial →
        term.1.length = coordinates) →
      mappedRawToRatPoly
          (expandSparseExponentCode coordinates)
          (sparsePolynomialRaw polynomial) = polynomial
  | [], _, _ => rfl
  | term :: rest, hintegral, hlength => by
      obtain ⟨monomial, coefficient⟩ := term
      obtain ⟨numerator, denominator⟩ := coefficient
      simp only [ratPolynomialIntegral, List.all_cons,
        Bool.and_eq_true] at hintegral
      unfold sparsePolynomialRaw mappedRawToRatPoly
      simp only [List.map_cons]
      have hden : denominator = 0 :=
        LawfulBEq.eq_of_beq hintegral.1
      subst denominator
      have hrest :=
        mappedRawToRatPoly_sparsePolynomialRaw_eq coordinates rest
          hintegral.2
          (fun other hother =>
            hlength other
              (List.mem_cons_of_mem
                (monomial, ⟨numerator, 0⟩) hother))
      unfold sparsePolynomialRaw mappedRawToRatPoly at hrest
      rw [expandSparseExponentCode_code
          (hlength (monomial, ⟨numerator, 0⟩)
            List.mem_cons_self),
        hrest]
      rfl

private theorem mappedRawToRatPoly_sparsePolynomialRaw_eq_canonical
    (blocks : Nat) :
    ∀ polynomial : RatPoly,
      ratPolynomialIntegral polynomial = true →
      (∀ term, term ∈ polynomial →
        term.1.length ≤ 4 * blocks) →
      mappedRawToRatPoly
          (expandSparseExponentCode (4 * blocks))
          (sparsePolynomialRaw polynomial) =
        canonicalQuaternionPolynomial blocks polynomial
  | [], _, _ => rfl
  | term :: rest, hintegral, hsupport => by
      obtain ⟨monomial, coefficient⟩ := term
      obtain ⟨numerator, denominator⟩ := coefficient
      simp only [ratPolynomialIntegral, List.all_cons,
        Bool.and_eq_true] at hintegral
      unfold sparsePolynomialRaw mappedRawToRatPoly
        canonicalQuaternionPolynomial
      simp only [List.map_cons]
      have hden : denominator = 0 :=
        LawfulBEq.eq_of_beq hintegral.1
      subst denominator
      have hrest :=
        mappedRawToRatPoly_sparsePolynomialRaw_eq_canonical blocks rest
          hintegral.2
          (fun other hother =>
            hsupport other
              (List.mem_cons_of_mem
                (monomial, ⟨numerator, 0⟩) hother))
      unfold sparsePolynomialRaw mappedRawToRatPoly
        canonicalQuaternionPolynomial at hrest
      rw [expandSparseExponentCode_code_canonical blocks monomial
          (hsupport (monomial, ⟨numerator, 0⟩)
            List.mem_cons_self),
        hrest]
      rfl

/-- Compact checked data saying that two rational polynomial expansions have
integer coefficients and the same combined commutative normal form. -/
private structure SparseNormalCertificate
    (coordinates : Nat)
    (left right : RatPoly) where
  leftCode : RawPoly
  rightCode : RawPoly
  leftRaw :
    mappedRawToRatPoly
      (expandSparseExponentCode coordinates)
      leftCode = left
  rightRaw :
    mappedRawToRatPoly
      (expandSparseExponentCode coordinates)
      rightCode = right
  normal :
    canon leftCode = canon rightCode

/-- Equality in every arbitrary-insertion product-Haar row. -/
private def SlabHaarCarrierEqv
    (blocks : Nat) (left right : RatPoly) : Prop :=
  ∀ insertion : RatPoly,
    quaternionHaar blocks (polyMul insertion left) ≈
      quaternionHaar blocks (polyMul insertion right)

private theorem SlabHaarCarrierEqv.refl
    (blocks : Nat) (polynomial : RatPoly) :
    SlabHaarCarrierEqv blocks polynomial polynomial := by
  intro insertion
  exact Q'.eqv_refl _

private theorem SlabHaarCarrierEqv.trans
    {blocks : Nat} {first middle last : RatPoly}
    (hfirst : SlabHaarCarrierEqv blocks first middle)
    (hlast : SlabHaarCarrierEqv blocks middle last) :
    SlabHaarCarrierEqv blocks first last := by
  intro insertion
  exact Q'.eqv_trans _ _ _
    (hfirst insertion) (hlast insertion)

private theorem SlabHaarCarrierEqv.mul_left
    {blocks : Nat} (factor : RatPoly) {left right : RatPoly}
    (h : SlabHaarCarrierEqv blocks left right) :
    SlabHaarCarrierEqv blocks
      (polyMul factor left) (polyMul factor right) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion factor) left)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        blocks insertion factor left)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion factor) right)) _
    (h (polyMul insertion factor)) ?_
  exact quaternionHaar_polyMul_assoc
    blocks insertion factor right

private theorem SlabHaarCarrierEqv.mul_right
    {blocks : Nat} {left right : RatPoly}
    (h : SlabHaarCarrierEqv blocks left right)
    (factor : RatPoly) :
    SlabHaarCarrierEqv blocks
      (polyMul left factor) (polyMul right factor) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul insertion (polyMul factor left))) _
    (quaternionHaar_polyMul_middle_comm
      blocks insertion left factor) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion factor) left)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        blocks insertion factor left)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion factor) right)) _
    (h (polyMul insertion factor)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul insertion (polyMul factor right))) _
    (quaternionHaar_polyMul_assoc
      blocks insertion factor right) ?_
  exact quaternionHaar_polyMul_middle_comm
    blocks insertion factor right

private theorem SlabHaarCarrierEqv.mul_congr
    {blocks : Nat} {left left' right right' : RatPoly}
    (hleft : SlabHaarCarrierEqv blocks left left')
    (hright : SlabHaarCarrierEqv blocks right right') :
    SlabHaarCarrierEqv blocks
      (polyMul left right) (polyMul left' right') :=
  SlabHaarCarrierEqv.trans
    (SlabHaarCarrierEqv.mul_right hleft right)
    (SlabHaarCarrierEqv.mul_left left' hright)

private theorem SlabHaarCarrierEqv.add_right
    {blocks : Nat} {left right : RatPoly}
    (h : SlabHaarCarrierEqv blocks left right)
    (factor : RatPoly) :
    SlabHaarCarrierEqv blocks
      (polyAdd left factor) (polyAdd right factor) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul insertion left) +
      quaternionHaar blocks (polyMul insertion factor)) _
    (quaternionHaar_polyMul_add_right
      blocks insertion left factor) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul insertion right) +
      quaternionHaar blocks (polyMul insertion factor)) _
    (Q'.add_eqv_congr_right _ _ _ (h insertion)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_add_right
      blocks insertion right factor)

private theorem SlabHaarCarrierEqv.add_left
    {blocks : Nat} (factor : RatPoly) {left right : RatPoly}
    (h : SlabHaarCarrierEqv blocks left right) :
    SlabHaarCarrierEqv blocks
      (polyAdd factor left) (polyAdd factor right) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul insertion factor) +
      quaternionHaar blocks (polyMul insertion left)) _
    (quaternionHaar_polyMul_add_right
      blocks insertion factor left) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul insertion factor) +
      quaternionHaar blocks (polyMul insertion right)) _
    (Q'.add_eqv_congr_left _ _ _ (h insertion)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_add_right
      blocks insertion factor right)

private theorem SlabHaarCarrierEqv.add_congr
    {blocks : Nat} {left left' right right' : RatPoly}
    (hleft : SlabHaarCarrierEqv blocks left left')
    (hright : SlabHaarCarrierEqv blocks right right') :
    SlabHaarCarrierEqv blocks
      (polyAdd left right) (polyAdd left' right') :=
  SlabHaarCarrierEqv.trans
    (SlabHaarCarrierEqv.add_right hleft right)
    (SlabHaarCarrierEqv.add_left left' hright)

private theorem SlabHaarCarrierEqv.smul
    {blocks : Nat} (scale : Q') {left right : RatPoly}
    (h : SlabHaarCarrierEqv blocks left right) :
    SlabHaarCarrierEqv blocks
      (polySmul scale left) (polySmul scale right) := by
  intro insertion
  refine Q'.eqv_trans _
    (scale * quaternionHaar blocks (polyMul insertion left)) _
    (quaternionHaar_polyMul_smul_right
      blocks scale insertion left) ?_
  refine Q'.eqv_trans _
    (scale * quaternionHaar blocks (polyMul insertion right)) _
    (Q'.mul_eqv_congr_left scale _ _ (h insertion)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_smul_right
      blocks scale insertion right)

private theorem SlabHaarCarrierEqv.character
    {blocks : Nat} {left right : RatPoly}
    (h : SlabHaarCarrierEqv blocks left right) :
    ∀ spin,
      SlabHaarCarrierEqv blocks
        (characterPolynomial left spin)
        (characterPolynomial right spin)
  | 0 => SlabHaarCarrierEqv.refl blocks polyOne
  | 1 => SlabHaarCarrierEqv.smul 2 h
  | spin + 2 =>
      SlabHaarCarrierEqv.add_congr
        (SlabHaarCarrierEqv.mul_congr
          (SlabHaarCarrierEqv.smul 2 h)
          (SlabHaarCarrierEqv.character h (spin + 1)))
        (SlabHaarCarrierEqv.smul (-1)
          (SlabHaarCarrierEqv.character h spin))

private theorem SlabHaarCarrierEqv.haar
    {blocks : Nat} {left right : RatPoly}
    (h : SlabHaarCarrierEqv blocks left right) :
    quaternionHaar blocks left ≈ quaternionHaar blocks right := by
  have hleft :
      quaternionHaar blocks (polyMul polyOne left) ≈
        quaternionHaar blocks left :=
    Q'.eqv_trans _
      (quaternionHaar blocks (polyMul left polyOne)) _
      (quaternionHaar_polyMul_comm blocks polyOne left)
      (quaternionHaar_polyMul_one_right blocks left)
  have hright :
      quaternionHaar blocks (polyMul polyOne right) ≈
        quaternionHaar blocks right :=
    Q'.eqv_trans _
      (quaternionHaar blocks (polyMul right polyOne)) _
      (quaternionHaar_polyMul_comm blocks polyOne right)
      (quaternionHaar_polyMul_one_right blocks right)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ (h polyOne) hright)

private theorem slabHaarCarrierEqv_of_sparse_normal
    (blocks : Nat) {left right : RatPoly}
    (certificate : SparseNormalCertificate (4 * blocks) left right) :
    SlabHaarCarrierEqv blocks left right := by
  obtain ⟨leftCode, rightCode, hleftRaw, hrightRaw, hnormal⟩ :=
    certificate
  intro insertion
  rw [← hleftRaw, ← hrightRaw]
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul
        (mappedRawToRatPoly
          (expandSparseExponentCode (4 * blocks))
          leftCode) insertion)) _
    (quaternionHaar_polyMul_comm blocks insertion _) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul
        (mappedRawToRatPoly
          (expandSparseExponentCode (4 * blocks))
          (canon leftCode)) insertion)) _
    (Q'.eqv_symm
      (quaternionHaar_mapped_raw_canon_mul
        blocks (expandSparseExponentCode (4 * blocks))
        leftCode insertion)) ?_
  rw [hnormal]
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul
        (mappedRawToRatPoly
          (expandSparseExponentCode (4 * blocks))
          rightCode) insertion)) _
    (quaternionHaar_mapped_raw_canon_mul
      blocks (expandSparseExponentCode (4 * blocks))
      rightCode insertion) ?_
  exact quaternionHaar_polyMul_comm blocks _ insertion

private theorem reflectCorrectedSlabPolynomial_term_length
    (extent : Nat) (polynomial : RatPoly) :
    ∀ term,
      term ∈ reflectCorrectedSlabPolynomial extent polynomial →
        term.1.length =
          4 * (boundaryCompleteSlabLinks extent).length := by
  intro term hterm
  unfold reflectCorrectedSlabPolynomial
    signSelectedPolynomial signSelectedTerm
    reindexQuaternionPolynomial at hterm
  obtain ⟨reindexed, hreindexed, htermEq⟩ :=
    List.mem_map.mp hterm
  obtain ⟨source, hsource, hreindexedEq⟩ :=
    List.mem_map.mp hreindexed
  rw [← htermEq, ← hreindexedEq,
    reindexQuaternionExponents_length]

private theorem canonicalQuaternionPolynomial_term_length
    (blocks : Nat) (polynomial : RatPoly) :
    ∀ term,
      term ∈ canonicalQuaternionPolynomial blocks polynomial →
        term.1.length = 4 * blocks := by
  intro term hterm
  unfold canonicalQuaternionPolynomial at hterm
  obtain ⟨source, hsource, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq, canonicalQuaternionMonomial_length]

/-- Padding a monomial to the displayed quaternion carrier preserves every
coordinate inside that carrier, independently of any trailing source data. -/
private theorem canonicalQuaternionMonomial_prefix_exponent
    (blocks : Nat) : ∀ (monomial : List Nat) (coordinate : Nat),
      coordinate < 4 * blocks →
      exponentAt (canonicalQuaternionMonomial blocks monomial) coordinate =
        exponentAt monomial coordinate := by
  induction blocks with
  | zero =>
      intro monomial coordinate hcoordinate
      omega
  | succ blocks induction =>
      intro monomial coordinate hcoordinate
      cases coordinate with
      | zero => simp [canonicalQuaternionMonomial, exponentAt]
      | succ coordinate =>
          cases coordinate with
          | zero => simp [canonicalQuaternionMonomial, exponentAt]
          | succ coordinate =>
              cases coordinate with
              | zero => simp [canonicalQuaternionMonomial, exponentAt]
              | succ coordinate =>
                  cases coordinate with
                  | zero => simp [canonicalQuaternionMonomial, exponentAt]
                  | succ coordinate =>
                      change
                        exponentAt
                            (canonicalQuaternionMonomial blocks
                              (monomial.drop 4)) coordinate =
                          exponentAt monomial (coordinate + 4)
                      rw [induction (monomial.drop 4) coordinate (by omega),
                        exponentAt_drop]
                      congr 1
                      omega

/-- Canonical zero-padding is an exact termwise prefix equivalence. -/
private theorem canonicalQuaternionPolynomial_prefix
    (blocks : Nat) : ∀ polynomial : RatPoly,
      QuaternionPrefixPolynomialEqv blocks
        (canonicalQuaternionPolynomial blocks polynomial) polynomial
  | [] => .nil
  | term :: rest => by
      unfold canonicalQuaternionPolynomial
      simp only [List.map_cons]
      apply QuaternionPrefixPolynomialEqv.cons
      · exact ⟨Q'.eqv_refl _, fun coordinate hcoordinate =>
          canonicalQuaternionMonomial_prefix_exponent
            blocks term.1 coordinate hcoordinate⟩
      · exact canonicalQuaternionPolynomial_prefix blocks rest

private def correctedSlabPlaquetteScalarNormalCheck
    (face : SlabFace) : Bool :=
  YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.compactCovarianceCheck
    face

/-- Kernel-checked commutative ring covariance for every literal plaquette.
Coefficient-integrality and support are certified separately by
`allFacesSideCheck`, preventing repeated expansion during normalization. -/
theorem correctedSlabPlaquetteScalar_normal_check :
    (boundaryCompleteSlabPlaquettes 1).all
      correctedSlabPlaquetteScalarNormalCheck = true := by
  unfold correctedSlabPlaquetteScalarNormalCheck
  rw [YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlices_cover]
  simp only [List.all_append,
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice0_normal,
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice1_normal,
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice2_normal,
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice3_normal,
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice4_normal,
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice5_normal,
    Bool.and_self]

private def correctedSlabPlaquetteScalar_normal
    {face : SlabFace}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    SparseNormalCertificate
      (4 * (boundaryCompleteSlabLinks 1).length)
      (reflectCorrectedSlabPolynomial 1
        (correctedSlabPlaquettePolynomial 1 face).scalar)
      (canonicalQuaternionPolynomial
        (boundaryCompleteSlabLinks 1).length
        (correctedSlabPlaquettePolynomial 1
          (timeReflectPlaquette 1 face)).scalar) := by
  let source := (correctedSlabPlaquettePolynomial 1 face).scalar
  let target :=
    (correctedSlabPlaquettePolynomial 1
      (timeReflectPlaquette 1 face)).scalar
  have hcheck := List.all_eq_true.mp
    correctedSlabPlaquetteScalar_normal_check face hface
  have hside := List.all_eq_true.mp
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.allFacesSideCheck
      face hface
  unfold correctedSlabPlaquetteScalarNormalCheck
    YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.compactCovarianceCheck
    at hcheck
  unfold YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.compactSideCheck
    at hside
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hside
  have hsourceIntegral : ratPolynomialIntegral source = true := by
    rw [ratPolynomialIntegral_eq_finite]
    exact hside.1.1.1
  have htargetIntegral : ratPolynomialIntegral target = true := by
    rw [ratPolynomialIntegral_eq_finite]
    exact hside.1.1.2
  have htargetSupport :
      ∀ term, term ∈ target →
        term.1.length ≤
          4 * (boundaryCompleteSlabLinks 1).length := by
    intro term hterm
    have htargetSide := hside.2
    unfold YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.supportedCoordinates
      at htargetSide
    have hentry := List.all_eq_true.mp htargetSide term hterm
    exact of_decide_eq_true hentry
  have hreflectedIntegral :
      ratPolynomialIntegral
        (reflectCorrectedSlabPolynomial 1 source) = true := by
    rw [ratPolynomialIntegral_eq_finite,
      reflectCorrectedSlabPolynomial_eq_finite]
    rw [YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.integralCoefficients_reflectPolynomial]
    exact hsourceIntegral
  exact
    ⟨YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.compactReflectRaw
        1 source,
     sparsePolynomialRaw target,
     by
       rw [YMGap.Continuum.BF4ExactSlabVacuumReflectionFiniteCheck.compactReflectRaw_eq_sparse_reflect]
       rw [← reflectCorrectedSlabPolynomial_eq_finite,
         ← sparsePolynomialRaw_eq_finite]
       exact mappedRawToRatPoly_sparsePolynomialRaw_eq _ _
         hreflectedIntegral
         (reflectCorrectedSlabPolynomial_term_length 1 source),
     mappedRawToRatPoly_sparsePolynomialRaw_eq_canonical _ target
       htargetIntegral htargetSupport,
     by
       have hnormal := LawfulBEq.eq_of_beq hcheck
       rw [← sparsePolynomialRaw_eq_finite target] at hnormal
       exact hnormal⟩

private theorem correctedSlabPlaquetteScalar_carrier
    {face : SlabFace}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    SlabHaarCarrierEqv
      (boundaryCompleteSlabLinks 1).length
      (reflectCorrectedSlabPolynomial 1
        (correctedSlabPlaquettePolynomial 1 face).scalar)
      (canonicalQuaternionPolynomial
        (boundaryCompleteSlabLinks 1).length
        (correctedSlabPlaquettePolynomial 1
          (timeReflectPlaquette 1 face)).scalar) :=
  slabHaarCarrierEqv_of_sparse_normal _
    (correctedSlabPlaquetteScalar_normal hface)

private theorem getD_idxOf_of_mem_local
    {A : Type} [BEq A] [LawfulBEq A]
    (fallback target : A) (xs : List A)
    (hmem : target ∈ xs) :
    xs.getD (xs.idxOf target) fallback = target := by
  have hlt := List.idxOf_lt_length_of_mem hmem
  have hfound : xs[xs.idxOf target] == target := by
    exact List.findIdx_getElem (w := hlt)
  have heq : xs[xs.idxOf target] = target :=
    LawfulBEq.eq_of_beq hfound
  have hget := List.getElem_eq_getD
    (l := xs) (i := xs.idxOf target) (h := hlt) fallback
  rw [← hget]
  exact heq

private theorem reflected_face_label_eq
    (faceLabel : SlabFaceLabelling) {face : SlabFace}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    reflectSlabFaceLabelling 1 faceLabel
        ((boundaryCompleteSlabPlaquettes 1).idxOf
          (timeReflectPlaquette 1 face)) =
      faceLabel ((boundaryCompleteSlabPlaquettes 1).idxOf face) := by
  have hreflected :=
    timeReflectPlaquette_mem_boundaryCompleteSlab hface
  have hfaceIdPhysical :
      (boundaryCompleteSlabPlaquettes 1).idxOf face ∈
        slabPhysicalFaceEdges 1 :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hface)
  have hreflectedId :
      slabFaceReflectId 1
          ((boundaryCompleteSlabPlaquettes 1).idxOf face) =
        (boundaryCompleteSlabPlaquettes 1).idxOf
          (timeReflectPlaquette 1 face) := by
    apply slabPlaquetteAt_injective_on_physical
    · exact slabFaceReflectId_physical hfaceIdPhysical
    · exact List.mem_range.mpr
        (List.idxOf_lt_length_of_mem hreflected)
    · rw [slabPlaquetteAt_slabFaceReflectId hfaceIdPhysical]
      unfold slabPlaquetteAt
      rw [getD_idxOf_of_mem_local fallbackPlaquette face _ hface,
        getD_idxOf_of_mem_local fallbackPlaquette
          (timeReflectPlaquette 1 face) _ hreflected]
  unfold reflectSlabFaceLabelling
  rw [← hreflectedId,
    slabFaceReflectId_involutive hfaceIdPhysical]

/-- The intermediate factor obtained by applying the exact link-variable
reflection while retaining the source face identifier. -/
def correctedSlabCovariantPlaquetteSpinFactor
    (faceLabel : SlabFaceLabelling) (face : SlabFace) : RatPoly :=
  characterPolynomial
    (reflectCorrectedSlabPolynomial 1
      (correctedSlabPlaquettePolynomial 1 face).scalar)
    (faceLabel ((boundaryCompleteSlabPlaquettes 1).idxOf face))

/-- The same reflected factor with every monomial padded to the full slab
quaternion prefix.  This is the exact syntactic bridge between temporal-word
permutation and the unpadded geometric factor. -/
def correctedSlabCanonicalReflectedPlaquetteSpinFactor
    (faceLabel : SlabFaceLabelling) (face : SlabFace) : RatPoly :=
  characterPolynomial
    (canonicalQuaternionPolynomial
      (boundaryCompleteSlabLinks 1).length
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 face)).scalar)
    (reflectSlabFaceLabelling 1 faceLabel
      ((boundaryCompleteSlabPlaquettes 1).idxOf
        (timeReflectPlaquette 1 face)))

/-- Reflection commutes with the all-spin character recursion up to the
prefix relation generated by exact rational coefficient equivalence. -/
theorem correctedSlabPlaquetteSpinFactor_reflection_prefix
    (faceLabel : SlabFaceLabelling) (face : SlabFace) :
    QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks 1).length
      (reflectCorrectedSlabPolynomial 1
        (correctedSlabPlaquetteSpinFactor 1 faceLabel face))
      (correctedSlabCovariantPlaquetteSpinFactor faceLabel face) := by
  unfold correctedSlabPlaquetteSpinFactor
    correctedSlabCovariantPlaquetteSpinFactor
  exact reflectCorrectedSlabPolynomial_character_prefix 1
    (correctedSlabPlaquettePolynomial 1 face).scalar
    (faceLabel ((boundaryCompleteSlabPlaquettes 1).idxOf face))

/-- The covariant factor and the canonically padded geometrically reflected
factor define the same arbitrary-insertion Haar row.  The load-bearing
identity is the checked commutative normal form of the cyclic-inverse
plaquette word, lifted through the all-spin character recursion. -/
theorem correctedSlabCovariantPlaquetteSpinFactor_carrier
    (faceLabel : SlabFaceLabelling) {face : SlabFace}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    SlabHaarCarrierEqv
      (boundaryCompleteSlabLinks 1).length
      (correctedSlabCovariantPlaquetteSpinFactor faceLabel face)
      (correctedSlabCanonicalReflectedPlaquetteSpinFactor
        faceLabel face) := by
  unfold correctedSlabCovariantPlaquetteSpinFactor
    correctedSlabCanonicalReflectedPlaquetteSpinFactor
  rw [reflected_face_label_eq faceLabel hface]
  exact SlabHaarCarrierEqv.character
    (correctedSlabPlaquetteScalar_carrier hface) _

theorem correctedSlabCanonicalReflectedPlaquetteSpinFactor_prefix
    (faceLabel : SlabFaceLabelling) (face : SlabFace) :
    QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks 1).length
      (correctedSlabCanonicalReflectedPlaquetteSpinFactor
        faceLabel face)
      (correctedSlabPlaquetteSpinFactor 1
        (reflectSlabFaceLabelling 1 faceLabel)
        (timeReflectPlaquette 1 face)) := by
  unfold correctedSlabCanonicalReflectedPlaquetteSpinFactor
    correctedSlabPlaquetteSpinFactor
  exact QuaternionPrefixPolynomialEqv.character
    (canonicalQuaternionPolynomial_prefix
      (boundaryCompleteSlabLinks 1).length
      (correctedSlabPlaquettePolynomial 1
        (timeReflectPlaquette 1 face)).scalar) _

/-- Face-product in the order inherited from reflecting the original list.
The next permutation step compares it with the canonical slab-face order. -/
def exactCorrectedSlabReflectedOrderedIntegrand
    (faceLabel : SlabFaceLabelling) : RatPoly :=
  (boundaryCompleteSlabPlaquettes 1).foldr
    (fun face total =>
      polyMul
        (correctedSlabPlaquetteSpinFactor 1
          (reflectSlabFaceLabelling 1 faceLabel)
          (timeReflectPlaquette 1 face))
        total)
    polyOne

/-- Face product immediately after the link-variable pullback and before
the exact temporal-word term permutations. -/
def exactCorrectedSlabCovariantOrderedIntegrand
    (faceLabel : SlabFaceLabelling) : RatPoly :=
  (boundaryCompleteSlabPlaquettes 1).foldr
    (fun face total =>
      polyMul
        (correctedSlabCovariantPlaquetteSpinFactor faceLabel face)
        total)
    polyOne

def exactCorrectedSlabCanonicalReflectedOrderedIntegrand
    (faceLabel : SlabFaceLabelling) : RatPoly :=
  (boundaryCompleteSlabPlaquettes 1).foldr
    (fun face total =>
      polyMul
        (correctedSlabCanonicalReflectedPlaquetteSpinFactor
          faceLabel face)
        total)
    polyOne

private theorem reflectedSpinNetworkFold_prefix
    (faceLabel : SlabFaceLabelling) :
    ∀ faces : List SlabFace,
      (∀ face, face ∈ faces →
        face ∈ boundaryCompleteSlabPlaquettes 1) →
      QuaternionPrefixPolynomialEqv
        (boundaryCompleteSlabLinks 1).length
        (reflectCorrectedSlabPolynomial 1
          (faces.foldr
            (fun face total =>
              polyMul
                (correctedSlabPlaquetteSpinFactor
                  1 faceLabel face)
                total)
            polyOne))
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabCovariantPlaquetteSpinFactor faceLabel face)
              total)
          polyOne)
  | [], _ => by
      simpa only [List.foldr] using
        (reflectCorrectedSlabPolynomial_character_prefix
          1 polyZero 0)
  | face :: rest, hfaces => by
      simp only [List.foldr]
      refine QuaternionPrefixPolynomialEqv.trans
        (reflectCorrectedSlabPolynomial_mul_prefix 1
          (correctedSlabPlaquetteSpinFactor 1 faceLabel face)
          (rest.foldr
            (fun next total =>
              polyMul
                (correctedSlabPlaquetteSpinFactor
                  1 faceLabel next)
                total)
            polyOne)) ?_
      exact QuaternionPrefixPolynomialEqv.mul
        (correctedSlabPlaquetteSpinFactor_reflection_prefix
          faceLabel face)
        (reflectedSpinNetworkFold_prefix faceLabel rest
          (fun next hnext =>
            hfaces next (List.mem_cons_of_mem face hnext)))

/-- The complete transformed all-spin network is the same reflected
face-product, before the harmless permutation back to canonical face order. -/
theorem exactCorrectedSlabSpinNetworkIntegrand_reflection_prefix
    (faceLabel : SlabFaceLabelling) :
    QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks 1).length
      (reflectCorrectedSlabPolynomial 1
        (exactCorrectedSlabSpinNetworkIntegrand 1 faceLabel))
      (exactCorrectedSlabCovariantOrderedIntegrand faceLabel) := by
  unfold exactCorrectedSlabSpinNetworkIntegrand
    exactCorrectedSlabCovariantOrderedIntegrand
  exact reflectedSpinNetworkFold_prefix faceLabel
    (boundaryCompleteSlabPlaquettes 1)
    (fun face hface => hface)

private theorem covariantReflectedFold_carrier
    (faceLabel : SlabFaceLabelling) :
    ∀ faces : List SlabFace,
      (∀ face, face ∈ faces →
        face ∈ boundaryCompleteSlabPlaquettes 1) →
      SlabHaarCarrierEqv
        (boundaryCompleteSlabLinks 1).length
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabCovariantPlaquetteSpinFactor
                faceLabel face)
              total)
          polyOne)
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabCanonicalReflectedPlaquetteSpinFactor
                faceLabel face)
              total)
          polyOne)
  | [], _ => SlabHaarCarrierEqv.refl _ polyOne
  | face :: rest, hfaces => by
      simp only [List.foldr]
      exact SlabHaarCarrierEqv.mul_congr
        (correctedSlabCovariantPlaquetteSpinFactor_carrier
          faceLabel (hfaces face List.mem_cons_self))
        (covariantReflectedFold_carrier faceLabel rest
          (fun next hnext =>
            hfaces next (List.mem_cons_of_mem face hnext)))

theorem exactCorrectedSlabCovariantOrderedIntegrand_carrier
    (faceLabel : SlabFaceLabelling) :
    SlabHaarCarrierEqv
      (boundaryCompleteSlabLinks 1).length
      (exactCorrectedSlabCovariantOrderedIntegrand faceLabel)
      (exactCorrectedSlabCanonicalReflectedOrderedIntegrand
        faceLabel) := by
  unfold exactCorrectedSlabCovariantOrderedIntegrand
    exactCorrectedSlabCanonicalReflectedOrderedIntegrand
  exact covariantReflectedFold_carrier faceLabel
    (boundaryCompleteSlabPlaquettes 1)
    (fun face hface => hface)

private theorem canonicalReflectedFold_prefix
    (faceLabel : SlabFaceLabelling) :
    ∀ faces : List SlabFace,
      QuaternionPrefixPolynomialEqv
        (boundaryCompleteSlabLinks 1).length
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabCanonicalReflectedPlaquetteSpinFactor
                faceLabel face)
              total)
          polyOne)
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor 1
                (reflectSlabFaceLabelling 1 faceLabel)
                (timeReflectPlaquette 1 face))
              total)
          polyOne)
  | [] => QuaternionPrefixPolynomialEqv.refl _ polyOne
  | face :: rest => by
      simp only [List.foldr]
      exact QuaternionPrefixPolynomialEqv.mul
        (correctedSlabCanonicalReflectedPlaquetteSpinFactor_prefix
          faceLabel face)
        (canonicalReflectedFold_prefix faceLabel rest)

theorem exactCorrectedSlabCanonicalReflectedOrderedIntegrand_prefix
    (faceLabel : SlabFaceLabelling) :
    QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks 1).length
      (exactCorrectedSlabCanonicalReflectedOrderedIntegrand faceLabel)
      (exactCorrectedSlabReflectedOrderedIntegrand faceLabel) := by
  unfold exactCorrectedSlabCanonicalReflectedOrderedIntegrand
    exactCorrectedSlabReflectedOrderedIntegrand
  exact canonicalReflectedFold_prefix faceLabel
    (boundaryCompleteSlabPlaquettes 1)

/-! ## 4. Syntactic support of the literal slab integrand -/

private theorem supported_polyZero
    (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyZero := by
  intro term hterm
  simp [polyZero] at hterm

private theorem supported_polyOne
    (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons, List.not_mem_nil,
    or_false] at hterm
  subst term
  simp

private theorem supported_polyVar
    {blocks coordinate : Nat}
    (hcoordinate : coordinate < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar coordinate) := by
  intro term hterm
  simp only [polyVar, List.mem_cons, List.not_mem_nil,
    or_false] at hterm
  subst term
  simp [YMGap.Continuum.RingNormaliser.varMono]
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

private theorem supportedPolyQuaternion_one
    (blocks : Nat) :
    SupportedPolyQuaternion blocks PolyQuaternion.one := by
  exact ⟨supported_polyOne blocks,
    supported_polyZero blocks,
    supported_polyZero blocks,
    supported_polyZero blocks⟩

private theorem supportedPolyQuaternion_coordinateVariable
    {blocks block : Nat} (hblock : block < blocks) :
    SupportedPolyQuaternion blocks
      (PolyQuaternion.coordinateVariable block) := by
  constructor <;> apply supported_polyVar <;> omega

private theorem supportedPolyQuaternion_conj
    {blocks : Nat} {quaternion : PolyQuaternion}
    (hsupport : SupportedPolyQuaternion blocks quaternion) :
    SupportedPolyQuaternion blocks
      (PolyQuaternion.conj quaternion) := by
  exact ⟨hsupport.scalar,
    supported_polyNeg hsupport.iPart,
    supported_polyNeg hsupport.jPart,
    supported_polyNeg hsupport.kPart⟩

private theorem supportedPolyQuaternion_mul
    {blocks : Nat} {left right : PolyQuaternion}
    (hleft : SupportedPolyQuaternion blocks left)
    (hright : SupportedPolyQuaternion blocks right) :
    SupportedPolyQuaternion blocks
      (PolyQuaternion.mul left right) := by
  constructor
  · apply supported_polyAdd
    · exact supported_polyMul hleft.scalar hright.scalar
    · apply supported_polyNeg
      apply supported_polyAdd
      · exact supported_polyMul hleft.iPart hright.iPart
      · apply supported_polyAdd
        · exact supported_polyMul hleft.jPart hright.jPart
        · exact supported_polyMul hleft.kPart hright.kPart
  · apply supported_polyAdd
    · exact supported_polyMul hleft.scalar hright.iPart
    · apply supported_polyAdd
      · exact supported_polyMul hleft.iPart hright.scalar
      · apply supported_polyAdd
        · exact supported_polyMul hleft.jPart hright.kPart
        · exact supported_polyNeg
            (supported_polyMul hleft.kPart hright.jPart)
  · apply supported_polyAdd
    · exact supported_polyMul hleft.scalar hright.jPart
    · apply supported_polyAdd
      · exact supported_polyMul hleft.jPart hright.scalar
      · apply supported_polyAdd
        · exact supported_polyMul hleft.kPart hright.iPart
        · exact supported_polyNeg
            (supported_polyMul hleft.iPart hright.kPart)
  · apply supported_polyAdd
    · exact supported_polyMul hleft.scalar hright.kPart
    · apply supported_polyAdd
      · exact supported_polyMul hleft.kPart hright.scalar
      · apply supported_polyAdd
        · exact supported_polyMul hleft.iPart hright.jPart
        · exact supported_polyNeg
            (supported_polyMul hleft.jPart hright.iPart)

private theorem correctedSlabLinkPolynomial_supported
    (extent : Nat) (link : SlabLink) :
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
    (extent : Nat) :
    ∀ (entries : List OrientedBF4Link) (total : PolyQuaternion),
      SupportedPolyQuaternion
        (boundaryCompleteSlabLinks extent).length total →
      SupportedPolyQuaternion
        (boundaryCompleteSlabLinks extent).length
        (entries.foldl
          (fun current entry =>
            PolyQuaternion.mul current
              (orientedCorrectedSlabLinkPolynomial extent entry))
          total)
  | [], total, htotal => htotal
  | entry :: rest, total, htotal => by
      simp only [List.foldl_cons]
      exact correctedSlabPlaquetteFold_supported extent rest _
        (supportedPolyQuaternion_mul htotal
          (orientedCorrectedSlabLinkPolynomial_supported extent entry))

private theorem correctedSlabPlaquettePolynomial_supported
    (extent : Nat) (face : SlabFace) :
    SupportedPolyQuaternion
      (boundaryCompleteSlabLinks extent).length
      (correctedSlabPlaquettePolynomial extent face) := by
  unfold correctedSlabPlaquettePolynomial
  exact correctedSlabPlaquetteFold_supported extent
    (orientedPlaquetteBoundary face) PolyQuaternion.one
    (supportedPolyQuaternion_one _)

private theorem characterPolynomial_supported
    {blocks : Nat} {scalar : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks scalar) :
    ∀ spin,
      SupportedQuaternionBlocks blocks
        (characterPolynomial scalar spin)
  | 0 => supported_polyOne blocks
  | 1 => supported_polySmul hsupport
  | spin + 2 => by
      apply supported_polyAdd
      · apply supported_polyMul
        · exact supported_polySmul hsupport
        · exact characterPolynomial_supported hsupport (spin + 1)
      · exact supported_polySmul
          (characterPolynomial_supported hsupport spin)

private theorem correctedSlabPlaquetteSpinFactor_supported
    (extent : Nat) (faceLabel : SlabFaceLabelling)
    (face : SlabFace) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length
      (correctedSlabPlaquetteSpinFactor extent faceLabel face) := by
  exact characterPolynomial_supported
    (correctedSlabPlaquettePolynomial_supported extent face).scalar _

private theorem correctedSlabSpinNetworkFold_supported
    (extent : Nat) (faceLabel : SlabFaceLabelling) :
    ∀ faces : List SlabFace,
      SupportedQuaternionBlocks
        (boundaryCompleteSlabLinks extent).length
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor
                extent faceLabel face)
              total)
          polyOne)
  | [] => supported_polyOne _
  | face :: rest =>
      supported_polyMul
        (correctedSlabPlaquetteSpinFactor_supported
          extent faceLabel face)
        (correctedSlabSpinNetworkFold_supported
          extent faceLabel rest)

/-- Public per-face support interface for downstream finite-carrier
contractors.  The implementation remains the literal corrected-slab
plaquette polynomial above. -/
theorem correctedSlabPlaquetteSpinFactor_support
    (extent : Nat) (faceLabel : SlabFaceLabelling)
    (face : SlabFace) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length
      (correctedSlabPlaquetteSpinFactor extent faceLabel face) :=
  correctedSlabPlaquetteSpinFactor_supported extent faceLabel face

/-- Any sublist of corrected-slab faces has a supported literal factor
fold.  This is the support input needed after spin-zero faces are removed
before a factorized Haar contraction. -/
theorem correctedSlabSpinNetworkFaces_support
    (extent : Nat) (faceLabel : SlabFaceLabelling)
    (faces : List SlabFace) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length
      (faces.foldr
        (fun face total =>
          polyMul
            (correctedSlabPlaquetteSpinFactor
              extent faceLabel face)
            total)
        polyOne) :=
  correctedSlabSpinNetworkFold_supported extent faceLabel faces

/-- The literal 24-face fixed-plane insertion is supported on exactly the
same 116 quaternion blocks as the complete corrected slab.  This public
support theorem is the finite-carrier input to selected-link Fubini. -/
theorem exactCorrectedSlabInteriorInsertion_supported
    (faceLabel : SlabFaceLabelling) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks 1).length
      (exactCorrectedSlabInteriorInsertion faceLabel) := by
  unfold exactCorrectedSlabInteriorInsertion
  exact correctedSlabSpinNetworkFold_supported 1 faceLabel
    exactCorrectedSlabFixedFaces

/-- Every term of the literal all-spin slab network is supported on the
displayed finite link carrier. -/
theorem exactCorrectedSlabSpinNetworkIntegrand_supported
    (extent : Nat) (faceLabel : SlabFaceLabelling) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length
      (exactCorrectedSlabSpinNetworkIntegrand extent faceLabel) := by
  unfold exactCorrectedSlabSpinNetworkIntegrand
  exact correctedSlabSpinNetworkFold_supported extent faceLabel
    (boundaryCompleteSlabPlaquettes extent)

private theorem reflectCorrectedSlabPolynomial_supported
    (extent : Nat) (polynomial : RatPoly) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length
      (reflectCorrectedSlabPolynomial extent polynomial) := by
  intro term hterm
  unfold reflectCorrectedSlabPolynomial
    signSelectedPolynomial signSelectedTerm
    reindexQuaternionPolynomial at hterm
  obtain ⟨reindexed, hreindexed, htermEq⟩ := List.mem_map.mp hterm
  obtain ⟨source, hsource, hreindexedEq⟩ := List.mem_map.mp hreindexed
  rw [← htermEq, ← hreindexedEq,
    reindexQuaternionExponents_length]
  exact Nat.le_refl _

private theorem covariantPlaquetteSpinFactor_supported
    (faceLabel : SlabFaceLabelling) (face : SlabFace) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks 1).length
      (correctedSlabCovariantPlaquetteSpinFactor faceLabel face) := by
  unfold correctedSlabCovariantPlaquetteSpinFactor
  exact characterPolynomial_supported
    (reflectCorrectedSlabPolynomial_supported 1
      (correctedSlabPlaquettePolynomial 1 face).scalar) _

private theorem covariantOrderedFold_supported
    (faceLabel : SlabFaceLabelling) :
    ∀ faces : List SlabFace,
      SupportedQuaternionBlocks
        (boundaryCompleteSlabLinks 1).length
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabCovariantPlaquetteSpinFactor
                faceLabel face)
              total)
          polyOne)
  | [] => supported_polyOne _
  | face :: rest =>
      supported_polyMul
        (covariantPlaquetteSpinFactor_supported faceLabel face)
        (covariantOrderedFold_supported faceLabel rest)

private theorem exactCorrectedSlabCovariantOrderedIntegrand_supported
    (faceLabel : SlabFaceLabelling) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks 1).length
      (exactCorrectedSlabCovariantOrderedIntegrand faceLabel) := by
  unfold exactCorrectedSlabCovariantOrderedIntegrand
  exact covariantOrderedFold_supported faceLabel
    (boundaryCompleteSlabPlaquettes 1)

private theorem canonicalReflectedPlaquetteSpinFactor_supported
    (faceLabel : SlabFaceLabelling) (face : SlabFace) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks 1).length
      (correctedSlabCanonicalReflectedPlaquetteSpinFactor
        faceLabel face) := by
  unfold correctedSlabCanonicalReflectedPlaquetteSpinFactor
  exact characterPolynomial_supported
    (canonicalQuaternionPolynomial_supported _ _) _

private theorem canonicalReflectedOrderedFold_supported
    (faceLabel : SlabFaceLabelling) :
    ∀ faces : List SlabFace,
      SupportedQuaternionBlocks
        (boundaryCompleteSlabLinks 1).length
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabCanonicalReflectedPlaquetteSpinFactor
                faceLabel face)
              total)
          polyOne)
  | [] => supported_polyOne _
  | face :: rest =>
      supported_polyMul
        (canonicalReflectedPlaquetteSpinFactor_supported
          faceLabel face)
        (canonicalReflectedOrderedFold_supported faceLabel rest)

/-- The literal link reflection always returns a polynomial on the finite slab carrier. -/
theorem reflectCorrectedSlabPolynomial_support (extent : Nat) (polynomial : RatPoly) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (reflectCorrectedSlabPolynomial extent polynomial) :=
  reflectCorrectedSlabPolynomial_supported extent polynomial

/-- All-spin geometric reflection with any spectator on the SAME physical link carrier.
The cyclic-inverse word identity is retained under the Haar integral; no positivity is used. -/
theorem correctedSlabPlaquetteSpinFactor_reflection_insert
    (faceLabel : SlabFaceLabelling) {face : SlabFace}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1)
    (insertion : RatPoly)
    (hsupport : SupportedQuaternionBlocks (boundaryCompleteSlabLinks 1).length insertion) :
    quaternionHaar (boundaryCompleteSlabLinks 1).length
        (polyMul insertion (reflectCorrectedSlabPolynomial 1
          (correctedSlabPlaquetteSpinFactor 1 faceLabel face))) ≈
      quaternionHaar (boundaryCompleteSlabLinks 1).length
        (polyMul insertion (correctedSlabPlaquetteSpinFactor 1
          (reflectSlabFaceLabelling 1 faceLabel) (timeReflectPlaquette 1 face))) := by
  refine Q'.eqv_trans _ _ _
    (quaternionHaar_prefixPolynomialEqv _
      (QuaternionPrefixPolynomialEqv.mul (QuaternionPrefixPolynomialEqv.refl _ insertion)
        (correctedSlabPlaquetteSpinFactor_reflection_prefix faceLabel face))
      (supported_polyMul hsupport (reflectCorrectedSlabPolynomial_supported 1 _))
      (supported_polyMul hsupport (covariantPlaquetteSpinFactor_supported faceLabel face))) ?_
  refine Q'.eqv_trans _ _ _
    (correctedSlabCovariantPlaquetteSpinFactor_carrier faceLabel hface insertion) ?_
  exact quaternionHaar_prefixPolynomialEqv _
    (QuaternionPrefixPolynomialEqv.mul (QuaternionPrefixPolynomialEqv.refl _ insertion)
      (correctedSlabCanonicalReflectedPlaquetteSpinFactor_prefix faceLabel face))
    (supported_polyMul hsupport (canonicalReflectedPlaquetteSpinFactor_supported faceLabel face))
    (supported_polyMul hsupport (correctedSlabPlaquetteSpinFactor_supported 1 _ _))

private theorem exactCorrectedSlabCanonicalReflectedOrderedIntegrand_supported
    (faceLabel : SlabFaceLabelling) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks 1).length
      (exactCorrectedSlabCanonicalReflectedOrderedIntegrand faceLabel) := by
  unfold exactCorrectedSlabCanonicalReflectedOrderedIntegrand
  exact canonicalReflectedOrderedFold_supported faceLabel
    (boundaryCompleteSlabPlaquettes 1)

private theorem reflectedOrderedFold_supported
    (faceLabel : SlabFaceLabelling) :
    ∀ faces : List SlabFace,
      SupportedQuaternionBlocks
        (boundaryCompleteSlabLinks 1).length
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor 1
                (reflectSlabFaceLabelling 1 faceLabel)
                (timeReflectPlaquette 1 face))
              total)
          polyOne)
  | [] => supported_polyOne _
  | face :: rest =>
      supported_polyMul
        (correctedSlabPlaquetteSpinFactor_supported 1
          (reflectSlabFaceLabelling 1 faceLabel)
          (timeReflectPlaquette 1 face))
        (reflectedOrderedFold_supported faceLabel rest)

private theorem exactCorrectedSlabReflectedOrderedIntegrand_supported
    (faceLabel : SlabFaceLabelling) :
    SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks 1).length
      (exactCorrectedSlabReflectedOrderedIntegrand faceLabel) := by
  unfold exactCorrectedSlabReflectedOrderedIntegrand
  exact reflectedOrderedFold_supported faceLabel
    (boundaryCompleteSlabPlaquettes 1)

private theorem quaternionHaar_polyMul_one_left
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks (polyMul polyOne polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact Q'.eqv_trans _
    (quaternionHaar blocks (polyMul polynomial polyOne)) _
    (quaternionHaar_polyMul_comm blocks polyOne polynomial)
    (quaternionHaar_polyMul_one_right blocks polynomial)

/-- Exact product Haar is insensitive to the syntactic order of polynomial
terms.  This is the analytic consumer of the cyclic-inverse plaquette-word
permutation above. -/
private theorem quaternionHaar_perm
    (blocks : Nat) {left right : RatPoly}
    (hperm : left.Perm right) :
    quaternionHaar blocks left ≈ quaternionHaar blocks right := by
  induction hperm with
  | nil => exact Q'.eqv_refl 0
  | cons term hperm induction =>
      change
        term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks _ ≈
          term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks _
      exact Q'.add_eqv_congr_left _ _ _ induction
  | swap first second rest =>
      let firstValue :=
        first.2 * quaternionHaarMono blocks first.1
      let secondValue :=
        second.2 * quaternionHaarMono blocks second.1
      let tailValue := quaternionHaar blocks rest
      change secondValue + (firstValue + tailValue) ≈
        firstValue + (secondValue + tailValue)
      exact Q'.eqv_trans _ ((secondValue + firstValue) + tailValue) _
        (Q'.eqv_symm
          (Q'.add_assoc_eqv secondValue firstValue tailValue))
        (Q'.eqv_trans _ ((firstValue + secondValue) + tailValue) _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.add_comm_eqv secondValue firstValue))
          (Q'.add_assoc_eqv firstValue secondValue tailValue))
  | trans hfirst hsecond inductionFirst inductionSecond =>
      exact Q'.eqv_trans _ _ _ inductionFirst inductionSecond

private theorem exactCorrectedSlabReflectedOrderedIntegrand_haar_eq
    (faceLabel : SlabFaceLabelling) :
    quaternionHaar (boundaryCompleteSlabLinks 1).length
        (exactCorrectedSlabReflectedOrderedIntegrand faceLabel) ≈
      quaternionHaar (boundaryCompleteSlabLinks 1).length
        (exactCorrectedSlabSpinNetworkIntegrand 1
          (reflectSlabFaceLabelling 1 faceLabel)) := by
  let factor : SlabFace → RatPoly := fun face =>
    correctedSlabPlaquetteSpinFactor 1
      (reflectSlabFaceLabelling 1 faceLabel) face
  have hperm := timeReflect_boundaryCompleteSlabPlaquettes_perm 1
  have hcarrier := quaternionHaar_factorFold_perm
    (boundaryCompleteSlabLinks 1).length factor hperm polyOne
  have honeLeft := quaternionHaar_polyMul_one_left
    (boundaryCompleteSlabLinks 1).length
    ((boundaryCompleteSlabPlaquettes 1).map
      (timeReflectPlaquette 1) |>.foldr
        (fun face total => polyMul (factor face) total) polyOne)
  have honeRight := quaternionHaar_polyMul_one_left
    (boundaryCompleteSlabLinks 1).length
    ((boundaryCompleteSlabPlaquettes 1).foldr
      (fun face total => polyMul (factor face) total) polyOne)
  unfold exactCorrectedSlabReflectedOrderedIntegrand
    exactCorrectedSlabSpinNetworkIntegrand
  rw [← List.foldr_map]
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm honeLeft)
    (Q'.eqv_trans _ _ _ hcarrier honeRight)

/-- **Exact signed-network reflection symmetry.**  Reflecting every face
label of the literal 72-face/116-link slab leaves its complete normalized
Haar contraction unchanged. -/
theorem exactCorrectedSlabHaarCoefficient_reflection
    (faceLabel : SlabFaceLabelling) :
    exactCorrectedSlabHaarCoefficient 1 faceLabel ≈
      exactCorrectedSlabHaarCoefficient 1
        (reflectSlabFaceLabelling 1 faceLabel) := by
  unfold exactCorrectedSlabHaarCoefficient
  refine Q'.eqv_trans _
    (quaternionHaar (boundaryCompleteSlabLinks 1).length
      (reflectCorrectedSlabPolynomial 1
        (exactCorrectedSlabSpinNetworkIntegrand 1 faceLabel))) _
    (Q'.eqv_symm
      (quaternionHaar_reflectCorrectedSlabPolynomial 1 _
        (exactCorrectedSlabSpinNetworkIntegrand_supported 1 faceLabel))) ?_
  refine Q'.eqv_trans _
    (quaternionHaar (boundaryCompleteSlabLinks 1).length
      (exactCorrectedSlabCovariantOrderedIntegrand faceLabel)) _ ?_ ?_
  · exact quaternionHaar_prefixPolynomialEqv
      (boundaryCompleteSlabLinks 1).length
      (exactCorrectedSlabSpinNetworkIntegrand_reflection_prefix faceLabel)
      (reflectCorrectedSlabPolynomial_supported 1 _)
      (exactCorrectedSlabCovariantOrderedIntegrand_supported faceLabel)
  · exact Q'.eqv_trans _
      (quaternionHaar (boundaryCompleteSlabLinks 1).length
        (exactCorrectedSlabCanonicalReflectedOrderedIntegrand
          faceLabel)) _
      (SlabHaarCarrierEqv.haar
        (exactCorrectedSlabCovariantOrderedIntegrand_carrier faceLabel))
      (Q'.eqv_trans _
        (quaternionHaar (boundaryCompleteSlabLinks 1).length
          (exactCorrectedSlabReflectedOrderedIntegrand faceLabel)) _
        (quaternionHaar_prefixPolynomialEqv
          (boundaryCompleteSlabLinks 1).length
          (exactCorrectedSlabCanonicalReflectedOrderedIntegrand_prefix
            faceLabel)
          (exactCorrectedSlabCanonicalReflectedOrderedIntegrand_supported
            faceLabel)
          (exactCorrectedSlabReflectedOrderedIntegrand_supported faceLabel))
        (exactCorrectedSlabReflectedOrderedIntegrand_haar_eq faceLabel))

private theorem correctedSlabSpinNetworkFold_eq_of_labels
    (extent : Nat) (left right : SlabFaceLabelling)
    (hlabels : ∀ id, id ∈ slabPhysicalFaceEdges extent →
      left id = right id) :
    ∀ faces : List SlabFace,
      (∀ face, face ∈ faces →
        face ∈ boundaryCompleteSlabPlaquettes extent) →
      faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor extent left face)
              total)
          polyOne =
        faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor extent right face)
              total)
          polyOne
  | [], _ => rfl
  | face :: rest, hfaces => by
      simp only [List.foldr]
      have hface := hfaces face List.mem_cons_self
      have hid :
          (boundaryCompleteSlabPlaquettes extent).idxOf face ∈
            slabPhysicalFaceEdges extent :=
        List.mem_range.mpr (List.idxOf_lt_length_of_mem hface)
      unfold correctedSlabPlaquetteSpinFactor
      rw [hlabels _ hid]
      congr 1
      exact correctedSlabSpinNetworkFold_eq_of_labels
        extent left right hlabels rest
        (fun next hnext =>
          hfaces next (List.mem_cons_of_mem face hnext))

theorem exactCorrectedSlabHaarCoefficient_eq_of_labels
    (extent : Nat) (left right : SlabFaceLabelling)
    (hlabels : ∀ id, id ∈ slabPhysicalFaceEdges extent →
      left id = right id) :
    exactCorrectedSlabHaarCoefficient extent left =
      exactCorrectedSlabHaarCoefficient extent right := by
  unfold exactCorrectedSlabHaarCoefficient
    exactCorrectedSlabSpinNetworkIntegrand
  rw [correctedSlabSpinNetworkFold_eq_of_labels
    extent left right hlabels
    (boundaryCompleteSlabPlaquettes extent)
    (fun face hface => hface)]

/-- Reflection may be zero-padded away from physical face identifiers
without changing the exact Haar network. -/
theorem exactCorrectedSlabHaarCoefficient_supported_reflection
    (faceLabel : SlabFaceLabelling) :
    exactCorrectedSlabHaarCoefficient 1 faceLabel ≈
      exactCorrectedSlabHaarCoefficient 1
        (reflectSupportedSlabFaceLabelling 1 faceLabel) := by
  refine Q'.eqv_trans _
    (exactCorrectedSlabHaarCoefficient 1
      (reflectSlabFaceLabelling 1 faceLabel)) _
    (exactCorrectedSlabHaarCoefficient_reflection faceLabel) ?_
  exact Q'.eqv_of_eq
    (exactCorrectedSlabHaarCoefficient_eq_of_labels 1 _ _
      (fun id hid =>
        (reflectSupportedSlabFaceLabelling_eq_on_physical
          1 faceLabel hid).symm))

private theorem slabPhysicalFaceFactor_eq_of_labels
    (w : Q') (K extent : Nat)
    (left right : SlabFaceLabelling)
    (hlabels : ∀ id, id ∈ slabPhysicalFaceEdges extent →
      left id = right id) :
    slabParametricKPhysicalFaceFactor w K extent left =
      slabParametricKPhysicalFaceFactor w K extent right := by
  unfold slabParametricKPhysicalFaceFactor
  have hproduct : ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id = right id) →
      eliminateLinks
          (fun edge => coeffAt (heatKernelPacket K w) (left edge)) ids =
        eliminateLinks
          (fun edge => coeffAt (heatKernelPacket K w) (right edge)) ids := by
    intro ids hagree
    induction ids with
    | nil => rfl
    | cons id rest induction =>
        simp only [eliminateLinks]
        rw [hagree id List.mem_cons_self]
        rw [induction
          (fun next hnext =>
            hagree next (List.mem_cons_of_mem id hnext))]
  exact hproduct (slabPhysicalFaceEdges extent) hlabels

private theorem slabPhysicalFaceFactor_supported_reflection
    (w : Q') (K : Nat) (faceLabel : SlabFaceLabelling) :
    slabParametricKPhysicalFaceFactor w K 1 faceLabel ≈
      slabParametricKPhysicalFaceFactor w K 1
        (reflectSupportedSlabFaceLabelling 1 faceLabel) := by
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor w K 1
      (reflectSlabFaceLabelling 1 faceLabel)) _
    (Q'.eqv_symm
      (slabParametricKPhysicalFaceFactor_reflection
        w K 1 faceLabel)) ?_
  exact Q'.eqv_of_eq
    (slabPhysicalFaceFactor_eq_of_labels w K 1 _ _
      (fun id hid =>
        (reflectSupportedSlabFaceLabelling_eq_on_physical
          1 faceLabel hid).symm))

/-- The exact heat-weighted dual term is invariant under supported slab
reflection at the physical extent. -/
theorem exactCorrectedSlabDualTerm_supported_reflection
    (w : Q') (K : Nat) (faceLabel : SlabFaceLabelling) :
    exactCorrectedSlabDualTerm w K 1 faceLabel ≈
      exactCorrectedSlabDualTerm w K 1
        (reflectSupportedSlabFaceLabelling 1 faceLabel) := by
  unfold exactCorrectedSlabDualTerm
  exact Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor w K 1
        (reflectSupportedSlabFaceLabelling 1 faceLabel) *
      exactCorrectedSlabHaarCoefficient 1 faceLabel) _
    (Q'.mul_eqv_congr_right _ _ _
      (slabPhysicalFaceFactor_supported_reflection
        w K faceLabel))
    (Q'.mul_eqv_congr_left _ _ _
      (exactCorrectedSlabHaarCoefficient_supported_reflection faceLabel))

/-- Swapping source and target labels leaves every fixed-interface summand
of the exact reflected slab unchanged. -/
theorem exactCorrectedSlabDualTerm_assembled_swap
    (w : Q') (K : Nat)
    (left boundary right : SlabFaceLabelling) :
    exactCorrectedSlabDualTerm w K 1
        (assembleReflectedSlabLabelling 0 left boundary right) ≈
      exactCorrectedSlabDualTerm w K 1
        (assembleReflectedSlabLabelling 0 right boundary left) := by
  refine Q'.eqv_trans _
    (exactCorrectedSlabDualTerm w K 1
      (reflectSupportedSlabFaceLabelling 1
        (assembleReflectedSlabLabelling 0 left boundary right))) _
    (exactCorrectedSlabDualTerm_supported_reflection
      w K (assembleReflectedSlabLabelling 0 left boundary right)) ?_
  have hswap :
      reflectSupportedSlabFaceLabelling 1
          (assembleReflectedSlabLabelling 0 left boundary right) =
        assembleReflectedSlabLabelling 0 right boundary left := by
    simpa [centralExtent] using
      (assembleReflectedSlabLabelling_reflection_swap
        0 left boundary right)
  rw [hswap]
  exact Q'.eqv_refl _

/-- **Literal kernel symmetry.**  No positivity carrier restriction is
needed: the exact signed reflected slab matrix is symmetric on all boundary
labellings. -/
theorem exactCorrectedSlabReflectedKernel_symmetric
    (w : Q') (K : Nat) (left right : SlabFaceLabelling) :
    exactCorrectedSlabReflectedKernel w K 0 left right ≈
      exactCorrectedSlabReflectedKernel w K 0 right left := by
  unfold exactCorrectedSlabReflectedKernel
  apply listQSum_congr
  intro boundary
  exact exactCorrectedSlabDualTerm_assembled_swap
    w K left boundary right

end YMGap.Continuum.BF4ExactSlabVacuumReflection

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.correctedSlabLinkAt_mem
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.correctedSlabLinkAt_reflectBlock
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.correctedSlabLinkAt_injective_on_physical
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.correctedSlabLinkReflectBlock_involutive
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.correctedSlabQuaternionBlockInvolution
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.timeReflectLink_direction
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.quaternionHaar_reflectCorrectedSlabPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.exactCorrectedSlabSpinNetworkIntegrand_supported
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.correctedSlabPlaquetteScalar_normal_check
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.correctedSlabPlaquetteSpinFactor_reflection_prefix
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.reflectCorrectedSlabPolynomial_support
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.correctedSlabPlaquetteSpinFactor_reflection_insert
#print axioms YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm.quaternionHaar_factorFold_perm
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.exactCorrectedSlabHaarCoefficient_reflection
#print axioms YMGap.Continuum.BF4ExactSlabVacuumReflection.exactCorrectedSlabReflectedKernel_symmetric
