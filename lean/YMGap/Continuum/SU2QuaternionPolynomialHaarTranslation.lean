/-
# Constructive polynomial left/right invariance for quaternion Haar

This module develops the finite algebraic core of Haar translation for the
repository's exact `S^3` moment functional.  A head quaternion `u` is
multiplied on the left or right by a tail quaternion `a`; the head block is
then integrated exactly.  The resulting coefficient polynomial in `a` is the
original head moment times the appropriate power of `|a|^2`.  The existing
sphere-ideal theorem later removes that radius power under the remaining Haar
integrals.

The moment identity is exposed as an executable certificate for each exponent
quadruple.  This keeps bounded-degree applications fully constructive while
leaving no unproved universal combinatorial identity hidden in the API.

## Axiom gate

Finite polynomial recursion, exact rational moments, kernel reduction, and
the already-proved sphere ideal only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles
import YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
import YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
import YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck

namespace YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Local support bookkeeping -/

private theorem supported_polyZero_local (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyZero := by
  intro term hterm
  simp [polyZero] at hterm

private theorem supported_polyOne_local (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp

private theorem supported_polyVar_local
    {blocks coordinate : Nat} (hcoordinate : coordinate < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar coordinate) := by
  intro term hterm
  simp only [polyVar, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp [RingNormaliser.varMono]
  omega

private theorem supported_polyAdd_local
    {blocks : Nat} {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks blocks left)
    (hright : SupportedQuaternionBlocks blocks right) :
    SupportedQuaternionBlocks blocks (polyAdd left right) := by
  intro term hterm
  rcases List.mem_append.mp hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem supported_polyNeg_local
    {blocks : Nat} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polyNeg polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact hsupport source hsource

private theorem supported_polySmul_local
    {blocks : Nat} {scale : Q'} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact hsupport source hsource

private theorem supported_weaken_local
    {small large : Nat} {polynomial : RatPoly}
    (hle : small ≤ large)
    (hsupport : SupportedQuaternionBlocks small polynomial) :
    SupportedQuaternionBlocks large polynomial := by
  intro term hterm
  have hlength := hsupport term hterm
  omega

private theorem insertRatTerm_supported_local
    {blocks : Nat} {monomial : List Nat} {coefficient : Q'}
    (hmonomial : monomial.length ≤ 4 * blocks) :
    ∀ polynomial : RatPoly,
      SupportedQuaternionBlocks blocks polynomial →
      SupportedQuaternionBlocks blocks
        (insertRatTerm monomial coefficient polynomial)
  | [], _ => by
      intro term hterm
      by_cases hzero : coefficient.num = 0
      · simp [insertRatTerm, hzero] at hterm
      · simp [insertRatTerm, hzero] at hterm
        rw [hterm]
        exact hmonomial
  | other :: rest, hsupport => by
      intro term hterm
      have hother := hsupport other List.mem_cons_self
      have hrestSupport : SupportedQuaternionBlocks blocks rest :=
        fun source hsource =>
          hsupport source (List.mem_cons_of_mem other hsource)
      by_cases hzero : coefficient.num = 0
      · exact hsupport term (by simpa [insertRatTerm, hzero] using hterm)
      · cases horder : monoCmp monomial other.1 with
        | lt =>
            simp [insertRatTerm, hzero, horder] at hterm
            rcases hterm with rfl | rfl | hrest
            · exact hmonomial
            · exact hother
            · exact hrestSupport term hrest
        | eq =>
            by_cases hcombined :
                (coefficient + other.2).num = 0
            · exact hrestSupport term (by
                simpa [insertRatTerm, hzero, horder, hcombined] using hterm)
            · simp [insertRatTerm, hzero, horder, hcombined] at hterm
              rcases hterm with rfl | hrest
              · exact hmonomial
              · exact hrestSupport term hrest
        | gt =>
            simp [insertRatTerm, hzero, horder] at hterm
            rcases hterm with rfl | hrest
            · exact hother
            · exact insertRatTerm_supported_local hmonomial rest
                hrestSupport term hrest

private theorem canonRat_supported_local
    {blocks : Nat} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (canonRat polynomial) := by
  unfold canonRat
  induction polynomial with
  | nil => exact supported_polyZero_local blocks
  | cons term rest induction =>
      simp only [List.foldr_cons]
      exact insertRatTerm_supported_local
        (hsupport term List.mem_cons_self) _
        (induction (fun source hsource =>
          hsupport source (List.mem_cons_of_mem term hsource)))

private structure SupportedPolyQuaternion
    (blocks : Nat) (quaternion : PolyQuaternion) : Prop where
  scalar : SupportedQuaternionBlocks blocks quaternion.scalar
  iPart : SupportedQuaternionBlocks blocks quaternion.iPart
  jPart : SupportedQuaternionBlocks blocks quaternion.jPart
  kPart : SupportedQuaternionBlocks blocks quaternion.kPart

private theorem supportedPolyQuaternion_coordinateVariable
    {blocks block : Nat} (hblock : block < blocks) :
    SupportedPolyQuaternion blocks
      (PolyQuaternion.coordinateVariable block) := by
  constructor <;> apply supported_polyVar_local <;> omega

private theorem supportedPolyQuaternion_mul
    {blocks : Nat} {left right : PolyQuaternion}
    (hleft : SupportedPolyQuaternion blocks left)
    (hright : SupportedPolyQuaternion blocks right) :
    SupportedPolyQuaternion blocks (PolyQuaternion.mul left right) := by
  constructor
  · apply supported_polyAdd_local
    · exact supported_polyMul hleft.scalar hright.scalar
    · apply supported_polyNeg_local
      apply supported_polyAdd_local
      · exact supported_polyMul hleft.iPart hright.iPart
      · apply supported_polyAdd_local
        · exact supported_polyMul hleft.jPart hright.jPart
        · exact supported_polyMul hleft.kPart hright.kPart
  · apply supported_polyAdd_local
    · exact supported_polyMul hleft.scalar hright.iPart
    · apply supported_polyAdd_local
      · exact supported_polyMul hleft.iPart hright.scalar
      · apply supported_polyAdd_local
        · exact supported_polyMul hleft.jPart hright.kPart
        · exact supported_polyNeg_local
            (supported_polyMul hleft.kPart hright.jPart)
  · apply supported_polyAdd_local
    · exact supported_polyMul hleft.scalar hright.jPart
    · apply supported_polyAdd_local
      · exact supported_polyMul hleft.jPart hright.scalar
      · apply supported_polyAdd_local
        · exact supported_polyMul hleft.kPart hright.iPart
        · exact supported_polyNeg_local
            (supported_polyMul hleft.iPart hright.kPart)
  · apply supported_polyAdd_local
    · exact supported_polyMul hleft.scalar hright.kPart
    · apply supported_polyAdd_local
      · exact supported_polyMul hleft.kPart hright.scalar
      · apply supported_polyAdd_local
        · exact supported_polyMul hleft.iPart hright.jPart
        · exact supported_polyNeg_local
            (supported_polyMul hleft.jPart hright.iPart)

/-! ## 1. Executable one-block translation moments -/

def ratPolyPow (polynomial : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | exponent + 1 =>
      polyMul (ratPolyPow polynomial exponent) polynomial

private theorem ratPolyPow_supported
    {blocks : Nat} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    ∀ exponent, SupportedQuaternionBlocks blocks
      (ratPolyPow polynomial exponent)
  | 0 => supported_polyOne_local blocks
  | exponent + 1 =>
      supported_polyMul
        (ratPolyPow_supported hsupport exponent) hsupport

def translatedHeadMonomial
    (translated : PolyQuaternion)
    (e0 e1 e2 e3 : Nat) : RatPoly :=
  polyMul (ratPolyPow translated.scalar e0)
    (polyMul (ratPolyPow translated.iPart e1)
      (polyMul (ratPolyPow translated.jPart e2)
        (ratPolyPow translated.kPart e3)))

/-- Tail block `a` multiplying head block `u` on the left. -/
def leftTranslatedHeadQuaternion : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.coordinateVariable 1)
    (PolyQuaternion.coordinateVariable 0)

/-- Head block `u` multiplying tail block `a` on the right. -/
def rightTranslatedHeadQuaternion : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.coordinateVariable 1)

def headExponentLedger (e0 e1 e2 e3 : Nat) : List Nat :=
  [e0, e1, e2, e3]

private theorem headQuaternionMoment_headExponentLedger
    (monomial : List Nat) :
    headQuaternionMoment
        (headExponentLedger
          (exponentAt monomial 0) (exponentAt monomial 1)
          (exponentAt monomial 2) (exponentAt monomial 3)) =
      headQuaternionMoment monomial := by
  rfl

def expectedTranslatedHeadMoment
    (e0 e1 e2 e3 : Nat) : RatPoly :=
  polySmul
    (headQuaternionMoment (headExponentLedger e0 e1 e2 e3))
    (quaternionRadiusIter 0 ((e0 + e1 + e2 + e3) / 2) polyOne)

private theorem translatedHeadMonomial_supported
    {blocks : Nat} {translated : PolyQuaternion}
    (hsupport : SupportedPolyQuaternion blocks translated)
    (e0 e1 e2 e3 : Nat) :
    SupportedQuaternionBlocks blocks
      (translatedHeadMonomial translated e0 e1 e2 e3) := by
  unfold translatedHeadMonomial
  exact supported_polyMul
    (ratPolyPow_supported hsupport.scalar e0)
    (supported_polyMul
      (ratPolyPow_supported hsupport.iPart e1)
      (supported_polyMul
        (ratPolyPow_supported hsupport.jPart e2)
        (ratPolyPow_supported hsupport.kPart e3)))

private theorem leftTranslatedHeadQuaternion_supported :
    SupportedPolyQuaternion 2 leftTranslatedHeadQuaternion := by
  exact supportedPolyQuaternion_mul
    (supportedPolyQuaternion_coordinateVariable (by omega : 1 < 2))
    (supportedPolyQuaternion_coordinateVariable (by omega : 0 < 2))

private theorem rightTranslatedHeadQuaternion_supported :
    SupportedPolyQuaternion 2 rightTranslatedHeadQuaternion := by
  exact supportedPolyQuaternion_mul
    (supportedPolyQuaternion_coordinateVariable (by omega : 0 < 2))
    (supportedPolyQuaternion_coordinateVariable (by omega : 1 < 2))

private theorem quaternionRadiusIter_supported_local
    {blocks block : Nat} (hblock : block < blocks)
    {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    ∀ count,
      SupportedQuaternionBlocks blocks
        (quaternionRadiusIter block count polynomial)
  | 0 => hsupport
  | count + 1 => supported_polyMul
      (quaternionRadiusIter_supported_local hblock hsupport count)
      (quaternionRadiusPolynomial_supported blocks block hblock)

private theorem expectedTranslatedHeadMoment_supported
    (e0 e1 e2 e3 : Nat) :
    SupportedQuaternionBlocks 1
      (expectedTranslatedHeadMoment e0 e1 e2 e3) := by
  apply supported_polySmul_local
  exact quaternionRadiusIter_supported_local (by omega : 0 < 1)
    (supported_polyOne_local 1) _

def leftTranslationMomentCheck (e0 e1 e2 e3 : Nat) : Bool :=
  quaternionPrefixPolynomialCheck 1
    (canonRat
      (partialHaarHead
        (translatedHeadMonomial leftTranslatedHeadQuaternion
          e0 e1 e2 e3)))
    (canonRat (expectedTranslatedHeadMoment e0 e1 e2 e3))

def rightTranslationMomentCheck (e0 e1 e2 e3 : Nat) : Bool :=
  quaternionPrefixPolynomialCheck 1
    (canonRat
      (partialHaarHead
        (translatedHeadMonomial rightTranslatedHeadQuaternion
          e0 e1 e2 e3)))
    (canonRat (expectedTranslatedHeadMoment e0 e1 e2 e3))

/-- Scan exactly the head exponent quadruples that occur in a finite
polynomial.  Unlike a rectangular degree table, this certificate does no
irrelevant work. -/
def translationPolynomialCheck
    (check : Nat → Nat → Nat → Nat → Bool)
    (polynomial : RatPoly) : Bool :=
  polynomial.all fun term =>
    check
      (exponentAt term.1 0) (exponentAt term.1 1)
      (exponentAt term.1 2) (exponentAt term.1 3)

/-- One term after substituting a translated head quaternion and performing
the head Haar integral, while retaining its coefficient and tail monomial. -/
def partialTranslatedHeadTerm
    (translated : PolyQuaternion) (term : RatTerm) : RatPoly :=
  polyMul
    (partialHaarHead
      (translatedHeadMonomial translated
        (exponentAt term.1 0) (exponentAt term.1 1)
        (exponentAt term.1 2) (exponentAt term.1 3)))
    [(term.1.drop 4, term.2)]

/-- Termwise translated-head substitution followed by exact head Haar. -/
def partialTranslatedHeadPolynomial
    (translated : PolyQuaternion) : RatPoly → RatPoly
  | [] => polyZero
  | term :: rest =>
      polyAdd (partialTranslatedHeadTerm translated term)
        (partialTranslatedHeadPolynomial translated rest)

theorem translationPolynomialCheck_term
    {check : Nat → Nat → Nat → Nat → Bool}
    {polynomial : RatPoly}
    (hcheck : translationPolynomialCheck check polynomial = true)
    {term : RatTerm} (hterm : term ∈ polynomial) :
    check
      (exponentAt term.1 0) (exponentAt term.1 1)
      (exponentAt term.1 2) (exponentAt term.1 3) = true := by
  exact List.all_eq_true.mp hcheck term hterm

private theorem quaternionPrefixPolynomialCheck_irrel
    (first second : Nat) : ∀ left right : RatPoly,
    quaternionPrefixPolynomialCheck first left right =
      quaternionPrefixPolynomialCheck second left right
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | left :: leftRest, right :: rightRest => by
      simp only [quaternionPrefixPolynomialCheck]
      have hterm :
          quaternionPrefixTermCheck first left right =
            quaternionPrefixTermCheck second left right := rfl
      rw [hterm]
      rw [quaternionPrefixPolynomialCheck_irrel
        first second leftRest rightRest]

def translationMomentChecksThrough
    (check : Nat → Nat → Nat → Nat → Bool)
    (maxDegree : Nat) : Bool :=
  (List.range (maxDegree + 1)).all fun e0 =>
    (List.range (maxDegree + 1)).all fun e1 =>
      (List.range (maxDegree + 1)).all fun e2 =>
        (List.range (maxDegree + 1)).all fun e3 =>
          if e0 + e1 + e2 + e3 ≤ maxDegree then
            check e0 e1 e2 e3
          else true

def translationMomentChecksAtDegree
    (check : Nat → Nat → Nat → Nat → Bool)
    (degree : Nat) : Bool :=
  (List.range (degree + 1)).all fun e0 =>
    (List.range (degree + 1)).all fun e1 =>
      (List.range (degree + 1)).all fun e2 =>
        (List.range (degree + 1)).all fun e3 =>
          if e0 + e1 + e2 + e3 = degree then
            check e0 e1 e2 e3
          else true

theorem translationMomentChecksThrough_apply
    {check : Nat → Nat → Nat → Nat → Bool}
    {maxDegree e0 e1 e2 e3 : Nat}
    (hchecks :
      translationMomentChecksThrough check maxDegree = true)
    (hdegree : e0 + e1 + e2 + e3 ≤ maxDegree) :
    check e0 e1 e2 e3 = true := by
  unfold translationMomentChecksThrough at hchecks
  have h0 := List.all_eq_true.mp hchecks e0
    (List.mem_range.mpr (by omega))
  have h1 := List.all_eq_true.mp h0 e1
    (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 e2
    (List.mem_range.mpr (by omega))
  have h3 := List.all_eq_true.mp h2 e3
    (List.mem_range.mpr (by omega))
  rw [if_pos hdegree] at h3
  exact h3

theorem translationMomentChecksAtDegree_apply
    {check : Nat → Nat → Nat → Nat → Bool}
    {degree e0 e1 e2 e3 : Nat}
    (hchecks :
      translationMomentChecksAtDegree check degree = true)
    (hdegree : e0 + e1 + e2 + e3 = degree) :
    check e0 e1 e2 e3 = true := by
  unfold translationMomentChecksAtDegree at hchecks
  have h0 := List.all_eq_true.mp hchecks e0
    (List.mem_range.mpr (by omega))
  have h1 := List.all_eq_true.mp h0 e1
    (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 e2
    (List.mem_range.mpr (by omega))
  have h3 := List.all_eq_true.mp h2 e3
    (List.mem_range.mpr (by omega))
  rw [if_pos hdegree] at h3
  exact h3

theorem leftTranslationMomentCheck_sound
    {e0 e1 e2 e3 : Nat}
    (hcheck : leftTranslationMomentCheck e0 e1 e2 e3 = true) :
    QuaternionPrefixPolynomialEqv 1
      (canonRat
        (partialHaarHead
          (translatedHeadMonomial leftTranslatedHeadQuaternion
            e0 e1 e2 e3)))
      (canonRat (expectedTranslatedHeadMoment e0 e1 e2 e3)) :=
  quaternionPrefixPolynomialCheck_sound 1 hcheck

theorem rightTranslationMomentCheck_sound
    {e0 e1 e2 e3 : Nat}
    (hcheck : rightTranslationMomentCheck e0 e1 e2 e3 = true) :
    QuaternionPrefixPolynomialEqv 1
      (canonRat
        (partialHaarHead
          (translatedHeadMonomial rightTranslatedHeadQuaternion
            e0 e1 e2 e3)))
      (canonRat (expectedTranslatedHeadMoment e0 e1 e2 e3)) :=
  quaternionPrefixPolynomialCheck_sound 1 hcheck

private theorem checkedTranslatedHeadMoment_mul
    (blocks : Nat) (hblocks : 0 < blocks)
    (translated : PolyQuaternion)
    (htranslated : SupportedPolyQuaternion 2 translated)
    (e0 e1 e2 e3 : Nat)
    (hcheck :
      quaternionPrefixPolynomialCheck 1
        (canonRat
          (partialHaarHead
            (translatedHeadMonomial translated e0 e1 e2 e3)))
        (canonRat
          (expectedTranslatedHeadMoment e0 e1 e2 e3)) = true)
    (tail : RatPoly)
    (htail : SupportedQuaternionBlocks blocks tail) :
    quaternionHaar blocks
        (polyMul
          (partialHaarHead
            (translatedHeadMonomial translated e0 e1 e2 e3))
          tail) ≈
      quaternionHaar blocks
        (polyMul
          (expectedTranslatedHeadMoment e0 e1 e2 e3)
          tail) := by
  let left := partialHaarHead
    (translatedHeadMonomial translated e0 e1 e2 e3)
  let right := expectedTranslatedHeadMoment e0 e1 e2 e3
  have hleftOne : SupportedQuaternionBlocks 1 left := by
    dsimp only [left]
    exact partialHaarHead_supported
      (translatedHeadMonomial_supported htranslated e0 e1 e2 e3)
  have hrightOne : SupportedQuaternionBlocks 1 right := by
    dsimp only [right]
    exact expectedTranslatedHeadMoment_supported e0 e1 e2 e3
  have hleft : SupportedQuaternionBlocks blocks left :=
    supported_weaken_local (by omega) hleftOne
  have hright : SupportedQuaternionBlocks blocks right :=
    supported_weaken_local (by omega) hrightOne
  have hcheckBlocks :
      quaternionPrefixPolynomialCheck blocks
          (canonRat left) (canonRat right) = true := by
    rw [quaternionPrefixPolynomialCheck_irrel blocks 1
      (canonRat left) (canonRat right)]
    simpa only [left, right] using hcheck
  have heqv : QuaternionPrefixPolynomialEqv blocks
      (canonRat left) (canonRat right) :=
    quaternionPrefixPolynomialCheck_sound blocks hcheckBlocks
  have hcanon := quaternionHaar_prefixPolynomialEqv blocks
    (QuaternionPrefixPolynomialEqv.mul heqv
      (QuaternionPrefixPolynomialEqv.refl blocks tail))
    (supported_polyMul (canonRat_supported_local hleft) htail)
    (supported_polyMul (canonRat_supported_local hright) htail)
  exact Q'.eqv_trans _
    (quaternionHaar blocks (polyMul (canonRat left) tail)) _
    (Q'.eqv_symm (quaternionHaar_canonRat_mul blocks left tail))
    (Q'.eqv_trans _
      (quaternionHaar blocks (polyMul (canonRat right) tail)) _
      hcanon
      (quaternionHaar_canonRat_mul blocks right tail))

/-- A checked left-translation moment can be multiplied by an arbitrary
supported tail polynomial before the remaining product-Haar integrations. -/
theorem leftTranslationMomentCheck_mul_sound
    (blocks : Nat) (hblocks : 0 < blocks)
    (e0 e1 e2 e3 : Nat)
    (hcheck : leftTranslationMomentCheck e0 e1 e2 e3 = true)
    (tail : RatPoly)
    (htail : SupportedQuaternionBlocks blocks tail) :
    quaternionHaar blocks
        (polyMul
          (partialHaarHead
            (translatedHeadMonomial leftTranslatedHeadQuaternion
              e0 e1 e2 e3))
          tail) ≈
      quaternionHaar blocks
        (polyMul
          (expectedTranslatedHeadMoment e0 e1 e2 e3)
          tail) := by
  exact checkedTranslatedHeadMoment_mul blocks hblocks
    leftTranslatedHeadQuaternion leftTranslatedHeadQuaternion_supported
    e0 e1 e2 e3 hcheck tail htail

/-- Right-translation companion of `leftTranslationMomentCheck_mul_sound`. -/
theorem rightTranslationMomentCheck_mul_sound
    (blocks : Nat) (hblocks : 0 < blocks)
    (e0 e1 e2 e3 : Nat)
    (hcheck : rightTranslationMomentCheck e0 e1 e2 e3 = true)
    (tail : RatPoly)
    (htail : SupportedQuaternionBlocks blocks tail) :
    quaternionHaar blocks
        (polyMul
          (partialHaarHead
            (translatedHeadMonomial rightTranslatedHeadQuaternion
              e0 e1 e2 e3))
          tail) ≈
      quaternionHaar blocks
        (polyMul
          (expectedTranslatedHeadMoment e0 e1 e2 e3)
          tail) := by
  exact checkedTranslatedHeadMoment_mul blocks hblocks
    rightTranslatedHeadQuaternion rightTranslatedHeadQuaternion_supported
    e0 e1 e2 e3 hcheck tail htail

/-- The multiplier-radius generated by a head translation is invisible under
the multiplier block's normalized Haar integral. -/
theorem expectedTranslatedHeadMoment_mul_haar
    (blocks : Nat) (hblocks : 0 < blocks)
    (e0 e1 e2 e3 : Nat) (tail : RatPoly) :
    quaternionHaar blocks
        (polyMul
          (expectedTranslatedHeadMoment e0 e1 e2 e3) tail) ≈
      headQuaternionMoment (headExponentLedger e0 e1 e2 e3) *
        quaternionHaar blocks tail := by
  let moment := headQuaternionMoment
    (headExponentLedger e0 e1 e2 e3)
  let count := (e0 + e1 + e2 + e3) / 2
  let radius := quaternionRadiusIter 0 count polyOne
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul tail (polySmul moment radius))) _
    (quaternionHaar_polyMul_comm blocks
      (polySmul moment radius) tail) ?_
  refine Q'.eqv_trans _
    (moment * quaternionHaar blocks (polyMul tail radius)) _
    (quaternionHaar_polyMul_smul_right
      blocks moment tail radius) ?_
  apply Q'.mul_eqv_congr_left
  exact Q'.eqv_trans _
    (quaternionHaar blocks (polyMul tail polyOne)) _
    (quaternionHaar_radiusIter_pair_right
      blocks 0 (by omega) tail polyOne count)
    (quaternionHaar_polyMul_one_right blocks tail)

/-- **Constructive left Haar invariance for one certified monomial.**  After
integrating the translated head and every supported tail factor, the result
is the untranslated head moment times the tail integral. -/
theorem leftTranslationMomentCheck_haar_sound
    (blocks : Nat) (hblocks : 0 < blocks)
    (e0 e1 e2 e3 : Nat)
    (hcheck : leftTranslationMomentCheck e0 e1 e2 e3 = true)
    (tail : RatPoly)
    (htail : SupportedQuaternionBlocks blocks tail) :
    quaternionHaar blocks
        (polyMul
          (partialHaarHead
            (translatedHeadMonomial leftTranslatedHeadQuaternion
              e0 e1 e2 e3))
          tail) ≈
      headQuaternionMoment (headExponentLedger e0 e1 e2 e3) *
        quaternionHaar blocks tail := by
  exact Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (expectedTranslatedHeadMoment e0 e1 e2 e3) tail)) _
    (leftTranslationMomentCheck_mul_sound blocks hblocks
      e0 e1 e2 e3 hcheck tail htail)
    (expectedTranslatedHeadMoment_mul_haar
      blocks hblocks e0 e1 e2 e3 tail)

/-- **Constructive right Haar invariance for one certified monomial.** -/
theorem rightTranslationMomentCheck_haar_sound
    (blocks : Nat) (hblocks : 0 < blocks)
    (e0 e1 e2 e3 : Nat)
    (hcheck : rightTranslationMomentCheck e0 e1 e2 e3 = true)
    (tail : RatPoly)
    (htail : SupportedQuaternionBlocks blocks tail) :
    quaternionHaar blocks
        (polyMul
          (partialHaarHead
            (translatedHeadMonomial rightTranslatedHeadQuaternion
              e0 e1 e2 e3))
          tail) ≈
      headQuaternionMoment (headExponentLedger e0 e1 e2 e3) *
        quaternionHaar blocks tail := by
  exact Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (expectedTranslatedHeadMoment e0 e1 e2 e3) tail)) _
    (rightTranslationMomentCheck_mul_sound blocks hblocks
      e0 e1 e2 e3 hcheck tail htail)
    (expectedTranslatedHeadMoment_mul_haar
      blocks hblocks e0 e1 e2 e3 tail)

private theorem partialTranslatedHeadTerm_haar
    (blocks : Nat) (translated : PolyQuaternion)
    (check : Nat → Nat → Nat → Nat → Bool)
    (hsound :
      ∀ (e0 e1 e2 e3 : Nat),
        check e0 e1 e2 e3 = true →
        ∀ tail : RatPoly,
          SupportedQuaternionBlocks blocks tail →
          quaternionHaar blocks
              (polyMul
                (partialHaarHead
                  (translatedHeadMonomial translated e0 e1 e2 e3))
                tail) ≈
            headQuaternionMoment
                (headExponentLedger e0 e1 e2 e3) *
              quaternionHaar blocks tail)
    (term : RatTerm)
    (hterm : term.1.length ≤ 4 * (blocks + 1))
    (hcheck :
      check
        (exponentAt term.1 0) (exponentAt term.1 1)
        (exponentAt term.1 2) (exponentAt term.1 3) = true) :
    quaternionHaar blocks
        (partialTranslatedHeadTerm translated term) ≈
      term.2 * quaternionHaarMono (blocks + 1) term.1 := by
  let tail : RatPoly := [(term.1.drop 4, term.2)]
  have htail : SupportedQuaternionBlocks blocks tail := by
    intro source hsource
    simp only [tail, List.mem_cons, List.not_mem_nil, or_false] at hsource
    subst source
    simp only
    rw [List.length_drop]
    omega
  have htranslated := hsound
    (exponentAt term.1 0) (exponentAt term.1 1)
    (exponentAt term.1 2) (exponentAt term.1 3)
    hcheck tail htail
  rw [headQuaternionMoment_headExponentLedger] at htranslated
  refine Q'.eqv_trans _
    (headQuaternionMoment term.1 * quaternionHaar blocks tail) _
    htranslated ?_
  refine Q'.eqv_trans _
    (headQuaternionMoment term.1 *
      (term.2 * quaternionHaarMono blocks (term.1.drop 4))) _
    (Q'.mul_eqv_congr_left _ _ _
      (QPoly.q_add_zero_eqv _)) ?_
  refine Q'.eqv_trans _
    ((headQuaternionMoment term.1 * term.2) *
      quaternionHaarMono blocks (term.1.drop 4)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    ((term.2 * headQuaternionMoment term.1) *
      quaternionHaarMono blocks (term.1.drop 4)) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _
    (term.2 *
      (headQuaternionMoment term.1 *
        quaternionHaarMono blocks (term.1.drop 4))) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (headMoment_mul_tailHaarMono blocks term.1)

private theorem partialTranslatedHeadPolynomial_haar
    (blocks : Nat) (translated : PolyQuaternion)
    (check : Nat → Nat → Nat → Nat → Bool)
    (hsound :
      ∀ (e0 e1 e2 e3 : Nat),
        check e0 e1 e2 e3 = true →
        ∀ tail : RatPoly,
          SupportedQuaternionBlocks blocks tail →
          quaternionHaar blocks
              (polyMul
                (partialHaarHead
                  (translatedHeadMonomial translated e0 e1 e2 e3))
                tail) ≈
            headQuaternionMoment
                (headExponentLedger e0 e1 e2 e3) *
              quaternionHaar blocks tail) :
    ∀ polynomial : RatPoly,
      SupportedQuaternionBlocks (blocks + 1) polynomial →
      translationPolynomialCheck check polynomial = true →
      quaternionHaar blocks
          (partialTranslatedHeadPolynomial translated polynomial) ≈
        quaternionHaar (blocks + 1) polynomial
  | [], _, _ => Q'.eqv_refl 0
  | term :: rest, hsupport, hcheck => by
      have htermCheck := translationPolynomialCheck_term hcheck
        (List.mem_cons_self : term ∈ term :: rest)
      have hrestCheck :
          translationPolynomialCheck check rest = true := by
        exact List.all_eq_true.mpr fun source hsource =>
          translationPolynomialCheck_term hcheck
            (List.mem_cons_of_mem term hsource)
      change
        quaternionHaar blocks
            (partialTranslatedHeadTerm translated term ++
              partialTranslatedHeadPolynomial translated rest) ≈
          term.2 * quaternionHaarMono (blocks + 1) term.1 +
            quaternionHaar (blocks + 1) rest
      refine Q'.eqv_trans _
        (quaternionHaar blocks
            (partialTranslatedHeadTerm translated term) +
          quaternionHaar blocks
            (partialTranslatedHeadPolynomial translated rest)) _
        (quaternionHaar_append blocks _ _) ?_
      exact Q'.add_eqv_congr'
        (partialTranslatedHeadTerm_haar blocks translated check hsound
          term (hsupport term List.mem_cons_self) htermCheck)
        (partialTranslatedHeadPolynomial_haar blocks translated check hsound
          rest
          (fun source hsource =>
            hsupport source (List.mem_cons_of_mem term hsource))
          hrestCheck)

/-- **Finite-polynomial constructive left Haar invariance.**  The executable
scan checks only exponent quadruples that occur in `polynomial`; a successful
scan transports the entire supported polynomial through the left head
translation and exact head integration. -/
theorem leftTranslationPolynomialCheck_haar_sound
    (blocks : Nat) (hblocks : 0 < blocks)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (blocks + 1) polynomial)
    (hcheck :
      translationPolynomialCheck leftTranslationMomentCheck polynomial =
        true) :
    quaternionHaar blocks
        (partialTranslatedHeadPolynomial
          leftTranslatedHeadQuaternion polynomial) ≈
      quaternionHaar (blocks + 1) polynomial := by
  exact partialTranslatedHeadPolynomial_haar blocks
    leftTranslatedHeadQuaternion leftTranslationMomentCheck
    (fun e0 e1 e2 e3 termCheck tail tailSupport =>
      leftTranslationMomentCheck_haar_sound blocks hblocks
        e0 e1 e2 e3 termCheck tail tailSupport)
    polynomial hsupport hcheck

/-- Finite-polynomial right-translation companion. -/
theorem rightTranslationPolynomialCheck_haar_sound
    (blocks : Nat) (hblocks : 0 < blocks)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (blocks + 1) polynomial)
    (hcheck :
      translationPolynomialCheck rightTranslationMomentCheck polynomial =
        true) :
    quaternionHaar blocks
        (partialTranslatedHeadPolynomial
          rightTranslatedHeadQuaternion polynomial) ≈
      quaternionHaar (blocks + 1) polynomial := by
  exact partialTranslatedHeadPolynomial_haar blocks
    rightTranslatedHeadQuaternion rightTranslationMomentCheck
    (fun e0 e1 e2 e3 termCheck tail tailSupport =>
      rightTranslationMomentCheck_haar_sound blocks hblocks
        e0 e1 e2 e3 termCheck tail tailSupport)
    polynomial hsupport hcheck

end YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation

#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation.leftTranslationMomentCheck_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation.rightTranslationMomentCheck_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation.leftTranslationPolynomialCheck_haar_sound
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation.rightTranslationPolynomialCheck_haar_sound
