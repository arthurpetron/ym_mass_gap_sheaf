/-
# Arbitrary-block odd-valent fundamental Haar vanishing

Every oriented fundamental matrix coefficient is linear in the four real
coordinates of its selected quaternion block.  Consequently an ordered word
of `n` such coefficients is block-homogeneous of degree `n`.  If `n` is odd,
every monomial in either honest complex component has an odd total block
degree, hence differs in at least one coordinate parity from the vacuum
monomial.  The exact finite-block parity theorem then makes its normalized
`S^3` moment zero.

This leaf packages that argument for an arbitrary ordered orientation word,
proves block locality independently, and lifts the zero beneath any complex
spectator independent of the selected in-range block.  Named valence-one,
valence-three, and valence-five corollaries supply the missing odd cases for
the cutoff-one local-kernel dispatcher.

No orientation family, Boolean assignment space, bounded labelling, or
global trace network is unfolded or materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector
import YMGap.Continuum.SU2QuaternionFiniteProductHaarParitySectors

namespace YMGap.Continuum.SU2QuaternionGenericBlockOddValentHaarVanishing

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector
open YMGap.Continuum.SU2QuaternionFiniteProductHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFiniteProductHaarParitySectors

local infix:50 " ≈ " => Q'.eqv

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-! ## 1. Ordered oriented words and block locality -/

/-- Right-associated literal product of a structurally nonempty ordered word
of oriented fundamental occurrences.  The tail is allowed to be empty, in
which case the result is literally the first coefficient rather than a
coefficient multiplied by a raw polynomial unit. -/
def orientedFundamentalWord
    (block : Nat) (first : FundamentalOccurrence) :
    List FundamentalOccurrence → ComplexRatPoly
  | [] => fundamentalOccurrenceCoefficient block first
  | second :: rest =>
      complexRatPolyMul
        (fundamentalOccurrenceCoefficient block first)
        (orientedFundamentalWord block second rest)

/-- Every ordered oriented word is supported entirely on its selected
quaternion block. -/
theorem complexQuaternionBlockLocal_orientedFundamentalWord
    (block : Nat) (first : FundamentalOccurrence)
    (rest : List FundamentalOccurrence) :
    ComplexQuaternionBlockLocal block
      (orientedFundamentalWord block first rest) := by
  induction rest generalizing first with
  | nil =>
      exact complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
        block first
  | cons second rest ih =>
      exact complexQuaternionBlockLocal_mul
        (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
          block first)
        (ih second)

/-! ## 2. Exact block degree of an oriented word -/

/-- Every raw monomial in a polynomial has one prescribed total degree in
the selected quaternion block. -/
def QuaternionBlockHomogeneousDegree
    (block degree : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    quaternionBlockDegree block term.1 = degree

/-- Both real components of an honest complex polynomial have one common
selected-block degree. -/
def ComplexQuaternionBlockHomogeneousDegree
    (block degree : Nat) (value : ComplexRatPoly) : Prop :=
  QuaternionBlockHomogeneousDegree block degree value.1 ∧
    QuaternionBlockHomogeneousDegree block degree value.2

private theorem quaternionBlockDegree_monoMul_local
    (block : Nat) (left right : List Nat) :
    quaternionBlockDegree block (monoMul left right) =
      quaternionBlockDegree block left +
        quaternionBlockDegree block right := by
  unfold quaternionBlockDegree
  simp only [exponentAt_monoMul]
  omega

private theorem quaternionBlockHomogeneousDegree_polyVar
    (block component : Nat) (hcomponent : component < 4) :
    QuaternionBlockHomogeneousDegree block 1
      (polyVar (4 * block + component)) := by
  intro term hterm
  simp only [polyVar, List.mem_singleton] at hterm
  subst term
  have hcases : component = 0 ∨ component = 1 ∨
      component = 2 ∨ component = 3 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    simp [quaternionBlockDegree, exponentAt_blockVariableNat,
      exponentAt_blockBase_base, exponentAt_blockBase_query,
      exponentAt_blockComponent_base]

private theorem quaternionBlockHomogeneousDegree_polyNeg
    {block degree : Nat} {polynomial : RatPoly}
    (hdegree : QuaternionBlockHomogeneousDegree
      block degree polynomial) :
    QuaternionBlockHomogeneousDegree block degree
      (polyNeg polynomial) := by
  intro term hterm
  unfold polyNeg at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  exact hdegree source hsource

private theorem quaternionBlockHomogeneousDegree_polyAdd
    {block degree : Nat} {left right : RatPoly}
    (hleft : QuaternionBlockHomogeneousDegree block degree left)
    (hright : QuaternionBlockHomogeneousDegree block degree right) :
    QuaternionBlockHomogeneousDegree block degree
      (polyAdd left right) := by
  intro term hterm
  simp only [polyAdd, List.mem_append] at hterm
  cases hterm with
  | inl hterm => exact hleft term hterm
  | inr hterm => exact hright term hterm

private theorem quaternionBlockHomogeneousDegree_polyMul
    {block leftDegree rightDegree : Nat} {left right : RatPoly}
    (hleft : QuaternionBlockHomogeneousDegree
      block leftDegree left)
    (hright : QuaternionBlockHomogeneousDegree
      block rightDegree right) :
    QuaternionBlockHomogeneousDegree block
      (leftDegree + rightDegree) (polyMul left right) := by
  intro term hterm
  unfold polyMul at hterm
  rw [List.mem_flatMap] at hterm
  obtain ⟨leftTerm, hleftTerm, hterm⟩ := hterm
  rw [List.mem_map] at hterm
  obtain ⟨rightTerm, hrightTerm, rfl⟩ := hterm
  rw [quaternionBlockDegree_monoMul_local,
    hleft leftTerm hleftTerm, hright rightTerm hrightTerm]

private theorem complexQuaternionBlockHomogeneousDegree_conj
    {block degree : Nat} {value : ComplexRatPoly}
    (hdegree : ComplexQuaternionBlockHomogeneousDegree
      block degree value) :
    ComplexQuaternionBlockHomogeneousDegree block degree
      (complexRatPolyConj value) := by
  exact ⟨hdegree.1,
    quaternionBlockHomogeneousDegree_polyNeg hdegree.2⟩

private theorem complexQuaternionBlockHomogeneousDegree_mul
    {block leftDegree rightDegree : Nat}
    {left right : ComplexRatPoly}
    (hleft : ComplexQuaternionBlockHomogeneousDegree
      block leftDegree left)
    (hright : ComplexQuaternionBlockHomogeneousDegree
      block rightDegree right) :
    ComplexQuaternionBlockHomogeneousDegree block
      (leftDegree + rightDegree) (complexRatPolyMul left right) := by
  constructor
  · exact quaternionBlockHomogeneousDegree_polyAdd
      (quaternionBlockHomogeneousDegree_polyMul hleft.1 hright.1)
      (quaternionBlockHomogeneousDegree_polyNeg
        (quaternionBlockHomogeneousDegree_polyMul hleft.2 hright.2))
  · exact quaternionBlockHomogeneousDegree_polyAdd
      (quaternionBlockHomogeneousDegree_polyMul hleft.1 hright.2)
      (quaternionBlockHomogeneousDegree_polyMul hleft.2 hright.1)

private theorem complexQuaternionBlockHomogeneousDegree_forward
    (block : Nat) (row column : Bool) :
    ComplexQuaternionBlockHomogeneousDegree block 1
      (forwardFundamentalCoefficient block row column) := by
  have hzero := quaternionBlockHomogeneousDegree_polyVar block 0 (by omega)
  have hone := quaternionBlockHomogeneousDegree_polyVar block 1 (by omega)
  have htwo := quaternionBlockHomogeneousDegree_polyVar block 2 (by omega)
  have hthree := quaternionBlockHomogeneousDegree_polyVar block 3 (by omega)
  cases row <;> cases column
  · exact ⟨hzero, hone⟩
  · exact ⟨htwo, hthree⟩
  · exact ⟨quaternionBlockHomogeneousDegree_polyNeg htwo, hthree⟩
  · exact ⟨hzero, quaternionBlockHomogeneousDegree_polyNeg hone⟩

private theorem complexQuaternionBlockHomogeneousDegree_reverse
    (block : Nat) (row column : Bool) :
    ComplexQuaternionBlockHomogeneousDegree block 1
      (reverseFundamentalCoefficient block row column) := by
  exact complexQuaternionBlockHomogeneousDegree_conj
    (complexQuaternionBlockHomogeneousDegree_forward block column row)

/-- Every packaged oriented fundamental occurrence is homogeneous of degree
one in its selected quaternion block. -/
theorem complexQuaternionBlockHomogeneousDegree_fundamentalOccurrence
    (block : Nat) (occurrence : FundamentalOccurrence) :
    ComplexQuaternionBlockHomogeneousDegree block 1
      (fundamentalOccurrenceCoefficient block occurrence) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation
  · exact complexQuaternionBlockHomogeneousDegree_forward block row column
  · exact complexQuaternionBlockHomogeneousDegree_reverse block row column

/-- The literal word length is exactly the total selected-block degree of
every monomial in both honest complex components. -/
theorem complexQuaternionBlockHomogeneousDegree_orientedFundamentalWord
    (block : Nat) (first : FundamentalOccurrence)
    (rest : List FundamentalOccurrence) :
    ComplexQuaternionBlockHomogeneousDegree block (rest.length + 1)
      (orientedFundamentalWord block first rest) := by
  induction rest generalizing first with
  | nil =>
      exact complexQuaternionBlockHomogeneousDegree_fundamentalOccurrence
        block first
  | cons second rest ih =>
      simpa only [orientedFundamentalWord, List.length_cons,
        Nat.add_comm] using
        (complexQuaternionBlockHomogeneousDegree_mul
          (complexQuaternionBlockHomogeneousDegree_fundamentalOccurrence
            block first)
          (ih second))

/-! ## 3. Odd degree gives an exact parity witness and zero moment -/

/-- An odd total degree in one quaternion block constructively exposes a
coordinate whose parity differs from the vacuum monomial. -/
theorem quaternionBlockParityMismatch_nil_of_odd_degree
    (block : Nat) (monomial : List Nat)
    (hodd : quaternionBlockDegree block monomial % 2 = 1) :
    QuaternionBlockParityMismatch block monomial [] := by
  unfold QuaternionBlockParityMismatch
  by_cases hzero : exponentAt monomial (4 * block) % 2 = 0
  · by_cases hone : exponentAt monomial (4 * block + 1) % 2 = 0
    · by_cases htwo : exponentAt monomial (4 * block + 2) % 2 = 0
      · by_cases hthree : exponentAt monomial (4 * block + 3) % 2 = 0
        · exfalso
          unfold quaternionBlockDegree at hodd
          omega
        · refine ⟨3, by omega, ?_⟩
          simpa [exponentAt] using hthree
      · refine ⟨2, by omega, ?_⟩
        simpa [exponentAt] using htwo
    · refine ⟨1, by omega, ?_⟩
      simpa [exponentAt] using hone
  · refine ⟨0, by omega, ?_⟩
    simpa [exponentAt] using hzero

private theorem monoMul_nil_right_local (monomial : List Nat) :
    monoMul monomial [] = monomial := by
  cases monomial <;> rfl

/-- The exact normalized `S^3` moment of an odd-degree selected-block
monomial is zero.  This is the degree-to-parity bridge used by every odd
oriented word below. -/
theorem quaternionBlockMoment_zero_of_odd_degree
    (block : Nat) (monomial : List Nat)
    (hodd : quaternionBlockDegree block monomial % 2 = 1) :
    quaternionBlockMoment block monomial = 0 := by
  have hzero := quaternionBlockMoment_monoMul_zero_of_parityMismatch
    block monomial []
      (quaternionBlockParityMismatch_nil_of_odd_degree
        block monomial hodd)
  rw [monoMul_nil_right_local] at hzero
  exact hzero

/-- A raw polynomial homogeneous of odd selected-block degree has zero exact
partially integrated coefficient sum. -/
theorem blockIntegratedCoefficientSum_zero_of_odd_homogeneous
    (block degree : Nat) (polynomial : RatPoly)
    (hdegree : QuaternionBlockHomogeneousDegree
      block degree polynomial)
    (hodd : degree % 2 = 1) :
    blockIntegratedCoefficientSum block polynomial ≈ 0 := by
  induction polynomial with
  | nil =>
      exact Q'.eqv_refl 0
  | cons term tail ih =>
      have htermDegree := hdegree term (by simp)
      have hmoment : quaternionBlockMoment block term.1 = 0 :=
        quaternionBlockMoment_zero_of_odd_degree block term.1 (by
          rw [htermDegree]
          exact hodd)
      have htail : QuaternionBlockHomogeneousDegree block degree tail := by
        intro other hother
        exact hdegree other (by simp [hother])
      change
        term.2 * quaternionBlockMoment block term.1 +
            blockIntegratedCoefficientSum block tail ≈ 0
      rw [hmoment]
      exact Q'.eqv_trans _ ((0 : Q') + 0) _
        (q_add_congr (Q'.mul_zero_eqv term.2) (ih htail))
        (QPoly.q_zero_add_eqv 0)

/-- Honest-complex form of odd homogeneous partial Haar vanishing. -/
theorem integratedComplexCoefficientSum_zero_of_odd_homogeneous
    (block degree : Nat) (value : ComplexRatPoly)
    (hdegree : ComplexQuaternionBlockHomogeneousDegree
      block degree value)
    (hodd : degree % 2 = 1) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block value) (0, 0) := by
  exact
    ⟨blockIntegratedCoefficientSum_zero_of_odd_homogeneous
        block degree value.1 hdegree.1 hodd,
      blockIntegratedCoefficientSum_zero_of_odd_homogeneous
        block degree value.2 hdegree.2 hodd⟩

/-- **Arbitrary-block odd-valent Haar vanishing.**  Every nonempty ordered
word of oriented fundamental coefficients with odd length has exact zero
partial Haar value at its selected quaternion block. -/
theorem integrated_orientedFundamentalWord_zero_of_odd
    (block : Nat) (first : FundamentalOccurrence)
    (rest : List FundamentalOccurrence)
    (hodd : (rest.length + 1) % 2 = 1) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedFundamentalWord block first rest))
      (0, 0) := by
  exact integratedComplexCoefficientSum_zero_of_odd_homogeneous
    block (rest.length + 1) (orientedFundamentalWord block first rest)
    (complexQuaternionBlockHomogeneousDegree_orientedFundamentalWord
      block first rest)
    hodd

/-! ## 4. Named cutoff-one odd-valence corollaries -/

def orientedOneValentFundamentalTerm
    (block : Nat) (first : FundamentalOccurrence) : ComplexRatPoly :=
  orientedFundamentalWord block first []

def orientedThreeValentFundamentalTerm
    (block : Nat)
    (first second third : FundamentalOccurrence) : ComplexRatPoly :=
  orientedFundamentalWord block first [second, third]

def orientedFiveValentFundamentalTerm
    (block : Nat)
    (first second third fourth fifth : FundamentalOccurrence) :
    ComplexRatPoly :=
  orientedFundamentalWord block first [second, third, fourth, fifth]

theorem integrated_orientedOneValentFundamentalTerm_zero
    (block : Nat) (first : FundamentalOccurrence) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedOneValentFundamentalTerm block first))
      (0, 0) := by
  exact integrated_orientedFundamentalWord_zero_of_odd
    block first [] (by simp)

theorem integrated_orientedThreeValentFundamentalTerm_zero
    (block : Nat)
    (first second third : FundamentalOccurrence) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedThreeValentFundamentalTerm block first second third))
      (0, 0) := by
  exact integrated_orientedFundamentalWord_zero_of_odd
    block first [second, third] (by simp)

theorem integrated_orientedFiveValentFundamentalTerm_zero
    (block : Nat)
    (first second third fourth fifth : FundamentalOccurrence) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedFiveValentFundamentalTerm block
          first second third fourth fifth))
      (0, 0) := by
  exact integrated_orientedFundamentalWord_zero_of_odd
    block first [second, third, fourth, fifth] (by simp)

/-! ## 5. Independent-spectator lift -/

private theorem rationalComplexMul_zero_right
    (value : RationalComplex) :
    RationalComplexEqv
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        value (0, 0))
      (0, 0) := by
  constructor
  · refine Q'.eqv_trans _ ((0 : Q') + (-0)) _ ?_ ?_
    · exact q_add_congr
        (Q'.mul_zero_eqv value.1)
        (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv value.2))
    · decide
  · refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
    · exact q_add_congr
        (Q'.mul_zero_eqv value.1)
        (Q'.mul_zero_eqv value.2)
    · exact QPoly.q_zero_add_eqv 0

/-- An odd local word annihilates every complex spectator independent of its
selected in-range block. -/
theorem genericBlock_orientedFundamentalWord_odd_zero_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (first : FundamentalOccurrence)
    (rest : List FundamentalOccurrence)
    (hodd : (rest.length + 1) % 2 = 1) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (orientedFundamentalWord block first rest)))
      (0, 0) := by
  have hfactor := genericBlock_localFactor_with_complex_spectator
    blockCount block hblock spectator
    (orientedFundamentalWord block first rest)
    hindependent
    (complexQuaternionBlockLocal_orientedFundamentalWord block first rest)
    (0, 0)
    (integrated_orientedFundamentalWord_zero_of_odd
      block first rest hodd)
  have hzero := rationalComplexMul_zero_right
    (finiteProductHaarComplex blockCount spectator)
  exact
    ⟨Q'.eqv_trans _ _ _ hfactor.1 hzero.1,
      Q'.eqv_trans _ _ _ hfactor.2 hzero.2⟩

/-- A one-valent oriented fundamental insertion annihilates every complex
spectator independent of its selected in-range block. -/
theorem genericBlock_orientedOneValentFundamentalTerm_zero_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (first : FundamentalOccurrence) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (orientedOneValentFundamentalTerm block first)))
      (0, 0) := by
  simpa only [orientedOneValentFundamentalTerm] using
    (genericBlock_orientedFundamentalWord_odd_zero_with_complex_spectator
      blockCount block hblock spectator hindependent first [] (by simp))

/-- A three-valent oriented fundamental insertion annihilates every complex
spectator independent of its selected in-range block. -/
theorem genericBlock_orientedThreeValentFundamentalTerm_zero_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (first second third : FundamentalOccurrence) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (orientedThreeValentFundamentalTerm block first second third)))
      (0, 0) := by
  simpa only [orientedThreeValentFundamentalTerm] using
    (genericBlock_orientedFundamentalWord_odd_zero_with_complex_spectator
      blockCount block hblock spectator hindependent first
      [second, third] (by simp))

/-- A five-valent oriented fundamental insertion annihilates every complex
spectator independent of its selected in-range block. -/
theorem genericBlock_orientedFiveValentFundamentalTerm_zero_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (first second third fourth fifth : FundamentalOccurrence) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (orientedFiveValentFundamentalTerm block
            first second third fourth fifth)))
      (0, 0) := by
  simpa only [orientedFiveValentFundamentalTerm] using
    (genericBlock_orientedFundamentalWord_odd_zero_with_complex_spectator
      blockCount block hblock spectator hindependent first
      [second, third, fourth, fifth] (by simp))

#print axioms complexQuaternionBlockLocal_orientedFundamentalWord
#print axioms complexQuaternionBlockHomogeneousDegree_fundamentalOccurrence
#print axioms complexQuaternionBlockHomogeneousDegree_orientedFundamentalWord
#print axioms quaternionBlockParityMismatch_nil_of_odd_degree
#print axioms quaternionBlockMoment_zero_of_odd_degree
#print axioms blockIntegratedCoefficientSum_zero_of_odd_homogeneous
#print axioms integrated_orientedFundamentalWord_zero_of_odd
#print axioms integrated_orientedOneValentFundamentalTerm_zero
#print axioms integrated_orientedThreeValentFundamentalTerm_zero
#print axioms integrated_orientedFiveValentFundamentalTerm_zero
#print axioms genericBlock_orientedFundamentalWord_odd_zero_with_complex_spectator
#print axioms genericBlock_orientedOneValentFundamentalTerm_zero_with_complex_spectator
#print axioms genericBlock_orientedThreeValentFundamentalTerm_zero_with_complex_spectator
#print axioms genericBlock_orientedFiveValentFundamentalTerm_zero_with_complex_spectator

end YMGap.Continuum.SU2QuaternionGenericBlockOddValentHaarVanishing
