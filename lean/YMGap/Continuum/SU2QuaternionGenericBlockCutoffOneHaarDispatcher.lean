/-
# Total cutoff-one local Haar dispatcher

A cutoff-one plaquette expansion can place at most six oriented fundamental
occurrences on one cubic-lattice link.  This leaf packages the seven possible
local valences as an inductive carrier.  Each branch reuses the exact theorem
already proved for that valence:

* valence zero is the normalized polynomial unit;
* valences one, three, and five vanish by selected-block parity;
* valence two is the orientation-complete Schur/epsilon kernel;
* valences four and six are the orientation-normalized inverse-Gram kernels.

The carrier is intentionally non-dependent.  In particular, no `Vector`,
bounded labelling family, Boolean assignment space, or global trace network is
materialized.  Each branch preserves the association of its source theorem.

The numbers `1,0,1,0,2,0,5` are named `invariantMultiplicity`: at this stage
they record the dimensions of the local invariant sectors selected by Haar.
This leaf does **not** call them ranks and makes no self-adjointness or
idempotence claim for a global operator.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGenericBlockOddValentHaarVanishing
import YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization

namespace YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector
open YMGap.Continuum.SU2QuaternionGenericBlockOddValentHaarVanishing
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization

/-! ## 1. Seven exact local valence branches -/

/-- A structurally exact cutoff-one local word.  Constructor payload order is
the literal occurrence order used by the corresponding polynomial carrier. -/
inductive CutoffOneHaarWord : Type where
  | v0
  | v1 (first : FundamentalOccurrence)
  | v2 (first second : FundamentalOccurrence)
  | v3 (first second third : FundamentalOccurrence)
  | v4 (first second third fourth : FundamentalOccurrence)
  | v5 (first second third fourth fifth : FundamentalOccurrence)
  | v6 (first second third fourth fifth sixth : FundamentalOccurrence)
deriving DecidableEq, Repr

/-- Literal number of fundamental occurrences in one local word. -/
def valence : CutoffOneHaarWord → Nat
  | .v0 => 0
  | .v1 _ => 1
  | .v2 _ _ => 2
  | .v3 _ _ _ => 3
  | .v4 _ _ _ _ => 4
  | .v5 _ _ _ _ _ => 5
  | .v6 _ _ _ _ _ _ => 6

/-- Dimension of the selected local `SU(2)` invariant sector.  This is a
local multiplicity only; no operator-rank statement is made here. -/
def invariantMultiplicity : CutoffOneHaarWord → Nat
  | .v0 => 1
  | .v1 _ => 0
  | .v2 _ _ => 1
  | .v3 _ _ _ => 0
  | .v4 _ _ _ _ => 2
  | .v5 _ _ _ _ _ => 0
  | .v6 _ _ _ _ _ _ => 5

/-- Exact table of `(valence, invariantMultiplicity)` for all seven
constructors.  Payloads do not affect either number. -/
theorem valence_invariantMultiplicity_table
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    (valence .v0, invariantMultiplicity .v0) = (0, 1) ∧
    (valence (.v1 first), invariantMultiplicity (.v1 first)) = (1, 0) ∧
    (valence (.v2 first second),
      invariantMultiplicity (.v2 first second)) = (2, 1) ∧
    (valence (.v3 first second third),
      invariantMultiplicity (.v3 first second third)) = (3, 0) ∧
    (valence (.v4 first second third fourth),
      invariantMultiplicity (.v4 first second third fourth)) = (4, 2) ∧
    (valence (.v5 first second third fourth fifth),
      invariantMultiplicity (.v5 first second third fourth fifth)) = (5, 0) ∧
    (valence (.v6 first second third fourth fifth sixth),
      invariantMultiplicity
        (.v6 first second third fourth fifth sixth)) = (6, 5) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/-! ## 2. Total polynomial term and total Haar kernel -/

/-- The exact local polynomial selected by one cutoff-one word.

The definitions used branchwise fix the raw association: the odd words retain
their right-associated nonempty carrier, the bivalent word its ordered binary
product, the four-word its paired association, and the six-word its canonical
left comb. -/
def cutoffOneFundamentalTerm
    (block : Nat) : CutoffOneHaarWord → ComplexRatPoly
  | .v0 => complexRatPolyOne
  | .v1 first =>
      orientedOneValentFundamentalTerm block first
  | .v2 first second =>
      orientedBivalentFundamentalTerm block first second
  | .v3 first second third =>
      orientedThreeValentFundamentalTerm block first second third
  | .v4 first second third fourth =>
      orientedFourFundamentalWord block first second third fourth
  | .v5 first second third fourth fifth =>
      orientedFiveValentFundamentalTerm block
        first second third fourth fifth
  | .v6 first second third fourth fifth sixth =>
      orientedSixFundamentalWord block
        first second third fourth fifth sixth

/-- The exact partial-Haar value of one cutoff-one local word. -/
def cutoffOneHaarKernel : CutoffOneHaarWord → RationalComplex
  | .v0 => rationalComplexOne
  | .v1 _ => rationalComplexZero
  | .v2 first second => orientedBivalentHaarKernel first second
  | .v3 _ _ _ => rationalComplexZero
  | .v4 first second third fourth =>
      orientedFourNormalizedHaarProjector first second third fourth
  | .v5 _ _ _ _ _ => rationalComplexZero
  | .v6 first second third fourth fifth sixth =>
      orientedSixNormalizedHaarProjector
        first second third fourth fifth sixth

/-! ## 3. The honest zero-valent branch -/

/-- The complex polynomial unit is local to every quaternion block.  This is
only the empty-word support statement needed by the dispatcher. -/
theorem complexQuaternionBlockLocal_complexRatPolyOne (block : Nat) :
    ComplexQuaternionBlockLocal block complexRatPolyOne := by
  constructor
  · intro term hterm coordinate _
    simp only [complexRatPolyOne, polyOne, List.mem_singleton] at hterm
    subst term
    rfl
  · intro term hterm
    simp only [complexRatPolyOne, polyZero, List.not_mem_nil] at hterm

/-- Partial integration of the empty local word is the normalized unit. -/
theorem integratedComplexCoefficientSum_complexRatPolyOne (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block complexRatPolyOne)
      rationalComplexOne := by
  constructor
  · change
      (1 * quaternionBlockMoment block [] + 0 : Q').eqv 1
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (q_add_zero_eqv (1 * quaternionBlockMoment block []))
        (Q'.one_mul_eqv (quaternionBlockMoment block [])))
      (quaternionBlockMoment_nil block)
  · exact Q'.eqv_refl 0

/-! ## 4. Total selected-block theorem -/

/-- Every cutoff-one local term is supported entirely on its selected block. -/
theorem complexQuaternionBlockLocal_cutoffOneFundamentalTerm
    (block : Nat) (word : CutoffOneHaarWord) :
    ComplexQuaternionBlockLocal block
      (cutoffOneFundamentalTerm block word) := by
  cases word with
  | v0 =>
      exact complexQuaternionBlockLocal_complexRatPolyOne block
  | v1 first =>
      exact complexQuaternionBlockLocal_orientedFundamentalWord
        block first []
  | v2 first second =>
      exact
        YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector.complexQuaternionBlockLocal_orientedBivalentFundamentalTerm
          block first second
  | v3 first second third =>
      exact complexQuaternionBlockLocal_orientedFundamentalWord
        block first [second, third]
  | v4 first second third fourth =>
      exact
        YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization.complexQuaternionBlockLocal_orientedFourFundamentalWord
          block first second third fourth
  | v5 first second third fourth fifth =>
      exact complexQuaternionBlockLocal_orientedFundamentalWord
        block first [second, third, fourth, fifth]
  | v6 first second third fourth fifth sixth =>
      exact
        YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization.complexQuaternionBlockLocal_orientedSixFundamentalWord
          block first second third fourth fifth sixth

/-- **Total exact selected-block projector for cutoff-one valence `0..6`.** -/
theorem integrated_cutoffOneFundamentalTerm_projector
    (block : Nat) (word : CutoffOneHaarWord) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (cutoffOneFundamentalTerm block word))
      (cutoffOneHaarKernel word) := by
  cases word with
  | v0 =>
      exact integratedComplexCoefficientSum_complexRatPolyOne block
  | v1 first =>
      exact integrated_orientedOneValentFundamentalTerm_zero block first
  | v2 first second =>
      exact integrated_orientedBivalentFundamentalTerm_projector
        block first second
  | v3 first second third =>
      exact integrated_orientedThreeValentFundamentalTerm_zero
        block first second third
  | v4 first second third fourth =>
      exact integrated_orientedFourFundamentalWord_projector
        block first second third fourth
  | v5 first second third fourth fifth =>
      exact integrated_orientedFiveValentFundamentalTerm_zero
        block first second third fourth fifth
  | v6 first second third fourth fifth sixth =>
      exact integrated_orientedSixFundamentalWord_projector
        block first second third fourth fifth sixth

/-! ## 5. One total independent-spectator theorem -/

/-- **Every cutoff-one local valence can be eliminated under one arbitrary
complex spectator independent of the selected in-range block.**

The proof deliberately performs constructor cases before invoking the generic
local-factor theorem.  Thus the seven carrier branches remain definitionally
visible and no hidden dependent-length conversion is introduced. -/
theorem genericBlock_cutoffOneFundamentalTerm_projector_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (word : CutoffOneHaarWord) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (cutoffOneFundamentalTerm block word)))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (cutoffOneHaarKernel word)) := by
  cases word with
  | v0 =>
      exact genericBlock_localFactor_with_complex_spectator
        blockCount block hblock spectator complexRatPolyOne
        hindependent
        (complexQuaternionBlockLocal_complexRatPolyOne block)
        rationalComplexOne
        (integratedComplexCoefficientSum_complexRatPolyOne block)
  | v1 first =>
      exact genericBlock_localFactor_with_complex_spectator
        blockCount block hblock spectator
        (orientedOneValentFundamentalTerm block first)
        hindependent
        (complexQuaternionBlockLocal_orientedFundamentalWord
          block first [])
        rationalComplexZero
        (integrated_orientedOneValentFundamentalTerm_zero block first)
  | v2 first second =>
      exact genericBlock_localFactor_with_complex_spectator
        blockCount block hblock spectator
        (orientedBivalentFundamentalTerm block first second)
        hindependent
        (YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector.complexQuaternionBlockLocal_orientedBivalentFundamentalTerm
          block first second)
        (orientedBivalentHaarKernel first second)
        (integrated_orientedBivalentFundamentalTerm_projector
          block first second)
  | v3 first second third =>
      exact genericBlock_localFactor_with_complex_spectator
        blockCount block hblock spectator
        (orientedThreeValentFundamentalTerm block first second third)
        hindependent
        (complexQuaternionBlockLocal_orientedFundamentalWord
          block first [second, third])
        rationalComplexZero
        (integrated_orientedThreeValentFundamentalTerm_zero
          block first second third)
  | v4 first second third fourth =>
      exact genericBlock_localFactor_with_complex_spectator
        blockCount block hblock spectator
        (orientedFourFundamentalWord block first second third fourth)
        hindependent
        (YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization.complexQuaternionBlockLocal_orientedFourFundamentalWord
          block first second third fourth)
        (orientedFourNormalizedHaarProjector first second third fourth)
        (integrated_orientedFourFundamentalWord_projector
          block first second third fourth)
  | v5 first second third fourth fifth =>
      exact genericBlock_localFactor_with_complex_spectator
        blockCount block hblock spectator
        (orientedFiveValentFundamentalTerm block
          first second third fourth fifth)
        hindependent
        (complexQuaternionBlockLocal_orientedFundamentalWord
          block first [second, third, fourth, fifth])
        rationalComplexZero
        (integrated_orientedFiveValentFundamentalTerm_zero
          block first second third fourth fifth)
  | v6 first second third fourth fifth sixth =>
      exact genericBlock_localFactor_with_complex_spectator
        blockCount block hblock spectator
        (orientedSixFundamentalWord block
          first second third fourth fifth sixth)
        hindependent
        (YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization.complexQuaternionBlockLocal_orientedSixFundamentalWord
          block first second third fourth fifth sixth)
        (orientedSixNormalizedHaarProjector
          first second third fourth fifth sixth)
        (integrated_orientedSixFundamentalWord_projector
          block first second third fourth fifth sixth)

#print axioms valence_invariantMultiplicity_table
#print axioms complexQuaternionBlockLocal_complexRatPolyOne
#print axioms integratedComplexCoefficientSum_complexRatPolyOne
#print axioms complexQuaternionBlockLocal_cutoffOneFundamentalTerm
#print axioms integrated_cutoffOneFundamentalTerm_projector
#print axioms genericBlock_cutoffOneFundamentalTerm_projector_with_complex_spectator

end YMGap.Continuum.SU2QuaternionGenericBlockCutoffOneHaarDispatcher
