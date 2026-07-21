/-
# Orientation-complete arbitrary-block bivalent SU(2) Haar projector

The existing generic Schur leaf contracts one forward and one reverse
fundamental coefficient.  A cutoff-one link word is not necessarily balanced:
its two occurrences may instead be `F F`, `R F`, or `R R`.  Fundamental
self-duality supplies the missing signed epsilon contractions.

This leaf gives one total bivalent kernel for all four orientation patterns,
proves its exact partial integral at an arbitrary quaternion block, and lifts
the replacement beneath an independent complex spectator.  The proof splits
only two orientations and four Boolean indices; no face-index network or
bounded labelling family is materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
import YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport

namespace YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality

/-! ## 1. Total oriented bivalent carrier -/

/-- The literal ordered product of two oriented fundamental occurrences. -/
def orientedBivalentFundamentalTerm
    (block : Nat)
    (first second : FundamentalOccurrence) : ComplexRatPoly :=
  complexRatPolyMul
    (fundamentalOccurrenceCoefficient block first)
    (fundamentalOccurrenceCoefficient block second)

/-- The total signed bivalent Haar kernel.  Opposite orientations use the
crossed Schur delta; equal orientations use the epsilon pairing. -/
def orientedBivalentHaarKernel
    (first second : FundamentalOccurrence) : RationalComplex :=
  match first.orientation, second.orientation with
  | .forward, .reverse =>
      orientedFundamentalSchurDelta
        first.row first.column second.row second.column
  | .reverse, .forward =>
      orientedFundamentalSchurDelta
        second.row second.column first.row first.column
  | .forward, .forward =>
      sameOrientationFundamentalSchurDelta
        first.row first.column second.row second.column
  | .reverse, .reverse =>
      sameOrientationFundamentalSchurDelta
        first.row first.column second.row second.column

/-! ## 2. Exact arbitrary-block projector -/

/-- Every oriented fundamental occurrence is local to its selected quaternion
block. -/
theorem complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
    (block : Nat) (occurrence : FundamentalOccurrence) :
    ComplexQuaternionBlockLocal block
      (fundamentalOccurrenceCoefficient block occurrence) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation
  · exact complexQuaternionBlockLocal_forwardFundamentalCoefficient
      block row column
  · exact complexQuaternionBlockLocal_reverseFundamentalCoefficient
      block row column

/-- The ordered bivalent word is supported entirely on its selected block. -/
theorem complexQuaternionBlockLocal_orientedBivalentFundamentalTerm
    (block : Nat) (first second : FundamentalOccurrence) :
    ComplexQuaternionBlockLocal block
      (orientedBivalentFundamentalTerm block first second) := by
  exact complexQuaternionBlockLocal_mul
    (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient block first)
    (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient block second)

/-- **Exact orientation-complete arbitrary-block bivalent projector.** -/
theorem integrated_orientedBivalentFundamentalTerm_projector
    (block : Nat) (first second : FundamentalOccurrence) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedBivalentFundamentalTerm block first second))
      (orientedBivalentHaarKernel first second) := by
  rcases first with ⟨firstOrientation, firstRow, firstColumn⟩
  rcases second with ⟨secondOrientation, secondRow, secondColumn⟩
  cases firstOrientation <;> cases secondOrientation <;>
    cases firstRow <;> cases firstColumn <;>
    cases secondRow <;> cases secondColumn <;>
    constructor <;>
      simp only [integratedComplexCoefficientSum,
        blockIntegratedCoefficientSum,
        integrateQuaternionBlock, integrateQuaternionBlockTerm,
        orientedBivalentFundamentalTerm, fundamentalOccurrenceCoefficient,
        orientedFundamentalCoefficient, forwardFundamentalCoefficient,
        reverseFundamentalCoefficient, complexRatPolyConj,
        fundamentalLinkQuaternion, fundamentalMatrixCoefficient, variablesAt,
        complexRatPolyMul, polyAdd, polyMul, polyNeg, polyVar, coefficientSum,
        List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.nil_append, List.cons_append,
        quaternionBlockMoment, exponentAt_monoMul,
        exponentAt_blockVariableNat, exponentAt_blockBase_query,
        exponentAt_blockComponent_base, exponentAt_blockBase_base,
        orientedBivalentHaarKernel, orientedFundamentalSchurDelta,
        sameOrientationFundamentalSchurDelta, fundamentalDualitySign] <;>
      decide

/-- The forward/reverse branch is exactly the existing arbitrary-block Schur
coefficient-sum theorem. -/
theorem integrated_orientedBivalent_forward_reverse_compatible
    (block : Nat)
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedBivalentFundamentalTerm block
          ⟨.forward, forwardRow, forwardColumn⟩
          ⟨.reverse, reverseRow, reverseColumn⟩))
      (orientedFundamentalSchurDelta
        forwardRow forwardColumn reverseRow reverseColumn) := by
  simpa [orientedBivalentFundamentalTerm,
    fundamentalOccurrenceCoefficient, orientedFundamentalCoefficient,
    orientedFundamentalLinkContraction] using
    integrated_orientedFundamentalLinkContraction_coefficientSum block
      forwardRow forwardColumn reverseRow reverseColumn

/-! ## 3. Independent-spectator lift -/

/-- **Orientation-complete bivalent projector beneath an independent complex
spectator at an arbitrary in-range block.** -/
theorem genericBlock_orientedBivalent_projector_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (first second : FundamentalOccurrence) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (orientedBivalentFundamentalTerm block first second)))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (orientedBivalentHaarKernel first second)) := by
  exact genericBlock_localFactor_with_complex_spectator
    blockCount block hblock spectator
    (orientedBivalentFundamentalTerm block first second)
    hindependent
    (complexQuaternionBlockLocal_orientedBivalentFundamentalTerm
      block first second)
    (orientedBivalentHaarKernel first second)
    (integrated_orientedBivalentFundamentalTerm_projector block first second)

/-! ## 4. Arbitrary-block sign pins -/

theorem integrated_twoForward_diagonal_selfDual (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedBivalentFundamentalTerm block
          ⟨.forward, false, false⟩ ⟨.forward, true, true⟩))
      (Q'.invSucc 1, 0) := by
  have h := integrated_orientedBivalentFundamentalTerm_projector block
    (⟨.forward, false, false⟩ : FundamentalOccurrence)
    (⟨.forward, true, true⟩ : FundamentalOccurrence)
  exact ⟨Q'.eqv_trans _ _ _ h.1 (by decide),
    Q'.eqv_trans _ _ _ h.2 (by decide)⟩

theorem integrated_twoForward_offDiagonal_selfDual (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedBivalentFundamentalTerm block
          ⟨.forward, false, true⟩ ⟨.forward, true, false⟩))
      (-Q'.invSucc 1, 0) := by
  have h := integrated_orientedBivalentFundamentalTerm_projector block
    (⟨.forward, false, true⟩ : FundamentalOccurrence)
    (⟨.forward, true, false⟩ : FundamentalOccurrence)
  exact ⟨Q'.eqv_trans _ _ _ h.1 (by decide),
    Q'.eqv_trans _ _ _ h.2 (by decide)⟩

#print axioms complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
#print axioms complexQuaternionBlockLocal_orientedBivalentFundamentalTerm
#print axioms integrated_orientedBivalentFundamentalTerm_projector
#print axioms integrated_orientedBivalent_forward_reverse_compatible
#print axioms genericBlock_orientedBivalent_projector_with_complex_spectator
#print axioms integrated_twoForward_diagonal_selfDual
#print axioms integrated_twoForward_offDiagonal_selfDual

end YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector
