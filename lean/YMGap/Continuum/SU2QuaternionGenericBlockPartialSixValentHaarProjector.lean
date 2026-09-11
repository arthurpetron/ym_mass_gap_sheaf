/-
# Arbitrary-block six-valent fundamental SU(2) Haar projector

This leaf closes the local production seam left by the one-link sixth moment:
the literal `F F F R R R` word may be integrated at any quaternion block,
then replaced beneath any complex spectator independent of that block.  The
same endpoint is supplied both in the signed inverse-Gram basis and in the
manifest five-channel Temperley--Lieb factorization.

# Evaluator fence

The 4,096 closed external-index configurations live in sixteen serially
chained modules, one 256-case theorem per Lean process.  This public theorem is
only a four-selector dispatcher.  No twelve-Bool sum, bounded labelling family,
trajectory, or raw weighted-SOS polynomial is materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjectorChunkTTTT
import YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge

namespace YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
open YMGap.Continuum.SU2QuaternionSixValentPairingGram
open YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge

/-! ## 1. Exact arbitrary-block normalized sixth moment -/

/-- **Exact arbitrary-block balanced fundamental sixth moment.**  Partial
integration at any quaternion block gives the same externally oriented
rank-five inverse-Gram projector as the certified block-zero Haar integral. -/
theorem integrated_threeForwardThreeReverse_projector
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (threeForwardThreeReverseFundamentalTerm block
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          thirdForwardRow thirdForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn
          thirdReverseRow thirdReverseColumn))
      (orientedSixFundamentalHaarProjector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn) := by
  change GenericBlockPartialSixValentProjectorStatement block
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    thirdForwardRow thirdForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn
    thirdReverseRow thirdReverseColumn
  cases firstForwardRow <;> cases firstForwardColumn <;>
    cases secondForwardRow <;> cases secondForwardColumn
  · exact genericBlock_partial_sixValent_chunk_ffff block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_ffft block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_fftf block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_fftt block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_ftff block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_ftft block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_fttf block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_fttt block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_tfff block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_tfft block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_tftf block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_tftt block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_ttff block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_ttft block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_tttf block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact genericBlock_partial_sixValent_chunk_tttt block
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn

/-! ## 2. Arbitrary-block sign and orientation regressions -/

theorem integrated_threeForwardThreeReverse_all_false (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (threeForwardThreeReverseFundamentalTerm block
          false false false false false false
          false false false false false false))
      (oneQuarter, 0) := by
  refine rationalComplexEqv_trans
    (integrated_threeForwardThreeReverse_projector block
      false false false false false false
      false false false false false false) ?_
  exact ⟨orientedSixFundamentalHaarProjectorScalar_all_false,
    Q'.eqv_refl 0⟩

theorem integrated_threeForwardThreeReverse_negative_entry (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (threeForwardThreeReverseFundamentalTerm block
          false false false false true true
          false false false true true false))
      (-oneTwelfth, 0) := by
  refine rationalComplexEqv_trans
    (integrated_threeForwardThreeReverse_projector block
      false false false false true true
      false false false true true false) ?_
  exact ⟨orientedSixFundamentalHaarProjectorScalar_negative_entry,
    Q'.eqv_refl 0⟩

theorem integrated_threeForwardThreeReverse_transpose_sensitive_entry
    (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (threeForwardThreeReverseFundamentalTerm block
          false false false false false true
          false false false false true false))
      (oneTwelfth, 0) := by
  refine rationalComplexEqv_trans
    (integrated_threeForwardThreeReverse_projector block
      false false false false false true
      false false false false true false) ?_
  exact ⟨orientedSixFundamentalHaarProjectorScalar_transpose_sensitive_entry,
    Q'.eqv_refl 0⟩

/-! ## 3. Compatibility and the manifest TL3 resolution -/

/-- At block zero the new partial-integration theorem agrees exactly with the
previous normalized one-link Haar functional. -/
theorem integrated_threeForwardThreeReverse_block_zero_compatible
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (integratedComplexCoefficientSum 0
        (threeForwardThreeReverseFundamentalTerm 0
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          thirdForwardRow thirdForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn
          thirdReverseRow thirdReverseColumn))
      (finiteProductHaarComplex 1
        (threeForwardThreeReverseFundamentalTerm 0
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          thirdForwardRow thirdForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn
          thirdReverseRow thirdReverseColumn)) := by
  exact rationalComplexEqv_trans
    (integrated_threeForwardThreeReverse_projector 0
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    (rationalComplexEqv_symm
      (oneLink_threeForward_threeReverse_fundamental_projector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn))

/-- The arbitrary-block partial integral equals the manifest sum of five
rank-one TL3 channel tensors with weights `1/4,1/2,1/2,2/3,2/3`. -/
theorem integrated_threeForwardThreeReverse_projector_TL_factorized
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (threeForwardThreeReverseFundamentalTerm block
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          thirdForwardRow thirdForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn
          thirdReverseRow thirdReverseColumn))
      (orientedSixFundamentalHaarProjectorTLFactorized
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn) := by
  exact rationalComplexEqv_trans
    (integrated_threeForwardThreeReverse_projector block
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    (rationalComplexEqv_trans
      (orientedSixFundamentalHaarProjector_eqv_TL_resolution
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn)
      (orientedSixFundamentalHaarProjectorTLResolved_eqv_factorized
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn))

/-! ## 4. Independent-spectator lifts -/

/-- **Arbitrary-block signed six-valent projector with an independent complex
spectator.** -/
theorem genericBlock_threeForwardThreeReverse_projector_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (threeForwardThreeReverseFundamentalTerm block
            firstForwardRow firstForwardColumn
            secondForwardRow secondForwardColumn
            thirdForwardRow thirdForwardColumn
            firstReverseRow firstReverseColumn
            secondReverseRow secondReverseColumn
            thirdReverseRow thirdReverseColumn)))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (orientedSixFundamentalHaarProjector
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          thirdForwardRow thirdForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn
          thirdReverseRow thirdReverseColumn)) := by
  exact genericBlock_localFactor_with_complex_spectator
    blockCount block hblock spectator
    (threeForwardThreeReverseFundamentalTerm block
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    hindependent
    (complexQuaternionBlockLocal_threeForwardThreeReverseFundamentalTerm
      block firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    (orientedSixFundamentalHaarProjector
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    (integrated_threeForwardThreeReverse_projector block
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)

/-- **Manifest positive-channel spectator endpoint.**  The local factor is
replaced directly by the five rank-one TL3 tensors, so no multiplication
congruence between two identically shaped rational-complex namespaces is
needed. -/
theorem genericBlock_threeForwardThreeReverse_projector_TL_factorized_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (threeForwardThreeReverseFundamentalTerm block
            firstForwardRow firstForwardColumn
            secondForwardRow secondForwardColumn
            thirdForwardRow thirdForwardColumn
            firstReverseRow firstReverseColumn
            secondReverseRow secondReverseColumn
            thirdReverseRow thirdReverseColumn)))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (orientedSixFundamentalHaarProjectorTLFactorized
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          thirdForwardRow thirdForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn
          thirdReverseRow thirdReverseColumn)) := by
  exact genericBlock_localFactor_with_complex_spectator
    blockCount block hblock spectator
    (threeForwardThreeReverseFundamentalTerm block
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    hindependent
    (complexQuaternionBlockLocal_threeForwardThreeReverseFundamentalTerm
      block firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    (orientedSixFundamentalHaarProjectorTLFactorized
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    (integrated_threeForwardThreeReverse_projector_TL_factorized block
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)

#print axioms integrated_threeForwardThreeReverse_projector
#print axioms integrated_threeForwardThreeReverse_all_false
#print axioms integrated_threeForwardThreeReverse_negative_entry
#print axioms integrated_threeForwardThreeReverse_transpose_sensitive_entry
#print axioms integrated_threeForwardThreeReverse_block_zero_compatible
#print axioms integrated_threeForwardThreeReverse_projector_TL_factorized
#print axioms genericBlock_threeForwardThreeReverse_projector_with_complex_spectator
#print axioms genericBlock_threeForwardThreeReverse_projector_TL_factorized_with_complex_spectator

end YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector
