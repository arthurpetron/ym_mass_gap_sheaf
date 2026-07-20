/-
# Exact one-link six-valent fundamental SU(2) Haar projector

This leaf identifies the normalized quaternion `S^3` sixth moment of three
forward and three reverse fundamental coefficients with the signed
five-channel inverse-Gram kernel constructed in
`SU2QuaternionSixValentPairingGram`.

The literal local word is ordered `F F F R R R`.  Each reverse coefficient
already contains conjugate transpose, so the target pairs forward rows with
external reverse columns and forward columns with external reverse rows.

# Evaluator fence

The 4096 closed index configurations are divided among sixteen declarations,
each with only eight Boolean cases (256 configurations).  Four chained chunk
modules hold four declarations apiece, forcing fresh Lean processes and
serial dependency order.  The public theorem below is only a four-index
dispatcher.  No twelve-deep Boolean sum is unfolded, reduced, evaluated, or
printed.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjectorChunkTT

namespace YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionSixValentPairingGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact normalized sixth moment -/

/-- **Exact balanced fundamental sixth moment.**  The normalized one-block
quaternion Haar integral is the externally oriented rank-five invariant
projector with the certified inverse Gram matrix. -/
theorem oneLink_threeForward_threeReverse_fundamental_projector
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (threeForwardThreeReverseFundamentalTerm 0
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
  change OneLinkSixValentProjectorStatement
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    thirdForwardRow thirdForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn
    thirdReverseRow thirdReverseColumn
  cases firstForwardRow <;> cases firstForwardColumn <;>
    cases secondForwardRow <;> cases secondForwardColumn
  · exact oneLink_sixValent_chunk_ffff
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_ffft
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_fftf
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_fftt
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_ftff
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_ftft
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_fttf
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_fttt
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_tfff
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_tfft
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_tftf
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_tftt
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_ttff
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_ttft
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_tttf
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn
  · exact oneLink_sixValent_chunk_tttt
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn

/-! ## 2. Independent degree-six moment table -/

/-- The three nonzero normalized `S^3` sixth-moment orbit types.  Odd
exponents vanish definitionally from `sphereMoment4`; these values certify
the denominator `4 * 6 * 8 = 192` independently of the matrix kernel. -/
theorem sphereMoment4_degree_six_orbit_table :
    sphereMoment4 6 0 0 0 ≈ Q'.mkPos 5 64 (by decide) ∧
    sphereMoment4 4 2 0 0 ≈ Q'.mkPos 1 64 (by decide) ∧
    sphereMoment4 2 2 2 0 ≈ Q'.mkPos 1 192 (by decide) := by
  decide

/-! ## 3. Analytic acceptance pins -/

/-- The exact sixth moment has the positive all-equal entry `1/4`. -/
theorem oneLink_threeForward_threeReverse_all_false :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (threeForwardThreeReverseFundamentalTerm 0
          false false false false false false
          false false false false false false))
      (oneQuarter, 0) := by
  refine rationalComplexEqv_trans
    (oneLink_threeForward_threeReverse_fundamental_projector
      false false false false false false
      false false false false false false) ?_
  exact ⟨orientedSixFundamentalHaarProjectorScalar_all_false,
    Q'.eqv_refl 0⟩

/-- The exact sixth moment retains the negative inverse-Gram interference
entry `-1/12`. -/
theorem oneLink_threeForward_threeReverse_negative_entry :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (threeForwardThreeReverseFundamentalTerm 0
          false false false false true true
          false false false true true false))
      (-oneTwelfth, 0) := by
  refine rationalComplexEqv_trans
    (oneLink_threeForward_threeReverse_fundamental_projector
      false false false false true true
      false false false true true false) ?_
  exact ⟨orientedSixFundamentalHaarProjectorScalar_negative_entry,
    Q'.eqv_refl 0⟩

/-- The raw sixth moment realizes the transpose-sensitive `1/12` entry. -/
theorem oneLink_threeForward_threeReverse_transpose_sensitive_entry :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (threeForwardThreeReverseFundamentalTerm 0
          false false false false false true
          false false false false true false))
      (oneTwelfth, 0) := by
  refine rationalComplexEqv_trans
    (oneLink_threeForward_threeReverse_fundamental_projector
      false false false false false true
      false false false false true false) ?_
  exact
    ⟨orientedSixFundamentalHaarProjectorScalar_transpose_sensitive_entry,
      Q'.eqv_refl 0⟩

#print axioms sphereMoment4_degree_six_orbit_table
#print axioms oneLink_threeForward_threeReverse_fundamental_projector
#print axioms oneLink_threeForward_threeReverse_all_false
#print axioms oneLink_threeForward_threeReverse_negative_entry
#print axioms oneLink_threeForward_threeReverse_transpose_sensitive_entry

end YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
