/-
# Located shifted-exponential quadratic limit for the compact BF4 action

For the genuine compact coupled BF4 action `A`, put

  D = 133/4 - A.

`BF4CompactActionShiftedExponential` proves that every rational coefficient

  (1/n!) H_10(P² Dⁿ)

is nonnegative for a supported insertion `P`.  This file proves the missing
quantitative analytic statement: the corresponding positive Taylor partials
have an explicit constructive factorial-tail modulus and therefore define a
located `CReal`.

The coefficient `L¹` norm is used only as a scalar majorant for convergence.
The coefficients and their positivity remain the exact tenfold-Haar
coefficients of the physical compact action.

## Axiom gate

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CompactActionShiftedExponential

namespace YMGap.Continuum.BF4CompactActionShiftedLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RatNat
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4CompactActionShiftedExponential

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact factorial majorant -/

/-- Coefficient `L¹` norm of the genuine normalized complement `D`. -/
def compactActionComplementL1 : Q' :=
  polynomialCoefficientL1 compactActionComplementPolynomial

/-- Squared coefficient norm of an inserted polynomial. -/
def compactActionShiftedInsertionL1
    (polynomial : RatPoly) : Q' :=
  polynomialCoefficientL1 polynomial *
    polynomialCoefficientL1 polynomial

theorem compactActionComplementL1_nonnegative :
    (0 : Q') ≤ compactActionComplementL1 :=
  polynomialCoefficientL1_nonnegative _

theorem compactActionShiftedInsertionL1_nonnegative
    (polynomial : RatPoly) :
    (0 : Q') ≤ compactActionShiftedInsertionL1 polynomial :=
  Q'.mul_nonneg _ _
    (polynomialCoefficientL1_nonnegative polynomial)
    (polynomialCoefficientL1_nonnegative polynomial)

private theorem qpow_nonnegative
  (value : Q') (hvalue : (0 : Q') ≤ value) :
    ∀ exponent : Nat,
      (0 : Q') ≤ qpow value exponent
  | 0 => by
      change (0 : Q') ≤ 1
      decide
  | exponent + 1 =>
      Q'.mul_nonneg _ _
        (qpow_nonnegative value hvalue exponent)
        hvalue

/-- Coefficient norm of a literal polynomial power. -/
theorem polynomialCoefficientL1_polynomialPower_le
    (polynomial : RatPoly) :
    ∀ exponent : Nat,
      polynomialCoefficientL1
          (polynomialPower polynomial exponent) ≤
        qpow (polynomialCoefficientL1 polynomial) exponent
  | 0 => by
      change Q'.abs (1 : Q') + 0 ≤ 1
      decide
  | exponent + 1 => by
      have hnorm0 :
          (0 : Q') ≤
            polynomialCoefficientL1 polynomial :=
        polynomialCoefficientL1_nonnegative polynomial
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le
          (polynomialPower polynomial exponent)
          polynomial)
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          (polynomialCoefficientL1_polynomialPower_le
            polynomial exponent)
          hnorm0)

private theorem compactActionShiftedHalfFactor_l1_le
    (polynomial : RatPoly) (exponent : Nat) :
    polynomialCoefficientL1
        (compactActionShiftedHalfFactor polynomial exponent) ≤
      polynomialCoefficientL1 polynomial *
        qpow compactActionComplementL1 (exponent / 2) := by
  exact Q'.le_trans' _ _ _
    (polynomialCoefficientL1_mul_le
      polynomial
      (compactActionComplementHalfPower exponent))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (polynomialCoefficientL1_polynomialPower_le
        compactActionComplementPolynomial
        (exponent / 2))
      (polynomialCoefficientL1_nonnegative polynomial))

/-- The manifest square/square-times-complement carrier has the expected
coefficient-norm growth `‖P‖₁² ‖D‖₁ⁿ`. -/
theorem compactActionShiftedMomentSquarePolynomial_l1_le
    (polynomial : RatPoly) (exponent : Nat) :
    polynomialCoefficientL1
        (compactActionShiftedMomentSquarePolynomial
          polynomial exponent) ≤
      compactActionShiftedInsertionL1 polynomial *
        qpow compactActionComplementL1 exponent := by
  let p := polynomialCoefficientL1 polynomial
  let d := compactActionComplementL1
  let halfIndex := exponent / 2
  let factor :=
    compactActionShiftedHalfFactor polynomial exponent
  let bound := p * qpow d halfIndex
  have hp0 : (0 : Q') ≤ p :=
    polynomialCoefficientL1_nonnegative polynomial
  have hd0 : (0 : Q') ≤ d :=
    compactActionComplementL1_nonnegative
  have hfactor0 :
      (0 : Q') ≤ polynomialCoefficientL1 factor :=
    polynomialCoefficientL1_nonnegative factor
  have hbound0 : (0 : Q') ≤ bound :=
    Q'.mul_nonneg _ _ hp0
      (qpow_nonnegative d hd0 halfIndex)
  have hfactor :
      polynomialCoefficientL1 factor ≤ bound :=
    compactActionShiftedHalfFactor_l1_le
      polynomial exponent
  unfold compactActionShiftedMomentSquarePolynomial
  by_cases heven : exponent % 2 = 0
  · rw [if_pos heven]
    have hexponent :
        halfIndex + halfIndex = exponent := by
      unfold halfIndex
      omega
    have hproduct :
        polynomialCoefficientL1
            (polyMul factor factor) ≤
          bound * bound := by
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le factor factor)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _
            hfactor hfactor0)
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            hfactor hbound0))
    refine Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv ?_)
    unfold bound
    refine Q'.eqv_trans _ _ _
      (q_mul4_swap p (qpow d halfIndex)
        p (qpow d halfIndex)) ?_
    rw [← hexponent]
    exact Q'.mul_eqv_congr_left (p * p) _ _
      (Q'.eqv_symm
        (qpow_add d halfIndex halfIndex))
  · rw [if_neg heven]
    have hodd : exponent % 2 = 1 := by
      have hlt : exponent % 2 < 2 :=
        Nat.mod_lt exponent (by decide)
      omega
    have hexponent :
        halfIndex + halfIndex + 1 = exponent := by
      unfold halfIndex
      omega
    have hfactorSquare :
        polynomialCoefficientL1
            (polyMul factor factor) ≤
          bound * bound := by
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le factor factor)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _
            hfactor hfactor0)
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            hfactor hbound0))
    have hproduct :
        polynomialCoefficientL1
            (polyMul (polyMul factor factor)
              compactActionComplementPolynomial) ≤
          (bound * bound) * d := by
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le
          (polyMul factor factor)
          compactActionComplementPolynomial)
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          hfactorSquare hd0)
    refine Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv ?_)
    unfold bound
    refine Q'.eqv_trans _
      (((p * p) *
        (qpow d halfIndex * qpow d halfIndex)) * d) _
      (Q'.mul_eqv_congr_right _ _ _
        (q_mul4_swap p (qpow d halfIndex)
          p (qpow d halfIndex))) ?_
    refine Q'.eqv_trans _
      (((p * p) *
        qpow d (halfIndex + halfIndex)) * d) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left (p * p) _ _
          (Q'.eqv_symm
            (qpow_add d halfIndex halfIndex)))) ?_
    refine Q'.eqv_trans _
      ((p * p) *
        (qpow d (halfIndex + halfIndex) * d)) _
      (Q'.mul_assoc_eqv
        (p * p) (qpow d (halfIndex + halfIndex)) d) ?_
    have hpower :
        qpow d (halfIndex + halfIndex) * d =
          qpow d (halfIndex + halfIndex + 1) := rfl
    rw [hpower, hexponent]
    exact Q'.eqv_refl _

/-- Factorization of the magnitude coefficient:
`xⁿ/n! = xⁿ · (1/n!)`. -/
theorem termAbs_eq_qpow_mul_unit
    (value : Q') :
    ∀ exponent : Nat,
      ExpNeg.termAbs value exponent ≈
        qpow value exponent *
          ExpNeg.termAbs 1 exponent
  | 0 => by
      exact Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      refine Q'.eqv_trans _
        ((qpow value exponent *
            ExpNeg.termAbs 1 exponent) *
          (value * Q'.invSucc exponent)) _
        (Q'.mul_eqv_congr_right _ _ _
          (termAbs_eq_qpow_mul_unit value exponent)) ?_
      refine Q'.eqv_trans _
        ((qpow value exponent * value) *
          (ExpNeg.termAbs 1 exponent *
            Q'.invSucc exponent)) _
        (q_mul4_swap
          (qpow value exponent)
          (ExpNeg.termAbs 1 exponent)
          value (Q'.invSucc exponent)) ?_
      exact Q'.mul_eqv_congr_left
        (qpow value exponent * value) _ _
        (Q'.eqv_symm
          (Q'.mul_eqv_congr_left
            (ExpNeg.termAbs 1 exponent)
            (1 * Q'.invSucc exponent)
            (Q'.invSucc exponent)
            (Q'.one_mul_eqv
              (Q'.invSucc exponent))))

/-- Quantitative all-label factorial domination of the genuine shifted
quadratic coefficient. -/
theorem compactActionShiftedTaylorQuadraticTerm_le_majorant
    (polynomial : RatPoly) (exponent : Nat) :
    compactActionShiftedTaylorQuadraticTerm
        polynomial exponent ≤
      compactActionShiftedInsertionL1 polynomial *
        ExpNeg.termAbs compactActionComplementL1 exponent := by
  let moment :=
    compactActionShiftedMomentSquarePolynomial
      polynomial exponent
  let scale := compactActionShiftedInsertionL1 polynomial
  let d := compactActionComplementL1
  have hunit0 :
      (0 : Q') ≤ ExpNeg.termAbs 1 exponent :=
    ExpNeg.termAbs_nonneg 1 (by decide) exponent
  have hmoment :
      tenfoldHaar moment ≤
        polynomialCoefficientL1 moment := by
    exact Q'.le_trans' _ _ _
      (Q'.le_abs_self (tenfoldHaar moment))
      (quaternionHaar_abs_le_coefficientL1 10 moment)
  have hl1 :=
    compactActionShiftedMomentSquarePolynomial_l1_le
      polynomial exponent
  unfold compactActionShiftedTaylorQuadraticTerm
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      hmoment hunit0)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        hl1 hunit0)
      (Q'.le_of_eqv ?_))
  refine Q'.eqv_trans _
    ((ExpNeg.termAbs 1 exponent * scale) *
      qpow d exponent) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (ExpNeg.termAbs 1 exponent)
        scale (qpow d exponent))) ?_
  refine Q'.eqv_trans _
    ((scale * ExpNeg.termAbs 1 exponent) *
      qpow d exponent) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv
        (ExpNeg.termAbs 1 exponent) scale)) ?_
  refine Q'.eqv_trans _
    (scale *
      (ExpNeg.termAbs 1 exponent *
        qpow d exponent)) _
    (Q'.mul_assoc_eqv scale
      (ExpNeg.termAbs 1 exponent)
      (qpow d exponent)) ?_
  refine Q'.eqv_trans _
    (scale *
      (qpow d exponent *
        ExpNeg.termAbs 1 exponent)) _
    (Q'.mul_eqv_congr_left scale _ _
      (Q'.mul_comm_eqv
        (ExpNeg.termAbs 1 exponent)
        (qpow d exponent))) ?_
  exact Q'.mul_eqv_congr_left scale _ _
    (Q'.eqv_symm
      (termAbs_eq_qpow_mul_unit d exponent))

/-! ## 2. Explicit Cauchy modulus -/

theorem compactActionShiftedTaylorQuadraticPartial_add_mono
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (start : Nat) :
    ∀ distance : Nat,
      compactActionShiftedTaylorQuadraticPartial
          polynomial start ≤
        compactActionShiftedTaylorQuadraticPartial
          polynomial (start + distance)
  | 0 => Q'.le_refl' _
  | distance + 1 => by
      exact Q'.le_trans' _ _ _
        (compactActionShiftedTaylorQuadraticPartial_add_mono
          polynomial hsupport start distance)
        (compactActionShiftedTaylorQuadraticPartial_monotone
          polynomial hsupport (start + distance))

private theorem compactActionShiftedTaylorQuadraticPartial_block_upper
    (polynomial : RatPoly) (start : Nat) :
    ∀ distance : Nat,
      compactActionShiftedTaylorQuadraticPartial
          polynomial (start + distance) ≤
        compactActionShiftedTaylorQuadraticPartial
            polynomial start +
          scaledTaylorBlockAbs
            (compactActionShiftedInsertionL1 polynomial)
            compactActionComplementL1 start distance
  | 0 =>
      Q'.add_le_self_of_nonneg _ _
        (Q'.le_refl' 0)
  | distance + 1 => by
      have hinduction :=
        compactActionShiftedTaylorQuadraticPartial_block_upper
          polynomial start distance
      have hterm :=
        compactActionShiftedTaylorQuadraticTerm_le_majorant
          polynomial (start + distance)
      exact Q'.le_trans' _ _ _
        (ExpNeg.add_le_add2 hinduction hterm)
        (Q'.le_of_eqv
          (Q'.add_assoc_eqv
            (compactActionShiftedTaylorQuadraticPartial
              polynomial start)
            (scaledTaylorBlockAbs
              (compactActionShiftedInsertionL1 polynomial)
              compactActionComplementL1 start distance)
            (compactActionShiftedInsertionL1 polynomial *
              ExpNeg.termAbs compactActionComplementL1
                (start + distance))))

/-- Explicit cutoff for the shifted quadratic series. -/
def compactActionShiftedTaylorModulus
    (polynomial : RatPoly) (epsilon : Q') : Nat :=
  let scale :=
    compactActionShiftedInsertionL1 polynomial
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  max
    (halfRatioCutoff compactActionComplementL1)
    (ExpNeg.termAbsModulus
      compactActionComplementL1
      (HalfPow.half * delta))

/-- Constructive factorial-tail Cauchy estimate for all supported insertions. -/
theorem compactActionShiftedTaylorPartial_cauchy
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (m n : Nat)
    (hm :
      compactActionShiftedTaylorModulus
          polynomial epsilon ≤ m)
    (hn :
      compactActionShiftedTaylorModulus
          polynomial epsilon ≤ n) :
    compactActionShiftedTaylorQuadraticPartial polynomial m ≤
          compactActionShiftedTaylorQuadraticPartial polynomial n +
            epsilon ∧
      compactActionShiftedTaylorQuadraticPartial polynomial n ≤
          compactActionShiftedTaylorQuadraticPartial polynomial m +
            epsilon := by
  let scale :=
    compactActionShiftedInsertionL1 polynomial
  let actionL1 := compactActionComplementL1
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  have hscale0 : (0 : Q') ≤ scale :=
    compactActionShiftedInsertionL1_nonnegative polynomial
  have haction0 : (0 : Q') ≤ actionL1 :=
    compactActionComplementL1_nonnegative
  have hepsilon0 : (0 : Q') ≤ epsilon :=
    Q'.le_of_lt hepsilon
  have hdeltaPos : (0 : Q') < delta :=
    Q'.mul_pos hepsilon
      (Q'.invSucc_pos scale.num.toNat)
  have hdelta0 : (0 : Q') ≤ delta :=
    Q'.le_of_lt hdeltaPos
  have hhalfDeltaPos :
      (0 : Q') < HalfPow.half * delta :=
    ExpNeg.half_mul_pos delta hdeltaPos
  have dir :
      ∀ smaller larger : Nat,
        compactActionShiftedTaylorModulus
            polynomial epsilon ≤ smaller →
        smaller ≤ larger →
        compactActionShiftedTaylorQuadraticPartial
              polynomial larger ≤
            compactActionShiftedTaylorQuadraticPartial
                polynomial smaller + epsilon ∧
          compactActionShiftedTaylorQuadraticPartial
              polynomial smaller ≤
            compactActionShiftedTaylorQuadraticPartial
                polynomial larger + epsilon := by
    intro smaller larger hsmaller horder
    obtain ⟨distance, rfl⟩ :=
      Nat.exists_eq_add_of_le horder
    have hcut :
        halfRatioCutoff actionL1 ≤ smaller :=
      Nat.le_trans
        (Nat.le_max_left _ _) hsmaller
    have hterm :
        ExpNeg.termAbs actionL1 smaller ≤
          HalfPow.half * delta :=
      ExpNeg.termAbs_le_of_modulus_le
        actionL1 (HalfPow.half * delta)
        haction0 hhalfDeltaPos smaller
        (Nat.le_trans
          (Nat.le_max_right _ _) hsmaller)
    have htail :
        ExpNeg.blockAbs actionL1 smaller distance ≤
          delta :=
      ExpNeg.expNeg_tail_bound
        actionL1 haction0 delta hdelta0
        smaller hcut hterm distance
    have hscaled :
        scaledTaylorBlockAbs
            scale actionL1 smaller distance ≤
          epsilon := by
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (scaledTaylorBlockAbs_eq
              scale actionL1 smaller distance))
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            htail hscale0))
        (ExpNeg.mul_le_of_mul_invSucc_toNat
          scale epsilon hscale0 hepsilon0)
    exact
      ⟨Q'.le_trans' _ _ _
        (compactActionShiftedTaylorQuadraticPartial_block_upper
          polynomial smaller distance)
        (Q'.add_le_add_left _ _ _ hscaled),
       Q'.le_trans' _ _ _
        (compactActionShiftedTaylorQuadraticPartial_add_mono
          polynomial hsupport smaller distance)
        (Q'.add_le_self_of_nonneg _ _
          hepsilon0)⟩
  rcases Nat.le_total m n with hmn | hnm
  · exact
      ⟨(dir m n hm hmn).2,
       (dir m n hm hmn).1⟩
  · exact
      ⟨(dir n m hn hnm).1,
       (dir n m hn hnm).2⟩

/-! ## 3. The located constructive-real quadratic -/

/-- Located positive shifted-exponential quadratic
`H_10(P² exp(D))` for every supported rational insertion. -/
def compactActionShiftedTaylorQuadraticLimit
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    CReal where
  approx :=
    compactActionShiftedTaylorQuadraticPartial polynomial
  cauchy := by
    intro epsilon hepsilon
    exact
      ⟨compactActionShiftedTaylorModulus
          polynomial epsilon,
       fun m n hm hn =>
        compactActionShiftedTaylorPartial_cauchy
          polynomial hsupport epsilon hepsilon
          m n hm hn⟩

@[simp] theorem compactActionShiftedTaylorQuadraticLimit_approx
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (terms : Nat) :
    (compactActionShiftedTaylorQuadraticLimit
      polynomial hsupport).approx terms =
        compactActionShiftedTaylorQuadraticPartial
          polynomial terms := rfl

/-- Every finite positive Taylor partial is a sound rational lower bound for
the located shifted quadratic. -/
theorem compactActionShiftedTaylorQuadraticLimit_ge_partial
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (terms : Nat) :
    ExpPos.geRat
      (compactActionShiftedTaylorQuadraticLimit
        polynomial hsupport)
      (compactActionShiftedTaylorQuadraticPartial
        polynomial terms) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨terms, fun later hlater => ?_⟩
  obtain ⟨distance, rfl⟩ :=
    Nat.exists_eq_add_of_le hlater
  exact
    compactActionShiftedTaylorQuadraticPartial_add_mono
      polynomial hsupport terms distance

/-- The located physical shifted quadratic is nonnegative in the sound
constructive-real order. -/
theorem compactActionShiftedTaylorQuadraticLimit_nonnegative
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    ExpPos.geRat
      (compactActionShiftedTaylorQuadraticLimit
        polynomial hsupport)
      0 := by
  apply ExpPos.geRat_of_eventually
  exact
    ⟨0, fun terms _ =>
      compactActionShiftedTaylorQuadraticPartial_nonnegative
        polynomial hsupport terms⟩

end YMGap.Continuum.BF4CompactActionShiftedLimit

#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.polynomialCoefficientL1_polynomialPower_le
#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.compactActionShiftedMomentSquarePolynomial_l1_le
#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.termAbs_eq_qpow_mul_unit
#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.compactActionShiftedTaylorQuadraticTerm_le_majorant
#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.compactActionShiftedTaylorQuadraticPartial_add_mono
#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.compactActionShiftedTaylorPartial_cauchy
#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.compactActionShiftedTaylorQuadraticLimit
#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.compactActionShiftedTaylorQuadraticLimit_ge_partial
#print axioms YMGap.Continuum.BF4CompactActionShiftedLimit.compactActionShiftedTaylorQuadraticLimit_nonnegative
