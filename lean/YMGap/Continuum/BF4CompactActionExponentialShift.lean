/-
# Exact negative-action/shifted-action Haar recurrence

This is the algebraic bridge required before passing from the located
positive series `H(P² exp(D))` to the physical negative-action series
`H(P² exp(-A))`.

The sphere identity is used under an arbitrary insertion:

  H(RD) + H(RA) = (133/4) H(R).

Consequently multiplication by `-A` is exactly multiplication by
`D - 133/4` after tenfold Haar.  The final theorem applies this identity
to every Taylor order of the genuine physical negative-action polynomial.
It is the recurrence needed for the subsequent Cauchy-product/constant-shift
identification.

## Axiom gate

Finite exact polynomial algebra only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompactActionShiftedLimit
import YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.BF4CompactActionExponentialShift

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4CompactActionShiftedExponential

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Solving the exact Haar sphere identity -/

private theorem neg_right_of_add_eqv
    (left right total : Q')
    (h : left + right ≈ total) :
    (-right) ≈ left + (-total) := by
  refine Q'.eqv_trans _
    (left + ((-right) + (-left))) _ ?_ ?_
  · exact Q'.add_sub_cancel_eqv (-right) left
  refine Q'.eqv_trans _
    (left + (-(left + right))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left left _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv (-right) (-left))
        (Q'.eqv_symm
          (Q'.neg_add_eqv left right)))
  exact Q'.add_eqv_congr_left left _ _
    (Q'.neg_eqv_congr _ _ h)

/-- **Exact arbitrary-insertion negative-action shift.**

After tenfold Haar, multiplication by the genuine physical `-A` equals
multiplication by `D - 133/4`.
-/
theorem compactPhysicalAction_negative_shift
    (insertion : RatPoly) :
    (-(tenfoldHaar
        (polyMul insertion
          compactCoupledBF4ActionPolynomial))) ≈
      tenfoldHaar
          (polyMul insertion
            compactActionComplementPolynomial) +
        (-(compactCoupledBF4ActionCeiling *
          tenfoldHaar insertion)) := by
  exact neg_right_of_add_eqv _ _ _
    (compactPhysicalAction_sphere_shift insertion)

/-! ## 2. The genuine negative-action Taylor recurrence -/

/-- Exact Haar coefficient obtained by inserting an arbitrary polynomial
against the `n`-th genuine physical negative-action Taylor polynomial. -/
def compactPhysicalNegativeTaylorHaarTerm
    (insertion : RatPoly) (exponent : Nat) : Q' :=
  tenfoldHaar
    (polyMul insertion
      (negativeExponentialPolynomialTerm
        compactCoupledBF4ActionPolynomial exponent))

private theorem quaternionHaar_polyMul_one_right
    (blocks : Nat) :
    ∀ polynomial : RatPoly,
      quaternionHaar blocks
          (polyMul polynomial polyOne) ≈
        quaternionHaar blocks polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (term.2 * 1) *
              quaternionHaarMono blocks
                (monoMul term.1 []) +
            quaternionHaar blocks
              (polyMul rest polyOne) ≈
          term.2 *
              quaternionHaarMono blocks term.1 +
            quaternionHaar blocks rest
      have hmono :
          monoMul term.1 [] = term.1 := by
        cases term.1 <;> rfl
      rw [hmono]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_one_eqv term.2))
        (quaternionHaar_polyMul_one_right
          blocks rest)

/-! ### Haar-coherent reassociation of finite products

The integral identities below deliberately retain arbitrary prefix and
suffix polynomials.  Equality of Haar integrals is not, by itself, a
multiplicative congruence; carrying the suffix explicitly is what makes the
subsequent power split sound.
-/

private theorem quaternionHaar_polyMul_assoc_four
    (blocks : Nat) (first second third fourth : RatPoly) :
    quaternionHaar blocks
        (polyMul
          (polyMul first (polyMul second third))
          fourth) ≈
      quaternionHaar blocks
        (polyMul
          (polyMul first second)
          (polyMul third fourth)) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul first
        (polyMul fourth
          (polyMul second third)))) _
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_assoc
        blocks first
        (polyMul second third) fourth)
      (quaternionHaar_polyMul_middle_comm
        blocks first
        (polyMul second third) fourth)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul
        (polyMul first fourth)
        (polyMul second third))) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        blocks first fourth
        (polyMul second third))) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul
        (polyMul first second)
        (polyMul fourth third))) _
    (quaternionHaar_polyMul_four_swap
      blocks first fourth second third) ?_
  exact quaternionHaar_polyMul_middle_comm
    blocks (polyMul first second) fourth third

private theorem quaternionHaar_polyMul_one_middle
    (blocks : Nat) (left right : RatPoly) :
    quaternionHaar blocks
        (polyMul left (polyMul polyOne right)) ≈
      quaternionHaar blocks
        (polyMul left right) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul left (polyMul right polyOne))) _
    (quaternionHaar_polyMul_middle_comm
      blocks left polyOne right) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul left right) polyOne)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        blocks left right polyOne)) ?_
  exact quaternionHaar_polyMul_one_right
    blocks (polyMul left right)

private theorem quaternionHaar_polynomialPower_add_suffix
    (blocks : Nat) (insertion base suffix : RatPoly)
    (leftExponent : Nat) :
    ∀ rightExponent : Nat,
      quaternionHaar blocks
          (polyMul
            (polyMul insertion
              (polynomialPower base
                (leftExponent + rightExponent)))
            suffix) ≈
        quaternionHaar blocks
          (polyMul
            (polyMul
              (polyMul insertion
                (polynomialPower base leftExponent))
              (polynomialPower base rightExponent))
            suffix)
  | 0 => by
      change
        quaternionHaar blocks
            (polyMul
              (polyMul insertion
                (polynomialPower base leftExponent))
              suffix) ≈
          quaternionHaar blocks
            (polyMul
              (polyMul
                (polyMul insertion
                  (polynomialPower base leftExponent))
                polyOne)
              suffix)
      refine Q'.eqv_symm
        (Q'.eqv_trans _
          (quaternionHaar blocks
            (polyMul
              (polyMul insertion
                (polynomialPower base leftExponent))
              (polyMul polyOne suffix))) _
          (quaternionHaar_polyMul_assoc
            blocks
            (polyMul insertion
              (polynomialPower base leftExponent))
            polyOne suffix) ?_)
      exact quaternionHaar_polyMul_one_middle
        blocks
        (polyMul insertion
          (polynomialPower base leftExponent))
        suffix
  | rightExponent + 1 => by
      change
        quaternionHaar blocks
            (polyMul
              (polyMul insertion
                (polyMul
                  (polynomialPower base
                    (leftExponent + rightExponent))
                  base))
              suffix) ≈
          quaternionHaar blocks
            (polyMul
              (polyMul
                (polyMul insertion
                  (polynomialPower base leftExponent))
                (polyMul
                  (polynomialPower base rightExponent)
                  base))
              suffix)
      refine Q'.eqv_trans _
        (quaternionHaar blocks
          (polyMul
            (polyMul insertion
              (polynomialPower base
                (leftExponent + rightExponent)))
            (polyMul base suffix))) _
        (quaternionHaar_polyMul_assoc_four
          blocks insertion
          (polynomialPower base
            (leftExponent + rightExponent))
          base suffix) ?_
      refine Q'.eqv_trans _
        (quaternionHaar blocks
          (polyMul
            (polyMul
              (polyMul insertion
                (polynomialPower base leftExponent))
              (polynomialPower base rightExponent))
            (polyMul base suffix))) _
        (quaternionHaar_polynomialPower_add_suffix
          blocks insertion base
          (polyMul base suffix)
          leftExponent rightExponent) ?_
      exact Q'.eqv_symm
        (quaternionHaar_polyMul_assoc_four
          blocks
          (polyMul insertion
            (polynomialPower base leftExponent))
          (polynomialPower base rightExponent)
          base suffix)

theorem compactPhysicalNegativeTaylorHaarTerm_zero
    (insertion : RatPoly) :
    compactPhysicalNegativeTaylorHaarTerm insertion 0 ≈
      tenfoldHaar insertion := by
  unfold compactPhysicalNegativeTaylorHaarTerm
    negativeExponentialPolynomialTerm
  refine Q'.eqv_trans _
    (tenfoldHaar insertion) _
    (quaternionHaar_polyMul_one_right
      10 insertion) ?_
  exact Q'.eqv_refl _

private theorem neg_inverse_mul_action
    (inverse actionValue : Q') :
    ((-inverse) * actionValue) ≈
      inverse * (-actionValue) := by
  refine Q'.eqv_trans _
    (-(inverse * actionValue)) _
    (Q'.neg_mul_eqv inverse actionValue) ?_
  exact Q'.eqv_symm
    (Q'.mul_neg_eqv inverse actionValue)

/-- **Physical constant-shift recurrence at every Taylor order.**

Writing `T_n(R) = H(R (-A)^n/n!)`, the exact recurrence is

  T_{n+1}(R)
    = (1/(n+1)) H(R E_n D)
      + ((-133/4)/(n+1)) T_n(R),

where `E_n` is the genuine physical negative-action polynomial term.
This is the coefficient recurrence needed to identify the negative-action
series with `exp(-133/4) H(R exp(D))`.
-/
theorem compactPhysicalNegativeTaylorHaarTerm_succ_shift
    (insertion : RatPoly) (exponent : Nat) :
    compactPhysicalNegativeTaylorHaarTerm
        insertion (exponent + 1) ≈
      Q'.invSucc exponent *
          tenfoldHaar
            (polyMul
              (polyMul insertion
                (negativeExponentialPolynomialTerm
                  compactCoupledBF4ActionPolynomial exponent))
              compactActionComplementPolynomial) +
        ((-compactCoupledBF4ActionCeiling) *
            Q'.invSucc exponent) *
          compactPhysicalNegativeTaylorHaarTerm
            insertion exponent := by
  let previous :=
    negativeExponentialPolynomialTerm
      compactCoupledBF4ActionPolynomial exponent
  let combined := polyMul insertion previous
  let inverse := Q'.invSucc exponent
  let actionValue :=
    tenfoldHaar
      (polyMul combined
        compactCoupledBF4ActionPolynomial)
  let complementValue :=
    tenfoldHaar
      (polyMul combined
        compactActionComplementPolynomial)
  let previousValue := tenfoldHaar combined
  have hscale :
      compactPhysicalNegativeTaylorHaarTerm
          insertion (exponent + 1) ≈
        (-inverse) *
          tenfoldHaar
            (polyMul insertion
              (polyMul previous
                compactCoupledBF4ActionPolynomial)) := by
    unfold compactPhysicalNegativeTaylorHaarTerm
      negativeExponentialPolynomialTerm
    exact quaternionHaar_polyMul_smul_right
      10 (-inverse) insertion
      (polyMul previous
        compactCoupledBF4ActionPolynomial)
  have hassoc :
      tenfoldHaar
          (polyMul insertion
            (polyMul previous
              compactCoupledBF4ActionPolynomial)) ≈
        actionValue := by
    unfold actionValue combined
    exact Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        10 insertion previous
        compactCoupledBF4ActionPolynomial)
  have hshift :
      (-actionValue) ≈
        complementValue +
          (-(compactCoupledBF4ActionCeiling *
            previousValue)) := by
    exact compactPhysicalAction_negative_shift combined
  refine Q'.eqv_trans _
    ((-inverse) * actionValue) _
    (Q'.eqv_trans _ _ _
      hscale
      (Q'.mul_eqv_congr_left
        (-inverse) _ _ hassoc)) ?_
  refine Q'.eqv_trans _
    (inverse * (-actionValue)) _
    (neg_inverse_mul_action inverse actionValue) ?_
  refine Q'.eqv_trans _
    (inverse *
      (complementValue +
        (-(compactCoupledBF4ActionCeiling *
          previousValue)))) _
    (Q'.mul_eqv_congr_left inverse _ _ hshift) ?_
  refine Q'.eqv_trans _
    (inverse * complementValue +
      inverse *
        (-(compactCoupledBF4ActionCeiling *
          previousValue))) _
    (Q'.mul_add_eqv inverse
      complementValue
      (-(compactCoupledBF4ActionCeiling *
        previousValue))) ?_
  refine Q'.add_eqv_congr_left
    (inverse * complementValue) _ _ ?_
  refine Q'.eqv_trans _
    ((-inverse) *
      (compactCoupledBF4ActionCeiling *
        previousValue)) _
    (Q'.eqv_trans _ _ _
      (Q'.mul_neg_eqv inverse
        (compactCoupledBF4ActionCeiling *
          previousValue))
      (Q'.eqv_symm
        (Q'.neg_mul_eqv inverse
          (compactCoupledBF4ActionCeiling *
            previousValue)))) ?_
  refine Q'.eqv_trans _
    (((-inverse) *
        compactCoupledBF4ActionCeiling) *
      previousValue) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (-inverse)
        compactCoupledBF4ActionCeiling
        previousValue)) ?_
  refine Q'.eqv_trans _
    (((-compactCoupledBF4ActionCeiling) *
        inverse) *
      previousValue) _
    (Q'.mul_eqv_congr_right _ _ previousValue
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv
          (-inverse)
          compactCoupledBF4ActionCeiling)
        (Q'.eqv_trans _ _ _
          (Q'.mul_neg_eqv
            compactCoupledBF4ActionCeiling
            inverse)
          (Q'.eqv_symm
            (Q'.neg_mul_eqv
              compactCoupledBF4ActionCeiling
              inverse))))) ?_
  exact Q'.mul_eqv_congr_left
    ((-compactCoupledBF4ActionCeiling) *
      inverse) _ _
    (Q'.eqv_refl _)

/-! ## 3. Complement moments and their weighted recurrence -/

/-- Canonically associated complement moment coefficient
`(1/n!) H(R Dⁿ)`.  Unlike the parity-arranged carrier used for positivity,
this right-recursive carrier is convenient for the Cauchy-product identity. -/
def compactComplementTaylorHaarTerm
    (insertion : RatPoly) (exponent : Nat) : Q' :=
  ExpNeg.termAbs 1 exponent *
    tenfoldHaar
      (polyMul insertion
      (polynomialPower
          compactActionComplementPolynomial exponent))

private theorem tenfoldHaar_polynomialPower_add
    (insertion base : RatPoly)
    (leftExponent rightExponent : Nat) :
    tenfoldHaar
        (polyMul insertion
          (polynomialPower base
            (leftExponent + rightExponent))) ≈
      tenfoldHaar
        (polyMul
          (polyMul insertion
            (polynomialPower base leftExponent))
          (polynomialPower base rightExponent)) := by
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul
        (polyMul insertion
          (polynomialPower base
            (leftExponent + rightExponent)))
        polyOne)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_one_right
        10
        (polyMul insertion
          (polynomialPower base
            (leftExponent + rightExponent))))) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul
        (polyMul
          (polyMul insertion
            (polynomialPower base leftExponent))
          (polynomialPower base rightExponent))
        polyOne)) _
    (quaternionHaar_polynomialPower_add_suffix
      10 insertion base polyOne
      leftExponent rightExponent) ?_
  exact quaternionHaar_polyMul_one_right
    10
    (polyMul
      (polyMul insertion
        (polynomialPower base leftExponent))
      (polynomialPower base rightExponent))

/-- The manifest parity-square carrier is exactly the canonical inserted
power carrier after tenfold Haar.  The odd case uses the arbitrary suffix in
`quaternionHaar_polynomialPower_add_suffix`; no illicit multiplication of an
already-integrated equality occurs. -/
theorem compactActionShiftedMomentSquarePolynomial_eq_canonicalHaar
    (polynomial : RatPoly) (exponent : Nat) :
    tenfoldHaar
        (compactActionShiftedMomentSquarePolynomial
          polynomial exponent) ≈
      tenfoldHaar
        (polyMul
          (polyMul polynomial polynomial)
          (polynomialPower
            compactActionComplementPolynomial
            exponent)) := by
  let halfIndex := exponent / 2
  let half :=
    polynomialPower compactActionComplementPolynomial
      halfIndex
  unfold compactActionShiftedMomentSquarePolynomial
    compactActionShiftedHalfFactor
    compactActionComplementHalfPower
  by_cases heven : exponent % 2 = 0
  · rw [if_pos heven]
    have hexponent :
        halfIndex + halfIndex = exponent := by
      unfold halfIndex
      omega
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul
          (polyMul polynomial polynomial)
          (polyMul half half))) _
      (quaternionHaar_polyMul_four_swap
        10 polynomial half polynomial half) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul
          (polyMul
            (polyMul polynomial polynomial)
            half)
          half)) _
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc
          10
          (polyMul polynomial polynomial)
          half half)) ?_
    rw [← hexponent]
    exact Q'.eqv_symm
      (tenfoldHaar_polynomialPower_add
        (polyMul polynomial polynomial)
        compactActionComplementPolynomial
        halfIndex halfIndex)
  · rw [if_neg heven]
    have hodd : exponent % 2 = 1 := by
      have hlt : exponent % 2 < 2 :=
        Nat.mod_lt exponent (by decide)
      omega
    have hexponent :
        halfIndex + halfIndex + 1 = exponent := by
      unfold halfIndex
      omega
    let squareInsertion :=
      polyMul polynomial polynomial
    let complement :=
      compactActionComplementPolynomial
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul
          (polyMul
            (polyMul polynomial half)
            polynomial)
          (polyMul half complement))) _
      (quaternionHaar_polyMul_assoc_four
        10
        (polyMul polynomial half)
        polynomial half complement) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul
          (polyMul polynomial half)
          (polyMul polynomial
            (polyMul half complement)))) _
      (quaternionHaar_polyMul_assoc
        10 (polyMul polynomial half)
        polynomial
        (polyMul half complement)) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul squareInsertion
          (polyMul half
            (polyMul half complement)))) _
      (quaternionHaar_polyMul_four_swap
        10 polynomial half polynomial
        (polyMul half complement)) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul
          (polyMul squareInsertion half)
          (polyMul half complement))) _
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc
          10 squareInsertion half
          (polyMul half complement))) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul
          (polyMul
            (polyMul squareInsertion half)
            half)
          complement)) _
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc
          10
          (polyMul squareInsertion half)
          half complement)) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul
          (polyMul squareInsertion
            (polynomialPower complement
              (halfIndex + halfIndex)))
          complement)) _
      (Q'.eqv_symm
        (quaternionHaar_polynomialPower_add_suffix
          10 squareInsertion complement complement
          halfIndex halfIndex)) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul squareInsertion
          (polyMul
            (polynomialPower complement
              (halfIndex + halfIndex))
            complement))) _
      (quaternionHaar_polyMul_assoc
        10 squareInsertion
        (polynomialPower complement
          (halfIndex + halfIndex))
        complement) ?_
    change
      tenfoldHaar
          (polyMul squareInsertion
            (polynomialPower complement
              (halfIndex + halfIndex + 1))) ≈
        tenfoldHaar
          (polyMul squareInsertion
            (polynomialPower complement exponent))
    rw [hexponent]
    exact Q'.eqv_refl _

/-- Coefficientwise identification of the located positive carrier with the
canonical complement Taylor coefficient. -/
theorem compactActionShiftedTaylorQuadraticTerm_eq_complement
    (polynomial : RatPoly) (exponent : Nat) :
    compactActionShiftedTaylorQuadraticTerm
        polynomial exponent ≈
      compactComplementTaylorHaarTerm
        (polyMul polynomial polynomial)
        exponent := by
  unfold compactActionShiftedTaylorQuadraticTerm
    compactComplementTaylorHaarTerm
  exact Q'.mul_eqv_congr_left
    (ExpNeg.termAbs 1 exponent) _ _
    (compactActionShiftedMomentSquarePolynomial_eq_canonicalHaar
      polynomial exponent)

private theorem compactComplementPower_succ_reorder
    (insertion : RatPoly) (exponent : Nat) :
    tenfoldHaar
        (polyMul insertion
          (polynomialPower
            compactActionComplementPolynomial
            (exponent + 1))) ≈
      tenfoldHaar
        (polyMul
          (polyMul insertion
            compactActionComplementPolynomial)
          (polynomialPower
            compactActionComplementPolynomial
            exponent)) := by
  change
    tenfoldHaar
        (polyMul insertion
          (polyMul
            (polynomialPower
              compactActionComplementPolynomial exponent)
            compactActionComplementPolynomial)) ≈
      tenfoldHaar
        (polyMul
          (polyMul insertion
            compactActionComplementPolynomial)
          (polynomialPower
            compactActionComplementPolynomial exponent))
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul insertion
        (polyMul compactActionComplementPolynomial
          (polynomialPower
            compactActionComplementPolynomial exponent)))) _
    (quaternionHaar_polyMul_middle_comm
      10 insertion
      (polynomialPower
        compactActionComplementPolynomial exponent)
      compactActionComplementPolynomial) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_assoc
      10 insertion
      compactActionComplementPolynomial
      (polynomialPower
        compactActionComplementPolynomial exponent))

theorem compactComplementTaylorHaarTerm_zero
    (insertion : RatPoly) :
    compactComplementTaylorHaarTerm insertion 0 ≈
      tenfoldHaar insertion := by
  unfold compactComplementTaylorHaarTerm
    polynomialPower
  refine Q'.eqv_trans _
    (1 * tenfoldHaar insertion) _
    (Q'.mul_eqv_congr_left 1 _ _
      (quaternionHaar_polyMul_one_right
        10 insertion)) ?_
  exact Q'.one_mul_eqv _

/-- Weighted complement recurrence:

`(n+1) (1/(n+1)!) H(RD^(n+1)) = (1/n!) H((RD)D^n)`.
-/
theorem ofNat_succ_mul_compactComplementTaylorHaarTerm
    (insertion : RatPoly) (exponent : Nat) :
    Q'.ofNat (exponent + 1) *
        compactComplementTaylorHaarTerm
          insertion (exponent + 1) ≈
      compactComplementTaylorHaarTerm
        (polyMul insertion
          compactActionComplementPolynomial)
        exponent := by
  let nextMoment :=
    tenfoldHaar
      (polyMul insertion
        (polynomialPower
          compactActionComplementPolynomial
          (exponent + 1)))
  let shiftedMoment :=
    tenfoldHaar
      (polyMul
        (polyMul insertion
          compactActionComplementPolynomial)
        (polynomialPower
          compactActionComplementPolynomial exponent))
  unfold compactComplementTaylorHaarTerm
  refine Q'.eqv_trans _
    ((Q'.ofNat (exponent + 1) *
        ExpNeg.termAbs 1 (exponent + 1)) *
      nextMoment) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (Q'.ofNat (exponent + 1))
        (ExpNeg.termAbs 1 (exponent + 1))
        nextMoment)) ?_
  refine Q'.eqv_trans _
    ((1 * ExpNeg.termAbs 1 exponent) *
      nextMoment) _
    (Q'.mul_eqv_congr_right _ _ nextMoment
      (ofNat_succ_mul_termAbs 1 exponent)) ?_
  refine Q'.eqv_trans _
    (ExpNeg.termAbs 1 exponent *
      nextMoment) _
    (Q'.mul_eqv_congr_right _ _ nextMoment
      (Q'.one_mul_eqv
        (ExpNeg.termAbs 1 exponent))) ?_
  exact Q'.mul_eqv_congr_left
    (ExpNeg.termAbs 1 exponent) _ _
    (compactComplementPower_succ_reorder
      insertion exponent)

/-! ## 4. Coefficientwise scalar-shift convolution -/

/-- One summand in the coefficient of
`exp(-133/4) H(R exp(D))`. -/
def compactPhysicalShiftConvolutionTerm
    (insertion : RatPoly) (total index : Nat) : Q' :=
  ExpNeg.term compactCoupledBF4ActionCeiling index *
    compactComplementTaylorHaarTerm
      insertion (total - index)

/-- The full degree-`total` Cauchy coefficient of the scalar constant shift
and the inserted complement exponential. -/
def compactPhysicalShiftConvolution
    (insertion : RatPoly) (total : Nat) : Q' :=
  finSum
    (compactPhysicalShiftConvolutionTerm insertion total)
    (total + 1)

private theorem compactPhysicalShiftConvolution_iWeighted
    (insertion : RatPoly) (total : Nat) :
    finSum
        (fun index =>
          Q'.ofNat index *
            compactPhysicalShiftConvolutionTerm
              insertion (total + 1) index)
        (total + 2) ≈
      (-compactCoupledBF4ActionCeiling) *
        compactPhysicalShiftConvolution insertion total := by
  have hpeel :=
    RationalTail.finSum_peel_left
      (fun index =>
        Q'.ofNat index *
          compactPhysicalShiftConvolutionTerm
            insertion (total + 1) index)
      (total + 1)
  have hzero :
      Q'.ofNat 0 *
          compactPhysicalShiftConvolutionTerm
            insertion (total + 1) 0 ≈
        0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (Q'.ofNat 0) 0 _ Q'.ofNat_zero_eqv) ?_
    exact Q'.zero_mul_eqv _
  have hstep :
      ∀ index : Nat,
        Q'.ofNat (index + 1) *
            compactPhysicalShiftConvolutionTerm
              insertion (total + 1) (index + 1) ≈
          (-compactCoupledBF4ActionCeiling) *
            compactPhysicalShiftConvolutionTerm
              insertion total index := by
    intro index
    have hsub :
        (total + 1) - (index + 1) =
          total - index := by omega
    unfold compactPhysicalShiftConvolutionTerm
    rw [hsub]
    refine Q'.eqv_trans _
      ((Q'.ofNat (index + 1) *
          ExpNeg.term
            compactCoupledBF4ActionCeiling
            (index + 1)) *
        compactComplementTaylorHaarTerm
          insertion (total - index)) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (Q'.ofNat (index + 1))
          (ExpNeg.term
            compactCoupledBF4ActionCeiling
            (index + 1))
          (compactComplementTaylorHaarTerm
            insertion (total - index)))) ?_
    refine Q'.eqv_trans _
      (((-compactCoupledBF4ActionCeiling) *
          ExpNeg.term
            compactCoupledBF4ActionCeiling index) *
        compactComplementTaylorHaarTerm
          insertion (total - index)) _
      (Q'.mul_eqv_congr_right _ _ _
        (ofNat_succ_mul_term
          compactCoupledBF4ActionCeiling index)) ?_
    exact Q'.mul_assoc_eqv
      (-compactCoupledBF4ActionCeiling)
      (ExpNeg.term
        compactCoupledBF4ActionCeiling index)
      (compactComplementTaylorHaarTerm
        insertion (total - index))
  have hsum :
      finSum
          (fun index =>
            Q'.ofNat (index + 1) *
              compactPhysicalShiftConvolutionTerm
                insertion (total + 1) (index + 1))
          (total + 1) ≈
        (-compactCoupledBF4ActionCeiling) *
          compactPhysicalShiftConvolution
            insertion total := by
    refine Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr
        _ (fun index =>
          (-compactCoupledBF4ActionCeiling) *
            compactPhysicalShiftConvolutionTerm
              insertion total index)
        hstep (total + 1)) ?_
    exact Q'.eqv_symm
      (RationalTail.const_mul_finSum
        (compactPhysicalShiftConvolutionTerm
          insertion total)
        (-compactCoupledBF4ActionCeiling)
        (total + 1))
  refine Q'.eqv_trans _ _ _ hpeel ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ 0 _ hzero) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 _ _ hsum) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' _)

private theorem compactPhysicalShiftConvolution_jWeighted
    (insertion : RatPoly) (total : Nat) :
    finSum
        (fun index =>
          Q'.ofNat ((total + 1) - index) *
            compactPhysicalShiftConvolutionTerm
              insertion (total + 1) index)
        (total + 2) ≈
      compactPhysicalShiftConvolution
        (polyMul insertion
          compactActionComplementPolynomial)
        total := by
  have hlast :
      Q'.ofNat ((total + 1) - (total + 1)) *
          compactPhysicalShiftConvolutionTerm
            insertion (total + 1) (total + 1) ≈
        0 := by
    have hzero : (total + 1) - (total + 1) = 0 := by
      omega
    rw [hzero]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (Q'.ofNat 0) 0 _ Q'.ofNat_zero_eqv) ?_
    exact Q'.zero_mul_eqv _
  have hstep :
      ∀ index : Nat, index < total + 1 →
        Q'.ofNat ((total + 1) - index) *
            compactPhysicalShiftConvolutionTerm
              insertion (total + 1) index ≈
          compactPhysicalShiftConvolutionTerm
            (polyMul insertion
              compactActionComplementPolynomial)
            total index := by
    intro index hindex
    have hsub :
        (total + 1) - index =
          (total - index) + 1 := by omega
    unfold compactPhysicalShiftConvolutionTerm
    rw [hsub]
    refine Q'.eqv_trans _
      (ExpNeg.term
          compactCoupledBF4ActionCeiling index *
        (compactComplementTaylorHaarTerm
            insertion ((total - index) + 1) *
          Q'.ofNat ((total - index) + 1))) _
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv _ _)
        (Q'.mul_assoc_eqv
          (ExpNeg.term
            compactCoupledBF4ActionCeiling index)
          (compactComplementTaylorHaarTerm
            insertion ((total - index) + 1))
          (Q'.ofNat ((total - index) + 1)))) ?_
    refine Q'.eqv_trans _
      (ExpNeg.term
          compactCoupledBF4ActionCeiling index *
        (Q'.ofNat ((total - index) + 1) *
          compactComplementTaylorHaarTerm
            insertion ((total - index) + 1))) _
      (Q'.mul_eqv_congr_left
        (ExpNeg.term
          compactCoupledBF4ActionCeiling index) _ _
        (Q'.mul_comm_eqv
          (compactComplementTaylorHaarTerm
            insertion ((total - index) + 1))
          (Q'.ofNat ((total - index) + 1)))) ?_
    exact Q'.mul_eqv_congr_left
      (ExpNeg.term
        compactCoupledBF4ActionCeiling index) _ _
      (ofNat_succ_mul_compactComplementTaylorHaarTerm
        insertion (total - index))
  change
    (finSum
        (fun index =>
          Q'.ofNat ((total + 1) - index) *
            compactPhysicalShiftConvolutionTerm
              insertion (total + 1) index)
        (total + 1) +
      Q'.ofNat ((total + 1) - (total + 1)) *
        compactPhysicalShiftConvolutionTerm
          insertion (total + 1) (total + 1)) ≈
      compactPhysicalShiftConvolution
        (polyMul insertion
          compactActionComplementPolynomial)
        total
  refine Q'.eqv_trans _
    (finSum
      (fun index =>
        Q'.ofNat ((total + 1) - index) *
          compactPhysicalShiftConvolutionTerm
            insertion (total + 1) index)
      (total + 1)) _
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ 0 hlast)
      (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
  exact RationalTail.finSum_eqv_congr_lt
    _ _
    (total + 1) hstep

theorem ofNat_succ_mul_compactPhysicalShiftConvolution
    (insertion : RatPoly) (total : Nat) :
    Q'.ofNat (total + 1) *
        compactPhysicalShiftConvolution
          insertion (total + 1) ≈
      (-compactCoupledBF4ActionCeiling) *
          compactPhysicalShiftConvolution insertion total +
        compactPhysicalShiftConvolution
          (polyMul insertion
            compactActionComplementPolynomial)
          total := by
  refine Q'.eqv_trans _
    (finSum
      (fun index =>
        Q'.ofNat (total + 1) *
          compactPhysicalShiftConvolutionTerm
            insertion (total + 1) index)
      (total + 2)) _
    (RationalTail.const_mul_finSum
      (compactPhysicalShiftConvolutionTerm
        insertion (total + 1))
      (Q'.ofNat (total + 1))
      (total + 2)) ?_
  have hsplit :
      ∀ index : Nat, index < total + 2 →
        Q'.ofNat (total + 1) *
            compactPhysicalShiftConvolutionTerm
              insertion (total + 1) index ≈
          Q'.ofNat index *
              compactPhysicalShiftConvolutionTerm
                insertion (total + 1) index +
            Q'.ofNat ((total + 1) - index) *
              compactPhysicalShiftConvolutionTerm
                insertion (total + 1) index := by
    intro index hindex
    have hle : index ≤ total + 1 :=
      Nat.lt_succ_iff.mp hindex
    have hnat :
        index + ((total + 1) - index) =
          total + 1 := by omega
    have hofnat :
        Q'.ofNat (total + 1) ≈
          Q'.ofNat index +
            Q'.ofNat ((total + 1) - index) := by
      have h :=
        Q'.ofNat_add_eqv index
          ((total + 1) - index)
      rw [hnat] at h
      exact h
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hofnat) ?_
    exact Q'.add_mul_eqv _ _ _
  refine Q'.eqv_trans _
    (finSum
      (fun index =>
        Q'.ofNat index *
              compactPhysicalShiftConvolutionTerm
                insertion (total + 1) index +
          Q'.ofNat ((total + 1) - index) *
              compactPhysicalShiftConvolutionTerm
                insertion (total + 1) index)
      (total + 2)) _
    (RationalTail.finSum_eqv_congr_lt
      _ _ (total + 2) hsplit) ?_
  refine Q'.eqv_trans _
    (finSum
        (fun index =>
          Q'.ofNat index *
            compactPhysicalShiftConvolutionTerm
              insertion (total + 1) index)
        (total + 2) +
      finSum
        (fun index =>
          Q'.ofNat ((total + 1) - index) *
            compactPhysicalShiftConvolutionTerm
              insertion (total + 1) index)
        (total + 2)) _
    (RationalTail.finSum_add _ _ _) ?_
  exact Q'.add_eqv_congr'
    (compactPhysicalShiftConvolution_iWeighted
      insertion total)
    (compactPhysicalShiftConvolution_jWeighted
      insertion total)

/-! ## 5. Coefficientwise identification with the physical action -/

private theorem compactPhysicalNegativeTaylorHaarTerm_shiftedInsertion
    (insertion : RatPoly) (exponent : Nat) :
    compactPhysicalNegativeTaylorHaarTerm
        (polyMul insertion
          compactActionComplementPolynomial)
        exponent ≈
      tenfoldHaar
        (polyMul
          (polyMul insertion
            (negativeExponentialPolynomialTerm
              compactCoupledBF4ActionPolynomial exponent))
          compactActionComplementPolynomial) := by
  let previous :=
    negativeExponentialPolynomialTerm
      compactCoupledBF4ActionPolynomial exponent
  unfold compactPhysicalNegativeTaylorHaarTerm
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul insertion
        (polyMul compactActionComplementPolynomial
          previous))) _
    (quaternionHaar_polyMul_assoc
      10 insertion
      compactActionComplementPolynomial
      previous) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul insertion
        (polyMul previous
          compactActionComplementPolynomial))) _
    (quaternionHaar_polyMul_middle_comm
      10 insertion
      compactActionComplementPolynomial
      previous) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_assoc
      10 insertion previous
      compactActionComplementPolynomial)

/-- Unweighted physical recurrence written entirely in terms of the same
Taylor coefficient family. -/
theorem compactPhysicalNegativeTaylorHaarTerm_succ_recurrence
    (insertion : RatPoly) (exponent : Nat) :
    compactPhysicalNegativeTaylorHaarTerm
        insertion (exponent + 1) ≈
      Q'.invSucc exponent *
          compactPhysicalNegativeTaylorHaarTerm
            (polyMul insertion
              compactActionComplementPolynomial)
            exponent +
        ((-compactCoupledBF4ActionCeiling) *
            Q'.invSucc exponent) *
          compactPhysicalNegativeTaylorHaarTerm
            insertion exponent := by
  refine Q'.eqv_trans _ _ _
    (compactPhysicalNegativeTaylorHaarTerm_succ_shift
      insertion exponent) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left
      (Q'.invSucc exponent) _ _
      (Q'.eqv_symm
        (compactPhysicalNegativeTaylorHaarTerm_shiftedInsertion
          insertion exponent)))

private theorem ofNat_succ_mul_invSucc_value
    (exponent : Nat) (value : Q') :
    Q'.ofNat (exponent + 1) *
        (Q'.invSucc exponent * value) ≈
      value := by
  refine Q'.eqv_trans _
    ((Q'.ofNat (exponent + 1) *
        Q'.invSucc exponent) * value) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (Q'.ofNat (exponent + 1))
        (Q'.invSucc exponent) value)) ?_
  refine Q'.eqv_trans _
    (1 * value) _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.ofNat_succ_mul_invSucc exponent)) ?_
  exact Q'.one_mul_eqv value

private theorem ofNat_succ_mul_scaledInvSucc_value
    (exponent : Nat) (coefficient value : Q') :
    Q'.ofNat (exponent + 1) *
        ((coefficient * Q'.invSucc exponent) * value) ≈
      coefficient * value := by
  refine Q'.eqv_trans _
    ((Q'.ofNat (exponent + 1) *
        (coefficient * Q'.invSucc exponent)) *
      value) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (Q'.ofNat (exponent + 1))
        (coefficient * Q'.invSucc exponent)
        value)) ?_
  refine Q'.eqv_trans _
    ((coefficient *
        (Q'.ofNat (exponent + 1) *
          Q'.invSucc exponent)) *
      value) _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.ofNat (exponent + 1))
            coefficient
            (Q'.invSucc exponent)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_comm_eqv
              (Q'.ofNat (exponent + 1))
              coefficient))
          (Q'.mul_assoc_eqv coefficient
            (Q'.ofNat (exponent + 1))
            (Q'.invSucc exponent))))) ?_
  refine Q'.eqv_trans _
    ((coefficient * 1) * value) _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.mul_eqv_congr_left coefficient _ _
        (Q'.ofNat_succ_mul_invSucc exponent))) ?_
  refine Q'.eqv_trans _
    (coefficient * value) _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.mul_one_eqv coefficient)) ?_
  exact Q'.eqv_refl _

/-- Weighted recurrence for the genuine physical negative-action
coefficients, in the same order as the scalar-shift convolution recurrence. -/
theorem ofNat_succ_mul_compactPhysicalNegativeTaylorHaarTerm
    (insertion : RatPoly) (exponent : Nat) :
    Q'.ofNat (exponent + 1) *
        compactPhysicalNegativeTaylorHaarTerm
          insertion (exponent + 1) ≈
      (-compactCoupledBF4ActionCeiling) *
          compactPhysicalNegativeTaylorHaarTerm
            insertion exponent +
        compactPhysicalNegativeTaylorHaarTerm
          (polyMul insertion
            compactActionComplementPolynomial)
          exponent := by
  let shifted :=
    compactPhysicalNegativeTaylorHaarTerm
      (polyMul insertion
        compactActionComplementPolynomial)
      exponent
  let previous :=
    compactPhysicalNegativeTaylorHaarTerm
      insertion exponent
  refine Q'.eqv_trans _
    (Q'.ofNat (exponent + 1) *
      (Q'.invSucc exponent * shifted +
        ((-compactCoupledBF4ActionCeiling) *
          Q'.invSucc exponent) * previous)) _
    (Q'.mul_eqv_congr_left
      (Q'.ofNat (exponent + 1)) _ _
      (compactPhysicalNegativeTaylorHaarTerm_succ_recurrence
        insertion exponent)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (exponent + 1) *
          (Q'.invSucc exponent * shifted) +
      Q'.ofNat (exponent + 1) *
          (((-compactCoupledBF4ActionCeiling) *
            Q'.invSucc exponent) * previous)) _
    (Q'.mul_add_eqv
      (Q'.ofNat (exponent + 1))
      (Q'.invSucc exponent * shifted)
      (((-compactCoupledBF4ActionCeiling) *
        Q'.invSucc exponent) * previous)) ?_
  refine Q'.eqv_trans _
    (shifted +
      (-compactCoupledBF4ActionCeiling) * previous) _
    (Q'.add_eqv_congr'
      (ofNat_succ_mul_invSucc_value
        exponent shifted)
      (ofNat_succ_mul_scaledInvSucc_value
        exponent
        (-compactCoupledBF4ActionCeiling)
        previous)) ?_
  exact Q'.add_comm_eqv shifted
    ((-compactCoupledBF4ActionCeiling) * previous)

theorem compactPhysicalShiftConvolution_zero
    (insertion : RatPoly) :
    compactPhysicalShiftConvolution insertion 0 ≈
      compactPhysicalNegativeTaylorHaarTerm
        insertion 0 := by
  change
    (0 +
      ExpNeg.term compactCoupledBF4ActionCeiling 0 *
        compactComplementTaylorHaarTerm insertion 0) ≈
      compactPhysicalNegativeTaylorHaarTerm insertion 0
  refine Q'.eqv_trans _
    (1 * compactComplementTaylorHaarTerm insertion 0) _
    (Q'.eqv_of_eq
      (Q'.zero_add'
        (ExpNeg.term compactCoupledBF4ActionCeiling 0 *
          compactComplementTaylorHaarTerm insertion 0))) ?_
  refine Q'.eqv_trans _
    (compactComplementTaylorHaarTerm insertion 0) _
    (Q'.one_mul_eqv _) ?_
  exact Q'.eqv_trans _ _ _
    (compactComplementTaylorHaarTerm_zero insertion)
    (Q'.eqv_symm
      (compactPhysicalNegativeTaylorHaarTerm_zero
        insertion))

/-- **Coefficientwise physical constant-shift identity.**

For every insertion and every order, the Cauchy coefficient of

`exp(-133/4) · H(R exp(D))`

is exactly the coefficient of the genuine physical negative-action series

`H(R exp(-A))`.
-/
theorem compactPhysicalShiftConvolution_eq_negative
    : ∀ (exponent : Nat) (insertion : RatPoly),
      compactPhysicalShiftConvolution
          insertion exponent ≈
        compactPhysicalNegativeTaylorHaarTerm
          insertion exponent
  | 0, insertion =>
      compactPhysicalShiftConvolution_zero insertion
  | exponent + 1, insertion => by
      apply Q'.mul_left_cancel_of_pos
        (Q'.ofNat_succ_pos exponent)
      refine Q'.eqv_trans _
        ((-compactCoupledBF4ActionCeiling) *
              compactPhysicalShiftConvolution
                insertion exponent +
          compactPhysicalShiftConvolution
            (polyMul insertion
              compactActionComplementPolynomial)
            exponent) _
        (ofNat_succ_mul_compactPhysicalShiftConvolution
          insertion exponent) ?_
      refine Q'.eqv_trans _
        ((-compactCoupledBF4ActionCeiling) *
              compactPhysicalNegativeTaylorHaarTerm
                insertion exponent +
          compactPhysicalNegativeTaylorHaarTerm
            (polyMul insertion
              compactActionComplementPolynomial)
            exponent) _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (-compactCoupledBF4ActionCeiling) _ _
            (compactPhysicalShiftConvolution_eq_negative
              exponent insertion))
          (compactPhysicalShiftConvolution_eq_negative
            exponent
            (polyMul insertion
              compactActionComplementPolynomial))) ?_
      exact Q'.eqv_symm
        (ofNat_succ_mul_compactPhysicalNegativeTaylorHaarTerm
          insertion exponent)

end YMGap.Continuum.BF4CompactActionExponentialShift

#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.compactPhysicalAction_negative_shift
#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.compactPhysicalNegativeTaylorHaarTerm_zero
#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.compactPhysicalNegativeTaylorHaarTerm_succ_shift
#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.compactActionShiftedMomentSquarePolynomial_eq_canonicalHaar
#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.compactActionShiftedTaylorQuadraticTerm_eq_complement
#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.ofNat_succ_mul_compactComplementTaylorHaarTerm
#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.ofNat_succ_mul_compactPhysicalShiftConvolution
#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.ofNat_succ_mul_compactPhysicalNegativeTaylorHaarTerm
#print axioms YMGap.Continuum.BF4CompactActionExponentialShift.compactPhysicalShiftConvolution_eq_negative
