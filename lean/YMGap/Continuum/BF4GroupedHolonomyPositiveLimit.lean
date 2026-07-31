/-
# Diagonal factorial control for the grouped BF4 holonomy endpoint

`BF4GroupedHolonomyCrossMajorant` removes the full kinetic-word cutoff at
each fixed diagonal Feynman--Kac order.  A joint two-parameter limit also
needs a diagonal estimate which is independent of the kinetic carrier.

This file proves that estimate at the coefficient-`L¹` level.  If `E` is
the literal positive one-sided BF4 complement and `D = ‖E‖₁`, then

  ‖E^n / n!‖₁ ≤ D^n / n!.

The parity-arranged square/square-times-`E` representative used to preserve
complete positivity is treated literally.  Consequently every omitted
diagonal block is bounded by `ExpNeg.blockAbs D`, and every finite diagonal
partial has one explicit rational upper bound.

This closes the scalar diagonal-tail input to the cofinal construction.  It
does not yet estimate the difference of the resulting *quadratic* packet
kernels, whose two half-amplitudes create a mixed cross term.

## Axiom gate

Finite polynomial algebra, exact `Q'` inequalities, and explicit factorial
tails only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedHolonomyCrossMajorant
import YMGap.Continuum.ExpProductFloor

namespace YMGap.Continuum.BF4GroupedHolonomyPositiveLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RatNat
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionShiftedLimit
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GroupedHolonomyCrossMajorant
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.ExpProductFloor
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal parity-arranged diagonal moment bound -/

/-- Coefficient norm of the normalized positive one-sided complement. -/
def bf4SourceDiagonalComplementL1 : Q' :=
  polynomialCoefficientL1
    sourceDiagonalComplementPolynomial

theorem bf4SourceDiagonalComplementL1_nonnegative :
    (0 : Q') ≤ bf4SourceDiagonalComplementL1 :=
  polynomialCoefficientL1_nonnegative _

private theorem qpow_nonnegative_local
    (value : Q') (hvalue : (0 : Q') ≤ value) :
    ∀ exponent : Nat,
      (0 : Q') ≤ qpow value exponent
  | 0 => by
      change (0 : Q') ≤ 1
      decide
  | exponent + 1 =>
      Q'.mul_nonneg _ _
        (qpow_nonnegative_local value hvalue exponent)
        hvalue

/-- The CP-preserving parity representative of the `n`-th complement
moment has the same scalar exponential growth as a literal power. -/
theorem sourceDiagonalComplementMomentPolynomial_l1_le
    (exponent : Nat) :
    polynomialCoefficientL1
        (sourceDiagonalComplementMomentPolynomial
          exponent) ≤
      qpow bf4SourceDiagonalComplementL1 exponent := by
  let d := bf4SourceDiagonalComplementL1
  let halfIndex := exponent / 2
  let factor :=
    polynomialPower
      sourceDiagonalComplementPolynomial halfIndex
  let bound := qpow d halfIndex
  have hd0 : (0 : Q') ≤ d :=
    bf4SourceDiagonalComplementL1_nonnegative
  have hfactor0 :
      (0 : Q') ≤
        polynomialCoefficientL1 factor :=
    polynomialCoefficientL1_nonnegative factor
  have hbound0 : (0 : Q') ≤ bound :=
    qpow_nonnegative_local d hd0 halfIndex
  have hfactor :
      polynomialCoefficientL1 factor ≤ bound :=
    polynomialCoefficientL1_polynomialPower_le
      sourceDiagonalComplementPolynomial halfIndex
  unfold sourceDiagonalComplementMomentPolynomial
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
    rw [← hexponent]
    exact Q'.eqv_symm
      (qpow_add d halfIndex halfIndex)
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
              sourceDiagonalComplementPolynomial) ≤
          (bound * bound) * d := by
      exact Q'.le_trans' _ _ _
        (polynomialCoefficientL1_mul_le
          (polyMul factor factor)
          sourceDiagonalComplementPolynomial)
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          hfactorSquare hd0)
    refine Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv ?_)
    unfold bound
    refine Q'.eqv_trans _
      (qpow d (halfIndex + halfIndex) * d) _
      (Q'.mul_eqv_congr_right _ _ d
        (Q'.eqv_symm
          (qpow_add d halfIndex halfIndex))) ?_
    have hpower :
        qpow d (halfIndex + halfIndex) * d =
          qpow d (halfIndex + halfIndex + 1) :=
      rfl
    rw [hpower, hexponent]
    exact Q'.eqv_refl _

/-- Each literal positive diagonal shell is bounded by the matching scalar
factorial term. -/
theorem sourceDiagonalShiftedTerm_l1_le
    (exponent : Nat) :
    polynomialCoefficientL1
        (sourceDiagonalShiftedTerm exponent) ≤
      ExpNeg.termAbs
        bf4SourceDiagonalComplementL1 exponent := by
  let unitTerm := ExpNeg.termAbs 1 exponent
  let d := bf4SourceDiagonalComplementL1
  have hunit0 : (0 : Q') ≤ unitTerm :=
    ExpNeg.termAbs_nonneg 1 (by decide) exponent
  have habsUnit : Q'.abs unitTerm = unitTerm := by
    unfold Q'.abs
    rw [if_pos hunit0]
  refine Q'.le_trans' _ _ _
    (polynomialCoefficientL1_smul_le
      unitTerm
      (sourceDiagonalComplementMomentPolynomial
        exponent)) ?_
  rw [habsUnit]
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (sourceDiagonalComplementMomentPolynomial_l1_le
        exponent)
      hunit0) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv unitTerm
        (qpow d exponent))
      (Q'.eqv_symm
        (termAbs_eq_qpow_mul_unit d exponent)))

/-! ## 2. Partial and omitted-block estimates -/

/-- The coefficient norm of the positive diagonal partial is bounded by
the scalar positive exponential partial. -/
theorem sourceDiagonalFeynmanKacPartial_l1_le :
    ∀ order : Nat,
      polynomialCoefficientL1
          (sourceDiagonalFeynmanKacPartial order) ≤
        ExpNeg.partialSumAbs
          bf4SourceDiagonalComplementL1 order
  | 0 => Q'.le_refl' 0
  | order + 1 => by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (polynomialCoefficientL1_polyAdd
            (sourceDiagonalFeynmanKacPartial order)
            (sourceDiagonalShiftedTerm order))) ?_
      exact Q'.add_le_add
        (sourceDiagonalFeynmanKacPartial_l1_le order)
        (sourceDiagonalShiftedTerm_l1_le order)

/-- Scalar coefficient mass of the omitted diagonal shells
`[start,start+distance)`. -/
def bf4SourceDiagonalL1Block
    (start : Nat) : Nat → Q'
  | 0 => 0
  | distance + 1 =>
      bf4SourceDiagonalL1Block start distance +
        polynomialCoefficientL1
          (sourceDiagonalShiftedTerm
            (start + distance))

/-- Every omitted diagonal block is dominated by the corresponding
factorial block. -/
theorem bf4SourceDiagonalL1Block_le
    (start : Nat) :
    ∀ distance : Nat,
      bf4SourceDiagonalL1Block start distance ≤
        ExpNeg.blockAbs
          bf4SourceDiagonalComplementL1
          start distance
  | 0 => Q'.le_refl' 0
  | distance + 1 => by
      exact Q'.add_le_add
        (bf4SourceDiagonalL1Block_le
          start distance)
        (sourceDiagonalShiftedTerm_l1_le
          (start + distance))

/-- Explicit coefficient-`L¹` modulus for every omitted diagonal block. -/
def bf4SourceDiagonalL1Modulus
    (epsilon : Q') : Nat :=
  max
    (halfRatioCutoff bf4SourceDiagonalComplementL1)
    (ExpNeg.termAbsModulus
      bf4SourceDiagonalComplementL1
      (HalfPow.half * epsilon))

theorem bf4SourceDiagonalL1Block_le_of_modulus
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (start distance : Nat)
    (hstart :
      bf4SourceDiagonalL1Modulus epsilon ≤ start) :
    bf4SourceDiagonalL1Block start distance ≤
      epsilon := by
  have hd0 :
      (0 : Q') ≤ bf4SourceDiagonalComplementL1 :=
    bf4SourceDiagonalComplementL1_nonnegative
  have hepsilon0 : (0 : Q') ≤ epsilon :=
    Q'.le_of_lt hepsilon
  have hhalfEpsilon :
      (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hcut :
      halfRatioCutoff bf4SourceDiagonalComplementL1 ≤
        start :=
    Nat.le_trans
      (Nat.le_max_left _ _) hstart
  have hterm :
      ExpNeg.termAbs
          bf4SourceDiagonalComplementL1 start ≤
        HalfPow.half * epsilon :=
    ExpNeg.termAbs_le_of_modulus_le
      bf4SourceDiagonalComplementL1
      (HalfPow.half * epsilon)
      hd0 hhalfEpsilon start
      (Nat.le_trans
        (Nat.le_max_right _ _) hstart)
  exact Q'.le_trans' _ _ _
    (bf4SourceDiagonalL1Block_le start distance)
    (ExpNeg.expNeg_tail_bound
      bf4SourceDiagonalComplementL1 hd0
      epsilon hepsilon0 start hcut hterm distance)

/-! ## 3. One rational bound for every diagonal partial -/

/-- The standard rational positive-exponential bound controls every finite
positive partial, not only an eventual tail. -/
theorem partialSumAbs_le_expPosBound
    (value : Q') (hvalue : (0 : Q') ≤ value)
    (order : Nat) :
    ExpNeg.partialSumAbs value order ≤
      expPosBound value := by
  let cutoff := halfRatioCutoff value
  rcases Nat.le_total order cutoff with horder | hcutoff
  · obtain ⟨distance, hdistance⟩ :=
      Nat.exists_eq_add_of_le horder
    have hmono :
        ExpNeg.partialSumAbs value order ≤
          ExpNeg.partialSumAbs value cutoff := by
      rw [hdistance]
      exact ExpPos.partialSumAbs_mono
        value hvalue order distance
    refine Q'.le_trans' _ _ _ hmono ?_
    unfold expPosBound cutoff
    exact Q'.add_le_self_of_nonneg _ _
      (Q'.zero_le_add _ _
        (ExpNeg.termAbs_nonneg value hvalue
          (halfRatioCutoff value))
        (ExpNeg.termAbs_nonneg value hvalue
          (halfRatioCutoff value)))
  · obtain ⟨distance, rfl⟩ :=
      Nat.exists_eq_add_of_le hcutoff
    have hterm0 :
        (0 : Q') ≤
          ExpNeg.termAbs value cutoff :=
      ExpNeg.termAbs_nonneg value hvalue cutoff
    have htail :
        ExpNeg.blockAbs value cutoff distance ≤
          ExpNeg.termAbs value cutoff +
            ExpNeg.termAbs value cutoff := by
      have hpair0 :
          (0 : Q') ≤
            ExpNeg.termAbs value cutoff +
              ExpNeg.termAbs value cutoff :=
        Q'.zero_le_add _ _ hterm0 hterm0
      have hhalfPair :
          HalfPow.half *
              (ExpNeg.termAbs value cutoff +
                ExpNeg.termAbs value cutoff) ≈
            ExpNeg.termAbs value cutoff :=
        Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv HalfPow.half
            (ExpNeg.termAbs value cutoff)
            (ExpNeg.termAbs value cutoff))
          (ExpNeg.two_halves
            (ExpNeg.termAbs value cutoff))
      exact ExpNeg.blockAbs_le
        value HalfPow.half
        (ExpNeg.termAbs value cutoff +
          ExpNeg.termAbs value cutoff)
        hvalue cutoff HalfPow.half_nonneg hpair0
        (ExpNeg.x_invSucc_le_half
          value hvalue cutoff (Nat.le_refl _))
        (ExpNeg.expNeg_recurrence value cutoff
          (ExpNeg.termAbs value cutoff +
            ExpNeg.termAbs value cutoff)
          (Q'.ge_of_eqv hhalfPair))
        distance
    exact Q'.le_trans' _ _ _
      (ExpPos.partialSumAbs_le_add_blockAbs
        value cutoff distance)
      (Q'.add_le_add_left _ _ _ htail)

/-- Uniform rational coefficient-norm bound for every positive diagonal
Feynman--Kac partial. -/
theorem sourceDiagonalFeynmanKacPartial_l1_uniform
    (order : Nat) :
    polynomialCoefficientL1
        (sourceDiagonalFeynmanKacPartial order) ≤
      expPosBound bf4SourceDiagonalComplementL1 := by
  exact Q'.le_trans' _ _ _
    (sourceDiagonalFeynmanKacPartial_l1_le order)
    (partialSumAbs_le_expPosBound
      bf4SourceDiagonalComplementL1
      bf4SourceDiagonalComplementL1_nonnegative
      order)

end YMGap.Continuum.BF4GroupedHolonomyPositiveLimit

#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalComplementMomentPolynomial_l1_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalShiftedTerm_l1_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalFeynmanKacPartial_l1_le
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.bf4SourceDiagonalL1Block_le_of_modulus
#print axioms YMGap.Continuum.BF4GroupedHolonomyPositiveLimit.sourceDiagonalFeynmanKacPartial_l1_uniform
