/-
# Vanishing against a finite weighted monomial span

The quaternion Haar weighted pairing is rational-bilinear even when its
polynomial carrier has a radical. Vanishing against every monomial appearing
in a test polynomial therefore implies vanishing against that polynomial.
No positivity or nondegeneracy premise is needed.
-/

import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.QuaternionHaarWeightedMonomialSpan

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem weighted_add_right (blocks : Nat) (weight p q r : RatPoly) :
    weightedPair blocks weight p (polyAdd q r) ≈
      weightedPair blocks weight p q + weightedPair blocks weight p r :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks weight p (polyAdd q r))
    (Q'.eqv_trans _ _ _ (weighted_add_left blocks weight q r p)
      (Q'.add_eqv_congr'
        (weighted_symm blocks weight q p)
        (weighted_symm blocks weight r p)))

private theorem weighted_smul_right (blocks : Nat) (weight : RatPoly)
    (coefficient : Q') (p q : RatPoly) :
    weightedPair blocks weight p (polySmul coefficient q) ≈
      coefficient * weightedPair blocks weight p q :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks weight p (polySmul coefficient q))
    (Q'.eqv_trans _ _ _ (weighted_smul_left blocks weight coefficient q p)
      (Q'.mul_eqv_congr_left _ _ _ (weighted_symm blocks weight q p)))

private theorem weighted_zero_right (blocks : Nat) (weight p : RatPoly) :
    weightedPair blocks weight p [] ≈ 0 := by
  exact Q'.eqv_trans _ _ _ (weighted_symm blocks weight p [])
    (Q'.eqv_refl 0)

private theorem singleton_coefficient (monomial : List Nat) (coefficient : Q') :
    RatPolyCoeffEqv [(monomial, coefficient)]
      (polySmul coefficient [(monomial, 1)]) := by
  intro testWeight
  change coefficient * testWeight monomial + 0 ≈
    (coefficient * 1) * testWeight monomial + 0
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv coefficient)))

private theorem singleton_pairing (blocks : Nat) (weight p : RatPoly)
    (monomial : List Nat) (coefficient : Q') :
    weightedPair blocks weight p [(monomial, coefficient)] ≈
      coefficient * weightedPair blocks weight p [(monomial, 1)] := by
  have hcoeff : weightedPair blocks weight p [(monomial, coefficient)] ≈
      weightedPair blocks weight p
        (polySmul coefficient [(monomial, 1)]) :=
    haar_of_coeff
      ((RatPolyCoeffEqv.mul_left p (singleton_coefficient monomial coefficient)).mul_right weight)
  exact Q'.eqv_trans _ _ _ hcoeff
    (weighted_smul_right blocks weight coefficient p [(monomial, 1)])

/-- Exact weighted pairing vanishes for any finite rational polynomial whose
unit-coefficient monomial pairings vanish. Duplicate and zero-coefficient terms
are allowed; the sphere radical is retained. -/
theorem weightedPair_zero_of_monomials (blocks : Nat) (weight p q : RatPoly)
    (hzero : ∀ term, term ∈ q →
      weightedPair blocks weight p [(term.1, 1)] ≈ 0) :
    weightedPair blocks weight p q ≈ 0 := by
  revert hzero
  induction q with
  | nil =>
      intro _
      exact weighted_zero_right blocks weight p
  | cons term rest ih =>
      intro hzero
      have hhead : weightedPair blocks weight p [term] ≈ 0 :=
        Q'.eqv_trans _ _ _
          (singleton_pairing blocks weight p term.1 term.2)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (hzero term List.mem_cons_self))
            (Q'.mul_zero_eqv _))
      have htail : weightedPair blocks weight p rest ≈ 0 :=
        ih (fun other hmem => hzero other (List.mem_cons_of_mem term hmem))
      change weightedPair blocks weight p (polyAdd [term] rest) ≈ 0
      exact Q'.eqv_trans _ _ _ (weighted_add_right blocks weight p [term] rest)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hhead htail)
          (by decide : (0 : Q') + 0 ≈ 0))

/-- A finite monomial test list suffices whenever it covers the literal terms
of the target polynomial. The list may contain additional monomials. -/
theorem weightedPair_zero_of_test_list (blocks : Nat) (weight p q : RatPoly)
    (monomials : List (List Nat))
    (hcover : ∀ term, term ∈ q → term.1 ∈ monomials)
    (hzero : ∀ monomial, monomial ∈ monomials →
      weightedPair blocks weight p [(monomial, 1)] ≈ 0) :
    weightedPair blocks weight p q ≈ 0 :=
  weightedPair_zero_of_monomials blocks weight p q
    (fun term hterm => hzero term.1 (hcover term hterm))

end YMGap.Continuum.QuaternionHaarWeightedMonomialSpan

#print axioms YMGap.Continuum.QuaternionHaarWeightedMonomialSpan.weightedPair_zero_of_monomials
#print axioms YMGap.Continuum.QuaternionHaarWeightedMonomialSpan.weightedPair_zero_of_test_list
