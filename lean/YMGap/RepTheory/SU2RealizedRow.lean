/-
# The SU(2) `RepData` Casimir/dimension row, read off the realized carrier

J04 parallel track, task T2.  The literal row `RepTheory.su2` stores
`C₂_fund = 3/4`, `C₂_adj = 2`.  This module re-derives those two numbers (and
the dimensions `s+1`) from objects that already exist in the repository:

* the rational unit-norm quaternion group
  (`RepTheory.RationalQuaternionUnitNormGroup`) and its sign quotient
  (`RepTheory.RationalQuaternionSignQuotient`), on which the spin character is
  evaluated as a class function of the real part (Chebyshev-`U`);
* the exact normalized `S³` Haar functional
  `BF4GeometricHaarMehlerProjection.quaternionHaar`, against which the spin-½
  character is shown to be normalized and mean-zero;
* the proved angular-Laplacian eigenvalue of the ordinary relative character
  (`SU2QuaternionRelativeCharacterCasimir.relativeCharacter_angularCasimir`,
  part of the `SU2QuaternionConditionalHeat*` import tree), which gives the
  Casimir `s(s+2)` up to the fixed normalization `1/4`.

## What is realized, precisely

* `RationalQuaternion.UnitNorm` is the group of **rational** points of `S³`.
  It is countable, not compact, and is **not** all of `SU(2)`; it is dense in
  `S³` but no density/completion statement is used or proved here.
* `spinCharacter s` is the Chebyshev polynomial `U_s` of the real part.  On a
  unit quaternion with real part `cos θ` this is the classical
  `sin((s+1)θ)/sin θ`; that trigonometric identity is *not* formalized.  What
  is proved is `dimension_eq` (value `s+1` at the identity) and the sign
  parity at `-1`.
* The Casimir value is taken from the proved Laplacian eigen-identity on the
  Haar carrier for the polynomial `relativeCharacter s`
  (`characterPolynomial`).  The identification of that polynomial with
  `spinCharacter s` composed with the relative scalar is **not** proved here
  (left open); both are `U_s` by construction in their respective files.
* The conversion `C₂ = (eigenvalue of −Δ_{S³}) / 4` is a normalization
  convention (the one making `A₁` fundamental `3/4`), not a derived fact.
* Only `C2_fund`, `C2_adj` are derived.  `g_sq`, `conv`, `rho_sf`, `eta_max`,
  `K_steps`, `sigma0` are copied from `su2` and remain operating-point
  literals.

## Axiom gate
Exact `Q'` arithmetic, structural recursion, `decide`; see `#print axioms`.
-/

import YMGap.RepTheory.CasimirData
import YMGap.RepTheory.SU2
import YMGap.RepTheory.RationalQuaternionSignQuotient
import YMGap.Continuum.BF4GeometricHaarMehlerProjection
import YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir
import YMGap.Continuum.SU2QuaternionConditionalHeatGenerator

namespace YMGap.RepTheory.SU2Realized

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

/-- Chebyshev-`U` pair `(U_n(t), U_{n+1}(t))`. -/
def chebPair : Nat → Q' → Q' × Q'
  | 0, t => (1, 2 * t)
  | n + 1, t => let p := chebPair n t; (p.2, 2 * t * p.2 - p.1)

/-- Chebyshev `U_n(t)`. -/
def chebU (n : Nat) (t : Q') : Q' := (chebPair n t).1

/-- The spin-`s/2` character as a class function of the real part. -/
def spinCharacter (s : SU2.Spin) (x : RationalQuaternion) : Q' := chebU s x.r

/-- On the unit-norm carrier. -/
def spinCharacterUnit (s : SU2.Spin) (x : RationalQuaternion.UnitNorm) : Q' :=
  spinCharacter s x.val

private theorem chebPair_one (n : Nat) :
    chebPair n 1 = (⟨(n : Int) + 1, 0⟩, ⟨(n : Int) + 2, 0⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show ((chebPair n 1).2, 2 * 1 * (chebPair n 1).2 - (chebPair n 1).1) = _
      rw [ih]
      show (_, Q'.add (Q'.mul (Q'.mul (Q'.ofNat 2) (Q'.ofInt 1)) ⟨(n : Int) + 2, 0⟩)
              (Q'.neg ⟨(n : Int) + 1, 0⟩)) = _
      simp only [Q'.add, Q'.mul, Q'.neg, Q'.ofNat, Q'.ofInt, Q'.den, Prod.mk.injEq,
        Q'.mk.injEq]
      refine ⟨⟨by push_cast; omega, trivial⟩, ⟨by push_cast; omega, trivial⟩⟩

/-- **Dimension from the realized character**: `χ_s(1) = s + 1`. -/
theorem dimension_eq (s : SU2.Spin) :
    (spinCharacter s RationalQuaternion.one).eqv (Q'.ofNat (SU2.dimension s)) := by
  have h : spinCharacter s RationalQuaternion.one = ⟨(s : Int) + 1, 0⟩ := by
    show (chebPair s 1).1 = _
    rw [chebPair_one]
  rw [h]
  show ((s : Int) + 1) * 1 = (Int.ofNat (s + 1)) * 1
  simp

/-- On the unit-norm group identity. -/
theorem dimension_eq_unit (s : SU2.Spin) :
    (spinCharacterUnit s RationalQuaternion.unitOne).eqv
      (Q'.ofNat (SU2.dimension s)) := dimension_eq s

/-- Central sign (spot checks): `χ_s(−1) = (−1)^s (s+1)` for `s ≤ 3`; the
fundamental does not descend to the sign quotient, the adjoint does. -/
theorem spinCharacter_negOne_small :
    (spinCharacter 1 (RationalQuaternion.neg RationalQuaternion.one)).eqv (-2) ∧
    (spinCharacter 2 (RationalQuaternion.neg RationalQuaternion.one)).eqv 3 ∧
    (spinCharacter 3 (RationalQuaternion.neg RationalQuaternion.one)).eqv (-4) := by
  decide

/-- Haar normalization of the spin-½ character on the realized `S³` Haar
functional: `∫ χ₁ = 0`, `∫ χ₁² = ∫ 4 r² = 1`. -/
theorem spinHalf_haar_orthonormal :
    (quaternionHaar 1 [([1], 2)]).eqv 0 ∧
    (quaternionHaar 1 [([2], 4)]).eqv 1 := by
  decide

/-- Realized Casimir from the Laplace eigenvalue `−s(s+2)`, normalized by `1/4`. -/
def realizedCasimir (s : SU2.Spin) : Q' :=
  (Q'.ofNat s * (Q'.ofNat s + 2)) * Q'.mkPos 1 4 (by decide)

/-- The eigen-identity the Casimir is read from (re-exported). -/
theorem realizedCasimir_source (s : SU2.Spin) :
    HaarCarrierEqv 2 (angularLaplacian (relativeCharacter s))
      (YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.polySmul (-(Q'.ofNat s * (Q'.ofNat s + 2)))
        (relativeCharacter s)) :=
  relativeCharacter_angularCasimir 2 s (by decide)

/-- The `RepData` row whose Casimirs are read from the realized characters
(fund = spin ½, `s = 1`; adjoint = spin 1, `s = 2`).  The remaining fields are
copied operating-point literals from `su2`. -/
def rowOfRealized : RepData :=
  { su2 with C2_fund := realizedCasimir 1, C2_adj := realizedCasimir 2 }

/-- **The literal su2 Casimir entries agree with the realized ones.** -/
theorem su2_row_of_realized :
    rowOfRealized.C2_fund.eqv su2.C2_fund ∧
    rowOfRealized.C2_adj.eqv su2.C2_adj ∧
    (spinCharacter 1 RationalQuaternion.one).eqv (Q'.ofNat 2) ∧
    (spinCharacter 2 RationalQuaternion.one).eqv (Q'.ofNat 3) := by
  refine ⟨by decide, by decide, dimension_eq 1, dimension_eq 2⟩

end YMGap.RepTheory.SU2Realized

#print axioms YMGap.RepTheory.SU2Realized.dimension_eq
#print axioms YMGap.RepTheory.SU2Realized.dimension_eq_unit
#print axioms YMGap.RepTheory.SU2Realized.spinCharacter_negOne_small
#print axioms YMGap.RepTheory.SU2Realized.spinHalf_haar_orthonormal
#print axioms YMGap.RepTheory.SU2Realized.realizedCasimir_source
#print axioms YMGap.RepTheory.SU2Realized.su2_row_of_realized
