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
* The Casimir value is read (`casimirReading`, `realizedCasimir`) from the
  proved Laplacian eigen-identity for `relativeCharacter s`, and
  `relativeCharacter_eq_spinCharacter` proves that polynomial evaluates to
  `spinCharacter s (g₀ g₁⁻¹)` at every rational environment.
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
import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.BF4CompactActionCPOrder

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


/-- The eigen-identity the Casimir is read from (re-exported). -/
theorem realizedCasimir_source (s : SU2.Spin) :
    HaarCarrierEqv 2 (angularLaplacian (relativeCharacter s))
      (YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.polySmul (-(Q'.ofNat s * (Q'.ofNat s + 2)))
        (relativeCharacter s)) :=
  relativeCharacter_angularCasimir 2 s (by decide)


/-! ## (a) The relative character IS the spin character of `g₀ g₁⁻¹`

`relativeCharacter s = characterPolynomial relativeScalar s`, where
`relativeScalar` is the scalar part of the polynomial word `x₀ · conj x₁`.
We show that at every rational environment `ρ` its value is
`spinCharacter s (x₀(ρ) · conj x₁(ρ))` computed in `RationalQuaternion`.
No trigonometric identity is needed: both sides are the same Chebyshev-`U`
recursion (`Cheb.U` = `chebU`, proved below), and the only content is the
Hamilton-product evaluation of the polynomial word. -/

open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.RingNormaliser

/-- Quaternion block `c` of an environment. -/
def quatAt (rho : Nat → Q') (c : Nat) : RationalQuaternion :=
  ⟨rho (4 * c), rho (4 * c + 1), rho (4 * c + 2), rho (4 * c + 3)⟩

/-- The rational relative element `g₀ · g₁⁻¹ = x₀ · conj x₁`. -/
def relativeElement (rho : Nat → Q') : RationalQuaternion :=
  RationalQuaternion.mul (quatAt rho 0) (RationalQuaternion.conj (quatAt rho 1))

theorem chebPair_eq_U (t : Q') : ∀ n, chebPair n t = (YMGap.Continuum.Cheb.U n t, YMGap.Continuum.Cheb.U (n + 1) t)
  | 0 => rfl
  | n + 1 => by
      show ((chebPair n t).2, 2 * t * (chebPair n t).2 - (chebPair n t).1) = _
      rw [chebPair_eq_U t n]
      rfl

theorem chebU_eq_U (n : Nat) (t : Q') : chebU n t = YMGap.Continuum.Cheb.U n t := by
  show (chebPair n t).1 = _
  rw [chebPair_eq_U]

private theorem qmul {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') : (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha) (Q'.mul_eqv_congr_left a' _ _ hb)

theorem U_congr {a b : Q'} (h : a.eqv b) : ∀ n,
    (YMGap.Continuum.Cheb.U n a).eqv (YMGap.Continuum.Cheb.U n b) ∧
    (YMGap.Continuum.Cheb.U (n + 1) a).eqv (YMGap.Continuum.Cheb.U (n + 1) b)
  | 0 => ⟨Q'.eqv_refl _, qmul (Q'.eqv_refl _) h⟩
  | n + 1 => by
      have ih := U_congr h n
      refine ⟨ih.2, ?_⟩
      rw [YMGap.Continuum.Cheb.U_succ_succ, YMGap.Continuum.Cheb.U_succ_succ]
      exact Q'.add_eqv_congr' (qmul (qmul (Q'.eqv_refl _) h) ih.2)
        (Q'.neg_eqv_congr _ _ ih.1)

private theorem regroup (a b c d : Q') :
    (a + -(b + (c + d))).eqv ((a + -b) + (-c + -d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _ (Q'.neg_add_eqv_split b (c + d))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _
    (Q'.add_eqv_congr_left (-b) _ _ (Q'.neg_add_eqv_split c d))) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a (-b) (-c + -d))

/-- Evaluation of the polynomial relative scalar is the real part of the
rational relative element. -/
theorem eval_relativeScalar (rho : Nat → Q') :
    (evalRatPoly rho relativeScalar).eqv (relativeElement rho).r := by
  have hm := (evalPolyQuaternion_mul rho (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))).scalar
  refine Q'.eqv_trans _ _ _ hm ?_
  have v := fun i => evalRatPoly_var rho i
  have n := fun i => Q'.eqv_trans _ _ _ (evalRatPoly_neg rho (polyVar i)) (Q'.neg_eqv_congr _ _ (v i))
  refine Q'.eqv_trans _ _ _ ?_ (regroup _ _ _ _)
  exact Q'.add_eqv_congr' (qmul (v 0) (v 4))
    (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' (qmul (v 1) (n 5))
      (Q'.add_eqv_congr' (qmul (v 2) (n 6)) (qmul (v 3) (n 7)))))

/-- **(a)** `relativeCharacter s` evaluates to `spinCharacter s (g₀ g₁⁻¹)` at
every rational environment. -/
theorem relativeCharacter_eq_spinCharacter (rho : Nat → Q') (s : SU2.Spin) :
    (evalRatPoly rho (relativeCharacter s)).eqv (spinCharacter s (relativeElement rho)) := by
  refine Q'.eqv_trans _ _ _ (eval_characterPolynomial rho relativeScalar s) ?_
  show Q'.eqv _ (chebU s (relativeElement rho).r)
  rw [chebU_eq_U]
  exact (U_congr (eval_relativeScalar rho) s).1

/-! ### Casimir read from the eigen-identity -/

/-- An eigen-reading of the realized character: a scalar `lam` with
`Δ_{S³} χ_s ≈ lam · χ_s` on the two-block Haar carrier. -/
structure CasimirReading (s : SU2.Spin) where
  lam : Q'
  eigen : HaarCarrierEqv 2 (angularLaplacian (relativeCharacter s))
    (YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.polySmul lam (relativeCharacter s))

/-- The reading supplied by the proved eigen-identity. -/
def casimirReading (s : SU2.Spin) : CasimirReading s :=
  ⟨-(Q'.ofNat s * (Q'.ofNat s + 2)), relativeCharacter_angularCasimir 2 s (by decide)⟩

/-- Realized Casimir: `−lam/4` of the eigen-reading (`1/4` = normalization
convention making `A₁` fundamental `3/4`).  Uniqueness of `lam` (needs
`∫ χ_s² ≠ 0`) is not proved here. -/
def realizedCasimir (s : SU2.Spin) : Q' :=
  (-(casimirReading s).lam) * Q'.mkPos 1 4 (by decide)


/-! ### Uniqueness of the eigen-reading (well-definedness of `realizedCasimir`)

Pairing the eigen-identity with `χ_s` itself gives `lam · N_s ≈ lam' · N_s`,
`N_s = ∫ χ_s · χ_s` on the two-block Haar carrier.  So the reading is unique
whenever `N_s ≉ 0`.  We prove `N_1 ≈ 1` and `N_2 ≈ 1` by exact evaluation, which
makes `realizedCasimir 1` and `realizedCasimir 2` (the ones used by the row)
well-defined.  The general `N_s ≈ 1` (Schur orthonormality for all `s`) is
not proved here. -/

/-- Self-pairing of the relative character. -/
def selfPairing (s : SU2.Spin) : Q' :=
  quaternionHaar 2 (polyMul (relativeCharacter s) (relativeCharacter s))

private theorem cancel_right {a b N : Q'} (hN : ¬ N.eqv 0) (h : (a * N).eqv (b * N)) :
    a.eqv b := by
  have hn : N.num ≠ 0 := by
    intro h0; apply hN; show N.num * 1 = 0 * (N.den : Int); rw [h0]; simp
  have hd : (N.den : Int) ≠ 0 := by have := N.den_pos; omega
  unfold Q'.eqv at h ⊢
  have h' : (N.num * (N.den : Int)) * (a.num * (b.den : Int)) =
      (N.num * (N.den : Int)) * (b.num * (a.den : Int)) := by
    have e : (a * N).num * ((b * N).den : Int) = (b * N).num * ((a * N).den : Int) := h
    have da : ((a * N).den : Int) = (a.den : Int) * (N.den : Int) := by
      show (((a.den * N.den - 1) + 1 : Nat) : Int) = _
      have := Nat.mul_pos a.den_pos N.den_pos
      rw [Nat.sub_add_cancel this]; push_cast; rfl
    have db : ((b * N).den : Int) = (b.den : Int) * (N.den : Int) := by
      show (((b.den * N.den - 1) + 1 : Nat) : Int) = _
      have := Nat.mul_pos b.den_pos N.den_pos
      rw [Nat.sub_add_cancel this]; push_cast; rfl
    rw [da, db] at e
    change (a.num * N.num) * ((b.den : Int) * N.den) = (b.num * N.num) * ((a.den : Int) * N.den) at e
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at e ⊢
    exact e
  exact Int.eq_of_mul_eq_mul_left (Int.mul_ne_zero hn hd) h'

/-- **Uniqueness**: two eigen-readings agree whenever `N_s ≉ 0`. -/
theorem casimirReading_unique {s : SU2.Spin} (hN : ¬ (selfPairing s).eqv 0)
    (r r' : CasimirReading s) : r.lam.eqv r'.lam := by
  have e := r.eigen (relativeCharacter s)
  have e' := r'.eigen (relativeCharacter s)
  have h1 := YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polyMul_smul_right 2 r.lam
    (relativeCharacter s) (relativeCharacter s)
  have h2 := YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polyMul_smul_right 2 r'.lam
    (relativeCharacter s) (relativeCharacter s)
  have k : (r.lam * selfPairing s).eqv (r'.lam * selfPairing s) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm h1)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm e) (Q'.eqv_trans _ _ _ e' h2))
  exact cancel_right hN k

/-- `N_1 ≈ 1` (exact evaluation). -/
theorem selfPairing_one : (selfPairing 1).eqv 1 := by decide

set_option maxRecDepth 100000 in
/-- `N_2 ≈ 1` (exact evaluation). -/
theorem selfPairing_two : (selfPairing 2).eqv 1 := by decide

theorem realizedCasimir_two_welldefined (r : CasimirReading 2) :
    r.lam.eqv (casimirReading 2).lam :=
  casimirReading_unique (fun h => absurd (Q'.eqv_trans _ _ _ (Q'.eqv_symm selfPairing_two) h)
    (by decide)) r _

/-- The realized Casimirs used by the row are independent of the reading. -/
theorem realizedCasimir_one_welldefined (r : CasimirReading 1) :
    r.lam.eqv (casimirReading 1).lam :=
  casimirReading_unique (fun h => absurd (Q'.eqv_trans _ _ _ (Q'.eqv_symm selfPairing_one) h)
    (by decide)) r _

/-- The dimension-normalized `RepData` row whose Casimirs are read from the realized characters
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
#print axioms YMGap.RepTheory.SU2Realized.relativeCharacter_eq_spinCharacter
#print axioms YMGap.RepTheory.SU2Realized.eval_relativeScalar
#print axioms YMGap.RepTheory.SU2Realized.casimirReading_unique
#print axioms YMGap.RepTheory.SU2Realized.selfPairing_one
#print axioms YMGap.RepTheory.SU2Realized.realizedCasimir_one_welldefined
#print axioms YMGap.RepTheory.SU2Realized.realizedCasimir_two_welldefined
