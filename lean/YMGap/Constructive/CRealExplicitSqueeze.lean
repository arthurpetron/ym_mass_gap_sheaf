/-
# Explicit constructive-real squeeze certificates

The legacy `CReal.leEv` and `CReal.leRat` interfaces are propositions: their
eventual thresholds live behind `Exists`.  That is sufficient for a statement
of convergence, but it cannot feed a Type-level continuum certificate.  This
module gives the smallest witness-bearing strengthening needed by a squeeze:

* `ExplicitLeEv` exposes an approximation modulus for an eventual order;
* `ExplicitWidth` exposes both the scale modulus and approximation modulus for
  a vanishing `leRat` width;
* `explicitEndpointsOfSandwich` compiles those witnesses and an explicit
  middle convergence certificate into explicit endpoint certificates.

No threshold is extracted from a proposition.  The order and width fields are
inputs, and the compiler only composes their supplied moduli.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Constructive.CRealComplete
import YMGap.Constructive.CRealCompleteRate
import YMGap.Constructive.CRealConvergenceCertificate

namespace YMGap.Constructive

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace CReal

open Q'

/-! ## Witness-bearing eventual bounds -/

/-- An explicit approximation modulus for the eventual order `x ≤ y`. -/
structure ExplicitLeEv (x y : CReal) : Type 1 where
  modulus : Q' → Nat
  bound : ∀ ε : Q', (0 : Q') < ε →
    ∀ n : Nat, modulus ε ≤ n → x.approx n ≤ y.approx n + ε

theorem ExplicitLeEv.toLeEv
    {x y : CReal} (certificate : ExplicitLeEv x y) : leEv x y := by
  intro ε hε
  exact ⟨certificate.modulus ε, fun n hn => certificate.bound ε hε n hn⟩

/--
An explicit scale and approximation modulus for
`leRat (sub (upper scale) (lower scale)) ε`, uniformly after a scale stage.

The second tolerance `δ` is kept explicit because `leRat` itself is an
eventual-in-approximation statement.
-/
structure ExplicitWidth (lower upper : Nat → CReal) : Type 1 where
  scaleModulus : Q' → Nat
  approximationModulus : Q' → Nat → Q' → Nat
  bound : ∀ ε : Q', (0 : Q') < ε →
    ∀ scale : Nat, scaleModulus ε ≤ scale →
      ∀ δ : Q', (0 : Q') < δ →
        ∀ n : Nat, approximationModulus ε scale δ ≤ n →
          (sub (upper scale) (lower scale)).approx n ≤ ε + δ

theorem ExplicitWidth.toLeRat
    {lower upper : Nat → CReal} (certificate : ExplicitWidth lower upper) :
    ∀ ε : Q', (0 : Q') < ε →
      ∃ start : Nat, ∀ scale : Nat, start ≤ scale →
        leRat (sub (upper scale) (lower scale)) ε := by
  intro ε hε
  refine ⟨certificate.scaleModulus ε, fun scale hscale δ hδ => ?_⟩
  exact ⟨certificate.approximationModulus ε scale δ,
    fun n hn => certificate.bound ε hε scale hscale δ hδ n hn⟩

/-! ## Explicit squeeze compiler -/

/--
Compile explicit eventual lower/middle and middle/upper order witnesses, an
explicit vanishing width, and an explicit middle convergence certificate into
certificates for both endpoint streams.

The error budget is four copies of `q = ε/4`: width contributes two copies,
each order comparison contributes one, and the middle certificate contributes
one.  All maxima are computed directly from the supplied moduli.
-/
def explicitEndpointsOfSandwich
    {lower middle upper : Nat → CReal} {limit : CReal}
    (middleCertificate : ExplicitConvergenceCertificate middle limit)
    (lowerLeMiddle : ∀ scale, ExplicitLeEv (lower scale) (middle scale))
    (middleLeUpper : ∀ scale, ExplicitLeEv (middle scale) (upper scale))
    (width : ExplicitWidth lower upper) :
    ExplicitConvergenceCertificate upper limit ×
      ExplicitConvergenceCertificate lower limit := by
  let buildUpper : ExplicitConvergenceCertificate upper limit := by
    refine {
      modulus := fun ε =>
        max (middleCertificate.modulus (HalfPow.half * (HalfPow.half * ε)))
          (width.scaleModulus (HalfPow.half * (HalfPow.half * ε)))
      approximationModulus := fun ε scale =>
        max (max (middleCertificate.approximationModulus
          (HalfPow.half * (HalfPow.half * ε)) scale)
          ((lowerLeMiddle scale).modulus
            (HalfPow.half * (HalfPow.half * ε))))
          (max ((middleLeUpper scale).modulus
            (HalfPow.half * (HalfPow.half * ε)))
            (width.approximationModulus (HalfPow.half * (HalfPow.half * ε))
              scale (HalfPow.half * (HalfPow.half * ε))))
      bound := ?_ }
    intro ε hε scale hscale n hn
    let q : Q' := HalfPow.half * (HalfPow.half * ε)
    have hqpos : (0 : Q') < q :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
    have hscaleMiddle : middleCertificate.modulus q ≤ scale := by
      exact Nat.le_trans (Nat.le_max_left _ _) hscale
    have hscaleWidth : width.scaleModulus q ≤ scale := by
      exact Nat.le_trans (Nat.le_max_right _ _) hscale
    have hnMiddle : middleCertificate.approximationModulus q scale ≤ n := by
      exact Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hnLower : (lowerLeMiddle scale).modulus q ≤ n := by
      exact Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hnUpper : (middleLeUpper scale).modulus q ≤ n := by
      exact Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hnWidth : width.approximationModulus q scale q ≤ n := by
      exact Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hMiddle := middleCertificate.bound q hqpos scale hscaleMiddle n hnMiddle
    have hLowerMiddle := (lowerLeMiddle scale).bound q hqpos n hnLower
    have hMiddleUpper := (middleLeUpper scale).bound q hqpos n hnUpper
    have hWidth := width.bound q hqpos scale hscaleWidth q hqpos n hnWidth
    have hUpperLower : (upper scale).approx n ≤
        (lower scale).approx n + (q + q) := by
      have hsub := CReal.leAddOfSubLe hWidth
      exact hsub
    have hLowerPad : (lower scale).approx n + (q + q) ≤
        (middle scale).approx n + q + (q + q) :=
      Q'.add_le_add_right _ _ (q + q) hLowerMiddle
    have hLowerAssoc : (middle scale).approx n + q + (q + q) ≤
        ((middle scale).approx n + q + q) + q :=
      Q'.ge_of_eqv
        (Q'.add_assoc_eqv ((middle scale).approx n + q) q q)
    have hUpperMiddle3 : (upper scale).approx n ≤
        ((middle scale).approx n + q + q) + q :=
      Q'.le_trans' _ _ _ hUpperLower
        (Q'.le_trans' _ _ _ hLowerPad hLowerAssoc)
    have hfour : (((q + q) + q) + q) ≤ ε :=
      CReal.fourQ_le ε hε
    have hMiddleToLimit1 : (middle scale).approx n + q ≤
        (limit.approx n + q) + q :=
      Q'.add_le_add_right _ _ q hMiddle.1
    have hMiddleToLimit2 : (middle scale).approx n + q + q ≤
        ((limit.approx n + q) + q) + q :=
      Q'.add_le_add_right _ _ q hMiddleToLimit1
    have hMiddleToLimit3 : (middle scale).approx n + q + q + q ≤
        (((limit.approx n + q) + q) + q) + q :=
      Q'.add_le_add_right _ _ q hMiddleToLimit2
    have hUpperLimit : (upper scale).approx n ≤ limit.approx n + ε :=
      Q'.le_trans' _ _ _ hUpperMiddle3
        (Q'.le_trans' _ _ _ hMiddleToLimit3
          (CReal.collapse4 (limit.approx n) q ε hfour))
    have hLimitUpper2 : limit.approx n ≤
        (upper scale).approx n + q + q :=
      Q'.le_trans' _ _ _ hMiddle.2
        (Q'.add_le_add_right _ _ q hMiddleUpper)
    have hUpperPad1 : (upper scale).approx n + q + q ≤
        ((upper scale).approx n + q + q) + q :=
      Q'.add_le_self_of_nonneg _ q (Q'.le_of_lt hqpos)
    have hUpperPad2 : ((upper scale).approx n + q + q) + q ≤
        (((upper scale).approx n + q + q) + q) + q :=
      Q'.add_le_self_of_nonneg _ q (Q'.le_of_lt hqpos)
    have hLimitUpper4 : limit.approx n ≤
        (((upper scale).approx n + q + q) + q) + q :=
      Q'.le_trans' _ _ _ hLimitUpper2
        (Q'.le_trans' _ _ _ hUpperPad1 hUpperPad2)
    have hcollapseUpper : ((((upper scale).approx n + q + q) + q) + q) ≤
        (upper scale).approx n + ε :=
      CReal.collapse4 ((upper scale).approx n) q ε hfour
    exact ⟨hUpperLimit, Q'.le_trans' _ _ _ hLimitUpper4 hcollapseUpper⟩
  let buildLower : ExplicitConvergenceCertificate lower limit := by
    refine {
      modulus := fun ε =>
        max (middleCertificate.modulus (HalfPow.half * (HalfPow.half * ε)))
          (width.scaleModulus (HalfPow.half * (HalfPow.half * ε)))
      approximationModulus := fun ε scale =>
        max (max (middleCertificate.approximationModulus
          (HalfPow.half * (HalfPow.half * ε)) scale)
          ((lowerLeMiddle scale).modulus
            (HalfPow.half * (HalfPow.half * ε))))
          (max ((middleLeUpper scale).modulus
            (HalfPow.half * (HalfPow.half * ε)))
            (width.approximationModulus (HalfPow.half * (HalfPow.half * ε))
              scale (HalfPow.half * (HalfPow.half * ε))))
      bound := ?_ }
    intro ε hε scale hscale n hn
    let q : Q' := HalfPow.half * (HalfPow.half * ε)
    have hqpos : (0 : Q') < q :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
    have hscaleMiddle : middleCertificate.modulus q ≤ scale := by
      exact Nat.le_trans (Nat.le_max_left _ _) hscale
    have hscaleWidth : width.scaleModulus q ≤ scale := by
      exact Nat.le_trans (Nat.le_max_right _ _) hscale
    have hnMiddle : middleCertificate.approximationModulus q scale ≤ n := by
      exact Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hnLower : (lowerLeMiddle scale).modulus q ≤ n := by
      exact Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hnUpper : (middleLeUpper scale).modulus q ≤ n := by
      exact Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hnWidth : width.approximationModulus q scale q ≤ n := by
      exact Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hMiddle := middleCertificate.bound q hqpos scale hscaleMiddle n hnMiddle
    have hLowerMiddle := (lowerLeMiddle scale).bound q hqpos n hnLower
    have hMiddleUpper := (middleLeUpper scale).bound q hqpos n hnUpper
    have hWidth := width.bound q hqpos scale hscaleWidth q hqpos n hnWidth
    have hUpperLower : (upper scale).approx n ≤
        (lower scale).approx n + (q + q) := by
      have hsub := CReal.leAddOfSubLe hWidth
      exact hsub
    have hLowerLimit2 : (lower scale).approx n ≤
        limit.approx n + q + q :=
      Q'.le_trans' _ _ _ hLowerMiddle
        (Q'.add_le_add_right _ _ q hMiddle.1)
    have hLowerPad1 : (lower scale).approx n + q + q ≤
        ((lower scale).approx n + q + q) + q :=
      Q'.add_le_self_of_nonneg _ q (Q'.le_of_lt hqpos)
    have hLowerPad2 : ((lower scale).approx n + q + q) + q ≤
        (((lower scale).approx n + q + q) + q) + q :=
      Q'.add_le_self_of_nonneg _ q (Q'.le_of_lt hqpos)
    have hfour : (((q + q) + q) + q) ≤ ε :=
      CReal.fourQ_le ε hε
    have hLowerLimit3 : (lower scale).approx n ≤
        (limit.approx n + q + q) + q :=
      Q'.le_trans' _ _ _ hLowerLimit2
        (Q'.add_le_self_of_nonneg _ q (Q'.le_of_lt hqpos))
    have hLowerLimit4 : (lower scale).approx n ≤
        ((limit.approx n + q + q) + q) + q :=
      Q'.le_trans' _ _ _ hLowerLimit3
        (Q'.add_le_self_of_nonneg _ q (Q'.le_of_lt hqpos))
    have hLowerLimit : (lower scale).approx n ≤ limit.approx n + ε :=
      Q'.le_trans' _ _ _ hLowerLimit4
        (CReal.collapse4 (limit.approx n) q ε hfour)
    have hLimitUpper2 : limit.approx n ≤
        (upper scale).approx n + q + q :=
      Q'.le_trans' _ _ _ hMiddle.2
        (Q'.add_le_add_right _ _ q hMiddleUpper)
    have hUpperLowerPad1 : (upper scale).approx n + q ≤
        ((lower scale).approx n + q + q) + q := by
      have h0 : (upper scale).approx n + q ≤
          ((lower scale).approx n + (q + q)) + q :=
        Q'.add_le_add_right _ _ q hUpperLower
      have h1 : ((lower scale).approx n + (q + q)) + q ≤
          ((lower scale).approx n + q + q) + q :=
        Q'.add_le_add_right _ _ q
          (Q'.ge_of_eqv (Q'.add_assoc_eqv ((lower scale).approx n) q q))
      exact Q'.le_trans' _ _ _ h0 h1
    have hUpperLowerPad2 : (upper scale).approx n + q + q ≤
        (((lower scale).approx n + q + q) + q) + q :=
      Q'.add_le_add_right _ _ q hUpperLowerPad1
    have hLimitLower4 : limit.approx n ≤
        (((lower scale).approx n + q + q) + q) + q :=
      Q'.le_trans' _ _ _ hLimitUpper2
        hUpperLowerPad2
    have hcollapseLower : ((((lower scale).approx n + q + q) + q) + q) ≤
        (lower scale).approx n + ε :=
      CReal.collapse4 ((lower scale).approx n) q ε hfour
    exact ⟨hLowerLimit, Q'.le_trans' _ _ _ hLimitLower4 hcollapseLower⟩
  exact ⟨buildUpper, buildLower⟩

/-! ## Non-vacuity witness -/

/-- The constant zero stream has an explicit convergence certificate. -/
def zeroExplicitConvergenceCertificate :
    ExplicitConvergenceCertificate
      (fun _ : Nat => CReal.ofQ' 0) CReal.czero where
  modulus := fun _ => 0
  approximationModulus := fun _ _ => 0
  bound := by
    intro ε hε N hN n hn
    simp only [CReal.czero, CReal.ofQ'_approx]
    exact ⟨Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε),
      Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε)⟩

/-- The constant zero streams satisfy explicit eventual order witnesses. -/
def zeroExplicitLeEv :
    ExplicitLeEv CReal.czero CReal.czero where
  modulus := fun _ => 0
  bound := by
    intro ε hε n hn
    simp only [CReal.czero, CReal.ofQ'_approx]
    exact Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε)

/-- The zero-width stream has an explicit scale and approximation modulus. -/
def zeroExplicitWidth : ExplicitWidth
    (fun _ : Nat => CReal.czero) (fun _ : Nat => CReal.czero) where
  scaleModulus := fun _ => 0
  approximationModulus := fun _ _ _ => 0
  bound := by
    intro ε hε scale hscale δ hδ n hn
    change (0 : Q') + (-(0 : Q')) ≤ ε + δ
    have hzero : ((0 : Q') + (-(0 : Q'))).eqv (0 : Q') :=
      Q'.add_neg_self_eqv 0
    have hεδ : (0 : Q') ≤ ε + δ :=
      Q'.le_trans' _ _ _ (Q'.le_of_lt hε)
        (Q'.add_le_self_of_nonneg ε δ (Q'.le_of_lt hδ))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero) hεδ

/-- A concrete inhabitant of the generic explicit squeeze compiler. -/
def explicitEndpoints_const_zero :
    ExplicitConvergenceCertificate
      (fun _ : Nat => CReal.czero) CReal.czero ×
      ExplicitConvergenceCertificate
        (fun _ : Nat => CReal.czero) CReal.czero :=
  explicitEndpointsOfSandwich
    zeroExplicitConvergenceCertificate
    (fun _ => zeroExplicitLeEv)
    (fun _ => zeroExplicitLeEv)
    zeroExplicitWidth

end CReal

end YMGap.Constructive

/-! ## Dependency gate -/

#print axioms
  YMGap.Constructive.CReal.ExplicitLeEv.toLeEv
#print axioms
  YMGap.Constructive.CReal.ExplicitWidth.toLeRat
#print axioms
  YMGap.Constructive.CReal.explicitEndpointsOfSandwich
#print axioms
  YMGap.Constructive.CReal.explicitEndpoints_const_zero
