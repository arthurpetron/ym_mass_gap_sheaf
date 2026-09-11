/-
# Fundamental plaquette trace as a symbolic four-index sum

The fundamental plaquette trace polynomial is the trace of four `2 x 2`
matrix coefficients; on unit-quaternion inputs it is the fundamental
`SU(2)` character.  This leaf expands that trace into four nested Boolean
binders without enumerating any assignment carrier.  Both cyclic words
required by the outward elementary-cube orientation are recorded literally:

    standard : U0 * U3 * conj(U2) * conj(U1),
    reversed : U1 * U2 * conj(U3) * conj(U0).

Every fixed summand is left-associated.  Reassociation occurs only after
evaluation, in `RationalComplexEqv`; no raw `RatPoly` associativity,
commutativity, normalization, or Haar extensionality is asserted.

The four Boolean binders are safe to unfold locally (sixteen terms).  This
file does not form the product of six face sums and does not unfold a
twenty-four-index cube sum.  Physical link blocks and face-corner tags are
deliberately left to the next cube-wiring leaf.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

namespace YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

/-! ## 1. Four nested symbolic Boolean binders -/

/-- Four nested false-before-true binders in the complex-polynomial carrier.
This is the depth-four specialization of the symbolic Boolean-sum API; it
contains only sixteen leaves and never constructs a list of assignments. -/
def complexRatPolyFourBoolSum
    (family : Bool → Bool → Bool → Bool → ComplexRatPoly) :
    ComplexRatPoly :=
  complexRatPolyBoolBind (fun first =>
    complexRatPolyBoolBind (fun second =>
      complexRatPolyBoolBind (fun third =>
        complexRatPolyBoolBind (fun fourth =>
          family first second third fourth))))

/-- Value-level four-binder sum with the identical addition tree. -/
def rationalComplexFourBoolSum
    (family : Bool → Bool → Bool → Bool → RationalComplex) :
    RationalComplex :=
  rationalComplexBoolBind (fun first =>
    rationalComplexBoolBind (fun second =>
      rationalComplexBoolBind (fun third =>
        rationalComplexBoolBind (fun fourth =>
          family first second third fourth))))

/-- Evaluation commutes with the bounded four-index symbolic sum. -/
theorem evalComplexRatPoly_fourBoolSum
    (rho : Nat → Q')
    (family : Bool → Bool → Bool → Bool → ComplexRatPoly) :
    RationalComplexEqv
      (evalComplexRatPoly rho (complexRatPolyFourBoolSum family))
      (rationalComplexFourBoolSum (fun first second third fourth =>
        evalComplexRatPoly rho (family first second third fourth))) := by
  unfold complexRatPolyFourBoolSum rationalComplexFourBoolSum
  refine rationalComplexEqv_trans
    (evalComplexRatPoly_boolBind rho _) ?_
  apply rationalComplexBoolBind_congr
  intro first
  refine rationalComplexEqv_trans
    (evalComplexRatPoly_boolBind rho _) ?_
  apply rationalComplexBoolBind_congr
  intro second
  refine rationalComplexEqv_trans
    (evalComplexRatPoly_boolBind rho _) ?_
  apply rationalComplexBoolBind_congr
  intro third
  exact evalComplexRatPoly_boolBind rho
    (fun fourth => family first second third fourth)

/-- Pointwise equivalence transports through four value-level binders. -/
theorem rationalComplexFourBoolSum_congr
    {left right : Bool → Bool → Bool → Bool → RationalComplex}
    (hpointwise : ∀ first second third fourth,
      RationalComplexEqv
        (left first second third fourth)
        (right first second third fourth)) :
    RationalComplexEqv
      (rationalComplexFourBoolSum left)
      (rationalComplexFourBoolSum right) := by
  unfold rationalComplexFourBoolSum
  exact rationalComplexBoolBind_congr (fun first =>
    rationalComplexBoolBind_congr (fun second =>
      rationalComplexBoolBind_congr (fun third =>
        rationalComplexBoolBind_congr (fun fourth =>
          hpointwise first second third fourth))))

/-! ## 2. Fixed four-factor terms and their evaluation -/

/-- Literal left-associated product of four complex polynomial factors. -/
def complexRatPolyMulFourLeft
    (first second third fourth : ComplexRatPoly) : ComplexRatPoly :=
  complexRatPolyMul
    (complexRatPolyMul (complexRatPolyMul first second) third) fourth

/-- Literal left-associated product of four rational-complex values. -/
def rationalComplexMulFourLeft
    (first second third fourth : RationalComplex) : RationalComplex :=
  rationalComplexMul
    (rationalComplexMul (rationalComplexMul first second) third) fourth

/-- Right-associated value product used only as the matrix-expansion proof
normal form. -/
def rationalComplexMulFourRight
    (first second third fourth : RationalComplex) : RationalComplex :=
  rationalComplexMul first
    (rationalComplexMul second (rationalComplexMul third fourth))

theorem rationalComplexMulFourLeft_eqv_right
    (first second third fourth : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMulFourLeft first second third fourth)
      (rationalComplexMulFourRight first second third fourth) := by
  unfold rationalComplexMulFourLeft rationalComplexMulFourRight
  exact rationalComplexEqv_trans
    (rationalComplexMul_assoc
      (rationalComplexMul first second) third fourth)
    (rationalComplexMul_assoc
      first second (rationalComplexMul third fourth))

theorem evalComplexRatPoly_mulFourLeft
    (rho : Nat → Q')
    (first second third fourth : ComplexRatPoly) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (complexRatPolyMulFourLeft first second third fourth))
      (rationalComplexMulFourLeft
        (evalComplexRatPoly rho first)
        (evalComplexRatPoly rho second)
        (evalComplexRatPoly rho third)
        (evalComplexRatPoly rho fourth)) := by
  unfold complexRatPolyMulFourLeft rationalComplexMulFourLeft
  exact rationalComplexEqv_trans
    (evalComplexRatPoly_mul rho
      (complexRatPolyMul (complexRatPolyMul first second) third) fourth)
    (rationalComplexMul_congr
      (rationalComplexEqv_trans
        (evalComplexRatPoly_mul rho
          (complexRatPolyMul first second) third)
        (rationalComplexMul_congr
          (evalComplexRatPoly_mul rho first second)
          (rationalComplexEqv_refl _)))
      (rationalComplexEqv_refl _))

/-! ## 3. The generic cyclic matrix-path identity -/

/-- Four-index cyclic path sum of four arbitrary fundamental matrices. -/
def rationalComplexFourCycleSum
    (first second third fourth : FundamentalMatrix) : RationalComplex :=
  rationalComplexFourBoolSum (fun a b c d =>
    rationalComplexMulFourLeft
      (first a b) (second b c) (third c d) (fourth d a))

private def rationalComplexFourCycleSumRight
    (first second third fourth : FundamentalMatrix) : RationalComplex :=
  rationalComplexFourBoolSum (fun a b c d =>
    rationalComplexMulFourRight
      (first a b) (second b c) (third c d) (fourth d a))

/-- The completely distributed cyclic path sum is the trace of the
right-associated matrix product.  Distribution and reassociation occur only
in the rational-complex setoid. -/
theorem rationalComplexFourCycleSum_eq_matrixTrace
    (first second third fourth : FundamentalMatrix) :
    RationalComplexEqv
      (rationalComplexFourCycleSum first second third fourth)
      (fundamentalMatrixTrace
        (fundamentalMatrixMul first
          (fundamentalMatrixMul second
            (fundamentalMatrixMul third fourth)))) := by
  have hleftRight : RationalComplexEqv
      (rationalComplexFourCycleSum first second third fourth)
      (rationalComplexFourCycleSumRight
        first second third fourth) := by
    exact rationalComplexFourBoolSum_congr
      (fun a b c d =>
        rationalComplexMulFourLeft_eqv_right
          (first a b) (second b c) (third c d) (fourth d a))
  have hrightTrace : RationalComplexEqv
      (rationalComplexFourCycleSumRight first second third fourth)
      (fundamentalMatrixTrace
        (fundamentalMatrixMul first
          (fundamentalMatrixMul second
            (fundamentalMatrixMul third fourth)))) := by
    unfold rationalComplexFourCycleSumRight rationalComplexFourBoolSum
      fundamentalMatrixTrace
    change RationalComplexEqv
      (rationalComplexBoolBind (fun a =>
        rationalComplexBoolBind (fun b =>
          rationalComplexBoolBind (fun c =>
            rationalComplexBoolBind (fun d =>
              rationalComplexMulFourRight
                (first a b) (second b c) (third c d) (fourth d a))))))
      (rationalComplexBoolBind (fun a =>
        (fundamentalMatrixMul first
          (fundamentalMatrixMul second
            (fundamentalMatrixMul third fourth))) a a))
    apply rationalComplexBoolBind_congr
    intro a
    have hfixedB : ∀ b,
        RationalComplexEqv
          (rationalComplexBoolBind (fun c =>
            rationalComplexBoolBind (fun d =>
              rationalComplexMulFourRight
                (first a b) (second b c) (third c d) (fourth d a))))
          (rationalComplexMul (first a b)
            ((fundamentalMatrixMul second
              (fundamentalMatrixMul third fourth)) b a)) := by
      intro b
      have hfixedC : ∀ c,
          RationalComplexEqv
            (rationalComplexBoolBind (fun d =>
              rationalComplexMulFourRight
                (first a b) (second b c) (third c d) (fourth d a)))
            (rationalComplexMul (first a b)
              (rationalComplexMul (second b c)
                ((fundamentalMatrixMul third fourth) c a))) := by
        intro c
        unfold rationalComplexMulFourRight
        exact rationalComplexEqv_trans
          (rationalComplexEqv_symm
            (rationalComplexMul_boolBind (first a b)
              (fun d => rationalComplexMul (second b c)
                (rationalComplexMul (third c d) (fourth d a)))))
          (rationalComplexMul_congr_right (first a b)
            (rationalComplexEqv_symm
              (rationalComplexMul_boolBind (second b c)
                (fun d =>
                  rationalComplexMul (third c d) (fourth d a)))))
      exact rationalComplexEqv_trans
        (rationalComplexBoolBind_congr hfixedC)
        (rationalComplexEqv_symm
          (rationalComplexMul_boolBind (first a b)
            (fun c => rationalComplexMul (second b c)
              ((fundamentalMatrixMul third fourth) c a))))
    change RationalComplexEqv
      (rationalComplexBoolBind (fun b =>
        rationalComplexBoolBind (fun c =>
          rationalComplexBoolBind (fun d =>
            rationalComplexMulFourRight
              (first a b) (second b c) (third c d) (fourth d a)))))
      ((fundamentalMatrixMul first
        (fundamentalMatrixMul second
          (fundamentalMatrixMul third fourth))) a a)
    exact rationalComplexBoolBind_congr hfixedB
  exact rationalComplexEqv_trans hleftRight hrightTrace

/-! ## 4. Standard and reversed plaquette coefficient sums -/

/-- One standard cyclic summand:
`F(block0,a,b) F(block3,b,c) R(block2,c,d) R(block1,d,a)`. -/
def standardPlaquetteTraceTerm
    (block0 block1 block2 block3 : Nat)
    (a b c d : Bool) : ComplexRatPoly :=
  complexRatPolyMulFourLeft
    (forwardFundamentalCoefficient block0 a b)
    (forwardFundamentalCoefficient block3 b c)
    (reverseFundamentalCoefficient block2 c d)
    (reverseFundamentalCoefficient block1 d a)

/-- Symbolic fundamental trace of the standard word
`U0 U3 conj(U2) conj(U1)`. -/
def standardPlaquetteTraceExpansion
    (block0 block1 block2 block3 : Nat) : ComplexRatPoly :=
  complexRatPolyFourBoolSum
    (standardPlaquetteTraceTerm block0 block1 block2 block3)

/-- One reversed cyclic summand:
`F(block1,a,b) F(block2,b,c) R(block3,c,d) R(block0,d,a)`. -/
def reversedPlaquetteTraceTerm
    (block0 block1 block2 block3 : Nat)
    (a b c d : Bool) : ComplexRatPoly :=
  complexRatPolyMulFourLeft
    (forwardFundamentalCoefficient block1 a b)
    (forwardFundamentalCoefficient block2 b c)
    (reverseFundamentalCoefficient block3 c d)
    (reverseFundamentalCoefficient block0 d a)

/-- Symbolic fundamental trace of the orientation-reversed conjugate word
`U1 U2 conj(U3) conj(U0)`.  It is the inverse word on the unit-quaternion
locus. -/
def reversedPlaquetteTraceExpansion
    (block0 block1 block2 block3 : Nat) : ComplexRatPoly :=
  complexRatPolyFourBoolSum
    (reversedPlaquetteTraceTerm block0 block1 block2 block3)

/-- Evaluated matrix of one reverse-oriented link coefficient. -/
def evaluatedReverseFundamentalLinkMatrix
    (rho : Nat → Q') (block : Nat) : FundamentalMatrix :=
  fun row column =>
    evalComplexRatPoly rho
      (reverseFundamentalCoefficient block row column)

/-- Matrix product whose trace is the standard coefficient expansion. -/
def standardPlaquetteTraceMatrix
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) : FundamentalMatrix :=
  fundamentalMatrixMul
    (evaluatedFundamentalMatrix rho (fundamentalLinkQuaternion block0))
    (fundamentalMatrixMul
      (evaluatedFundamentalMatrix rho (fundamentalLinkQuaternion block3))
      (fundamentalMatrixMul
        (evaluatedReverseFundamentalLinkMatrix rho block2)
        (evaluatedReverseFundamentalLinkMatrix rho block1)))

/-- Matrix product whose trace is the reversed coefficient expansion. -/
def reversedPlaquetteTraceMatrix
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) : FundamentalMatrix :=
  fundamentalMatrixMul
    (evaluatedFundamentalMatrix rho (fundamentalLinkQuaternion block1))
    (fundamentalMatrixMul
      (evaluatedFundamentalMatrix rho (fundamentalLinkQuaternion block2))
      (fundamentalMatrixMul
        (evaluatedReverseFundamentalLinkMatrix rho block3)
        (evaluatedReverseFundamentalLinkMatrix rho block0)))

theorem eval_standardPlaquetteTraceExpansion_eq_matrixTrace
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (standardPlaquetteTraceExpansion block0 block1 block2 block3))
      (fundamentalMatrixTrace
        (standardPlaquetteTraceMatrix rho block0 block1 block2 block3)) := by
  exact rationalComplexEqv_trans
    (evalComplexRatPoly_fourBoolSum rho
      (standardPlaquetteTraceTerm block0 block1 block2 block3))
    (rationalComplexEqv_trans
      (rationalComplexFourBoolSum_congr (fun a b c d =>
        evalComplexRatPoly_mulFourLeft rho
          (forwardFundamentalCoefficient block0 a b)
          (forwardFundamentalCoefficient block3 b c)
          (reverseFundamentalCoefficient block2 c d)
          (reverseFundamentalCoefficient block1 d a)))
      (rationalComplexFourCycleSum_eq_matrixTrace
        (evaluatedFundamentalMatrix rho
          (fundamentalLinkQuaternion block0))
        (evaluatedFundamentalMatrix rho
          (fundamentalLinkQuaternion block3))
        (evaluatedReverseFundamentalLinkMatrix rho block2)
        (evaluatedReverseFundamentalLinkMatrix rho block1)))

theorem eval_reversedPlaquetteTraceExpansion_eq_matrixTrace
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (reversedPlaquetteTraceExpansion block0 block1 block2 block3))
      (fundamentalMatrixTrace
        (reversedPlaquetteTraceMatrix rho block0 block1 block2 block3)) := by
  exact rationalComplexEqv_trans
    (evalComplexRatPoly_fourBoolSum rho
      (reversedPlaquetteTraceTerm block0 block1 block2 block3))
    (rationalComplexEqv_trans
      (rationalComplexFourBoolSum_congr (fun a b c d =>
        evalComplexRatPoly_mulFourLeft rho
          (forwardFundamentalCoefficient block1 a b)
          (forwardFundamentalCoefficient block2 b c)
          (reverseFundamentalCoefficient block3 c d)
          (reverseFundamentalCoefficient block0 d a)))
      (rationalComplexFourCycleSum_eq_matrixTrace
        (evaluatedFundamentalMatrix rho
          (fundamentalLinkQuaternion block1))
        (evaluatedFundamentalMatrix rho
          (fundamentalLinkQuaternion block2))
        (evaluatedReverseFundamentalLinkMatrix rho block3)
        (evaluatedReverseFundamentalLinkMatrix rho block0)))

/-! ## 5. Quaternion-word and Chebyshev semantics -/

/-- Evaluated coordinate quaternion on one link block. -/
def evaluatedFundamentalLinkQuaternion
    (rho : Nat → Q') (block : Nat) : RationalQuaternion :=
  RationalQuaternionRatPoly.eval rho (fundamentalLinkQuaternion block)

/-- Right-associated standard oriented quaternion word. -/
def standardPlaquetteQuaternionWord
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) : RationalQuaternion :=
  RationalQuaternion.mul
    (evaluatedFundamentalLinkQuaternion rho block0)
    (RationalQuaternion.mul
      (evaluatedFundamentalLinkQuaternion rho block3)
      (RationalQuaternion.mul
        (RationalQuaternion.conj
          (evaluatedFundamentalLinkQuaternion rho block2))
        (RationalQuaternion.conj
          (evaluatedFundamentalLinkQuaternion rho block1))))

/-- Right-associated reversed oriented quaternion word. -/
def reversedPlaquetteQuaternionWord
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) : RationalQuaternion :=
  RationalQuaternion.mul
    (evaluatedFundamentalLinkQuaternion rho block1)
    (RationalQuaternion.mul
      (evaluatedFundamentalLinkQuaternion rho block2)
      (RationalQuaternion.mul
        (RationalQuaternion.conj
          (evaluatedFundamentalLinkQuaternion rho block3))
        (RationalQuaternion.conj
          (evaluatedFundamentalLinkQuaternion rho block0))))

private theorem rationalQuaternionEqv_refl
    (quaternion : RationalQuaternion) : quaternion.Equivalent quaternion :=
  ⟨Q'.eqv_refl quaternion.r, Q'.eqv_refl quaternion.i,
    Q'.eqv_refl quaternion.j, Q'.eqv_refl quaternion.k⟩

private theorem rationalQuaternionEqv_symm
    {left right : RationalQuaternion}
    (h : left.Equivalent right) : right.Equivalent left :=
  ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2.1,
    Q'.eqv_symm h.2.2.1, Q'.eqv_symm h.2.2.2⟩

private theorem rationalQuaternionEqv_trans
    {first second third : RationalQuaternion}
    (hfirst : first.Equivalent second)
    (hsecond : second.Equivalent third) : first.Equivalent third :=
  ⟨Q'.eqv_trans _ _ _ hfirst.1 hsecond.1,
    Q'.eqv_trans _ _ _ hfirst.2.1 hsecond.2.1,
    Q'.eqv_trans _ _ _ hfirst.2.2.1 hsecond.2.2.1,
    Q'.eqv_trans _ _ _ hfirst.2.2.2 hsecond.2.2.2⟩

/-- Reversing the cyclic word and conjugating every factor is exactly whole
word quaternion conjugation, modulo the constructive rational setoid.  This
identity does not require unit norm; on the unit-quaternion locus it is the
usual inverse-word identity. -/
theorem conj_standardPlaquetteQuaternionWord_eqv_reversed
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) :
    (RationalQuaternion.conj
      (standardPlaquetteQuaternionWord
        rho block0 block1 block2 block3)).Equivalent
      (reversedPlaquetteQuaternionWord
        rho block0 block1 block2 block3) := by
  let q0 := evaluatedFundamentalLinkQuaternion rho block0
  let q1 := evaluatedFundamentalLinkQuaternion rho block1
  let q2 := evaluatedFundamentalLinkQuaternion rho block2
  let q3 := evaluatedFundamentalLinkQuaternion rho block3
  have houter := RationalQuaternion.conj_mul q0
    (RationalQuaternion.mul q3
      (RationalQuaternion.mul
        (RationalQuaternion.conj q2)
        (RationalQuaternion.conj q1)))
  have hq3 := RationalQuaternion.mul_congr
    (RationalQuaternion.conj_mul q3
      (RationalQuaternion.mul
        (RationalQuaternion.conj q2)
        (RationalQuaternion.conj q1)))
    (rationalQuaternionEqv_refl (RationalQuaternion.conj q0))
  have hinnerConj := RationalQuaternion.conj_mul
    (RationalQuaternion.conj q2) (RationalQuaternion.conj q1)
  have hinner := RationalQuaternion.mul_congr
    (RationalQuaternion.mul_congr hinnerConj
      (rationalQuaternionEqv_refl (RationalQuaternion.conj q3)))
    (rationalQuaternionEqv_refl (RationalQuaternion.conj q0))
  have hdouble := RationalQuaternion.mul_congr
    (RationalQuaternion.mul_congr
      (RationalQuaternion.mul_congr
        (RationalQuaternion.conj_conj q1)
        (RationalQuaternion.conj_conj q2))
      (rationalQuaternionEqv_refl (RationalQuaternion.conj q3)))
    (rationalQuaternionEqv_refl (RationalQuaternion.conj q0))
  have hassocOuter := RationalQuaternion.mul_assoc
    (RationalQuaternion.mul q1 q2)
    (RationalQuaternion.conj q3)
    (RationalQuaternion.conj q0)
  have hassocInner := RationalQuaternion.mul_assoc q1 q2
    (RationalQuaternion.mul
      (RationalQuaternion.conj q3)
      (RationalQuaternion.conj q0))
  exact rationalQuaternionEqv_trans
    (by simpa [standardPlaquetteQuaternionWord, q0, q1, q2, q3] using houter)
    (rationalQuaternionEqv_trans hq3
      (rationalQuaternionEqv_trans hinner
        (rationalQuaternionEqv_trans hdouble
          (rationalQuaternionEqv_trans hassocOuter
            (by
              simpa [reversedPlaquetteQuaternionWord, q0, q1, q2, q3]
                using hassocInner)))))

private theorem fundamentalMatrixEqv_refl
    (matrix : FundamentalMatrix) : FundamentalMatrixEqv matrix matrix := by
  intro row column
  exact rationalComplexEqv_refl _

private theorem fundamentalMatrixEqv_symm
    {left right : FundamentalMatrix}
    (h : FundamentalMatrixEqv left right) :
    FundamentalMatrixEqv right left := by
  intro row column
  exact rationalComplexEqv_symm (h row column)

private theorem fundamentalMatrixEqv_trans
    {first second third : FundamentalMatrix}
    (hfirst : FundamentalMatrixEqv first second)
    (hsecond : FundamentalMatrixEqv second third) :
    FundamentalMatrixEqv first third := by
  intro row column
  exact rationalComplexEqv_trans
    (hfirst row column) (hsecond row column)

private theorem fundamentalMatrixMul_congr
    {left left' right right' : FundamentalMatrix}
    (hleft : FundamentalMatrixEqv left left')
    (hright : FundamentalMatrixEqv right right') :
    FundamentalMatrixEqv
      (fundamentalMatrixMul left right)
      (fundamentalMatrixMul left' right') := by
  intro row column
  exact rationalComplexAdd_congr
    (rationalComplexMul_congr
      (hleft row false) (hright false column))
    (rationalComplexMul_congr
      (hleft row true) (hright true column))

private theorem fundamentalMatrixTrace_congr
    {left right : FundamentalMatrix}
    (h : FundamentalMatrixEqv left right) :
    RationalComplexEqv
      (fundamentalMatrixTrace left)
      (fundamentalMatrixTrace right) := by
  unfold fundamentalMatrixTrace
  exact rationalComplexAdd_congr (h false false) (h true true)

private theorem rightAssociatedMatrixWord_eqv
    (first second third fourth : FundamentalMatrix)
    (qfirst qsecond qthird qfourth : RationalQuaternion)
    (hfirst : FundamentalMatrixEqv first
      (fundamentalMatrixValue qfirst))
    (hsecond : FundamentalMatrixEqv second
      (fundamentalMatrixValue qsecond))
    (hthird : FundamentalMatrixEqv third
      (fundamentalMatrixValue qthird))
    (hfourth : FundamentalMatrixEqv fourth
      (fundamentalMatrixValue qfourth)) :
    FundamentalMatrixEqv
      (fundamentalMatrixMul first
        (fundamentalMatrixMul second
          (fundamentalMatrixMul third fourth)))
      (fundamentalMatrixValue
        (RationalQuaternion.mul qfirst
          (RationalQuaternion.mul qsecond
            (RationalQuaternion.mul qthird qfourth)))) := by
  have hinputs : FundamentalMatrixEqv
      (fundamentalMatrixMul first
        (fundamentalMatrixMul second
          (fundamentalMatrixMul third fourth)))
      (fundamentalMatrixMul (fundamentalMatrixValue qfirst)
        (fundamentalMatrixMul (fundamentalMatrixValue qsecond)
          (fundamentalMatrixMul
            (fundamentalMatrixValue qthird)
            (fundamentalMatrixValue qfourth)))) :=
    fundamentalMatrixMul_congr hfirst
      (fundamentalMatrixMul_congr hsecond
        (fundamentalMatrixMul_congr hthird hfourth))
  have hthirdFourth := fundamentalMatrixEqv_symm
    (fundamentalMatrixValue_mul qthird qfourth)
  have hsecondTail := fundamentalMatrixEqv_symm
    (fundamentalMatrixValue_mul qsecond
      (RationalQuaternion.mul qthird qfourth))
  have hfirstTail := fundamentalMatrixEqv_symm
    (fundamentalMatrixValue_mul qfirst
      (RationalQuaternion.mul qsecond
        (RationalQuaternion.mul qthird qfourth)))
  exact fundamentalMatrixEqv_trans hinputs
    (fundamentalMatrixEqv_trans
      (fundamentalMatrixMul_congr (fundamentalMatrixEqv_refl _)
        (fundamentalMatrixMul_congr (fundamentalMatrixEqv_refl _)
          hthirdFourth))
      (fundamentalMatrixEqv_trans
        (fundamentalMatrixMul_congr (fundamentalMatrixEqv_refl _)
          hsecondTail)
        hfirstTail))

private theorem evaluatedReverseFundamentalLinkMatrix_eq_value_conj
    (rho : Nat → Q') (block : Nat) :
    FundamentalMatrixEqv
      (evaluatedReverseFundamentalLinkMatrix rho block)
      (fundamentalMatrixValue
        (RationalQuaternion.conj
          (evaluatedFundamentalLinkQuaternion rho block))) := by
  intro row column
  exact eval_reverseFundamentalCoefficient_as_conjugate
    rho block row column

theorem standardPlaquetteTraceMatrix_eq_word
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) :
    FundamentalMatrixEqv
      (standardPlaquetteTraceMatrix rho block0 block1 block2 block3)
      (fundamentalMatrixValue
        (standardPlaquetteQuaternionWord
          rho block0 block1 block2 block3)) := by
  exact rightAssociatedMatrixWord_eqv
    (evaluatedFundamentalMatrix rho (fundamentalLinkQuaternion block0))
    (evaluatedFundamentalMatrix rho (fundamentalLinkQuaternion block3))
    (evaluatedReverseFundamentalLinkMatrix rho block2)
    (evaluatedReverseFundamentalLinkMatrix rho block1)
    (evaluatedFundamentalLinkQuaternion rho block0)
    (evaluatedFundamentalLinkQuaternion rho block3)
    (RationalQuaternion.conj
      (evaluatedFundamentalLinkQuaternion rho block2))
    (RationalQuaternion.conj
      (evaluatedFundamentalLinkQuaternion rho block1))
    (evaluatedFundamentalMatrix_eq_value rho
      (fundamentalLinkQuaternion block0))
    (evaluatedFundamentalMatrix_eq_value rho
      (fundamentalLinkQuaternion block3))
    (evaluatedReverseFundamentalLinkMatrix_eq_value_conj rho block2)
    (evaluatedReverseFundamentalLinkMatrix_eq_value_conj rho block1)

theorem reversedPlaquetteTraceMatrix_eq_word
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) :
    FundamentalMatrixEqv
      (reversedPlaquetteTraceMatrix rho block0 block1 block2 block3)
      (fundamentalMatrixValue
        (reversedPlaquetteQuaternionWord
          rho block0 block1 block2 block3)) := by
  exact rightAssociatedMatrixWord_eqv
    (evaluatedFundamentalMatrix rho (fundamentalLinkQuaternion block1))
    (evaluatedFundamentalMatrix rho (fundamentalLinkQuaternion block2))
    (evaluatedReverseFundamentalLinkMatrix rho block3)
    (evaluatedReverseFundamentalLinkMatrix rho block0)
    (evaluatedFundamentalLinkQuaternion rho block1)
    (evaluatedFundamentalLinkQuaternion rho block2)
    (RationalQuaternion.conj
      (evaluatedFundamentalLinkQuaternion rho block3))
    (RationalQuaternion.conj
      (evaluatedFundamentalLinkQuaternion rho block0))
    (evaluatedFundamentalMatrix_eq_value rho
      (fundamentalLinkQuaternion block1))
    (evaluatedFundamentalMatrix_eq_value rho
      (fundamentalLinkQuaternion block2))
    (evaluatedReverseFundamentalLinkMatrix_eq_value_conj rho block3)
    (evaluatedReverseFundamentalLinkMatrix_eq_value_conj rho block0)

/-- The two orientation choices give the same evaluated fundamental trace.
This is whole-word conjugation invariance and therefore holds for arbitrary
rational environments; interpreting conjugation as inversion is a separate
unit-norm statement. -/
theorem eval_reversedPlaquetteTraceExpansion_eq_standard
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (reversedPlaquetteTraceExpansion block0 block1 block2 block3))
      (evalComplexRatPoly rho
        (standardPlaquetteTraceExpansion block0 block1 block2 block3)) := by
  have hword :=
    conj_standardPlaquetteQuaternionWord_eqv_reversed
      rho block0 block1 block2 block3
  have hreverseToConj : FundamentalMatrixEqv
      (fundamentalMatrixValue
        (reversedPlaquetteQuaternionWord
          rho block0 block1 block2 block3))
      (fundamentalMatrixValue
        (RationalQuaternion.conj
          (standardPlaquetteQuaternionWord
            rho block0 block1 block2 block3))) :=
    fundamentalMatrixValue_congr (rationalQuaternionEqv_symm hword)
  exact rationalComplexEqv_trans
    (eval_reversedPlaquetteTraceExpansion_eq_matrixTrace
      rho block0 block1 block2 block3)
    (rationalComplexEqv_trans
      (fundamentalMatrixTrace_congr
        (reversedPlaquetteTraceMatrix_eq_word
          rho block0 block1 block2 block3))
      (rationalComplexEqv_trans
        (fundamentalMatrixTrace_congr hreverseToConj)
        (rationalComplexEqv_trans
          (fundamentalMatrixTrace_conj
            (standardPlaquetteQuaternionWord
              rho block0 block1 block2 block3))
          (rationalComplexEqv_symm
            (rationalComplexEqv_trans
              (eval_standardPlaquetteTraceExpansion_eq_matrixTrace
                rho block0 block1 block2 block3)
              (fundamentalMatrixTrace_congr
                (standardPlaquetteTraceMatrix_eq_word
                  rho block0 block1 block2 block3)))))))

/-- The standard symbolic coefficient sum evaluates to the rank-one
Chebyshev trace polynomial of the exact oriented quaternion word.  On the
unit-quaternion locus this is the fundamental `SU(2)` character. -/
theorem eval_standardPlaquetteTraceExpansion_eq_chebOne
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (standardPlaquetteTraceExpansion block0 block1 block2 block3))
      (YMGap.Continuum.Cheb.U 1
        (standardPlaquetteQuaternionWord
          rho block0 block1 block2 block3).r, 0) := by
  exact rationalComplexEqv_trans
    (eval_standardPlaquetteTraceExpansion_eq_matrixTrace
      rho block0 block1 block2 block3)
    (rationalComplexEqv_trans
      (fundamentalMatrixTrace_congr
        (standardPlaquetteTraceMatrix_eq_word
          rho block0 block1 block2 block3))
      (fundamentalMatrixTrace_value
        (standardPlaquetteQuaternionWord
          rho block0 block1 block2 block3)))

/-- The reversed symbolic coefficient sum evaluates to the rank-one
Chebyshev trace polynomial of the orientation-reversed conjugate word.  On
the unit-quaternion locus this is the character of the inverse word. -/
theorem eval_reversedPlaquetteTraceExpansion_eq_chebOne
    (rho : Nat → Q')
    (block0 block1 block2 block3 : Nat) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (reversedPlaquetteTraceExpansion block0 block1 block2 block3))
      (YMGap.Continuum.Cheb.U 1
        (reversedPlaquetteQuaternionWord
          rho block0 block1 block2 block3).r, 0) := by
  exact rationalComplexEqv_trans
    (eval_reversedPlaquetteTraceExpansion_eq_matrixTrace
      rho block0 block1 block2 block3)
    (rationalComplexEqv_trans
      (fundamentalMatrixTrace_congr
        (reversedPlaquetteTraceMatrix_eq_word
          rho block0 block1 block2 block3))
      (fundamentalMatrixTrace_value
        (reversedPlaquetteQuaternionWord
          rho block0 block1 block2 block3)))

#print axioms evalComplexRatPoly_fourBoolSum
#print axioms rationalComplexFourBoolSum_congr
#print axioms rationalComplexMulFourLeft_eqv_right
#print axioms evalComplexRatPoly_mulFourLeft
#print axioms rationalComplexFourCycleSum_eq_matrixTrace
#print axioms eval_standardPlaquetteTraceExpansion_eq_matrixTrace
#print axioms eval_reversedPlaquetteTraceExpansion_eq_matrixTrace
#print axioms standardPlaquetteTraceMatrix_eq_word
#print axioms reversedPlaquetteTraceMatrix_eq_word
#print axioms conj_standardPlaquetteQuaternionWord_eqv_reversed
#print axioms eval_reversedPlaquetteTraceExpansion_eq_standard
#print axioms eval_standardPlaquetteTraceExpansion_eq_chebOne
#print axioms eval_reversedPlaquetteTraceExpansion_eq_chebOne

end YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
