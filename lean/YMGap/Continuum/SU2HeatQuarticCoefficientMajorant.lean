/-
# A scalar second-fusion quartic coefficient majorant

For a bulk spin j with n=j+1, the second fusion of the finite SU(2) heat
prefix factors into w^((j-1)^2-1) times the polynomial `quarticP` below, at
`A=w^(2n-3)` and `V=w^2`.  This file proves the short scalar inequality

  P <= n*(1-A)^4 + 12*(1-V)*(1-A) + 15*(n+2)*(1-V)^2.

The proof is a direct polynomial sum-of-nonnegative-terms identity.  It does
not yet join this scalar fact to the original finite character coefficients:
the low-spin range needs j>=2 and j+2<=K, and the high-spin tail and finite
boundary remain separate obligations.  No physical survival claim follows.
-/

import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CRealMulMono

namespace YMGap.Continuum.SU2HeatQuarticCoefficientMajorant

set_option autoImplicit false
set_option maxRecDepth 2048

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def subE (x y : PE) : PE := .add x (.neg y)

private def pExpr : PE := Id.run do
  let n : PE := .var 0
  let a : PE := .var 1
  let v : PE := .var 2
  return .add
    (.add
      (.add
        (.add (subE n (.const 2))
          (.neg (.mul (.const 4) (.mul (subE n (.const 1)) a))))
        (.mul (.const 6) (.mul n (.mul (.pow a 2) v))))
      (.neg (.mul (.const 4)
        (.mul (.add n (.const 1)) (.mul (.pow a 3) (.pow v 3))))))
    (.mul (.add n (.const 2)) (.mul (.pow a 4) (.pow v 6)))

private def majorantExpr : PE := Id.run do
  let n : PE := .var 0
  let d := subE (.const 1) (.var 1)
  let e := subE (.const 1) (.var 2)
  return .add
    (.add (.mul n (.pow d 4))
      (.mul (.const 12) (.mul e d)))
    (.mul (.const 15) (.mul (.add n (.const 2)) (.pow e 2)))

private def gapExpr : PE := Id.run do
  let n : PE := .var 0
  let a : PE := .var 1
  let v : PE := .var 2
  let d := subE (.const 1) a
  let e := subE (.const 1) v
  let t1 := .mul (.const 2) (.mul (.pow d 3) (.add (.const 1) a))
  let t2 := .mul (.const 6)
    (.mul n (.mul (.pow a 2) (.mul (.pow d 2) e)))
  let t3 := .mul (.const 12)
    (.mul e (.mul (.pow d 2)
      (.add (.add (.const 1) a) (.pow a 2))))
  let t4 := .mul (.const 15)
    (.mul (.add n (.const 2))
      (.mul (.pow e 2) (.mul d
        (.add (.add (.add (.const 1) a) (.pow a 2)) (.pow a 3)))))
  let t5 := .mul (.const 4)
    (.mul (.add n (.const 1))
      (.mul (.pow a 3) (.mul (.pow e 2) (.add (.const 2) v))))
  let t6 := .mul (.add n (.const 2))
    (.mul (.pow a 4) (.mul (.pow e 3)
      (.add
        (.add (.add (.pow v 3) (.mul (.const 3) (.pow v 2)))
          (.mul (.const 6) v))
        (.const 10))))
  return .add (.add (.add (.add (.add t1 t2) t3) t4) t5) t6

private def env (n A V : Q') : Nat → Q'
  | 0 => n
  | 1 => A
  | _ => V

/-- The exact five-term bulk polynomial, in the order
`(n-2)-4(n-1)A+6n A^2 V-4(n+1)A^3 V^3+(n+2)A^4 V^6`. -/
def quarticP (n A V : Q') : Q' := eval (env n A V) pExpr

/-- An unfolded pin for consumers joining the scalar certificate to the
original second-fusion coefficient. -/
theorem quarticP_formula (n A V : Q') :
    quarticP n A V ≈
      ((((n + -(2 : Q')) +
        -(4 * ((n + -(1 : Q')) * A))) +
        6 * (n * (RingNormaliser.qpow A 2 * V))) +
        -(4 * ((n + 1) *
          (RingNormaliser.qpow A 3 * RingNormaliser.qpow V 3)))) +
        (n + 2) * (RingNormaliser.qpow A 4 * RingNormaliser.qpow V 6) := by
  rfl

/-- The short, dimension-weighted defect majorant. -/
def quarticMajorant (n A V : Q') : Q' :=
  eval (env n A V) majorantExpr

/-- The majorant written directly in the nome defects. -/
theorem quarticMajorant_formula (n A V : Q') :
    quarticMajorant n A V ≈
      (n * RingNormaliser.qpow ((1 : Q') + -A) 4 +
        12 * (((1 : Q') + -V) * ((1 : Q') + -A))) +
        15 * ((n + 2) * RingNormaliser.qpow ((1 : Q') + -V) 2) := by
  rfl

/-- Its exact sum-of-nonnegative-terms excess over `quarticP`. -/
private def quarticGap (n A V : Q') : Q' :=
  eval (env n A V) gapExpr

/-- A polynomial identity, not an analytic heat-kernel estimate.  The six
terms of `quarticGap` are displayed in `gapExpr`; the final one uses the exact
factorization
`1-V^6-6(1-V)+15(1-V)^2 = (1-V)^3(V^3+3V^2+6V+10)`. -/
private theorem majorant_identity (n A V : Q') :
    quarticMajorant n A V ≈ quarticP n A V + quarticGap n A V := by
  unfold quarticMajorant quarticP quarticGap
  exact poly_identity_of_normal_eq majorantExpr
    (.add pExpr gapExpr) (by decide) (env n A V)

private theorem qpow_nonnegative {x : Q'} (hx : (0 : Q') ≤ x) :
    ∀ k, (0 : Q') ≤ RingNormaliser.qpow x k
  | 0 => by
      change (0 : Q') ≤ 1
      decide
  | k + 1 =>
      Q'.mul_nonneg _ _ (qpow_nonnegative hx k) hx

/-- Every term in the exact excess is nonnegative on the rational box. -/
private theorem quarticGap_nonnegative {n A V : Q'}
    (hn : (0 : Q') ≤ n)
    (hA0 : (0 : Q') ≤ A) (hA1 : A ≤ (1 : Q'))
    (hV0 : (0 : Q') ≤ V) (hV1 : V ≤ (1 : Q')) :
    (0 : Q') ≤ quarticGap n A V := by
  let d := (1 : Q') + -A
  let e := (1 : Q') + -V
  have hd : (0 : Q') ≤ d := Q'.sub_nonneg_of_le hA1
  have he : (0 : Q') ≤ e := Q'.sub_nonneg_of_le hV1
  have hn1 : (0 : Q') ≤ n + 1 := Q'.zero_le_add _ _ hn (by decide)
  have hn2 : (0 : Q') ≤ n + 2 := Q'.zero_le_add _ _ hn (by decide)
  have ha2 := qpow_nonnegative hA0 2
  have ha3 := qpow_nonnegative hA0 3
  have ha4 := qpow_nonnegative hA0 4
  have hd2 := qpow_nonnegative hd 2
  have hd3 := qpow_nonnegative hd 3
  have he2 := qpow_nonnegative he 2
  have he3 := qpow_nonnegative he 3
  have hv2 := qpow_nonnegative hV0 2
  have hv3 := qpow_nonnegative hV0 3
  have hsumA2 : (0 : Q') ≤ (1 + A) + RingNormaliser.qpow A 2 :=
    Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (by decide) hA0) ha2
  have hsumA3 : (0 : Q') ≤
      ((1 + A) + RingNormaliser.qpow A 2) + RingNormaliser.qpow A 3 :=
    Q'.zero_le_add _ _ hsumA2 ha3
  have hsumV : (0 : Q') ≤
      ((RingNormaliser.qpow V 3 + 3 * RingNormaliser.qpow V 2) + 6 * V) + 10 := by
    apply Q'.zero_le_add
    · apply Q'.zero_le_add
      · exact Q'.zero_le_add _ _ hv3
          (Q'.mul_nonneg _ _ (by decide) hv2)
      · exact Q'.mul_nonneg _ _ (by decide) hV0
    · decide
  have h1 : (0 : Q') ≤
      2 * (RingNormaliser.qpow d 3 * (1 + A)) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hd3 (Q'.zero_le_add _ _ (by decide) hA0))
  have h2 : (0 : Q') ≤
      6 * (n * (RingNormaliser.qpow A 2 * (RingNormaliser.qpow d 2 * e))) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hn
        (Q'.mul_nonneg _ _ ha2 (Q'.mul_nonneg _ _ hd2 he)))
  have h3 : (0 : Q') ≤
      12 * (e * (RingNormaliser.qpow d 2 *
        ((1 + A) + RingNormaliser.qpow A 2))) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ he (Q'.mul_nonneg _ _ hd2 hsumA2))
  have h4 : (0 : Q') ≤
      15 * ((n + 2) * (RingNormaliser.qpow e 2 *
        (d * (((1 + A) + RingNormaliser.qpow A 2) +
          RingNormaliser.qpow A 3)))) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hn2
        (Q'.mul_nonneg _ _ he2 (Q'.mul_nonneg _ _ hd hsumA3)))
  have h5 : (0 : Q') ≤
      4 * ((n + 1) * (RingNormaliser.qpow A 3 *
        (RingNormaliser.qpow e 2 * (2 + V)))) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hn1
        (Q'.mul_nonneg _ _ ha3
          (Q'.mul_nonneg _ _ he2 (Q'.zero_le_add _ _ (by decide) hV0))))
  have h6 : (0 : Q') ≤
      (n + 2) * (RingNormaliser.qpow A 4 *
        (RingNormaliser.qpow e 3 *
          (((RingNormaliser.qpow V 3 + 3 * RingNormaliser.qpow V 2) +
            6 * V) + 10))) :=
    Q'.mul_nonneg _ _ hn2
      (Q'.mul_nonneg _ _ ha4 (Q'.mul_nonneg _ _ he3 hsumV))
  unfold quarticGap gapExpr
  dsimp only [env, eval, subE]
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _ h1 h2) h3) h4) h5) h6

/-- Scalar bulk-polynomial bound on `0<=A,V<=1`.  At this stage there is no
character-channel, cutoff, or interacting source in the statement. -/
theorem quarticP_le_majorant {n A V : Q'}
    (hn : (0 : Q') ≤ n)
    (hA0 : (0 : Q') ≤ A) (hA1 : A ≤ (1 : Q'))
    (hV0 : (0 : Q') ≤ V) (hV1 : V ≤ (1 : Q')) :
    quarticP n A V ≤ quarticMajorant n A V := by
  have hg := quarticGap_nonnegative hn hA0 hA1 hV0 hV1
  have hi := majorant_identity n A V
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (quarticP n A V) (quarticGap n A V) hg)
    (Q'.ge_of_eqv hi)

end YMGap.Continuum.SU2HeatQuarticCoefficientMajorant

#print axioms YMGap.Continuum.SU2HeatQuarticCoefficientMajorant.majorant_identity
#print axioms YMGap.Continuum.SU2HeatQuarticCoefficientMajorant.quarticP_formula
#print axioms YMGap.Continuum.SU2HeatQuarticCoefficientMajorant.quarticMajorant_formula
#print axioms YMGap.Continuum.SU2HeatQuarticCoefficientMajorant.quarticP_le_majorant
