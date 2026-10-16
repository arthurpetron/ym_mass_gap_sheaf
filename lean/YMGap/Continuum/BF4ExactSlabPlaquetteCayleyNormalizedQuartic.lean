/-
# Exact denominator-normalized Cayley quartic coefficient

For the exact cleared Cayley numerator N and positive denominator D, the
degree-four coefficient of N/D is not H4 alone.  This leaf defines

  F4 = H4 - (sum of the four directed-vector norms) * H2

and proves an exact division-free identity

  N = D * (e^2 H2 + e^3 H3 + e^4 F4) + e^5 * R(e),

with every higher coefficient of the explicit finite polynomial R retained.
Thus F4 is identified without analytic division, a big-O premise or a
pointwise comparison with H2.  No measure, expectation, uniform remainder
bound or physical mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyPolynomial

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCayleyNormalizedQuartic

set_option autoImplicit false
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
open YMGap.RepTheory.RationalQuaternionSphereNets

local infix:50 " ≈ " => Q'.eqv

def cayleyNormSum (a b c d : Triple) : Q' :=
  (norm3 a + norm3 b) + (norm3 c + norm3 d)

def cayleyNormPairSum (a b c d : Triple) : Q' :=
  ((norm3 a*norm3 b + norm3 a*norm3 c) + norm3 a*norm3 d) +
    ((norm3 b*norm3 c + norm3 b*norm3 d) + norm3 c*norm3 d)

def cayleyNormTripleSum (a b c d : Triple) : Q' :=
  (norm3 a*norm3 b*norm3 c + norm3 a*norm3 b*norm3 d) +
    (norm3 a*norm3 c*norm3 d + norm3 b*norm3 c*norm3 d)

def cayleyNormFourProduct (a b c d : Triple) : Q' :=
  ((norm3 a*norm3 b)*norm3 c)*norm3 d

/-- Exact degree-four coefficient after denominator normalization. -/
def normalizedCayleyH4 (a b c d : Triple) : Q' :=
  H4 a b c d + -(cayleyNormSum a b c d * H2 a b c d)

/-- Every order-five-through-twelve term left by exact division-free
quartic truncation. -/
def normalizedQuarticRemainder (e : Q') (a b c d : Triple) : Q' :=
  (H5 a b c d + -(cayleyNormSum a b c d * H3 a b c d)) +
  e *
    ((H6 a b c d +
        -(cayleyNormSum a b c d * normalizedCayleyH4 a b c d)) +
      -(cayleyNormPairSum a b c d * H2 a b c d)) +
  -((e*e) * (cayleyNormPairSum a b c d * H3 a b c d)) +
  -(((e*e)*e) *
    (cayleyNormPairSum a b c d * normalizedCayleyH4 a b c d +
      cayleyNormTripleSum a b c d * H2 a b c d)) +
  -(((e*e)*(e*e)) *
    (cayleyNormTripleSum a b c d * H3 a b c d)) +
  -((((e*e)*(e*e))*e) *
    (cayleyNormTripleSum a b c d * normalizedCayleyH4 a b c d +
      cayleyNormFourProduct a b c d * H2 a b c d)) +
  -((((e*e)*(e*e))*(e*e)) *
    (cayleyNormFourProduct a b c d * H3 a b c d)) +
  -(((((e*e)*(e*e))*(e*e))*e) *
    (cayleyNormFourProduct a b c d * normalizedCayleyH4 a b c d))

private abbrev PE := PolyExpr

local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private def epow2 (e : PE) : PE := e*e
private def epow3 (e : PE) : PE := (e*e)*e
private def epow4 (e : PE) : PE := (e*e)*(e*e)
private def epow5 (e : PE) : PE := ((e*e)*(e*e))*e
private def epow6 (e : PE) : PE := ((e*e)*(e*e))*(e*e)
private def epow7 (e : PE) : PE := (((e*e)*(e*e))*(e*e))*e

private def eNormSum (ra rb rc rd : PE) : PE :=
  (ra+rb)+(rc+rd)

private def eNormPairSum (ra rb rc rd : PE) : PE :=
  ((ra*rb+ra*rc)+ra*rd)+((rb*rc+rb*rd)+rc*rd)

private def eNormTripleSum (ra rb rc rd : PE) : PE :=
  (ra*rb*rc+ra*rb*rd)+(ra*rc*rd+rb*rc*rd)

private def eNormFourProduct (ra rb rc rd : PE) : PE :=
  ((ra*rb)*rc)*rd

private def eNormalizedH4 (ra rb rc rd h2 h4 : PE) : PE :=
  h4 + -(eNormSum ra rb rc rd*h2)

private def eDenominator (e ra rb rc rd : PE) : PE :=
  (((1+epow2 e*ra)*(1+epow2 e*rb))*(1+epow2 e*rc))*(1+epow2 e*rd)

private def eNumerator (e h2 h3 h4 h5 h6 : PE) : PE :=
  (((epow2 e*h2+epow3 e*h3)+epow4 e*h4)+epow5 e*h5)+epow6 e*h6

private def eTruncation (e ra rb rc rd h2 h3 h4 : PE) : PE :=
  (epow2 e*h2+epow3 e*h3)+
    epow4 e*eNormalizedH4 ra rb rc rd h2 h4

private def eRemainder (e ra rb rc rd h2 h3 h4 h5 h6 : PE) : PE :=
  (h5 + -(eNormSum ra rb rc rd*h3)) +
  e*((h6 + -(eNormSum ra rb rc rd*
      eNormalizedH4 ra rb rc rd h2 h4)) +
    -(eNormPairSum ra rb rc rd*h2)) +
  -(epow2 e*(eNormPairSum ra rb rc rd*h3)) +
  -(epow3 e*(eNormPairSum ra rb rc rd*
      eNormalizedH4 ra rb rc rd h2 h4 +
    eNormTripleSum ra rb rc rd*h2)) +
  -(epow4 e*(eNormTripleSum ra rb rc rd*h3)) +
  -(epow5 e*(eNormTripleSum ra rb rc rd*
      eNormalizedH4 ra rb rc rd h2 h4 +
    eNormFourProduct ra rb rc rd*h2)) +
  -(epow6 e*(eNormFourProduct ra rb rc rd*h3)) +
  -(epow7 e*(eNormFourProduct ra rb rc rd*
    eNormalizedH4 ra rb rc rd h2 h4))

private theorem normalized_quartic_normal :
    normalize (eNumerator (.var 0) (.var 5) (.var 6) (.var 7) (.var 8) (.var 9)) =
      normalize
        (eDenominator (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) *
            eTruncation (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
              (.var 5) (.var 6) (.var 7) +
          epow5 (.var 0) *
            eRemainder (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
              (.var 5) (.var 6) (.var 7) (.var 8) (.var 9)) := by
  decide

private def coefficientEnvironment (e : Q') (a b c d : Triple) : Nat → Q'
  | 0 => e
  | 1 => norm3 a
  | 2 => norm3 b
  | 3 => norm3 c
  | 4 => norm3 d
  | 5 => H2 a b c d
  | 6 => H3 a b c d
  | 7 => H4 a b c d
  | 8 => H5 a b c d
  | _ => H6 a b c d

/-- Exact division-free identification of the denominator-normalized quartic
coefficient, with an explicit polynomial remainder beginning at order five. -/
theorem cayleyDeficit_normalized_quartic
    (e : Q') (a b c d : Triple) :
    cayleyDeficit e a b c d ≈
      cayleyDenominator e a b c d *
        (((e*e)*H2 a b c d + ((e*e)*e)*H3 a b c d) +
          ((e*e)*(e*e))*normalizedCayleyH4 a b c d) +
      (((e*e)*(e*e))*e) *
        normalizedQuarticRemainder e a b c d := by
  change eval (coefficientEnvironment e a b c d)
      (eNumerator (.var 0) (.var 5) (.var 6) (.var 7) (.var 8) (.var 9)) ≈
    eval (coefficientEnvironment e a b c d)
      (eDenominator (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) *
          eTruncation (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
            (.var 5) (.var 6) (.var 7) +
        epow5 (.var 0) *
          eRemainder (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
            (.var 5) (.var 6) (.var 7) (.var 8) (.var 9))
  exact poly_identity_of_normal_eq _ _ normalized_quartic_normal
    (coefficientEnvironment e a b c d)

end YMGap.Continuum.BF4ExactSlabPlaquetteCayleyNormalizedQuartic

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyNormalizedQuartic.cayleyDeficit_normalized_quartic
