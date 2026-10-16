/-
# Exact Cayley plaquette polynomial

This lightweight module contains only the directed-vector algebra and the exact
degree-two-through-six Cayley polynomial.  The separate source-matching module
identifies this polynomial with the original corrected-slab plaquette scalar.
-/

import YMGap.RepTheory.RationalQuaternionSphereNets

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternionSphereNets

def add3 (a b : Triple) : Triple := ⟨a.x+b.x,a.y+b.y,a.z+b.z⟩
def neg3 (a : Triple) : Triple := ⟨-a.x,-a.y,-a.z⟩
def scale3 (e : Q') (a : Triple) : Triple := ⟨e*a.x,e*a.y,e*a.z⟩
def dot3 (a b : Triple) : Q' := (a.x*b.x+a.y*b.y)+a.z*b.z
def cross3 (a b : Triple) : Triple :=
  ⟨a.y*b.z + -(a.z*b.y), a.z*b.x + -(a.x*b.z), a.x*b.y + -(a.y*b.x)⟩
def det3 (a b c : Triple) : Q' := dot3 (cross3 a b) c

def pairCrosses (a b c d : Triple) : Triple :=
  add3 (add3 (add3 (cross3 a b) (cross3 a c)) (cross3 a d))
    (add3 (add3 (cross3 b c) (cross3 b d)) (cross3 c d))

/-- Quadratic coefficient for the four DIRECTED chart vectors. -/
def H2 (a b c d : Triple) : Q' := 4*norm3 (add3 (add3 (add3 a b) c) d)

/-- Cubic coefficient; equivalently 16 times sum-vectors dot sum-pair-crosses. -/
def H3 (a b c d : Triple) : Q' :=
  16*((det3 a b c+det3 a b d)+(det3 a c d+det3 b c d))

/-- Cleared quartic coefficient, not the normalized quartic coefficient. -/
def H4 (a b c d : Triple) : Q' :=
  -(8*((dot3 a b*(norm3 c+norm3 d)+dot3 a c*(norm3 b+norm3 d))+
    dot3 a d*(norm3 b+norm3 c)+
    ((dot3 b c*(norm3 a+norm3 d)+dot3 b d*(norm3 a+norm3 c))+
      dot3 c d*(norm3 a+norm3 b)))) +
  -(32*(dot3 a b*dot3 c d + -(dot3 (cross3 a b) (cross3 c d))))

def H5 (a b c d : Triple) : Q' :=
  -(16*((det3 a b c*norm3 d+det3 a b d*norm3 c)+
    (det3 a c d*norm3 b+det3 b c d*norm3 a)))

def H6 (a b c d : Triple) : Q' :=
  4*((norm3 a*norm3 b*norm3 c+norm3 a*norm3 b*norm3 d)+
    (norm3 a*norm3 c*norm3 d+norm3 b*norm3 c*norm3 d)) +
  8*((dot3 a b*(norm3 c*norm3 d)+dot3 a c*(norm3 b*norm3 d))+
    dot3 a d*(norm3 b*norm3 c)+
    ((dot3 b c*(norm3 a*norm3 d)+dot3 b d*(norm3 a*norm3 c))+
      dot3 c d*(norm3 a*norm3 b)))

def factor (e : Q') (a : Triple) : Q' := 1+(e*e)*norm3 a

private theorem norm3_nonnegative (a : Triple) : (0 : Q') ≤ norm3 a :=
  Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (SumOfSquares.q_mul_self_nonneg a.x)
      (SumOfSquares.q_mul_self_nonneg a.y))
    (SumOfSquares.q_mul_self_nonneg a.z)

theorem factor_positive (e : Q') (a : Triple) : (0 : Q') < factor e a := by
  exact Q'.pos_add_nonneg (by decide)
    (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg e) (norm3_nonnegative a))

/-- Product of the four positive chart denominators, in directed-vector form. -/
def cayleyDenominator (e : Q') (a b c d : Triple) : Q' :=
  ((factor e a*factor e b)*factor e c)*factor e d

theorem cayleyDenominator_positive (e : Q') (a b c d : Triple) :
    (0 : Q') < cayleyDenominator e a b c d :=
  Q'.mul_pos
    (Q'.mul_pos (Q'.mul_pos (factor_positive e a) (factor_positive e b))
      (factor_positive e c))
    (factor_positive e d)

/-- Exact finite polynomial; its residual consists of the displayed fifth and
sixth degree terms, not a supplied analytic big-O estimate. -/
def cayleyDeficit (e : Q') (a b c d : Triple) : Q' :=
  ((((e*e)*H2 a b c d+((e*e)*e)*H3 a b c d)+
    ((e*e)*(e*e))*H4 a b c d)+
    (((e*e)*(e*e))*e)*H5 a b c d)+
    (((e*e)*(e*e))*(e*e))*H6 a b c d

/-- Exact denominator-normalized local Cayley deficit. -/
def normalizedCayleyDeficit (e : Q') (a b c d : Triple) : Q' :=
  cayleyDeficit e a b c d *
    Q'.recipPos (cayleyDenominator e a b c d)
      (cayleyDenominator_positive e a b c d)

#print axioms factor_positive
#print axioms cayleyDenominator_positive
#print axioms normalizedCayleyDeficit

end YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
