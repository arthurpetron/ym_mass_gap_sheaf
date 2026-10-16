/-
# Dot-product expansion of the exact Cayley quartic

The cleared Cayley coefficient H4 contains one cross-product contraction.
This leaf proves the three-dimensional Lagrange identity for that contraction
and rewrites the complete H4 as a fixed list of fifteen weighted products of
ordinary dot products: twelve dot-times-norm terms and three four-slot terms.

The shared term list is intended for literal finite-Gaussian averaging.  This
is an exact rational polynomial identity only; it supplies no measure
comparison, denominator bound, asymptotic remainder or physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyPolynomial

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuarticDotIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
open YMGap.RepTheory.RationalQuaternionSphereNets

local infix:50 " ≈ " => Q'.eqv

/-- One weighted product `weight * dot(slot i,slot j) * dot(slot k,slot l)`
in the exact dot expansion of H4. -/
structure H4DotTerm where
  weight : Int
  firstLeft : Nat
  firstRight : Nat
  secondLeft : Nat
  secondRight : Nat

/-- The exact fifteen signed dot products in H4, with slots
`0=a, 1=b, 2=c, 3=d`. -/
def h4DotTerms : List H4DotTerm :=
  [⟨-8, 0, 1, 2, 2⟩,
   ⟨-8, 0, 1, 3, 3⟩,
   ⟨-8, 0, 2, 1, 1⟩,
   ⟨-8, 0, 2, 3, 3⟩,
   ⟨-8, 0, 3, 1, 1⟩,
   ⟨-8, 0, 3, 2, 2⟩,
   ⟨-8, 1, 2, 0, 0⟩,
   ⟨-8, 1, 2, 3, 3⟩,
   ⟨-8, 1, 3, 0, 0⟩,
   ⟨-8, 1, 3, 2, 2⟩,
   ⟨-8, 2, 3, 0, 0⟩,
   ⟨-8, 2, 3, 1, 1⟩,
   ⟨-32, 0, 1, 2, 3⟩,
   ⟨32, 0, 2, 1, 3⟩,
   ⟨-32, 0, 3, 1, 2⟩]

/-- Four directed rational slots in the order used by H4. -/
def cayleySlot (a b c d : Triple) : Nat → Triple
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

def h4DotTermValue (slots : Nat → Triple) (term : H4DotTerm) : Q' :=
  Q'.ofInt term.weight *
    (dot3 (slots term.firstLeft) (slots term.firstRight) *
      dot3 (slots term.secondLeft) (slots term.secondRight))

private def qTermSum : List Q' → Q'
  | [] => 0
  | value :: values => value + qTermSum values

/-- Fixed signed dot-product presentation of the exact quartic coefficient. -/
def h4DotTermSum (slots : Nat → Triple) : Q' :=
  qTermSum (h4DotTerms.map (h4DotTermValue slots))

private abbrev PE := PolyExpr

local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private structure VE where
  x : PE
  y : PE
  z : PE

private def ev (offset : Nat) : VE :=
  ⟨.var offset, .var (offset+1), .var (offset+2)⟩

private def edot (a b : VE) : PE :=
  (a.x*b.x+a.y*b.y)+a.z*b.z

private def ecross (a b : VE) : VE :=
  ⟨a.y*b.z + -(a.z*b.y),
    a.z*b.x + -(a.x*b.z),
    a.x*b.y + -(a.y*b.x)⟩

private def enorm (a : VE) : PE :=
  (a.x*a.x+a.y*a.y)+a.z*a.z

private def eH4 (a b c d : VE) : PE :=
  -(8*((edot a b*(enorm c+enorm d)+edot a c*(enorm b+enorm d))+
    edot a d*(enorm b+enorm c)+
    ((edot b c*(enorm a+enorm d)+edot b d*(enorm a+enorm c))+
      edot c d*(enorm a+enorm b)))) +
  -(32*(edot a b*edot c d + -(edot (ecross a b) (ecross c d))))

private def exprSlot (a b c d : VE) : Nat → VE
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

private def eH4DotTermValue (slots : Nat → VE) (term : H4DotTerm) : PE :=
  (PolyExpr.const term.weight) *
    (edot (slots term.firstLeft) (slots term.firstRight) *
      edot (slots term.secondLeft) (slots term.secondRight))

private def eListSum : List PE → PE
  | [] => .const 0
  | value :: values => .add value (eListSum values)

private theorem cross_dot_cross_normal :
    normalize (edot (ecross (ev 0) (ev 3)) (ecross (ev 6) (ev 9))) =
      normalize
        (edot (ev 0) (ev 6) * edot (ev 3) (ev 9) +
          -(edot (ev 0) (ev 9) * edot (ev 3) (ev 6))) := by
  decide

private theorem H4_dot_terms_normal :
    normalize (eH4 (ev 0) (ev 3) (ev 6) (ev 9)) =
      normalize (eListSum
        (h4DotTerms.map
          (eH4DotTermValue (exprSlot (ev 0) (ev 3) (ev 6) (ev 9))))) := by
  decide

private def coordinateEnvironment (a b c d : Triple) : Nat → Q'
  | 0 => a.x
  | 1 => a.y
  | 2 => a.z
  | 3 => b.x
  | 4 => b.y
  | 5 => b.z
  | 6 => c.x
  | 7 => c.y
  | 8 => c.z
  | 9 => d.x
  | 10 => d.y
  | _ => d.z

/-- Three-dimensional Lagrange identity in the exact rational triple algebra. -/
theorem dot_cross_cross (a b c d : Triple) :
    dot3 (cross3 a b) (cross3 c d) ≈
      dot3 a c * dot3 b d + -(dot3 a d * dot3 b c) :=
  by
    change eval (coordinateEnvironment a b c d)
        (edot (ecross (ev 0) (ev 3)) (ecross (ev 6) (ev 9))) ≈
      eval (coordinateEnvironment a b c d)
        (edot (ev 0) (ev 6) * edot (ev 3) (ev 9) +
          -(edot (ev 0) (ev 9) * edot (ev 3) (ev 6)))
    exact poly_identity_of_normal_eq _ _ cross_dot_cross_normal
      (coordinateEnvironment a b c d)

/-- The existing exact Cayley H4 is precisely the shared fifteen-term signed
dot expansion used by the finite-Gaussian consumer. -/
theorem H4_eq_dotTermSum (a b c d : Triple) :
    H4 a b c d ≈ h4DotTermSum (cayleySlot a b c d) :=
  by
    change eval (coordinateEnvironment a b c d)
        (eH4 (ev 0) (ev 3) (ev 6) (ev 9)) ≈
      eval (coordinateEnvironment a b c d)
        (eListSum
          (h4DotTerms.map
            (eH4DotTermValue (exprSlot (ev 0) (ev 3) (ev 6) (ev 9)))))
    exact poly_identity_of_normal_eq _ _ H4_dot_terms_normal
      (coordinateEnvironment a b c d)

end YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuarticDotIdentity

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuarticDotIdentity.dot_cross_cross
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuarticDotIdentity.H4_eq_dotTermSum
