/-
# Core-B second-offset exact quotient factor

This small module isolates the reflective algebra for `(s,r) = (0,2)` from
the subsequent order proof.  The split keeps each kernel artifact modest:
the raw degree-92 quotient is normalized only to prove its common-monomial
factorization, while the subsequent order proof works solely with the
degree-20 reduced factor and its six adverse monomials.
-/

import YMGap.Continuum.CoreBResidualOffsetOne

namespace YMGap.Continuum.CoreBResidualOffsetTwoFactor

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

open YMGap.Continuum.CoreBResidualSimplex

def monoTerm (c : Int) (ew eh : Nat) : RingNormaliser.PolyExpr :=
  .mul (.const c) (.mul (.pow (.var 0) ew) (.pow (.var 1) eh))

def sumTerms : List (Int × Nat × Nat) → RingNormaliser.PolyExpr
  | [] => .const 0
  | (c, ew, eh) :: ts => .add (monoTerm c ew eh) (sumTerms ts)

/-- The manifestly nonnegative part of the reduced quotient, excluding its
constant reserve. -/
def r02TailExpr : RingNormaliser.PolyExpr :=
  sumTerms
    [ (1920, 12, 6), (1536, 12, 0),
      (1920, 10, 8), (36, 10, 2),
      (1920, 8, 10), (2880, 8, 6),
      (36, 8, 4), (2304, 8, 0), (1920, 6, 12),
      (2880, 6, 8), (36, 6, 6),
      (2304, 6, 2), (36, 4, 8), (2304, 4, 4),
      (2560, 4, 0), (36, 2, 10),
      (2304, 2, 6), (2560, 2, 2),
      (1536, 0, 12), (2304, 0, 8), (2560, 0, 4) ]

/-- The six adverse monomials in the reduced quotient.  Their coefficient
mass is `13500`; the physical cap pays the whole block uniformly. -/
def r02AdverseExpr : RingNormaliser.PolyExpr :=
  sumTerms
    [ (900, 10, 10), (1000, 10, 6), (1000, 8, 8),
      (1000, 6, 10), (4800, 4, 2), (4800, 2, 4) ]

/-- The 28-term quotient left after extracting `w^36 h^36`, grouped as a
constant reserve plus a nonnegative tail minus six adverse monomials. -/
def r02ReducedExpr : RingNormaliser.PolyExpr :=
  .add (.add (.const 3840) r02TailExpr) (.neg r02AdverseExpr)

/-- The common-monomial quotient really reduces to total degree at most 20.
This is the small structural input required by the reusable simplex consumer. -/
theorem reducedDegreeBound02 :
    TwoVariableDegreeBound 20 (RingNormaliser.normalize r02ReducedExpr) := by
  decide

/-- The common monomial in the second-offset square quotient. -/
def r02CommonExpr : RingNormaliser.PolyExpr :=
  .mul (.pow (.var 0) 36) (.pow (.var 1) 36)

/-- Exact factorization of the computed antisymmetric square quotient. -/
theorem quotientNormal02 :
    RingNormaliser.normalize (residualQuotientExpr 0 2) =
      RingNormaliser.normalize (.mul r02CommonExpr r02ReducedExpr) := by
  decide

/-- Exact extraction of the universal square difference `w^2-h^2`. -/
theorem factorNormal02 :
    RingNormaliser.normalize (residualExpr 0 2) =
      RingNormaliser.normalize
        (.mul
          (.add (.pow (.var 0) 2) (.neg (.pow (.var 1) 2)))
          (residualQuotientExpr 0 2)) := by
  decide

#print axioms quotientNormal02
#print axioms factorNormal02
#print axioms reducedDegreeBound02

end YMGap.Continuum.CoreBResidualOffsetTwoFactor
