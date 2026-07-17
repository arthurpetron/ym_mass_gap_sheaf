/-
# Core-B row-one cell `(1,1)` — exact quotient factor

Reflective algebra for the second cell of the shifted row `s = 1`, split from
the order proof exactly as in `CoreBResidualOffsetTwoFactor`: the raw
degree-92 quotient is normalized only to prove its common-monomial
factorization `(wh)^32 * reduced`, while the order proof works with the
degree-28 reduced factor (constant reserve `11664`, forty-four positive
monomials, thirteen adverse monomials of total mass `64188`).
-/

import YMGap.Continuum.CoreBResidualRowOneCellZero
import YMGap.Continuum.CoreBResidualOffsetTwoFactor

namespace YMGap.Continuum.CoreBResidualRowOneCellOneFactor

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.CoreBResidualOffsetTwoFactor (monoTerm sumTerms)

/-- The manifestly nonnegative part of the reduced `(1,1)` quotient,
excluding its constant reserve. -/
def r11TailExpr : RingNormaliser.PolyExpr :=
  sumTerms
    [ (2160, 16, 8), (3456, 16, 2), (1944, 16, 0),
      (2160, 14, 10), (3456, 14, 4),
      (2160, 12, 12), (2880, 12, 10), (3780, 12, 8),
      (3456, 12, 6), (648, 12, 4), (10368, 12, 2), (5832, 12, 0),
      (2160, 10, 14), (2880, 10, 12), (3780, 10, 10),
      (3456, 10, 8), (648, 10, 6), (10368, 10, 4), (5832, 10, 2),
      (2160, 8, 16), (3780, 8, 12), (3456, 8, 10),
      (4248, 8, 8), (1728, 8, 6), (5832, 8, 4), (3240, 8, 0),
      (3456, 6, 12), (648, 6, 10), (1728, 6, 8),
      (3456, 4, 14), (648, 4, 12), (10368, 4, 10),
      (5832, 4, 8), (24192, 4, 2), (13608, 4, 0),
      (3456, 2, 16), (10368, 2, 12), (5832, 2, 10),
      (24192, 2, 4), (4392, 2, 2),
      (1944, 0, 16), (5832, 0, 12), (3240, 0, 8), (13608, 0, 4) ]

/-- The thirteen adverse monomials in the reduced quotient.  Their total
coefficient mass is `64188`; every monomial carries `w^2 h^2`, so the
physical cap pays the whole block from the constant reserve at once. -/
def r11AdverseExpr : RingNormaliser.PolyExpr :=
  sumTerms
    [ (9720, 2, 6), (5760, 2, 8), (1656, 2, 14),
      (2808, 4, 4), (5760, 4, 6),
      (9720, 6, 2), (5760, 6, 4), (9288, 6, 6), (2700, 6, 14),
      (5760, 8, 2), (1656, 14, 2), (2700, 14, 6), (900, 14, 14) ]

/-- The 58-term quotient after extracting `(wh)^32`, grouped as a constant
reserve plus a nonnegative tail minus thirteen adverse monomials. -/
def r11ReducedExpr : RingNormaliser.PolyExpr :=
  .add (.add (.const 11664) r11TailExpr) (.neg r11AdverseExpr)

/-- The common monomial in the `(1,1)` square quotient. -/
def r11CommonExpr : RingNormaliser.PolyExpr :=
  .mul (.pow (.var 0) 32) (.pow (.var 1) 32)

/-- Exact factorization of the computed antisymmetric square quotient. -/
theorem quotientNormal11 :
    RingNormaliser.normalize (residualQuotientExpr 1 1) =
      RingNormaliser.normalize (.mul r11CommonExpr r11ReducedExpr) := by
  decide

/-- Exact extraction of the universal square difference `w^2-h^2`. -/
theorem factorNormal11 :
    RingNormaliser.normalize (residualExpr 1 1) =
      RingNormaliser.normalize
        (.mul
          (.add (.pow (.var 0) 2) (.neg (.pow (.var 1) 2)))
          (residualQuotientExpr 1 1)) := by
  decide

#print axioms quotientNormal11
#print axioms factorNormal11

end YMGap.Continuum.CoreBResidualRowOneCellOneFactor
