import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

namespace ScratchDenseHighRows

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate
open YMGap.Constructive
open YMGap.Continuum

abbrev PE := RingNormaliser.PolyExpr
abbrev UP := List Int
abbrev BP := List UP

private def uAdd : UP → UP → UP
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: uAdd p q

private def uScale (a : Int) : UP → UP
  | [] => []
  | b :: q => (a * b) :: uScale a q

private def uShift : UP → UP
  | [] => []
  | q => 0 :: q

private def uMul : UP → UP → UP
  | [], _ => []
  | a :: p, q => uAdd (uScale a q) (uShift (uMul p q))

private def uNeg : UP → UP
  | [] => []
  | a :: p => (-a) :: uNeg p

private def bAdd : BP → BP → BP
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => uAdd a b :: bAdd p q

private def bScale (a : UP) : BP → BP
  | [] => []
  | b :: q => uMul a b :: bScale a q

private def bShift : BP → BP
  | [] => []
  | q => [] :: q

private def bMul : BP → BP → BP
  | [], _ => []
  | a :: p, q => bAdd (bScale a q) (bShift (bMul p q))

private def bNeg : BP → BP
  | [] => []
  | a :: p => uNeg a :: bNeg p

private def bPow (p : BP) : Nat → BP
  | 0 => [[1]]
  | n + 1 => bMul (bPow p n) p

/-- Dense bivariate expansion: inner lists are coefficients in variable zero
and the outer list consists of coefficients in variable one. -/
def denseRows : PE → BP
  | .const c => [[c]]
  | .var i => if i = 0 then [[0, 1]] else if i = 1 then [[], [1]] else [[]]
  | .add a b => bAdd (denseRows a) (denseRows b)
  | .mul a b => bMul (denseRows a) (denseRows b)
  | .neg a => bNeg (denseRows a)
  | .pow a n => bPow (denseRows a) n

private def intsNonnegative : UP → Bool
  | [] => true
  | a :: p => decide (0 ≤ a) && intsNonnegative p

def denseRowsNonnegative (e : PE) : Bool :=
  (denseRows e).all intsNonnegative

theorem pExactLowerHigh_dense_nonnegative :
    denseRowsNonnegative pExactLowerHigh = true := by
  decide

#print axioms pExactLowerHigh_dense_nonnegative

end ScratchDenseHighRows
