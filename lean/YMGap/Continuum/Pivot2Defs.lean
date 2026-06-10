/-
Shared definitions for the SU(2) heat-kernel 2×2 PSD pivot (Track B / E1).

The 2×2 Gram pivot is `D₁ = 1 + m₂ − m₁²` with moments
`m₁ = 2·e^{−3t/4}`, `m₂ = 3·e^{−2t}`.  In the variable `r = e^{−t/2}` it is
the degree-4 polynomial `1 + 3r⁴ − 4r³` with the manifest-SOS factorization
`(1−r)²(3r²+2r+1)`.  This file fixes the exact `CReal` expressions; the
three independent lemmas (`Pivot2Identity`, `Pivot2Moments`,
`Pivot2Nonneg`) are proved against them and assembled in `Pivot2`.
-/

import YMGap.Constructive.ExpNeg
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.Pivot2

open YMGap.Constructive

/-- Rational constant as a `CReal`. -/
def C (n : Nat) : CReal := CReal.ofQ' (Q'.ofNat n)

/-- `n · x`. -/
def smul (n : Nat) (x : CReal) : CReal := CReal.mul (C n) x

/-- `e^{−t·q}`. -/
def expo (t : Q') (ht : (0 : Q') ≤ t) (q : Q') (hq : (0 : Q') ≤ q) : CReal :=
  ExpNeg.expNeg (t * q) (Q'.mul_nonneg t q ht hq)

/-! ## The variable `r = e^{−t/2}` and the moments -/

def r (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  expo t ht (Q'.mkPos 1 2 (by decide)) (by decide)

/-- `m₁ = 2·e^{−3t/4}`. -/
def m1 (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  smul 2 (expo t ht (Q'.mkPos 3 4 (by decide)) (by decide))

/-- `m₂ = 3·e^{−2t}`. -/
def m2 (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  smul 3 (expo t ht (Q'.mkPos 2 1 (by decide)) (by decide))

/-- The 2×2 Gram pivot `D₁ = 1 + m₂ − m₁²`. -/
def pivotGram (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  CReal.add (CReal.add (C 1) (m2 t ht)) (CReal.neg (CReal.mul (m1 t ht) (m1 t ht)))

/-! ## Generic polynomial / SOS expressions in a variable `x` -/

def sq (x : CReal) : CReal := CReal.mul x x
def cube (x : CReal) : CReal := CReal.mul x (CReal.mul x x)
def quart (x : CReal) : CReal := CReal.mul x (CReal.mul x (CReal.mul x x))

/-- `1 + 3x⁴ − 4x³` (the pivot polynomial). -/
def pivotPoly (x : CReal) : CReal :=
  CReal.add (CReal.add (C 1) (smul 3 (quart x))) (CReal.neg (smul 4 (cube x)))

/-- `1 − x`. -/
def oneSub (x : CReal) : CReal := CReal.add (C 1) (CReal.neg x)

/-- `3x² + 2x + 1`. -/
def quad (x : CReal) : CReal :=
  CReal.add (CReal.add (smul 3 (sq x)) (smul 2 x)) (C 1)

/-- `(1−x)²·(3x²+2x+1)` — the manifest-SOS factorization of `pivotPoly`. -/
def sosProduct (x : CReal) : CReal := CReal.mul (sq (oneSub x)) (quad x)

end YMGap.Continuum.Pivot2
