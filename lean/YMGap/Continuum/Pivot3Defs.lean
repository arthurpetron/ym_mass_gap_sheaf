/-
Shared definitions for the SU(2) heat-kernel **3×3** Gram PSD (the extension of
the 2×2 pivot to degree-≤2 observables `a = c₀χ₀ + c₁χ₁ + c₂χ₂`).

The heat-kernel moments are `m_k = ⟨χ_k⟩_t = (k+1)·e^{−t·k(k+2)/4}`.  In the
base variable `a = e^{−t/4}` they are `m_k = (k+1)·a^{k(k+2)}`, i.e.

    m₁ = 2·a³,   m₂ = 3·a⁸,   m₃ = 4·a¹⁵,   m₄ = 5·a²⁴.

Using the SU(2) fusion `χ_iχ_j = Σ χ_{|i−j|..i+j step 2}` the normalized
3×3 Gram (basis χ₀,χ₁,χ₂) is

    G₀₀ = 1,        G₀₁ = m₁,        G₀₂ = m₂,
    G₁₁ = 1+m₂,     G₁₂ = m₁+m₃,     G₂₂ = 1+m₂+m₄,

and `form3 = Σ_{i,j<3} c_i c_j G_{ij}` is the energy `E((c₀χ₀+c₁χ₁+c₂χ₂)²)`.

This file fixes the exact `CReal` expressions: the base `a`, the power helper
`apow`, the four moments, the Gram entries, `form3`, and the polynomial
building blocks `Pp`, `bigp`, `S12p`, `M0`, `M1`, `M2` of the
manifest-SOS certificate proved in the sibling files.
-/

import YMGap.Constructive.ExpNeg
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.Pivot3

open YMGap.Constructive

/-- Rational constant as a `CReal`. -/
def C (n : Nat) : CReal := CReal.ofQ' (Q'.ofNat n)

/-- `n · x`. -/
def smul (n : Nat) (x : CReal) : CReal := CReal.mul (C n) x

/-! ## The base `a = e^{−t/4}` and its integer powers -/

/-- The quarter-exponent `t·(k/4)` is `≥ 0` for `t ≥ 0`. -/
theorem quarter_nonneg (t : Q') (ht : (0 : Q') ≤ t) (k : Nat) :
    (0 : Q') ≤ t * Q'.mkPos (Int.ofNat k) 4 (by decide) :=
  Q'.mul_nonneg t _ ht (by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg k)

/-- `a^k = e^{−t·k/4}` — the `k`-th power of the base `a = e^{−t/4}`. -/
def apow (t : Q') (ht : (0 : Q') ≤ t) (k : Nat) : CReal :=
  ExpNeg.expNeg (t * Q'.mkPos (Int.ofNat k) 4 (by decide)) (quarter_nonneg t ht k)

/-- The base `a = a^1 = e^{−t/4}`. -/
def base (t : Q') (ht : (0 : Q') ≤ t) : CReal := apow t ht 1

/-! ## The four moments `m_k = (k+1)·a^{k(k+2)}` -/

/-- `m₁ = 2·a³ = 2·e^{−3t/4}`. -/
def m1 (t : Q') (ht : (0 : Q') ≤ t) : CReal := smul 2 (apow t ht 3)

/-- `m₂ = 3·a⁸ = 3·e^{−2t}`. -/
def m2 (t : Q') (ht : (0 : Q') ≤ t) : CReal := smul 3 (apow t ht 8)

/-- `m₃ = 4·a¹⁵ = 4·e^{−15t/4}`. -/
def m3 (t : Q') (ht : (0 : Q') ≤ t) : CReal := smul 4 (apow t ht 15)

/-- `m₄ = 5·a²⁴ = 5·e^{−6t}`. -/
def m4 (t : Q') (ht : (0 : Q') ≤ t) : CReal := smul 5 (apow t ht 24)

/-! ## The 3×3 Gram entries -/

def G00 : CReal := C 1
def G01 (t : Q') (ht : (0 : Q') ≤ t) : CReal := m1 t ht
def G02 (t : Q') (ht : (0 : Q') ≤ t) : CReal := m2 t ht
def G11 (t : Q') (ht : (0 : Q') ≤ t) : CReal := CReal.add (C 1) (m2 t ht)
def G12 (t : Q') (ht : (0 : Q') ≤ t) : CReal := CReal.add (m1 t ht) (m3 t ht)
def G22 (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  CReal.add (CReal.add (C 1) (m2 t ht)) (m4 t ht)

/-- The 3×3 heat-kernel energy `form3 = Σ_{i,j<3} c_i c_j G_{ij}`:
`c₀²G₀₀ + c₁²G₁₁ + c₂²G₂₂ + 2c₀c₁G₀₁ + 2c₀c₂G₀₂ + 2c₁c₂G₁₂`. -/
def form3 (t : Q') (ht : (0 : Q') ≤ t) (c0 c1 c2 : Q') : CReal :=
  CReal.add
    (CReal.add
      (CReal.add (CReal.mul (CReal.ofQ' (c0 * c0)) (G00))
                 (CReal.mul (CReal.ofQ' (c1 * c1)) (G11 t ht)))
      (CReal.add (CReal.mul (CReal.ofQ' (c2 * c2)) (G22 t ht))
                 (CReal.mul (CReal.ofQ' (2 * (c0 * c1))) (G01 t ht))))
    (CReal.add (CReal.mul (CReal.ofQ' (2 * (c0 * c2))) (G02 t ht))
               (CReal.mul (CReal.ofQ' (2 * (c1 * c2))) (G12 t ht)))

end YMGap.Continuum.Pivot3
