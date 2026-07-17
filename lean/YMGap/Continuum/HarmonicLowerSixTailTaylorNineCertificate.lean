/-
# Exact homogeneous Bernstein certificate for the lower-six T9 polynomial

Let `L9NUM(D,n)` be the numerator over `D^9` of the ninth alternating
Taylor truncation of `(1 - 1/D)^(2n+1)`.  The transparent integer polynomial
`tailTaylor9Cleared` below is exactly `9! * L9NUM`, expanded into 46 integer
power terms.

For `392 <= D` and `n <= D`, use the two projective interval coordinates

  `(392, D - 392)` and `(n, D - n)`.

The exact 9 by 10 tensor-Bernstein table has nonnegative integer entries.
After substitution its homogeneous polynomial is literally

  `(1470 * 392^8) * D^8 * tailTaylor9Cleared(D,n)`.

Both the coefficient signs and this polynomial identity are kernel-reduced by
the eager normalizer.  The positive chart factor and `D^8` are then cancelled
constructively.  No floating-point or measured coefficient enters the proof.
-/

import YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificateRows

namespace YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificate

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificateRows
open YMGap.Continuum.TensorBernsteinHomogeneousCertificate

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The cleared integer polynomial -/

/-- The symbolic mode `m = 2*n+1`. -/
def tailTaylor9ModeExpr : RingNormaliser.PolyExpr :=
  .add (.mul (.const 2) (.var 1)) (.const 1)

/-- The falling factorial `(2*n+1) * ... * (2*n+2-j)`. -/
def tailTaylor9FallingExpr : Nat → RingNormaliser.PolyExpr
  | 0 => .const 1
  | j + 1 =>
      .mul (tailTaylor9FallingExpr j)
        (.add tailTaylor9ModeExpr (.const (-(Int.ofNat j))))

/-- The signed integer coefficient `(-1)^j * 9!/j!`. -/
def tailTaylor9FactorialCoefficient : Nat → Int
  | 0 => 362880
  | 1 => -362880
  | 2 => 181440
  | 3 => -60480
  | 4 => 15120
  | 5 => -3024
  | 6 => 504
  | 7 => -72
  | 8 => 9
  | 9 => -1
  | _ => 0

def tailTaylor9FactorialTerm (j : Nat) : RingNormaliser.PolyExpr :=
  .mul (.const (tailTaylor9FactorialCoefficient j))
    (.mul (tailTaylor9FallingExpr j) (.pow (.var 0) (9 - j)))

/-- The defining alternating Taylor formula
`sum_j (-1)^j (9!/j!) (2n+1)_j D^(9-j)`, hence literally `9! * L9NUM`. -/
def tailTaylor9ClearedExpr : RingNormaliser.PolyExpr :=
  .add (tailTaylor9FactorialTerm 0)
    (.add (tailTaylor9FactorialTerm 1)
      (.add (tailTaylor9FactorialTerm 2)
        (.add (tailTaylor9FactorialTerm 3)
          (.add (tailTaylor9FactorialTerm 4)
            (.add (tailTaylor9FactorialTerm 5)
              (.add (tailTaylor9FactorialTerm 6)
                (.add (tailTaylor9FactorialTerm 7)
                  (.add (tailTaylor9FactorialTerm 8)
                    (tailTaylor9FactorialTerm 9)))))))))

/-- The independently generated 46-term power expansion of the defining
factorial expression.  Each triple encodes
`(D exponent, n exponent, integer coefficient)`. -/
def tailTaylor9ExpandedExpr : RingNormaliser.PolyExpr :=
  bivariatePowerExpr [
    (9, 0, 362880),
    (8, 1, -725760), (8, 0, -362880),
    (7, 2, 725760), (7, 1, 362880),
    (6, 3, -483840), (6, 1, 120960),
    (5, 4, 241920), (5, 3, -241920), (5, 2, -60480),
      (5, 1, 60480),
    (4, 5, -96768), (4, 4, 241920), (4, 3, -120960),
      (4, 2, -60480), (4, 1, 36288),
    (3, 6, 32256), (3, 5, -145152), (3, 4, 201600),
      (3, 3, -60480), (3, 2, -52416), (3, 1, 24192),
    (2, 7, -9216), (2, 6, 64512), (2, 5, -161280),
      (2, 4, 161280), (2, 3, -28224), (2, 2, -44352),
      (2, 1, 17280),
    (1, 8, 2304), (1, 7, -23040), (1, 6, 88704),
      (1, 5, -161280), (1, 4, 128016), (1, 3, -10080),
      (1, 2, -37584), (1, 1, 12960),
    (0, 9, -512), (0, 8, 6912), (0, 7, -37632),
      (0, 6, 104832), (0, 5, -153888), (0, 4, 101808),
      (0, 3, 512), (0, 2, -32112), (0, 1, 10080)
  ]

def tailTaylor9Rho (D n : Q') : Nat → Q'
  | 0 => D
  | 1 => n
  | _ => 0

/-- The exact integer polynomial `9! * L9NUM`, evaluated in `Q'`. -/
def tailTaylor9Cleared (D n : Q') : Q' :=
  RingNormaliser.eval (tailTaylor9Rho D n) tailTaylor9ClearedExpr

/-! ## 2. Closed homogeneous certificate -/

def tailTaylor9BernsteinExpr : RingNormaliser.PolyExpr :=
  homogeneousTensorExpr 8 9 tailTaylor9BernsteinRows

/-- Substitute the homogeneous chart coordinates
`392`, `D-392`, `n`, and `D-n`. -/
def tailTaylor9ChartSubstitution : Nat → RingNormaliser.PolyExpr
  | 0 => .const (Int.ofNat tailTaylor9ChartBase)
  | 1 => .add (.var 0) (.const (-(Int.ofNat tailTaylor9ChartBase)))
  | 2 => .var 1
  | 3 => .add (.var 0) (.neg (.var 1))
  | _ => .const 0

/-- The positive chart quotient times `D^8` times the cleared polynomial. -/
def tailTaylor9PhysicalExpr : RingNormaliser.PolyExpr :=
  .mul (.const tailTaylor9ChartQuotient)
    (.mul (.pow (.var 0) 8) tailTaylor9ClearedExpr)

/-- The factorial Taylor formula and the generated 46-term expansion agree
exactly. -/
theorem tailTaylor9_factorial_expansion_identity :
    fastNormalize tailTaylor9ClearedExpr =
      fastNormalize tailTaylor9ExpandedExpr := by
  rfl

/-- All 90 homogeneous tensor coefficients, including the basis binomial
factors, are nonnegative.  This is a closed kernel computation. -/
theorem tailTaylor9Bernstein_coefficients_nonnegative :
    RawCoefficientsNonnegative
      (fastNormalize tailTaylor9BernsteinExpr) = true := by
  rfl

/-- Exact polynomial identity after the physical chart substitution. -/
theorem tailTaylor9Bernstein_physical_identity :
    fastNormalize
        (substitute tailTaylor9ChartSubstitution
          tailTaylor9BernsteinExpr) =
      fastNormalize tailTaylor9PhysicalExpr := by
  rfl

theorem tailTaylor9TableScale_eq :
    tailTaylor9TableScale = 362880 * tailTaylor9ChartQuotient := by
  decide

/-! ## 3. Physical chart and positive-factor cancellation -/

private theorem rnqpow_pos {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat,
      (0 : Q') < RingNormaliser.qpow value exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 =>
      Q'.mul_pos (rnqpow_pos hvalue exponent) hvalue

private theorem ofNat_le_local {a b : Nat} (h : a ≤ b) :
    Q'.ofNat a ≤ Q'.ofNat b := by
  show (Int.ofNat a) * (1 : Int) ≤ (Int.ofNat b) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

private theorem ofNat_nonnegative_local (a : Nat) :
    (0 : Q') ≤ Q'.ofNat a := by
  change Q'.ofNat 0 ≤ Q'.ofNat a
  exact ofNat_le_local (Nat.zero_le a)

private theorem chart_coordinates_nonnegative
    (D n : Nat) (hD : tailTaylor9ChartBase ≤ D) (hn : n ≤ D) :
    ∀ i,
      (0 : Q') ≤ RingNormaliser.eval
        (tailTaylor9Rho (Q'.ofNat D) (Q'.ofNat n))
        (tailTaylor9ChartSubstitution i) := by
  intro i
  rcases i with _ | i
  · change (0 : Q') ≤ Q'.ofNat tailTaylor9ChartBase
    exact ofNat_nonnegative_local _
  · rcases i with _ | i
    · change (0 : Q') ≤
        Q'.ofNat D + -(Q'.ofNat tailTaylor9ChartBase)
      exact Q'.sub_nonneg_of_le (ofNat_le_local hD)
    · rcases i with _ | i
      · change (0 : Q') ≤ Q'.ofNat n
        exact ofNat_nonnegative_local n
      · rcases i with _ | i
        · change (0 : Q') ≤ Q'.ofNat D + -(Q'.ofNat n)
          exact Q'.sub_nonneg_of_le (ofNat_le_local hn)
        · change (0 : Q') ≤ Q'.ofInt 0
          decide

private theorem tailTaylor9Physical_eval
    (D n : Nat) :
    RingNormaliser.eval
        (tailTaylor9Rho (Q'.ofNat D) (Q'.ofNat n))
        tailTaylor9PhysicalExpr =
      Q'.ofInt tailTaylor9ChartQuotient *
        (RingNormaliser.qpow (Q'.ofNat D) 8 *
          tailTaylor9Cleared (Q'.ofNat D) (Q'.ofNat n)) := rfl

/-- **Exact T9 sign certificate.**  On the full low-step chart
`392 <= D`, `0 <= n <= D`, the cleared ninth Taylor numerator is
nonnegative. -/
theorem tailTaylor9Cleared_nonnegative
    (D n : Nat) (hD : tailTaylor9ChartBase ≤ D) (hn : n ≤ D) :
    (0 : Q') ≤
      tailTaylor9Cleared (Q'.ofNat D) (Q'.ofNat n) := by
  let rho := tailTaylor9Rho (Q'.ofNat D) (Q'.ofNat n)
  have hphysical :
      (0 : Q') ≤ RingNormaliser.eval rho tailTaylor9PhysicalExpr :=
    physical_nonnegative_of_homogeneous_certificate
      rho tailTaylor9ChartSubstitution tailTaylor9BernsteinExpr
      tailTaylor9PhysicalExpr
      (chart_coordinates_nonnegative D n hD hn)
      tailTaylor9Bernstein_coefficients_nonnegative
      tailTaylor9Bernstein_physical_identity
  change (0 : Q') ≤
      Q'.ofInt tailTaylor9ChartQuotient *
        (RingNormaliser.qpow (Q'.ofNat D) 8 *
          tailTaylor9Cleared (Q'.ofNat D) (Q'.ofNat n)) at hphysical
  have hDpos : (0 : Q') < Q'.ofNat D := by
    have hDposNat : 0 < D :=
      Nat.lt_of_lt_of_le (by decide : 0 < tailTaylor9ChartBase) hD
    have hshape : D = (D - 1) + 1 := by omega
    rw [hshape]
    exact Q'.ofNat_succ_pos (D - 1)
  have hchartPos : (0 : Q') < Q'.ofInt tailTaylor9ChartQuotient := by
    decide
  have hfactorPos :
      (0 : Q') < Q'.ofInt tailTaylor9ChartQuotient *
        RingNormaliser.qpow (Q'.ofNat D) 8 :=
    Q'.mul_pos hchartPos (rnqpow_pos hDpos 8)
  have hregroup :
      Q'.ofInt tailTaylor9ChartQuotient *
          (RingNormaliser.qpow (Q'.ofNat D) 8 *
            tailTaylor9Cleared (Q'.ofNat D) (Q'.ofNat n)) ≈
        (Q'.ofInt tailTaylor9ChartQuotient *
            RingNormaliser.qpow (Q'.ofNat D) 8) *
          tailTaylor9Cleared (Q'.ofNat D) (Q'.ofNat n) :=
    Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (Q'.ofInt tailTaylor9ChartQuotient)
        (RingNormaliser.qpow (Q'.ofNat D) 8)
        (tailTaylor9Cleared (Q'.ofNat D) (Q'.ofNat n)))
  have hscaled :
      (0 : Q') ≤
        (Q'.ofInt tailTaylor9ChartQuotient *
            RingNormaliser.qpow (Q'.ofNat D) 8) *
          tailTaylor9Cleared (Q'.ofNat D) (Q'.ofNat n) :=
    Q'.le_trans' _ _ _ hphysical (Q'.le_of_eqv hregroup)
  exact YMGap.Continuum.FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    hfactorPos hscaled

/-! ## Dependency gates -/

#print axioms tailTaylor9Cleared
#print axioms tailTaylor9_factorial_expansion_identity
#print axioms tailTaylor9Bernstein_coefficients_nonnegative
#print axioms tailTaylor9Bernstein_physical_identity
#print axioms tailTaylor9TableScale_eq
#print axioms tailTaylor9Cleared_nonnegative

end YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificate
