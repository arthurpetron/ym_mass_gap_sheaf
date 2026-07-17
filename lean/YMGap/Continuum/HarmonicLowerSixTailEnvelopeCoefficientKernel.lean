/-
# Coefficient kernel for the lower-six E8/E9 envelope charts

This module contains only generic integer-grid operations.  Closed generated
tables instantiate them in the four chart certificates.  The two chart maps
share the quadratic projective substitution

  x * n = constant,    r * n^2 = D.

Chart A then uses `r = 1+y`.  Chart B uses
`r = z + x/28*(1-z)`; `affineChartBClearedCoeff` clears the common
`28^degreeY` coefficient denominator before checking that substitution.
-/

import YMGap.Continuum.TensorBernsteinSeparableReconstruction

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel

open YMGap.RG
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

/-- A row slice of a closed grid relation.  `actual` is indexed locally while
`expected` retains the global row index. -/
def GridRelationSlice (start height width : Nat)
    (actual expected : Nat → Nat → Int) : Bool :=
  allNat height (fun localRow =>
    allNat width (fun j =>
      decide (actual localRow j = expected (start + localRow) j)))

theorem gridRelationSlice_true_at {start height width : Nat}
    {actual expected : Nat → Nat → Int}
    (h : GridRelationSlice start height width actual expected = true)
    {localRow j : Nat} (hrow : localRow < height) (hj : j < width) :
    actual localRow j = expected (start + localRow) j := by
  have hrowTrue := allNat_true_at h hrow
  have hjTrue := allNat_true_at hrowTrue hj
  exact of_decide_eq_true hjTrue

/-- The integer coefficient multiplying the normalized tensor Bernstein
basis.  Generated tables store the unweighted Bernstein coefficients. -/
def weightedGrid (degreeX degreeY : Nat) (rows : List (List Int))
    (i j : Nat) : Int :=
  gridCoeff rows i j * Int.ofNat (binom degreeX i * binom degreeY j)

/-- The first Pascal pass, exposed as a grid for a closed relation check. -/
def xPascalExpected (degreeX : Nat) (power : List (List Int))
    (i b : Nat) : Int :=
  pascalTransformRow degreeX (fun a => gridCoeff power a b) i

/-- The second Pascal pass, using a generated cache of the first pass. -/
def yPascalExpected (degreeY : Nat) (xPascal : List (List Int))
    (i j : Nat) : Int :=
  pascalTransformRow degreeY (fun b => gridCoeff xPascal i b) j

/-- Coefficient relation between the pre-chart table and the cleared raw
polynomial.  The raw monomial is selected by `u + 2*i + j = totalDegree`.
Multiplication by `constant^u` clears `x = constant/n`. -/
def quadraticRawExpected (totalDegree chartQuotient : Nat)
    (raw : List (List Int)) (u i : Nat) : Int :=
  if u + 2 * i ≤ totalDegree then
    Int.ofNat chartQuotient * gridCoeff raw i (totalDegree - u - 2 * i)
  else
    0

def intFinSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | count + 1 => intFinSum f count + f count

def alternatingIntSign (exponent : Nat) : Int :=
  if exponent % 2 = 0 then 1 else -1

/-- The authoritative lower mode in both projective envelope charts. -/
def tailEnvelopeModeChartBase : Nat := 14

/-- The authoritative denominator in the chart-B affine substitution. -/
def affineChartBScale : Nat := 28

/-- Coefficient of `x^a*z^b`, multiplied by
`affineChartBScale^degreeY`, after the chart-B substitution
`r = z + x/affineChartBScale*(1-z)` in a pre-chart tensor power table. -/
def affineChartBClearedCoeff (degreeY : Nat)
    (preChart : List (List Int)) (a b : Nat) : Int :=
  intFinSum (fun ell =>
    if ell ≤ a then
      intFinSum (fun i =>
        if ell ≤ i ∧ i ≤ b + ell ∧ b + ell - i ≤ ell then
          let q := b + ell - i
          gridCoeff preChart (a - ell) i *
            Int.ofNat
              (binom i ell * binom ell q *
                affineChartBScale ^ (degreeY - ell)) *
            alternatingIntSign q
        else
          0) (degreeY + 1)
    else
      0) (degreeY + 1)

/-! The following declarations are computational data, hence axiom-free. -/

#print axioms weightedGrid
#print axioms gridRelationSlice_true_at
#print axioms xPascalExpected
#print axioms yPascalExpected
#print axioms quadraticRawExpected
#print axioms tailEnvelopeModeChartBase
#print axioms affineChartBScale
#print axioms affineChartBClearedCoeff

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
