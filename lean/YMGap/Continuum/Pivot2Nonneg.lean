/-
Nonnegativity of the manifest-SOS factorization `(1−x)²·(3x²+2x+1)` for `x ≥ 0`.

`sosProduct x = (1−x)²·(3x²+2x+1)` is `≥ 0` because `(1−x)²` is a square
(`geRat_sq_nonneg`) and `quad x = 3x²+2x+1 ≥ 0` for `x ≥ 0`: each summand
`3x² ≥ 0`, `2x ≥ 0`, `1 ≥ 0` is nonnegative, and the product of two
nonnegatives is nonnegative (`CReal.mul_nonneg`).

# Axiom-gate (AGENTS.md Rule 1)

`[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.Pivot2Defs

namespace YMGap.Continuum.Pivot2

open YMGap.Constructive

/-- `quad x = 3x² + 2x + 1 ≥ 0` for `x ≥ 0`. -/
theorem quad_nonneg (x : CReal) (hx : ExpPos.geRat x 0) :
    ExpPos.geRat (quad x) 0 := by
  -- `3·x² ≥ 0`
  have h3 : ExpPos.geRat (smul 3 (sq x)) 0 :=
    CReal.mul_nonneg
      (SumOfSquares.geRat_ofQ'_nonneg (by decide))
      (SumOfSquares.geRat_sq_nonneg x)
  -- `2·x ≥ 0`
  have h2 : ExpPos.geRat (smul 2 x) 0 :=
    CReal.mul_nonneg
      (SumOfSquares.geRat_ofQ'_nonneg (by decide))
      hx
  -- `1 ≥ 0`
  have h1 : ExpPos.geRat (C 1) 0 :=
    SumOfSquares.geRat_ofQ'_nonneg (by decide)
  -- `(3x² + 2x) ≥ 0`
  have h32 : ExpPos.geRat (CReal.add (smul 3 (sq x)) (smul 2 x)) 0 :=
    ExpPos.geRat_mono (SumOfSquares.geRat_add h3 h2) (by decide)
  -- `((3x² + 2x) + 1) ≥ 0`
  exact ExpPos.geRat_mono (SumOfSquares.geRat_add h32 h1) (by decide)

/-- `sosProduct x = (1−x)²·(3x²+2x+1) ≥ 0` for `x ≥ 0`. -/
theorem sosProduct_nonneg (x : CReal) (hx : ExpPos.geRat x 0) :
    ExpPos.geRat (sosProduct x) 0 :=
  CReal.mul_nonneg
    (SumOfSquares.geRat_sq_nonneg (oneSub x))
    (quad_nonneg x hx)

end YMGap.Continuum.Pivot2

/-! ## Axiom-dependency gate (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Pivot2.sosProduct_nonneg
