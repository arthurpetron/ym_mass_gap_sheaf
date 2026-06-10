/-
Track B / E1 — the SU(2) heat-kernel 2×2 Gram **pivot positivity**, the
first genuine *off-cone* (sign-indefinite) positivity of the heat-kernel
functional, assembled from three independently-proved pieces:

  * `Pivot2Moments.pivotGram_eqv_poly` — `D₁ = 1 + m₂ − m₁² ≃ 1 + 3r⁴ − 4r³`
    (`r = e^{−t/2}`), via the `expNeg` addition/power law.
  * `Pivot2Identity.pivotPoly_eqv_sos` — `1 + 3r⁴ − 4r³ ≃ (1−r)²(3r²+2r+1)`,
    via the reflective `Q'` polynomial ring (`QPoly`).
  * `Pivot2Nonneg.sosProduct_nonneg` — `(1−r)²(3r²+2r+1) ≥ 0`, via the SOS
    primitives.

Chaining them: `D₁ ≃ (1−r)²(3r²+2r+1) ≥ 0`, so `D₁ ≥ 0`.  This is the Schur
complement of the (normalized) 2×2 Gram matrix `[[1, m₁],[m₁, 1+m₂]]`; its
nonnegativity plus `G₀₀ = 1 > 0` is exactly 2×2 positive-semidefiniteness —
heat-kernel positivity on degree-≤1 observables, the content that the
nonnegative-cone result (`WilsonFunctional.coneExp_nonneg`) could not reach.
-/

import YMGap.Continuum.Pivot2Defs
import YMGap.Continuum.Pivot2Identity
import YMGap.Continuum.Pivot2Moments
import YMGap.Continuum.Pivot2Nonneg
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.Pivot2

open YMGap.Constructive

/-- `r = e^{−t/2} ≥ 0`. -/
theorem r_nonneg (t : Q') (ht : (0 : Q') ≤ t) : ExpPos.geRat (r t ht) 0 := by
  unfold r expo
  exact expNeg_geRat_zero _ _

/-- **The 2×2 heat-kernel Gram pivot is nonnegative:** `0 ≤ 1 + m₂ − m₁²`.

Equivalently the Schur complement of `[[1, m₁],[m₁, 1+m₂]]` is `≥ 0`, so the
matrix is positive-semidefinite — heat-kernel positivity on sign-indefinite
degree-≤1 observables. -/
theorem pivotGram_nonneg (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (pivotGram t ht) 0 :=
  SU3CharFactor.geRat_of_equiv
    (equiv_trans (pivotGram_eqv_poly t ht) (pivotPoly_eqv_sos (r t ht)))
    (sosProduct_nonneg (r t ht) (r_nonneg t ht))

end YMGap.Continuum.Pivot2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.Pivot2.pivotGram_nonneg
