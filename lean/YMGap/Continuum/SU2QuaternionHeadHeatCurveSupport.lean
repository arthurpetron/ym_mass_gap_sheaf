/-
# Support of finite conditional heat curves and their angular energies

The polynomial-in-nome rows retain support in the original finite carrier.
Angular differentiation, products and the six-plane sum preserve that
support. These are algebraic guards only; they provide no positivity,
curvature estimate, or cutoff-uniform analytic bound.
-/

import YMGap.Continuum.SU2QuaternionHeadHeatGenerator
import YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.QuaternionHaarLinearAngularEnergy
import YMGap.Continuum.SU2QuaternionAngularBochner

namespace YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2QuaternionAngularBochner

private theorem polySum_supported {blocks : Nat} :
    ∀ ps : List RatPoly,
      (∀ p, p ∈ ps → SupportedQuaternionBlocks blocks p) →
      SupportedQuaternionBlocks blocks (polySum ps)
  | [], _ => by
      intro term hterm
      simp [polySum, polyZero] at hterm
  | p :: ps, hps => by
      change SupportedQuaternionBlocks blocks (polyAdd p (polySum ps))
      apply polyAdd_supported
      · exact hps p List.mem_cons_self
      · exact polySum_supported ps (fun q hq => hps q (List.mem_cons_of_mem p hq))

/-- Every nome row retains the support of its computed harmonic group. -/
theorem nomeHeatPolynomial_supported (tail : Nat) (p : RatPoly) :
    ∀ row, row ∈ nomeHeatPolynomial tail p →
      SupportedQuaternionBlocks (tail+1) row.2 := by
  unfold nomeHeatPolynomial
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨d, hd, rfl⟩
  change SupportedQuaternionBlocks (tail+1)
    (grouped d (modes (tail+1) (Nat.zero_lt_succ tail) p))
  exact grouped_supported d (modes (tail+1) (Nat.zero_lt_succ tail) p)

/-- The evaluated finite nome flow remains in the original finite carrier at
every rational nome, with no support premise on the incoming polynomial. -/
theorem finiteNomeFlow_supported (tail : Nat) (p : RatPoly) (r : Q') :
    SupportedQuaternionBlocks (tail+1) (finiteNomeFlow tail p r) := by
  unfold finiteNomeFlow
  apply polySum_supported
  intro q hq
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hq
  exact polySmul_supported (nomeHeatPolynomial_supported tail p row hrow) _

private theorem six_supported {blocks : Nat} (f : Nat → Nat → RatPoly)
    (hf : ∀ i j, i < 4 → j < 4 → SupportedQuaternionBlocks blocks (f i j)) :
    SupportedQuaternionBlocks blocks (six f) := by
  unfold six
  exact polyAdd_supported (hf 0 1 (by decide) (by decide))
    (polyAdd_supported (hf 0 2 (by decide) (by decide))
      (polyAdd_supported (hf 0 3 (by decide) (by decide))
        (polyAdd_supported (hf 1 2 (by decide) (by decide))
          (polyAdd_supported (hf 1 3 (by decide) (by decide))
            (hf 2 3 (by decide) (by decide))))))

private theorem polyNeg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term hterm
  unfold polyNeg at hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hp source hsource

/-- The original six-plane Laplacian preserves every nonempty carrier. -/
theorem angularLaplacian_supported {blocks : Nat} (hb : 0 < blocks)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (angularLaplacian p) := by
  unfold angularLaplacian
  apply six_supported
  intro i j hi hj
  exact angularDerivative_supported hb hi hj
    (angularDerivative_supported hb hi hj hp)

/-- The original six-plane angular square preserves every nonempty carrier. -/
theorem angularSquare_supported {blocks : Nat} (hb : 0 < blocks)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (angularSquare p) := by
  unfold angularSquare
  apply six_supported
  intro i j hi hj
  exact supported_polyMul
    (angularDerivative_supported hb hi hj hp)
    (angularDerivative_supported hb hi hj hp)

/-- The polarized six-plane energy preserves support in both arguments. -/
theorem mixedGamma_supported {blocks : Nat} (hb : 0 < blocks)
    {p q : RatPoly} (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (mixedGamma p q) := by
  unfold mixedGamma
  apply six_supported
  intro i j hi hj
  exact supported_polyMul
    (angularDerivative_supported hb hi hj hp)
    (angularDerivative_supported hb hi hj hq)

/-- The actual iterated carré du champ stays on the same finite carrier. -/
theorem gamma2_supported {blocks : Nat} (hb : 0 < blocks)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (gamma2 p) := by
  unfold gamma2
  apply polyAdd_supported
  · exact polySmul_supported
      (angularLaplacian_supported hb (angularSquare_supported hb hp)) _
  · exact polyNeg_supported
      (mixedGamma_supported hb hp (angularLaplacian_supported hb hp))

/-- The Bochner curvature-margin polynomial also remains in that carrier. -/
theorem bochnerMargin_supported {blocks : Nat} (hb : 0 < blocks)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks
      (polyAdd (gamma2 p) (polyNeg (angularSquare p))) := by
  exact polyAdd_supported (gamma2_supported hb hp)
    (polyNeg_supported (angularSquare_supported hb hp))

end YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport.nomeHeatPolynomial_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport.finiteNomeFlow_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport.angularLaplacian_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport.angularSquare_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport.mixedGamma_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport.gamma2_supported
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport.bochnerMargin_supported
