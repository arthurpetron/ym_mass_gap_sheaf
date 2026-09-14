/-
# Factorized Haar integration with an unintegrated boundary

Stop the existing exact bivalent contractor after a specified number of
quaternion blocks. An arbitrary polynomial in all remaining coordinates is
carried through unchanged. This is a conditional identity, not a scalar
network evaluation and not a positivity estimate for interacting weights.
-/

import YMGap.Continuum.SU2QuaternionBivalentHaarContraction

namespace YMGap.Continuum.SU2QuaternionPartialFactorizedHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionBivalentHaarContraction

local infix:50 " ≈ " => Q'.eqv

/-- Reserve one quaternion block before every coordinate of a polynomial. -/
def liftHead (p : RatPoly) : RatPoly :=
  p.map fun t => (0 :: 0 :: 0 :: 0 :: t.1, t.2)

theorem liftHead_independent (p : RatPoly) :
    headIndependentCheck (liftHead p) = true := by
  apply List.all_eq_true.mpr
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  rfl

theorem drop_liftHead (p : RatPoly) :
    dropHeadPolynomial (liftHead p) = p := by
  simp [dropHeadPolynomial, liftHead, List.map_map, Function.comp_def]

/-- Put the observable after precisely the blocks to be integrated. -/
def liftBoundary : Nat → RatPoly → RatPoly
  | 0, p => p
  | n + 1, p => liftHead (liftBoundary n p)

theorem factorizedHeadStep_boundary (fs : List RatPoly) (p : RatPoly) :
    factorizedHeadStep (fs ++ [liftHead p]) =
      factorizedHeadStep fs ++ [p] := by
  simp [factorizedHeadStep, headIncidentFactors, headIndependentFactors,
    List.filter_append, liftHead_independent, drop_liftHead]

theorem bivalentHeadStep_boundary (fs : List RatPoly) (p : RatPoly) :
    bivalentFactorizedHeadStep (fs ++ [liftHead p]) =
      bivalentFactorizedHeadStep fs ++ [p] := by
  simp only [bivalentFactorizedHeadStep_eq, factorizedHeadStep_boundary]

/-- Integrate only the first `n` blocks; the output is still a factor list. -/
def partialFactors : Nat → List RatPoly → List RatPoly
  | 0, fs => fs
  | n + 1, fs => partialFactors n (bivalentFactorizedHeadStep fs)

/-- All boundary/spectator polynomials are retained, with no degree bound.
The number `blocks` of subsequent Haar integrations is also arbitrary. -/
theorem partialFactors_boundary_haar : ∀ (n blocks : Nat)
    (fs : List RatPoly) (p : RatPoly),
    quaternionHaar (blocks + n)
        (factorProduct (fs ++ [liftBoundary n p])) ≈
      quaternionHaar blocks (factorProduct (partialFactors n fs ++ [p]))
  | 0, _, _, _ => Q'.eqv_refl _
  | n + 1, blocks, fs, p => by
      have h := quaternionHaar_factorizedHeadStep (blocks + n)
        (fs ++ [liftHead (liftBoundary n p)])
      rw [← bivalentFactorizedHeadStep_eq, bivalentHeadStep_boundary] at h
      exact Q'.eqv_trans _ _ _ h
        (partialFactors_boundary_haar n blocks (bivalentFactorizedHeadStep fs) p)

end YMGap.Continuum.SU2QuaternionPartialFactorizedHaar

#print axioms YMGap.Continuum.SU2QuaternionPartialFactorizedHaar.liftHead_independent
#print axioms YMGap.Continuum.SU2QuaternionPartialFactorizedHaar.drop_liftHead
#print axioms YMGap.Continuum.SU2QuaternionPartialFactorizedHaar.factorizedHeadStep_boundary
#print axioms YMGap.Continuum.SU2QuaternionPartialFactorizedHaar.bivalentHeadStep_boundary
#print axioms YMGap.Continuum.SU2QuaternionPartialFactorizedHaar.partialFactors_boundary_haar
