/-
# Literal Casimir commutes with integration of preceding blocks

The output block list is shifted past the integrated input blocks.  This
coefficient identity preserves arbitrary inserted factors and the complete
sum of block operators; it is the differential part of the actual character
kernel-to-path eigenaction, not an assumed spectral decomposition.
-/

import YMGap.Continuum.SU2QuaternionChannelCasimirLocality

namespace YMGap.Continuum.SU2QuaternionCasimirHeadIntegration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

private theorem blockDerivative_heads (heads block i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j (partialHaarHeads heads p))
      (partialHaarHeads heads (blockAngularDerivative (heads+block) i j p)) := by
  simpa only [blockAngularDerivative, Nat.mul_add, Nat.add_assoc] using
    angularDerivative_partialHaarHeads heads (4*block+i) (4*block+j) p

private theorem secondDerivative_heads (heads block i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j
        (blockAngularDerivative block i j (partialHaarHeads heads p)))
      (partialHaarHeads heads (blockAngularDerivative (heads+block) i j
        (blockAngularDerivative (heads+block) i j p))) :=
  (angularDerivative_congr (4*block+i) (4*block+j)
    (blockDerivative_heads heads block i j p)).trans
    (blockDerivative_heads heads block i j (blockAngularDerivative (heads+block) i j p))

private theorem six_congr {f g : Nat → Nat → RatPoly}
    (h : ∀ i j, RatPolyCoeffEqv (f i j) (g i j)) :
    RatPolyCoeffEqv (six f) (six g) :=
  (h 0 1).add ((h 0 2).add ((h 0 3).add ((h 1 2).add ((h 1 3).add (h 2 3)))))

private theorem heads_six (heads : Nat) (f : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads heads (six f))
      (six fun i j => partialHaarHeads heads (f i j)) := by
  simp only [six, partialHaarHeads_add]
  exact RatPolyCoeffEqv.refl _

/-- The literal output block Laplacian commutes with exact input integration. -/
theorem blockAngularLaplacian_partialHaarHeads (heads block : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (blockAngularLaplacian block (partialHaarHeads heads p))
      (partialHaarHeads heads (blockAngularLaplacian (heads+block) p)) :=
  (blockAngularLaplacian_eq_six block (partialHaarHeads heads p)).trans
    ((six_congr (fun i j => secondDerivative_heads heads block i j p)).trans
      ((heads_six heads _).symm.trans
        (partialHaarHeads_congr heads (blockAngularLaplacian_eq_six (heads+block) p).symm)))

private theorem heads_zero : ∀ heads : Nat,
    partialHaarHeads heads polyZero = polyZero
  | 0 => rfl
  | heads+1 => heads_zero heads

/-- The complete active Casimir passes through exact head integration with
its original output slots shifted by the number of integrated blocks. -/
theorem activeCasimirPolynomial_partialHaarHeads (heads : Nat) :
    ∀ (active : List Nat) (p : RatPoly),
    RatPolyCoeffEqv (activeCasimirPolynomial active (partialHaarHeads heads p))
      (partialHaarHeads heads
        (activeCasimirPolynomial (active.map fun block => heads+block) p))
  | [], _p => by
      change RatPolyCoeffEqv polyZero (partialHaarHeads heads polyZero)
      rw [heads_zero]
      exact RatPolyCoeffEqv.refl _
  | block::active, p => by
      change RatPolyCoeffEqv (polyAdd _ _) (partialHaarHeads heads (polyAdd _ _))
      rw [partialHaarHeads_add]
      exact ((RatPolyCoeffEqv.neg (blockAngularLaplacian_partialHaarHeads heads block p)).trans
        (partialHaarHeads_neg heads (blockAngularLaplacian (heads+block) p)).symm).add
        (activeCasimirPolynomial_partialHaarHeads heads active p)

end YMGap.Continuum.SU2QuaternionCasimirHeadIntegration

#print axioms YMGap.Continuum.SU2QuaternionCasimirHeadIntegration.blockAngularLaplacian_partialHaarHeads
#print axioms YMGap.Continuum.SU2QuaternionCasimirHeadIntegration.activeCasimirPolynomial_partialHaarHeads
