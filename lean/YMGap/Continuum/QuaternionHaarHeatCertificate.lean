/-
# Small-nome heat certificates for any actual Haar-unit scalar

The existing character intervals give a cutoff-independent remainder cap
delta(w)=128*w^3. This module constructs certificates for the heat prefix
of any supported scalar with square cap one, retaining its actual Haar
carrier. In particular no disjointness of the scalar's links is required.
The coupling guards are explicit. This is not a spectral or limit result.
-/

import YMGap.Continuum.QuaternionHaarCharacterInterval

namespace YMGap.Continuum.QuaternionHaarHeatCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BondMovingStep

def heatPrefix (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  finitePolySum (fun n => polySmul (coeffW w n) (characterPolynomial p n)) (List.range (K+1))

def heatRemainder (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  finitePolySum (fun i => polySmul (coeffW w (1+i)) (characterPolynomial p (1+i))) (List.range K)

private theorem sum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, finitePolySum, sum_map f g xs]

/-- Literal coefficient pin between the full prefix and its positive labels. -/
theorem heatPrefix_split (w : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (heatPrefix w K p) (polyAdd polyOne (heatRemainder w K p)) := by
  unfold heatPrefix heatRemainder
  rw [List.range_succ_eq_map]
  simp only [finitePolySum, sum_map, coeffW_zero, characterPolynomial, Nat.add_comm 1]
  exact (RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _)

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half)

/-- Constructed two-sided bound, independent of cutoff and carrier size. -/
def remainderInterval {blocks : Nat} {p : RatPoly} (P : SquareBound blocks p 1) (K : Nat) :
    Interval blocks (heatRemainder w K p) (heatRemainderBound w) :=
  (Interval.finiteRange (fun i => polySmul (coeffW w (1+i)) (characterPolynomial p (1+i)))
    (fun i => heatTermBound w (1+i))
    (fun i => Interval.smul (coeffW w (1+i)) (coeffW_nonneg hw0 _)
      (characterInterval P (1+i))) K).weaken (heatPositiveLabels_bound hw0 hw1 hsmall K)

/-- Ordinary Haar positivity of the actual prefix, not merely OS positivity. -/
def prefixCertificate (hdelta : heatRemainderBound w ≤ 1)
    {blocks : Nat} {p : RatPoly} (P : SquareBound blocks p 1) (K : Nat) :
    Certificate blocks (heatPrefix w K p) :=
  .ofCoeff ((heatPrefix_split w K p).trans
    ((RatPolyCoeffEqv.one_smul polyOne).symm.add (RatPolyCoeffEqv.refl _)))
    ((remainderInterval hw0 hw1 hsmall P K).weaken hdelta).lower

end YMGap.Continuum.QuaternionHaarHeatCertificate

#print axioms YMGap.Continuum.QuaternionHaarHeatCertificate.heatPrefix
#print axioms YMGap.Continuum.QuaternionHaarHeatCertificate.heatRemainder
#print axioms YMGap.Continuum.QuaternionHaarHeatCertificate.heatPrefix_split
#print axioms YMGap.Continuum.QuaternionHaarHeatCertificate.remainderInterval
#print axioms YMGap.Continuum.QuaternionHaarHeatCertificate.prefixCertificate
