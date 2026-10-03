/-
# Exact variance tower on the ORIGINAL shared-tail carrier

The inner and outer kernels and the signed source remain literal. Ordered
head Fubini gives the actual total-variance decomposition coefficientwise.
For a positive kernel whose actual conditional mass is one under EVERY
surviving insertion, the own-mean variance receives a constructed square
Certificate, hence conditional Jensen with any certified output weight.

This is finite conditional algebra for the active-product Poincare join.
It supplies neither the selected heat/angular estimate nor the width-free
Efron--Stein join, interacting relative survival, scaling, OS or Clay closure.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.SU2QuaternionConditionalVarianceTower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
  (determinant determinant_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "I" heads:arg p:arg => partialHaarHeads heads p
local infix:50 " ≈ " => Q'.eqv

/-- Own conditional mean; every surviving coordinate is shared. -/
def mean (heads : Nat) (W p : RatPoly) : RatPoly := I heads (polyMul W p)

/-- The normalized own-mean expression. Positivity requires the explicit
actual mass-one pin below, not a free-coefficient normalization assertion. -/
def variance (heads : Nat) (W p : RatPoly) : RatPoly :=
  polyAdd (mean heads W (polyMul p p))
    (polyNeg (polyMul (mean heads W p) (mean heads W p)))

theorem determinant_variance_pin (tail heads : Nat) (W p : RatPoly)
    (unit : HaarCarrierEqv tail (I heads W) polyOne) :
    HaarCarrierEqv tail (determinant heads W p) (variance heads W p) := by
  unfold determinant variance mean
  exact HaarCarrierEqv.add
    ((HaarCarrierEqv.mul_right _ unit).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul _)))
    (HaarCarrierEqv.refl tail _)

/-- Conditional Jensen is produced from the actual two-copy square witness.
No variance inequality or positive normalizer inverse is an input. -/
def variance_certificate (tail heads : Nat) (W p : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (P : Certificate (tail+heads) W)
    (unit : HaarCarrierEqv tail (I heads W) polyOne) :
    Certificate tail (variance heads W p) :=
  .transport (determinant_variance_pin tail heads W p unit).symm
    (determinant_certificate tail heads W p hW hp P)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- The same output weight surrounds both sides of conditional Jensen. -/
theorem weighted_jensen (tail heads : Nat) (W p R : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (P : Certificate (tail+heads) W) (PR : Certificate tail R)
    (unit : HaarCarrierEqv tail (I heads W) polyOne) :
    quaternionHaar tail (polyMul R (polyMul (mean heads W p) (mean heads W p))) ≤
      quaternionHaar tail (polyMul R (mean heads W (polyMul p p))) := by
  have hpos := (PR.mul (variance_certificate tail heads W p hW hp P unit)).haar_nonnegative
  have he : RatPolyCoeffEqv (polyMul R (variance heads W p))
      (polyAdd (polyMul R (mean heads W (polyMul p p)))
        (polyNeg (polyMul R (polyMul (mean heads W p) (mean heads W p))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => R | 1 => mean heads W (polyMul p p)
                       | _ => polyMul (mean heads W p) (mean heads W p))
  have hi := Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append tail _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg tail _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv hi))

/-- Actual inner/outer kernel, not a separately postulated total law. -/
def towerWeight (inner : Nat) (W R : RatPoly) : RatPoly :=
  polyMul W (liftBoundary inner R)

theorem heads_compose : ∀ (inner outer : Nat) (p : RatPoly),
    I (inner+outer) p = I outer (I inner p)
  | 0, outer, p => by simp only [Nat.zero_add, partialHaarHeads]
  | inner+1, outer, p => by
      rw [show inner+1+outer = (inner+outer)+1 by omega]
      exact heads_compose inner outer (partialHaarHead p)

/-- Exact conditional Fubini for the literal joined kernel and source. -/
theorem tower_mean_pin (inner outer : Nat) (W R p : RatPoly) :
    RatPolyCoeffEqv (mean (inner+outer) (towerWeight inner W R) p)
      (mean outer R (mean inner W p)) := by
  unfold mean towerWeight
  rw [heads_compose]
  have hr : RatPolyCoeffEqv (polyMul (polyMul W (liftBoundary inner R)) p)
      (polyMul (polyMul W p) (liftBoundary inner R)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => W | 1 => liftBoundary inner R | _ => p)
  exact (partialHaarHeads_congr outer
    ((partialHaarHeads_congr inner hr).trans
      (partialHaarHeads_mul_lift inner (polyMul W p) R))).trans
    (partialHaarHeads_congr outer (RatPolyCoeffEqv.mul_comm _ _))

/-- Total variance is EXACTLY the variance of the conditional mean plus
the remaining conditional variance. No independence, sign or unit premise
is needed for this polynomial identity; no cross term is discarded. -/
theorem variance_tower_pin (inner outer : Nat) (W R p : RatPoly) :
    RatPolyCoeffEqv (variance (inner+outer) (towerWeight inner W R) p)
      (polyAdd (variance outer R (mean inner W p))
        (mean outer R (variance inner W p))) := by
  let m := mean inner W p
  let s := mean inner W (polyMul p p)
  have htotal : RatPolyCoeffEqv (variance (inner+outer) (towerWeight inner W R) p)
      (polyAdd (mean outer R s)
        (polyNeg (polyMul (mean outer R m) (mean outer R m)))) :=
    (tower_mean_pin inner outer W R (polyMul p p)).add
      (RatPolyCoeffEqv.neg ((tower_mean_pin inner outer W R p).mul
        (tower_mean_pin inner outer W R p)))
  have hinner : RatPolyCoeffEqv (mean outer R (variance inner W p))
      (polyAdd (mean outer R s) (polyNeg (mean outer R (polyMul m m)))) := by
    have hex : RatPolyCoeffEqv (polyMul R (variance inner W p))
        (polyAdd (polyMul R s) (polyNeg (polyMul R (polyMul m m)))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => R | 1 => s | _ => polyMul m m)
    unfold mean
    refine (partialHaarHeads_congr outer hex).trans ?_
    rw [partialHaarHeads_add]
    exact (RatPolyCoeffEqv.refl _).add (partialHaarHeads_neg outer _)
  have hcancel : RatPolyCoeffEqv
      (polyAdd (variance outer R m)
        (polyAdd (mean outer R s) (polyNeg (mean outer R (polyMul m m)))))
      (polyAdd (mean outer R s)
        (polyNeg (polyMul (mean outer R m) (mean outer R m)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 0))))
      (.add (.var 2) (.neg (.var 1))) (by decide)
      (fun | 0 => mean outer R (polyMul m m)
           | 1 => polyMul (mean outer R m) (mean outer R m)
           | _ => mean outer R s)
  exact htotal.trans (((RatPolyCoeffEqv.refl _).add hinner).trans hcancel).symm

/-- Normalization of the actual joined law is DERIVED from its two actual
conditional mass pins. Equality is only on the original Haar carrier. -/
theorem tower_mass_pin (tail inner outer : Nat) (W R : RatPoly)
    (unitW : HaarCarrierEqv (tail+outer) (I inner W) polyOne)
    (unitR : HaarCarrierEqv tail (I outer R) polyOne) :
    HaarCarrierEqv tail (I (inner+outer) (towerWeight inner W R)) polyOne := by
  unfold towerWeight
  rw [heads_compose]
  have hinner : HaarCarrierEqv (tail+outer)
      (I inner (polyMul W (liftBoundary inner R))) R :=
    (RatPolyCoeffEqv.haarCarrier (partialHaarHeads_mul_lift inner W R)).trans
      ((HaarCarrierEqv.mul_right R unitW).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul R)))
  exact (partialHaarHeads_carrier hinner).trans unitR

/-- The tower also holds for the ORIGINAL determinant consumed by the
reference-variance node, under the two actual conditional mass pins. -/
theorem determinant_tower_pin (tail inner outer : Nat) (W R p : RatPoly)
    (unitW : HaarCarrierEqv (tail+outer) (I inner W) polyOne)
    (unitR : HaarCarrierEqv tail (I outer R) polyOne) :
    HaarCarrierEqv tail (determinant (inner+outer) (towerWeight inner W R) p)
      (polyAdd (determinant outer R (mean inner W p))
        (mean outer R (determinant inner W p))) := by
  have hinner : HaarCarrierEqv tail (mean outer R (variance inner W p))
      (mean outer R (determinant inner W p)) :=
    partialHaarHeads_carrier (HaarCarrierEqv.mul_left R
      (determinant_variance_pin (tail+outer) inner W p unitW).symm)
  exact (determinant_variance_pin tail (inner+outer) (towerWeight inner W R) p
    (tower_mass_pin tail inner outer W R unitW unitR)).trans
    ((RatPolyCoeffEqv.haarCarrier (variance_tower_pin inner outer W R p)).trans
      (HaarCarrierEqv.add
        (determinant_variance_pin tail outer R (mean inner W p) unitR).symm hinner))

#print axioms determinant_variance_pin
#print axioms variance_certificate
#print axioms weighted_jensen
#print axioms heads_compose
#print axioms tower_mean_pin
#print axioms variance_tower_pin
#print axioms tower_mass_pin
#print axioms determinant_tower_pin

end YMGap.Continuum.SU2QuaternionConditionalVarianceTower
