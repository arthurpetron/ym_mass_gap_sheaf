/-
# Innovation comparison for the original non-unit-mass conditional tower

The joined density is W*lift(R), with its ACTUAL conditional mass.
For any middle polynomial phi, retain e=I(W*p)-I(W)*phi and its signed
outer covariance. A two-copy square constructs
  det(joined,p) - det(R*I(W),phi) - 2*Cov >= 0.
The remainder is exactly det(joined,p-lift(phi)), not a reconstruction
error asserted to vanish. No unit-mass pin, inverse, or exact quotient occurs.

This is finite Haar-cone positivity with arbitrary shared tails. It does
not supply smallness of the covariance/history or a scaling-family estimate.
-/

import YMGap.Continuum.SU2QuaternionConditionalVarianceTower
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.SU2QuaternionUnnormalizedVarianceTower

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
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionConditionalVarianceTower (mean towerWeight heads_compose tower_mean_pin)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant determinant_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "I" heads:arg p:arg => partialHaarHeads heads p

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private theorem mean_congr (heads : Nat) (W : RatPoly) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (mean heads W p) (mean heads W q) :=
  partialHaarHeads_congr heads (h.mul_left W)

private theorem mean_sub (heads : Nat) (W p q : RatPoly) :
    RatPolyCoeffEqv (mean heads W (polyAdd p (polyNeg q)))
      (polyAdd (mean heads W p) (polyNeg (mean heads W q))) := by
  have he := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
    (by decide) (fun | 0 => W | 1 => p | _ => q)
  refine (partialHaarHeads_congr heads he).trans ?_
  dsimp only [coeffEvalExpr]
  rw [partialHaarHeads_add]
  exact (RatPolyCoeffEqv.refl _).add (partialHaarHeads_neg heads _)

private def covariance (heads : Nat) (W p q : RatPoly) : RatPoly :=
  polyAdd (polyMul (I heads W) (mean heads W (polyMul p q)))
    (polyNeg (polyMul (mean heads W p) (mean heads W q)))

private theorem determinant_sub_pin (heads : Nat) (W p q : RatPoly) :
    let z := polyAdd p (polyNeg q)
    let C := covariance heads W q z
    RatPolyCoeffEqv (determinant heads W z)
      (polyAdd (determinant heads W p)
        (polyNeg (polyAdd (determinant heads W q) (polyAdd C C)))) := by
  dsimp only
  let z := polyAdd p (polyNeg q)
  let A := I heads W
  let P := mean heads W p
  let Q := mean heads W q
  let H := mean heads W (polyMul p p)
  let J := mean heads W (polyMul p q)
  let F := mean heads W (polyMul q q)
  have hm := mean_sub heads W p q
  have hs : RatPolyCoeffEqv (mean heads W (polyMul z z))
      (polyAdd (polyAdd (polyAdd H (polyNeg J)) (polyNeg J)) F) := by
    have he := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2)))
        (.add (.var 1) (.neg (.var 2)))))
      (.add (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.neg (.mul (.var 0) (.mul (.var 1) (.var 2)))))
        (.neg (.mul (.var 0) (.mul (.var 1) (.var 2)))))
        (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => W | 1 => p | _ => q)
    refine (partialHaarHeads_congr heads he).trans ?_
    dsimp only [coeffEvalExpr]
    rw [partialHaarHeads_add, partialHaarHeads_add, partialHaarHeads_add]
    exact (((RatPolyCoeffEqv.refl _).add (partialHaarHeads_neg heads _)).add
      (partialHaarHeads_neg heads _)).add (RatPolyCoeffEqv.refl _)
  have hx : RatPolyCoeffEqv (mean heads W (polyMul q z)) (polyAdd J (polyNeg F)) := by
    have he := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 2) (.add (.var 1) (.neg (.var 2)))))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.var 0) (.mul (.var 2) (.var 2)))))
      (by decide) (fun | 0 => W | 1 => p | _ => q)
    refine (partialHaarHeads_congr heads he).trans ?_
    dsimp only [coeffEvalExpr]
    rw [partialHaarHeads_add]
    exact (RatPolyCoeffEqv.refl _).add (partialHaarHeads_neg heads _)
  have hleft := ((RatPolyCoeffEqv.refl A).mul hs).add (RatPolyCoeffEqv.neg (hm.mul hm))
  have hc := ((RatPolyCoeffEqv.refl A).mul hx).add
    (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.refl Q).mul hm))
  have hright := (RatPolyCoeffEqv.refl (determinant heads W p)).add
    (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.refl (determinant heads W q)).add (hc.add hc)))
  let dz : PolyExpr := .add
    (.mul (.var 0) (.add (.add (.add (.var 1) (.neg (.var 2))) (.neg (.var 2))) (.var 3)))
    (.neg (.mul (.add (.var 4) (.neg (.var 5))) (.add (.var 4) (.neg (.var 5)))))
  let dp : PolyExpr := .add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 4) (.var 4)))
  let dq : PolyExpr := .add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 5) (.var 5)))
  let ce : PolyExpr := .add (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))
    (.neg (.mul (.var 5) (.add (.var 4) (.neg (.var 5)))))
  have hring := coeffEvalExpr_eqv_of_normalize_eq dz (.add dp (.neg (.add dq (.add ce ce))))
    (by decide) (fun | 0 => A | 1 => H | 2 => J | 3 => F | 4 => P | _ => Q)
  exact hleft.trans (hring.trans hright.symm)

/-- Signed covariance caused by the ACTUAL middle prediction error.
Neither phi nor its finite reciprocal construction is treated as b/a. -/
def innovationCovariance (inner outer : Nat) (W R p phi : RatPoly) : RatPoly :=
  let a := I inner W
  let b := mean inner W p
  let e := polyAdd b (polyNeg (polyMul a phi))
  let A := mean outer R a
  let v := mean outer R (polyMul a phi)
  let z := mean outer R e
  polyAdd (polyMul A (mean outer R (polyMul phi e))) (polyNeg (polyMul v z))

/-- Original non-unit-mass innovation comparison, constructed from the
actual joined law and its residual square. The historical variance is not
silently identified with an error that vanishes as prediction improves. -/
def innovation_certificate (tail inner outer : Nat) (W R p phi : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+outer+inner) W)
    (hR : SupportedQuaternionBlocks (tail+outer) R)
    (hp : SupportedQuaternionBlocks (tail+outer+inner) p)
    (hphi : SupportedQuaternionBlocks (tail+outer) phi)
    (PW : Certificate (tail+outer+inner) W) (PR : Certificate (tail+outer) R) :
    let C := innovationCovariance inner outer W R p phi
    Certificate tail (polyAdd (determinant (inner+outer) (towerWeight inner W R) p)
      (polyNeg (polyAdd (determinant outer (polyMul R (I inner W)) phi) (polyAdd C C)))) := by
  dsimp only
  let a := I inner W
  let q := liftBoundary inner phi
  let z := polyAdd p (polyNeg q)
  let e := polyAdd (mean inner W p) (polyNeg (polyMul a phi))
  let J := towerWeight inner W R
  have hsize : tail+outer+inner = tail+(inner+outer) := by omega
  have hJ : SupportedQuaternionBlocks (tail+(inner+outer)) J :=
    hsize ▸ supported_polyMul hW (lift_supported hR inner)
  have hz : SupportedQuaternionBlocks (tail+(inner+outer)) z :=
    hsize ▸ supported_add hp (support_neg (lift_supported hphi inner))
  have PJ : Certificate (tail+(inner+outer)) J :=
    hsize ▸ PW.mul (lift_certificate inner PR)
  have Pos := determinant_certificate tail (inner+outer) J z hJ hz PJ
  have hmass : RatPolyCoeffEqv (I (inner+outer) J) (mean outer R a) := by
    unfold J towerWeight
    rw [heads_compose]
    exact (partialHaarHeads_congr outer (partialHaarHeads_mul_lift inner W R)).trans
      (partialHaarHeads_congr outer (RatPolyCoeffEqv.mul_comm a R))
  have middle (f : RatPoly) : RatPolyCoeffEqv
      (mean (inner+outer) J (liftBoundary inner f)) (mean outer R (polyMul a f)) :=
    (tower_mean_pin inner outer W R (liftBoundary inner f)).trans
      (mean_congr outer R (partialHaarHeads_mul_lift inner W f))
  have assoc (f : RatPoly) : RatPolyCoeffEqv
      (mean outer R (polyMul a f)) (mean outer (polyMul R a) f) :=
    partialHaarHeads_congr outer (RatPolyCoeffEqv.mul_assoc R a f).symm
  have hq := (middle phi).trans (assoc phi)
  have hlift : RatPolyCoeffEqv (polyMul q q) (liftBoundary inner (polyMul phi phi)) := by
    rw [lift_product]
    exact RatPolyCoeffEqv.refl _
  have hq2 := ((mean_congr (inner+outer) J hlift).trans
    (middle (polyMul phi phi))).trans (assoc (polyMul phi phi))
  have hdet : RatPolyCoeffEqv (determinant (inner+outer) J q)
      (determinant outer (polyMul R a) phi) :=
    (hmass.mul hq2).add (RatPolyCoeffEqv.neg (hq.mul hq))
  have he : RatPolyCoeffEqv (mean inner W z) e :=
    (mean_sub inner W p q).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (partialHaarHeads_mul_lift inner W phi)))
  have hzmean := (tower_mean_pin inner outer W R z).trans (mean_congr outer R he)
  have hcross : RatPolyCoeffEqv (mean (inner+outer) J (polyMul q z))
      (mean outer R (polyMul phi e)) := by
    have hreorder : RatPolyCoeffEqv (polyMul W (polyMul q z))
        (polyMul (polyMul W z) q) :=
      coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => W | 1 => q | _ => z)
    have hi := (partialHaarHeads_congr inner hreorder).trans
      ((partialHaarHeads_mul_lift inner (polyMul W z) phi).trans
        ((he.mul_right phi).trans (RatPolyCoeffEqv.mul_comm e phi)))
    exact (tower_mean_pin inner outer W R (polyMul q z)).trans (mean_congr outer R hi)
  have hc : RatPolyCoeffEqv (covariance (inner+outer) J q z)
      (innovationCovariance inner outer W R p phi) :=
    (hmass.mul hcross).add (RatPolyCoeffEqv.neg ((middle phi).mul hzmean))
  have hpin := (determinant_sub_pin (inner+outer) J p q).trans
    ((RatPolyCoeffEqv.refl (determinant (inner+outer) J p)).add
      (RatPolyCoeffEqv.neg (hdet.add (hc.add hc))))
  exact Certificate.ofCoeff hpin.symm Pos

end YMGap.Continuum.SU2QuaternionUnnormalizedVarianceTower

#print axioms YMGap.Continuum.SU2QuaternionUnnormalizedVarianceTower.innovationCovariance
#print axioms YMGap.Continuum.SU2QuaternionUnnormalizedVarianceTower.innovation_certificate
