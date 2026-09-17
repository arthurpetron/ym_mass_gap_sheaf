/-
# Original edge energy dominates its full spatially weighted product variance

The certified residual K-kineticFloor is multiplied by BOTH complete
endpoint weights Vg and by the squared jump. Exact product-Haar integration
identifies the removed constant-kernel term with twice the unnormalized
Vg-variance. Cancelling only the positive rational 2 yields the displayed
energy lower bound. No spatial factor, conditional mean or denominator is
replaced. The floor retains its actual width and nome dependence.

This is a finite original-action estimate, not a width-independent gap,
a stationary-vacuum construction or a continuum/physical-mass assertion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.SU2QuaternionHaarMarkovContraction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction (haar_split_pairing)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem variance_algebra (a b f h : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul a b) (polyMul (polyAdd f (polyNeg h)) (polyAdd f (polyNeg h))))
      (polyAdd (polyMul (polyMul a (polyMul f f)) b)
        (polyAdd (polyNeg (polyMul (polyMul a f) (polyMul b h)))
          (polyAdd (polyNeg (polyMul (polyMul a f) (polyMul b h)))
            (polyMul a (polyMul b (polyMul h h)))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1))
      (.mul (.add (.var 2) (.neg (.var 3))) (.add (.var 2) (.neg (.var 3)))))
    (.add (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
      (.add (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
        (.add (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
          (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))))))
    (by decide) (fun | 0 => a | 1 => b | 2 => f | _ => h)

private theorem twice_variance (a b c : Q') :
    c*a + (-(b*b) + (-(b*b) + a*c)) ≈ (2 : Q')*(a*c + -(b*b)) :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 2) (.var 0))
      (.add (.neg (.mul (.var 1) (.var 1)))
        (.add (.neg (.mul (.var 1) (.var 1))) (.mul (.var 0) (.var 2)))))
    (.mul (.const 2) (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
    (by decide) (fun | 0 => a | 1 => b | _ => c)

private theorem product_variance {blocks : Nat} {a f : RatPoly}
    (ha : SupportedQuaternionBlocks blocks a) (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar (blocks+blocks)
      (polyMul (polyMul a (liftBoundary blocks a))
        (polyMul (polyAdd f (polyNeg (liftBoundary blocks f)))
          (polyAdd f (polyNeg (liftBoundary blocks f))))) ≈
      (2 : Q') * (quaternionHaar blocks a * quaternionHaar blocks (polyMul a (polyMul f f)) +
        -(quaternionHaar blocks (polyMul a f) * quaternionHaar blocks (polyMul a f))) := by
  have hp : RatPolyCoeffEqv
      (polyMul (polyMul a (liftBoundary blocks a))
        (polyMul (polyAdd f (polyNeg (liftBoundary blocks f)))
          (polyAdd f (polyNeg (liftBoundary blocks f)))))
      (polyAdd (polyMul (polyMul a (polyMul f f)) (liftBoundary blocks a))
        (polyAdd (polyNeg (polyMul (polyMul a f) (liftBoundary blocks (polyMul a f))))
          (polyAdd (polyNeg (polyMul (polyMul a f) (liftBoundary blocks (polyMul a f))))
            (polyMul a (liftBoundary blocks (polyMul a (polyMul f f))))))) := by
    simpa only [lift_product] using variance_algebra a (liftBoundary blocks a) f (liftBoundary blocks f)
  have hfirst := haar_split_pairing (supported_polyMul ha (supported_polyMul hf hf)) a
  have hcross := haar_split_pairing (supported_polyMul ha hf) (polyMul a f)
  have hlast := haar_split_pairing ha (polyMul a (polyMul f f))
  have hneg := Q'.eqv_trans _ _ _ (haar_neg (blocks+blocks) _)
    (Q'.neg_eqv_congr _ _ hcross)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hfirst
          (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
            (Q'.add_eqv_congr' hneg
              (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
                (Q'.add_eqv_congr' hneg hlast)))))
        (twice_variance _ _ _)))

/-- Exact independent-endpoint variance with the SAME complete spatial Vg.
No positivity or normalization is needed for this identity. -/
theorem independent_jump_identity (w : Q') (K width : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width+N width)
      (polyMul
        (polyMul (polyMul (spatialWeight w K width) g)
          (liftBoundary (N width) (polyMul (spatialWeight w K width) g)))
        (polyMul (jump width f) (jump width f))) ≈
      (2 : Q') * (weightedMass w K width g * weightedMass w K width (polyMul g (polyMul f f)) +
        -(weightedMass w K width (polyMul g f) * weightedMass w K width (polyMul g f))) := by
  have h := product_variance (supported_polyMul (spatialWeight_supported w K width) hg) hf
  have hm : quaternionHaar (N width) (polyMul (spatialWeight w K width) g) ≈
      weightedMass w K width g := by unfold weightedMass; exact Q'.eqv_refl _
  have hf1 : quaternionHaar (N width) (polyMul (polyMul (spatialWeight w K width) g) f) ≈
      weightedMass w K width (polyMul g f) := by
    unfold weightedMass
    exact haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)
  have hf2 : quaternionHaar (N width)
      (polyMul (polyMul (spatialWeight w K width) g) (polyMul f f)) ≈
      weightedMass w K width (polyMul g (polyMul f f)) := by
    unfold weightedMass
    exact haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)
  exact Q'.eqv_trans _ _ _ h
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr' (qmul hm hf2) (Q'.neg_eqv_congr _ _ (qmul hf1 hf1))))

private theorem residual_algebra (k c a b s : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (polyAdd k (polyNeg c)) (polyMul a b)) s)
      (polyAdd (polyMul (polyMul (polyMul k a) b) s)
        (polyNeg (polyMul c (polyMul (polyMul a b) s)))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.add (.var 0) (.neg (.var 1))) (.mul (.var 2) (.var 3))) (.var 4))
    (.add (.mul (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.var 4))
      (.neg (.mul (.var 1) (.mul (.mul (.var 2) (.var 3)) (.var 4)))))
    (by decide) (fun | 0 => k | 1 => c | 2 => a | 3 => b | _ => s)

private theorem residual_haar (blocks : Nat) (k a b s : RatPoly) (c : Q') :
    quaternionHaar blocks (polyMul (polyMul (polyAdd k (polyNeg (cap c))) (polyMul a b)) s) ≈
      quaternionHaar blocks (polyMul (polyMul (polyMul k a) b) s) +
        -(c * quaternionHaar blocks (polyMul (polyMul a b) s)) := by
  have hc := Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c (polyMul (polyMul a b) s)))
    (quaternionHaar_polySmul blocks c _)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (residual_algebra k (cap c) a b s))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_neg blocks _) (Q'.neg_eqv_congr _ _ hc))))

private theorem scale_two (a b : Q') : a*((2 : Q')*b) ≈ (2 : Q')*(a*b) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.const 2) (.var 1)))
    (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
    (fun | 0 => a | _ => b)

/-- The actual kinetic floor controls the complete original Vg-variance.
There is no denominator and no unproved energy/coercivity input. -/
theorem energy_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (G : Certificate (N width) g) :
    kineticFloor w width *
      (weightedMass w K width g * weightedMass w K width (polyMul g (polyMul f f)) +
        -(weightedMass w K width (polyMul g f) * weightedMass w K width (polyMul g f))) ≤
      energy w K width g f := by
  let a := polyMul (spatialWeight w K width) g
  let b := liftBoundary (N width) a
  let s := polyMul (jump width f) (jump width f)
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width) hg
  let A : Certificate (N width) a :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul G
  let R := ((kineticFloorCertificate hw0 hw1 K width hK).mul
    ((certificate_extend (N width) ha A).mul (lift_certificate (N width) A))).mul
      (Certificate.square (jump width f) (jump_supported width hf))
  have hr := residual_haar (N width+N width) (kineticWeight w K width) a b s (kineticFloor w width)
  have hl : kineticFloor w width * quaternionHaar (N width+N width) (polyMul (polyMul a b) s) ≤
      quaternionHaar (N width+N width) (polyMul (edgeDensity w K width g) s) :=
    Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ R.haar_nonnegative (Q'.le_of_eqv hr))
  have hleft := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (kineticFloor w width) _ _ (independent_jump_identity w K width hg hf))
    (scale_two (kineticFloor w width) _)
  have htwo := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
    (Q'.le_trans' _ _ _ hl (Q'.le_of_eqv (Q'.eqv_symm (energy_identity w K width hg hf))))
  exact Q'.le_of_mul_le_mul_left htwo (by decide)

end YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletFloor

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletFloor.independent_jump_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletFloor.energy_floor
