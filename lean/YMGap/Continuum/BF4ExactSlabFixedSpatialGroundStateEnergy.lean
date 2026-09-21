/-
# Exact endpoint-source split of the original temporal energy

For `a = V*g`, the original finite temporal energy is the bare product-heat
energy of `a*f`, plus the explicit defect measuring `P a - a`.  Both terms
retain the original spatial weight, terminal source, product kernel, and Haar
measure.  This is an algebraic identity: it neither assumes nor proves that
`a` is a ground state or an eigenvector of the kinetic map.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.QuaternionHaarWeightedAngularCancellation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
  (transferStep_eq_productMap original_quadratic_pin)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap productMap_congr)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angularSquare angularLaplacian)
open YMGap.Continuum.QuaternionHaarWeightedAngularCancellation (weighted_angular_cancellation)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight activeBlocks productMap weightedMass

/-- The complete lower endpoint source `V*g`. -/
def endpointSource (w : Q') (K width : Nat) (g : RatPoly) : RatPoly :=
  polyMul (spatialWeight w K width) g

/-- Product-heat energy of the complete endpoint-weighted test. -/
def bareEnergy (w : Q') (K width : Nat) (g f : RatPoly) : Q' :=
  let a := endpointSource w K width g
  let u := polyMul a f
  quaternionHaar (N width) (polyMul u u) +
    -(quaternionHaar (N width)
      (polyMul u (productMap (N width) w K (activeBlocks width) u)))

/-- The exact failure of the endpoint source to be fixed by the bare kinetic
map.  No sign is asserted for this term. -/
def correction (w : Q') (K width : Nat) (g f : RatPoly) : Q' :=
  let a := endpointSource w K width g
  let Pa := productMap (N width) w K (activeBlocks width) a
  quaternionHaar (N width)
    (polyMul (polyMul a (polyMul f f)) (polyAdd Pa (polyNeg a)))

private theorem source_test (w : Q') (K width : Nat) (g f : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (spatialWeight w K width) (polyMul g f))
      (polyMul (endpointSource w K width g) f) :=
  (RatPolyCoeffEqv.mul_assoc _ _ _).symm

private theorem first_pin (w : Q') (K width : Nat) (g f : RatPoly) :
    weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) (polyMul f f)) ≈
      quaternionHaar (N width)
        (polyMul (polyMul (endpointSource w K width g) (polyMul f f))
          (productMap (N width) w K (activeBlocks width)
            (endpointSource w K width g))) := by
  unfold weightedMass
  rw [transferStep_eq_productMap]
  apply haar_of_coeff
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 2))))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2))) (.var 3))
    (by decide) (fun
      | 0 => spatialWeight w K width
      | 1 => g
      | 2 => f
      | _ => productMap (N width) w K (activeBlocks width)
          (polyMul (spatialWeight w K width) g))

private theorem second_pin (w : Q') (K width : Nat) (g f : RatPoly) :
    weightedMass w K width
      (polyMul (polyMul g f) (transferStep w K width (polyMul g f))) ≈
      let u := polyMul (endpointSource w K width g) f
      quaternionHaar (N width)
        (polyMul u (productMap (N width) w K (activeBlocks width) u)) := by
  let u := polyMul (endpointSource w K width g) f
  have hs := source_test w K width g f
  have hp := productMap_congr (N width) w K (activeBlocks width) hs
  exact Q'.eqv_trans _ _ _ (original_quadratic_pin w K width (polyMul g f))
    (haar_of_coeff (hs.mul hp))

private theorem square_reorder (a f : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a (polyMul f f)) a)
      (polyMul (polyMul a f) (polyMul a f)) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (by decide) (fun | 0 => a | _ => f)

private theorem neg_one_mul (x : Q') : (-1 : Q') * x ≈ -x :=
  poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
    (by decide) (fun _ => x)

private theorem correction_expand (w : Q') (K width : Nat) (g f : RatPoly) :
    correction w K width g f ≈
      let a := endpointSource w K width g
      let u := polyMul a f
      let Pa := productMap (N width) w K (activeBlocks width) a
      quaternionHaar (N width) (polyMul (polyMul a (polyMul f f)) Pa) +
        -(quaternionHaar (N width) (polyMul u u)) := by
  let a := endpointSource w K width g
  let u := polyMul a f
  let Pa := productMap (N width) w K (activeBlocks width) a
  unfold correction
  have he : RatPolyCoeffEqv
      (polyMul (polyMul a (polyMul f f)) (polyAdd Pa (polyNeg a)))
      (polyAdd (polyMul (polyMul a (polyMul f f)) Pa)
        (polySmul (-1) (polyMul u u))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.mul_left (polyMul a (polyMul f f)) (neg_smul a)).trans
          ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
            ((square_reorder a f).smul (-1)))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) (-1) _)
          (neg_one_mul _))))

/-- Exact finite split of the original temporal energy.  The correction is
kept explicit; the theorem has no support, positivity, or eigenvector premise. -/
theorem energy_eq_bare_add_correction (w : Q') (K width : Nat) (g f : RatPoly) :
    energy w K width g f ≈
      bareEnergy w K width g f + correction w K width g f := by
  let a := endpointSource w K width g
  let u := polyMul a f
  let Pa := productMap (N width) w K (activeBlocks width) a
  let first := quaternionHaar (N width) (polyMul (polyMul a (polyMul f f)) Pa)
  let square := quaternionHaar (N width) (polyMul u u)
  let mixed := quaternionHaar (N width)
    (polyMul u (productMap (N width) w K (activeBlocks width) u))
  have hfirst : weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) (polyMul f f)) ≈ first :=
    first_pin w K width g f
  have hmixed : weightedMass w K width
      (polyMul (polyMul g f) (transferStep w K width (polyMul g f))) ≈ mixed :=
    second_pin w K width g f
  have hcorr : correction w K width g f ≈ first + -square :=
    correction_expand w K width g f
  unfold energy bareEnergy
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hfirst (Q'.neg_eqv_congr _ _ hmixed))
    (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 1) (.neg (.var 2))) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => first | 1 => square | _ => mixed))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hcorr.symm))

/-- On the same original source `a=V*g`, its weight derivatives cancel from
the corrected head-angular form. The single geometric guard supplies a head
block; this does not identify the angular Laplacian with the finite P. -/
theorem endpoint_angular_cancellation (w : Q') (K width : Nat) (g f : RatPoly)
    (hb : 0 < N width) :
    let a := endpointSource w K width g
    quaternionHaar (N width) (angularSquare (polyMul a f)) +
      quaternionHaar (N width)
        (polyMul (polyMul a (polyMul f f)) (angularLaplacian a)) ≈
      quaternionHaar (N width) (polyMul (polyMul a a) (angularSquare f)) := by
  have hN : N width - 1 + 1 = N width := by omega
  simpa only [hN] using
    weighted_angular_cancellation (N width - 1) (endpointSource w K width g) f

end YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy.endpointSource
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy.bareEnergy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy.correction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy.energy_eq_bare_add_correction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy.endpoint_angular_cancellation
