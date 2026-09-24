/-
# Source geometry for one actual fixed-spatial plaquette

The literal fundamental plaquette has square cap four on the original product
Haar carrier.  Multiplying that certificate by an arbitrary supported source
square gives two positive raw source quantities: its mass and the geometric
defect `H[q^2 (4-f^2)]`.  The exact plaquette channel cost is also collected
into these same mass and plaquette-square moments.

These are unnormalised source-dependent Haar quantities.  No comparison with
the interacting centered variance, scaling limit, or continuum theory is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect (plaquetteSquareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)

/-- Raw source-square mass on the actual base-link Haar carrier. -/
def rawSourceMass (width : Nat) (q : RatPoly) : Q' :=
  H width (polyMul (polyMul q q) polyOne)

/-- The same source square weighted by the literal plaquette square. -/
def rawSourceSquare (width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  let f := characterPolynomial (plaquette width face).scalar 1
  H width (polyMul (polyMul q q) (polyMul f f))

/-- The geometric source defect `4 H[q^2] - H[q^2 f^2]`. -/
def geometricSourceCost (width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  (4 : Q') * rawSourceMass width q + -rawSourceSquare width face q

/-- Every supported source has nonnegative raw Haar square mass. -/
theorem rawSourceMass_nonnegative (width : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    (0 : Q') ≤ rawSourceMass width q := by
  have hn := (Certificate.square q hq).haar_nonnegative
  have he : H width (polyMul q q) ≈ rawSourceMass width q :=
    Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul q q)))
  exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he)

/-- The square-cap certificate identifies the geometric cost with the Haar
integral of the explicitly positive polynomial `q^2 (4-f^2)`. -/
theorem geometricSourceCost_eq_haar_gap (width : Nat) (face : Z4Plaq) (q : RatPoly) :
    geometricSourceCost width face q ≈
      H width (polyMul (polyMul q q)
        (gap 4 (characterPolynomial (plaquette width face).scalar 1))) := by
  let f := characterPolynomial (plaquette width face).scalar 1
  let q2 := polyMul q q
  let A := H width (polyMul q2 polyOne)
  let F := H width (polyMul q2 (polyMul f f))
  have hcap : H width (polyMul q2 (cap 4)) ≈ (4 : Q') * A := by
    unfold cap
    exact quaternionHaar_polyMul_smul_right (N width) 4 q2 polyOne
  have hneg : H width (polyMul q2 (polyNeg (polyMul f f))) ≈ -F :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl q2).mul (neg_smul (polyMul f f))))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_smul_right (N width) (-1) q2 (polyMul f f))
        (poly_identity_of_normal_eq
          (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => F)))
  have hgap : H width (polyMul q2 (gap 4 f)) ≈ (4 : Q') * A + -F :=
    Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right (N width) q2 (cap 4)
        (polyNeg (polyMul f f)))
      (Q'.add_eqv_congr' hcap hneg)
  exact Q'.eqv_symm hgap

/-- The actual plaquette square cap makes the geometric source cost
nonnegative for every supported source. -/
theorem geometricSourceCost_nonnegative (width : Nat) (face : Z4Plaq) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    (0 : Q') ≤ geometricSourceCost width face q := by
  have hn := ((Certificate.square q hq).mul
    (plaquetteSquareBound width face).certificate).haar_nonnegative
  exact Q'.le_trans' _ _ _ hn
    (Q'.le_of_eqv (Q'.eqv_symm (geometricSourceCost_eq_haar_gap width face q)))

/-- Exact collected form of the already-computed plaquette channel cost.
No face-membership or heat-cutoff premise is needed for this algebra. -/
theorem plaquetteChannelCost_collected (w : Q') (width : Nat)
    (face : Z4Plaq) (q : RatPoly) :
    plaquetteChannelCost width face w q ≈
      ((1 : Q') - qpow w 32) * rawSourceMass width q +
      ((1 : Q') + qpow w 32 - (2 : Q') * qpow w 12) *
        rawSourceSquare width face q := by
  let p := (plaquette width face).scalar
  let f := characterPolynomial p 1
  let chi2 := characterPolynomial p 2
  let A := rawSourceMass width q
  let F := rawSourceSquare width face q
  have hcenter : RatPolyCoeffEqv chi2
      (polyAdd (polyMul f f) (polySmul (-1) polyOne)) := by
    have hpad0 : RatPolyCoeffEqv chi2
        (polyAdd (polyAdd polyOne chi2) (polyMul (cap (-1)) polyOne)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.var 0) (.add (.add (.var 1) (.var 0))
          (.mul (.const (-1)) (.var 1))) (by decide)
        (fun | 0 => chi2 | _ => polyOne)
    have hpad : RatPolyCoeffEqv chi2
        (polyAdd (polyAdd polyOne chi2) (polySmul (-1) polyOne)) :=
      hpad0.trans ((RatPolyCoeffEqv.refl _).add (cap_mul_left (-1) polyOne))
    exact hpad.trans
      ((first_character_square p).symm.add
        (RatPolyCoeffEqv.refl (polySmul (-1) polyOne)))
  have hnegative :
      H width (polyMul (polyMul q q) (polySmul (-1) polyOne)) ≈ -A :=
    Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_smul_right (N width) (-1) (polyMul q q) polyOne)
      (poly_identity_of_normal_eq
        (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => A))
  have hchi : H width (polyMul (polyMul q q) chi2) ≈ F + -A :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl (polyMul q q)).mul hcenter))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_add_right (N width) (polyMul q q)
          (polyMul f f) (polySmul (-1) polyOne))
        (Q'.add_eqv_congr_left _ _ _ hnegative))
  have hassoc :
      H width (polyMul (polyMul (polyMul q q) f) f) ≈ F :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc (polyMul q q) f f)
  unfold plaquetteChannelCost
  dsimp only
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left F _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left A _ _
          (Q'.mul_eqv_congr_left (qpow w 32) _ _ hchi))
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _
          (Q'.mul_eqv_congr_left (qpow w 12) _ _ hassoc)))))
    (poly_identity_of_normal_eq
      (.add (.var 1)
        (.add
          (.add (.var 0) (.mul (.var 2) (.add (.var 1) (.neg (.var 0)))))
          (.neg (.mul (.const 2) (.mul (.var 3) (.var 1))))))
      (.add
        (.mul (.add (.const 1) (.neg (.var 2))) (.var 0))
        (.mul
          (.add (.add (.const 1) (.var 2))
            (.neg (.mul (.const 2) (.var 3)))) (.var 1)))
      (by decide)
      (fun | 0 => A | 1 => F | 2 => qpow w 32 | _ => qpow w 12))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.rawSourceMass
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.rawSourceSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.geometricSourceCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.rawSourceMass_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.geometricSourceCost_eq_haar_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.geometricSourceCost_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.plaquetteChannelCost_collected
