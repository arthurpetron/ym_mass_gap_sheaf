/-
# An auxiliary physical plaquette has a negative centered Ward residual

The weight below uses the literal four-link fundamental character and a
linear coefficient parameter.  It is not a Wilson terminal message.  The
calculation rules out a source-independent favorable sign for the integrated
projected Ward residual; it makes no claim about the actual terminal source,
nor a checked heat-image or positivity certificate for every parameter.
-/

import YMGap.Continuum.SU2QuaternionPlaquetteQuarticHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.QuaternionHaarNormalizedCenter

namespace YMGap.Continuum.SU2QuaternionPlaquetteAuxiliaryWardSign

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCurvature
open YMGap.Continuum.SU2QuaternionPlaquetteQuarticHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff haar_of_carrier)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)

private def quarter : Q' := Q'.mkPos 1 4 (by decide)
private def eighth : Q' := Q'.mkPos 1 8 (by decide)
private def sixteenth : Q' := Q'.mkPos 1 16 (by decide)
private def threeQuarters : Q' := Q'.mkPos 3 4 (by decide)

/-- A linear auxiliary factor on the original physical face. -/
def linearSource (a : Q') (f : RatPoly) : RatPoly :=
  polyAdd polyOne (polyMul (cap a) f)

def auxiliaryWeight (lambda : Q') (f : RatPoly) : RatPoly :=
  polyMul (linearSource quarter f) (linearSource (quarter*lambda) f)

private theorem weighted_monomial (blocks : Nat) (a b : Q') (f g : RatPoly) :
    quaternionHaar blocks
      (polyMul (polyMul (linearSource a f) (linearSource b f)) g) ≈
    quaternionHaar blocks g +
      (a * quaternionHaar blocks (polyMul f g) +
        (b * quaternionHaar blocks (polyMul f g) +
          a * (b * quaternionHaar blocks (polyMul (polyMul f f) g)))) := by
  have he : RatPolyCoeffEqv
      (polyMul (polyMul (linearSource a f) (linearSource b f)) g)
      (polyAdd g
        (polyAdd (polyMul (cap a) (polyMul f g))
          (polyAdd (polyMul (cap b) (polyMul f g))
            (polyMul (cap a) (polyMul (cap b) (polyMul (polyMul f f) g)))))) := by
    unfold linearSource
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.add (.const 1) (.mul (.var 0) (.var 2)))
        (.add (.const 1) (.mul (.var 1) (.var 2)))) (.var 3))
      (.add (.var 3)
        (.add (.mul (.var 0) (.mul (.var 2) (.var 3)))
          (.add (.mul (.var 1) (.mul (.var 2) (.var 3)))
            (.mul (.var 0) (.mul (.var 1)
              (.mul (.mul (.var 2) (.var 2)) (.var 3)))))))
      (by decide) (fun | 0 => cap a | 1 => cap b | 2 => f | _ => g)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks) he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks)
              (cap_mul_left a (polyMul f g)))
              (quaternionHaar_polySmul blocks a _))
            (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
              (Q'.add_eqv_congr'
                (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks)
                  (cap_mul_left b (polyMul f g)))
                  (quaternionHaar_polySmul blocks b _))
                (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks)
                  (cap_mul_left a _))
                  (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks a _)
                    (Q'.mul_eqv_congr_left a _ _
                      (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks)
                        (cap_mul_left b _))
                        (quaternionHaar_polySmul blocks b _)))))))))))

private theorem weighted_values (width : Nat) (face : Z4Plaq)
    (lambda : Q') (g : RatPoly) (v0 v1 v2 : Q')
    (h0 : H width g ≈ v0)
    (h1 : H width (polyMul (characterPolynomial (plaquette width face).scalar 1) g) ≈ v1)
    (h2 : H width (polyMul
      (polyMul (characterPolynomial (plaquette width face).scalar 1)
        (characterPolynomial (plaquette width face).scalar 1)) g) ≈ v2) :
    H width (polyMul (auxiliaryWeight lambda
      (characterPolynomial (plaquette width face).scalar 1)) g) ≈
      v0 + (quarter*v1 + ((quarter*lambda)*v1 +
        quarter*((quarter*lambda)*v2))) := by
  exact Q'.eqv_trans _ _ _
    (weighted_monomial (N width) quarter (quarter*lambda)
      (characterPolynomial (plaquette width face).scalar 1) g)
    (Q'.add_eqv_congr' h0
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left quarter _ _ h1)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left (quarter*lambda) _ _ h1)
          (Q'.mul_eqv_congr_left quarter _ _
            (Q'.mul_eqv_congr_left (quarter*lambda) _ _ h2)))))

private theorem scalar_moment (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q') (g : RatPoly)
    (hg0 : H width g ≈ 1)
    (hg1 : H width (polyMul (characterPolynomial (plaquette width face).scalar 1) g) ≈ 0)
    (hg2 : H width (polyMul
      (polyMul (characterPolynomial (plaquette width face).scalar 1)
        (characterPolynomial (plaquette width face).scalar 1)) g) ≈ 1) :
    H width (polyMul (auxiliaryWeight lambda
      (characterPolynomial (plaquette width face).scalar 1)) g) ≈
      1 + sixteenth*lambda := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have hring : 1 + (quarter*0 +
      ((quarter*lambda)*0 + quarter*((quarter*lambda)*1))) ≈
      1+(quarter*quarter)*lambda :=
    poly_identity_of_normal_eq
      (.add (.const 1)
        (.add (.mul (.var 0) (.const 0))
          (.add (.mul (.mul (.var 0) (.var 1)) (.const 0))
            (.mul (.var 0)
              (.mul (.mul (.var 0) (.var 1)) (.const 1))))))
      (.add (.const 1) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => quarter | _ => lambda)
  have hcoef : quarter*quarter ≈ sixteenth := by decide
  exact Q'.eqv_trans _ _ _
    (weighted_values width face lambda g 1 0 1 hg0 hg1 hg2)
    (Q'.eqv_trans _ _ _ hring
      (Q'.add_eqv_congr' (Q'.eqv_refl 1)
        (Q'.mul_eqv_congr_right (quarter*quarter) sixteenth lambda hcoef)))

/-- Same physical plaquette, same auxiliary source: its exact Haar mass. -/
theorem auxiliary_mass (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q') :
    H width (auxiliaryWeight lambda
      (characterPolynomial (plaquette width face).scalar 1)) ≈
      1 + sixteenth*lambda := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have hone : H width polyOne ≈ 1 :=
    QPolyHaarPositiveSubstitution.haar_one (N width)
  have h1 : H width (polyMul f polyOne) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N width)
      (RatPolyCoeffEqv.mul_one f)) (plaquette_mean_zero width face hf)
  have h2 : H width (polyMul (polyMul f f) polyOne) ≈ 1 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N width)
      (RatPolyCoeffEqv.mul_one (polyMul f f)))
      (plaquette_square_one width face hf)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff (blocks := N width)
      (RatPolyCoeffEqv.mul_one (auxiliaryWeight lambda f))))
    (scalar_moment width face hf lambda polyOne hone h1 h2)

/-- The first source moment belongs to this same auxiliary physical weight. -/
theorem auxiliary_first (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q') :
    let f := characterPolynomial (plaquette width face).scalar 1
    H width (polyMul (auxiliaryWeight lambda f) f) ≈
      quarter*(1+lambda) := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  have h0 : H width f ≈ 0 := plaquette_mean_zero width face hf
  have h1 : H width (polyMul f f) ≈ 1 :=
    plaquette_square_one width face hf
  have h2 : H width (polyMul (polyMul f f) f) ≈ 0 :=
    plaquette_cubic_zero width face hf
  exact Q'.eqv_trans _ _ _
    (weighted_values width face lambda f 0 1 0 h0 h1 h2)
    (poly_identity_of_normal_eq
      (.add (.const 0)
        (.add (.mul (.var 0) (.const 1))
          (.add (.mul (.mul (.var 0) (.var 1)) (.const 1))
            (.mul (.var 0)
              (.mul (.mul (.var 0) (.var 1)) (.const 0))))))
      (.mul (.var 0) (.add (.const 1) (.var 1)))
      (by decide) (fun | 0 => quarter | _ => lambda))

/-- The second source moment retains the physical quartic Haar channel. -/
theorem auxiliary_second (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q') :
    let f := characterPolynomial (plaquette width face).scalar 1
    H width (polyMul (auxiliaryWeight lambda f) (polyMul f f)) ≈
      1 + eighth*lambda := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  have h0 : H width (polyMul f f) ≈ 1 :=
    plaquette_square_one width face hf
  have h1 : H width (polyMul f (polyMul f f)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (blocks := N width) (RatPolyCoeffEqv.mul_assoc f f f).symm)
      (plaquette_cubic_zero width face hf)
  have h2 : H width (polyMul (polyMul f f) (polyMul f f)) ≈ 2 :=
    plaquette_quartic_two width face hf
  have hring : 1+(quarter*0+((quarter*lambda)*0+
      quarter*((quarter*lambda)*2))) ≈
      1+((2*(quarter*quarter))*lambda) :=
    poly_identity_of_normal_eq
      (.add (.const 1)
        (.add (.mul (.var 0) (.const 0))
          (.add (.mul (.mul (.var 0) (.var 1)) (.const 0))
            (.mul (.var 0)
              (.mul (.mul (.var 0) (.var 1)) (.const 2))))))
      (.add (.const 1)
        (.mul (.mul (.const 2) (.mul (.var 0) (.var 0))) (.var 1)))
      (by decide) (fun | 0 => quarter | _ => lambda)
  have hcoef : 2*(quarter*quarter) ≈ eighth := by decide
  exact Q'.eqv_trans _ _ _
    (weighted_values width face lambda (polyMul f f) 1 0 2 h0 h1 h2)
    (Q'.eqv_trans _ _ _ hring
      (Q'.add_eqv_congr' (Q'.eqv_refl 1)
        (Q'.mul_eqv_congr_right (2*(quarter*quarter)) eighth lambda hcoef)))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_gamma_formula (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q') :
    let f := characterPolynomial (plaquette width face).scalar 1
    let U := auxiliaryWeight lambda f
    H width (polyMul U (activeGamma (List.range (N width)) f f)) ≈
      4 * (4 * H width U + -(H width (polyMul U (polyMul f f)))) := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  let U := auxiliaryWeight lambda f
  let f2 := polyMul f f
  let gap := polyAdd (cap 4) (polyNeg f2)
  have hgamma := plaquette_gamma width face hf
  have hright : H width (polyMul U (polySmul 4 gap)) ≈
      4 * (4 * H width U + -(H width (polyMul U f2))) := by
    have hgap : RatPolyCoeffEqv (polyMul U gap)
        (polyAdd (polyMul (cap 4) U) (polyNeg (polyMul U f2))) := by
      unfold gap
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => U | 1 => cap 4 | _ => f2)
    have hlinear : H width (polyMul U gap) ≈
        4 * H width U + -(H width (polyMul U f2)) :=
      Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N width) hgap)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N width)
              (cap_mul_left 4 U)) (quaternionHaar_polySmul (N width) 4 U))
            (haar_neg (N width) (polyMul U f2))))
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (blocks := N width)
        (RatPolyCoeffEqv.polyMul_smul_right 4 U gap))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) 4 (polyMul U gap))
        (Q'.mul_eqv_congr_left 4 _ _ hlinear))
  exact Q'.eqv_trans _ _ _
    (haar_of_carrier (HaarCarrierEqv.mul_left U hgamma)) hright

/-- Exact angular moment for the same literal four-link face and weight. -/
theorem auxiliary_angular (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q') :
    let f := characterPolynomial (plaquette width face).scalar 1
    H width (polyMul (auxiliaryWeight lambda f)
      (activeGamma (List.range (N width)) f f)) ≈
      12 + HalfPow.half*lambda := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  have hM := auxiliary_mass width face hf lambda
  have hS := auxiliary_second width face hf lambda
  have hring : 4*(4*(1+sixteenth*lambda)+-(1+eighth*lambda)) ≈
      12+(16*sixteenth+-(4*eighth))*lambda :=
    poly_identity_of_normal_eq
      (.mul (.const 4)
        (.add (.mul (.const 4)
          (.add (.const 1) (.mul (.var 0) (.var 2))))
          (.neg (.add (.const 1) (.mul (.var 1) (.var 2))))))
      (.add (.const 12)
        (.mul (.add (.mul (.const 16) (.var 0))
          (.neg (.mul (.const 4) (.var 1)))) (.var 2)))
      (by decide) (fun | 0 => sixteenth | 1 => eighth | _ => lambda)
  have hcoef : 16*sixteenth+-(4*eighth) ≈ HalfPow.half := by decide
  exact Q'.eqv_trans _ _ _ (weighted_gamma_formula width face hf lambda)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 4 _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left 4 _ _ hM)
          (Q'.neg_eqv_congr _ _ hS)))
      (Q'.eqv_trans _ _ _ hring
        (Q'.add_eqv_congr' (Q'.eqv_refl 12)
          (Q'.mul_eqv_congr_right
            (16*sixteenth+-(4*eighth)) HalfPow.half lambda hcoef))))

/-- Positive mass is proved for the source itself, then used for its own mean. -/
theorem auxiliary_mass_positive (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q')
    (hLambda : (0 : Q') ≤ lambda) :
    (0 : Q') < H width (auxiliaryWeight lambda
      (characterPolynomial (plaquette width face).scalar 1)) := by
  have hz : (0 : Q') < 1 + sixteenth*lambda :=
    Q'.pos_add_nonneg (by decide)
      (Q'.mul_nonneg sixteenth lambda (by decide) hLambda)
  exact Q'.pos_of_lt_of_le hz
    (Q'.ge_of_eqv (auxiliary_mass width face hf lambda))

/-- This is the exact normalized mean of U, not a bare-Haar recentering. -/
def auxiliaryCenter (width : Nat) (face : Z4Plaq) (lambda : Q')
    (hZ : (0 : Q') < H width (auxiliaryWeight lambda
      (characterPolynomial (plaquette width face).scalar 1))) : RatPoly :=
  QuaternionHaarNormalizedCenter.center (N width)
    (auxiliaryWeight lambda (characterPolynomial (plaquette width face).scalar 1))
    hZ (characterPolynomial (plaquette width face).scalar 1)

theorem auxiliary_center_mean_zero (width : Nat) (face : Z4Plaq)
    (lambda : Q')
    (hZ : (0 : Q') < H width (auxiliaryWeight lambda
      (characterPolynomial (plaquette width face).scalar 1))) :
    H width (polyMul (auxiliaryWeight lambda
      (characterPolynomial (plaquette width face).scalar 1))
      (auxiliaryCenter width face lambda hZ)) ≈ 0 :=
  QuaternionHaarNormalizedCenter.center_mean_zero (N width)
    (auxiliaryWeight lambda (characterPolynomial (plaquette width face).scalar 1))
    hZ (characterPolynomial (plaquette width face).scalar 1)

private theorem qmul {a b c d : Q'} (ha : a ≈ b) (hc : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hc)

/-- Physical auxiliary source, its own mass/mean, and all four-link angular
blocks give an exact signed Ward residual. This is not a terminal source. -/
theorem auxiliary_ward_residual_pin (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q')
    (hLambda : (0 : Q') ≤ lambda) :
    let f := characterPolynomial (plaquette width face).scalar 1
    let U := auxiliaryWeight lambda f
    let hZ := auxiliary_mass_positive width face hf lambda hLambda
    12 * H width (polyMul U
      (polyMul (auxiliaryCenter width face lambda hZ)
        (auxiliaryCenter width face lambda hZ))) +
      -(H width (polyMul U (activeGamma (List.range (N width)) f f))) ≈
    lambda + -(threeQuarters *
      ((1+lambda)*(1+lambda)*
        Q'.recipPos (1+sixteenth*lambda)
          (Q'.pos_add_nonneg (by decide)
            (Q'.mul_nonneg sixteenth lambda (by decide) hLambda)))) := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  let U := auxiliaryWeight lambda f
  let Z := H width U
  let z : Q' := 1 + sixteenth*lambda
  have hZ : (0 : Q') < Z := auxiliary_mass_positive width face hf lambda hLambda
  have hz : (0 : Q') < z := Q'.pos_add_nonneg (by decide)
    (Q'.mul_nonneg sixteenth lambda (by decide) hLambda)
  have hM : Z ≈ z := auxiliary_mass width face hf lambda
  have hF : H width (polyMul U f) ≈ quarter*(1+lambda) :=
    auxiliary_first width face hf lambda
  have hS : H width (polyMul U (polyMul f f)) ≈ 1+eighth*lambda :=
    auxiliary_second width face hf lambda
  have hA : H width (polyMul U (activeGamma (List.range (N width)) f f)) ≈
      12+HalfPow.half*lambda := auxiliary_angular width face hf lambda
  have hr : Q'.recipPos Z hZ ≈ Q'.recipPos z hz :=
    Q'.recipPos_eqv_congr Z z hZ hz hM
  have hcenter := QuaternionHaarNormalizedCenter.center_norm_identity
    (N width) U hZ f
  have hcenter' : H width (polyMul U
      (polyMul (auxiliaryCenter width face lambda hZ)
        (auxiliaryCenter width face lambda hZ))) ≈
      (1+eighth*lambda) +
        -(((quarter*(1+lambda))*(quarter*(1+lambda)))*Q'.recipPos z hz) :=
    Q'.eqv_trans _ _ _ hcenter
      (Q'.add_eqv_congr' hS
        (Q'.neg_eqv_congr _ _ (qmul (qmul hF hF) hr)))
  have hring :
      12*((1+eighth*lambda) +
        -(((quarter*(1+lambda))*(quarter*(1+lambda)))*Q'.recipPos z hz)) +
        -(12+HalfPow.half*lambda) ≈
      (12*eighth+-HalfPow.half)*lambda +
        -((12*(quarter*quarter))*
          (((1+lambda)*(1+lambda))*Q'.recipPos z hz)) :=
    poly_identity_of_normal_eq
      (.add
        (.mul (.const 12)
          (.add (.add (.const 1) (.mul (.var 0) (.var 3)))
            (.neg (.mul
              (.mul (.mul (.var 1) (.add (.const 1) (.var 3)))
                (.mul (.var 1) (.add (.const 1) (.var 3))))
              (.var 4)))))
        (.neg (.add (.const 12) (.mul (.var 2) (.var 3)))))
      (.add
        (.mul (.add (.mul (.const 12) (.var 0)) (.neg (.var 2))) (.var 3))
        (.neg (.mul (.mul (.const 12) (.mul (.var 1) (.var 1)))
          (.mul (.mul (.add (.const 1) (.var 3))
            (.add (.const 1) (.var 3))) (.var 4)))))
      (by decide) (fun | 0 => eighth | 1 => quarter | 2 => HalfPow.half
                       | 3 => lambda | _ => Q'.recipPos z hz)
  have hc1 : 12*eighth+-HalfPow.half ≈ 1 := by decide
  have hc2 : 12*(quarter*quarter) ≈ threeQuarters := by decide
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 12 _ _ hcenter')
      (Q'.neg_eqv_congr _ _ hA))
    (Q'.eqv_trans _ _ _ hring
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right (12*eighth+-HalfPow.half) 1 lambda hc1)
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_right (12*(quarter*quarter)) threeQuarters
              (((1+lambda)*(1+lambda))*Q'.recipPos z hz) hc2)))
        (Q'.add_eqv_congr' (Q'.one_mul_eqv lambda) (Q'.eqv_refl _))))

private def elevenQuarters : Q' := Q'.mkPos 11 4 (by decide)

private theorem scalar_residual_floor (lambda : Q')
    (hLambda : HalfPow.half ≤ lambda) :
    let z : Q' := 1+sixteenth*lambda
    let hz : (0 : Q') < z := Q'.pos_add_nonneg (by decide)
      (Q'.mul_nonneg sixteenth lambda (by decide)
        (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ HalfPow.half) hLambda))
    lambda + -(threeQuarters *
      ((1+lambda)*(1+lambda)*Q'.recipPos z hz)) ≤ -1 := by
  dsimp only
  let z : Q' := 1+sixteenth*lambda
  have hLambda0 : (0 : Q') ≤ lambda := Q'.le_trans' _ _ _
    (by decide : (0 : Q') ≤ HalfPow.half) hLambda
  have hz : (0 : Q') < z := Q'.pos_add_nonneg (by decide)
    (Q'.mul_nonneg sixteenth lambda (by decide) hLambda0)
  let r := Q'.recipPos z hz
  let t : Q' := 1+lambda
  let cost : Q' := threeQuarters*((t*t)*r)
  have ht : (0 : Q') ≤ t := Q'.zero_le_add _ _ (by decide) hLambda0
  have hr : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos z hz)
  have hscaled := Q'.mul_le_mul_of_nonneg_left HalfPow.half lambda
    elevenQuarters hLambda (by decide)
  have hlin : (1 : Q') ≤ elevenQuarters*lambda :=
    Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ elevenQuarters*HalfPow.half) hscaled
  have hlinear := Q'.add_le_add_left (3+quarter*lambda)
    1 (elevenQuarters*lambda) hlin
  have hs : 4*sixteenth ≈ quarter := by decide
  have hleft : 4*z ≈ (3+quarter*lambda)+1 :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.const 4) (.add (.const 1) (.mul (.var 0) (.var 2))))
        (.add (.add (.const 3)
          (.mul (.mul (.const 4) (.var 0)) (.var 2))) (.const 1))
        (by decide) (fun | 0 => sixteenth | 2 => lambda | _ => 0))
      (Q'.add_eqv_congr_right _ _ 1
        (Q'.add_eqv_congr_left 3 _ _
          (Q'.mul_eqv_congr_right (4*sixteenth) quarter lambda hs)))
  have hc : quarter+elevenQuarters ≈ 3 := by decide
  have hright : (3+quarter*lambda)+(elevenQuarters*lambda) ≈ 3*t :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.const 3) (.mul (.var 0) (.var 2)))
          (.mul (.var 1) (.var 2)))
        (.add (.const 3) (.mul (.add (.var 0) (.var 1)) (.var 2)))
        (by decide) (fun | 0 => quarter | 1 => elevenQuarters | _ => lambda))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl 3)
          (Q'.mul_eqv_congr_right (quarter+elevenQuarters) 3 lambda hc))
        (poly_identity_of_normal_eq
          (.add (.const 3) (.mul (.const 3) (.var 0)))
          (.mul (.const 3) (.add (.const 1) (.var 0)))
          (by decide) (fun _ => lambda)))
  have hbound : 4*z ≤ 3*t :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hlinear (Q'.le_of_eqv hright))
  have hmult := Q'.mul_le_mul_of_nonneg_right
    (4*z) (3*t) (quarter*(t*r)) hbound
    (Q'.mul_nonneg quarter (t*r) (by decide) (Q'.mul_nonneg t r ht hr))
  have h4q : 4*quarter ≈ 1 := by decide
  have hcancel : (4*z)*(quarter*(t*r)) ≈ t :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 4) (.var 0))
          (.mul (.var 3) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.const 4) (.var 3))
          (.mul (.var 1) (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => z | 1 => t | 2 => r | _ => quarter))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (4*quarter) 1 _ h4q)
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left t _ _ (Q'.mul_recipPos_eqv z hz))
            (Q'.mul_one_eqv t))))
  have h3q : 3*quarter ≈ threeQuarters := by decide
  have hcollect : (3*t)*(quarter*(t*r)) ≈ cost :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 3) (.var 0))
          (.mul (.var 2) (.mul (.var 0) (.var 1))))
        (.mul (.mul (.const 3) (.var 2))
          (.mul (.mul (.var 0) (.var 0)) (.var 1)))
        (by decide) (fun | 0 => t | 1 => r | _ => quarter))
      (Q'.mul_eqv_congr_right (3*quarter) threeQuarters _ h3q)
  have hcost : t ≤ cost := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hcancel)
    (Q'.le_trans' _ _ _ hmult (Q'.le_of_eqv hcollect))
  have hsub := Q'.add_le_add_right t cost (-t) hcost
  have hnonneg : (0 : Q') ≤ cost + -t := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.add_neg_self_eqv t)) hsub
  have hconvert : (-1 : Q') + -(lambda + -cost) ≈ cost + -t :=
    poly_identity_of_normal_eq
      (.add (.neg (.const 1))
        (.neg (.add (.var 0) (.neg (.var 1)))))
      (.add (.var 1) (.neg (.add (.const 1) (.var 0))))
      (by decide) (fun | 0 => lambda | _ => cost)
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hnonneg (Q'.ge_of_eqv hconvert))

/-- An exact negative residual for these literal plaquette auxiliary weights.
No heat-image pin, scaling-smallness conclusion or identification with a
terminal-message source of the Yang--Mills measure is supplied here. -/
theorem auxiliary_ward_residual_le_neg_one (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (lambda : Q')
    (hLambda : HalfPow.half ≤ lambda) :
    let f := characterPolynomial (plaquette width face).scalar 1
    let U := auxiliaryWeight lambda f
    let hZ := auxiliary_mass_positive width face hf lambda
      (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ HalfPow.half) hLambda)
    12 * H width (polyMul U
      (polyMul (auxiliaryCenter width face lambda hZ)
        (auxiliaryCenter width face lambda hZ))) +
      -(H width (polyMul U (activeGamma (List.range (N width)) f f))) ≤ -1 := by
  dsimp only
  have hLambda0 : (0 : Q') ≤ lambda := Q'.le_trans' _ _ _
    (by decide : (0 : Q') ≤ HalfPow.half) hLambda
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (auxiliary_ward_residual_pin width face hf lambda hLambda0))
    (scalar_residual_floor lambda hLambda)

#print axioms linearSource
#print axioms auxiliaryWeight
#print axioms auxiliary_mass
#print axioms auxiliary_first
#print axioms auxiliary_second
#print axioms auxiliary_angular
#print axioms auxiliary_mass_positive
#print axioms auxiliaryCenter
#print axioms auxiliary_center_mean_zero
#print axioms auxiliary_ward_residual_pin
#print axioms auxiliary_ward_residual_le_neg_one

end YMGap.Continuum.SU2QuaternionPlaquetteAuxiliaryWardSign
