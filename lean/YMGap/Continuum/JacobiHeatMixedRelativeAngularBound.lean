/-
# Mixed relative angular bounds for the actual positive Jacobi heat

The original positive factor recurrence gives a mixed cost
    m*R + d*e*R^2,
where R is the sum of the relative slopes, d/e bound the two first scalar
derivatives, and m bounds their ordered mixed derivative. The same induction
also controls the positive Leibniz derivative defining the Jacobi heat.
The existing summable slope budget removes the finite Jacobi cutoff from
all three costs. No reciprocal of the full heat minimum enters them.

These are finite WEIGHTED Jacobi heat polynomials. Passage to the original
unweighted heat prefix still requires its mixed-derivative deficit modulus.
No interacting-family, scaling, or continuum conclusion is claimed.
-/

import YMGap.Continuum.JacobiHeatRelativeAngularBound
import YMGap.Continuum.QuaternionHaarMixedRelativeAngularBound

namespace YMGap.Continuum.JacobiHeatMixedRelativeAngularBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativePolynomialInterval
open YMGap.Continuum.QuaternionHaarMixedRelativeAngularBound
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.JTPFullProductDerivativeNormalization
open YMGap.Continuum.SU2PointwiseHeatPositiveCompletion
open YMGap.Continuum.JacobiShiftedPositiveCoefficients
open YMGap.Continuum.JacobiShiftedRelativeSlope
open YMGap.Continuum.JacobiHeatRelativeAngularBound (prefixCost relativeCost)

local infix:50 " ≈ " => Q'.eqv

private theorem cap_derivative (i j : Nat) (a : Q') :
    RatPolyCoeffEqv (angularDerivative i j (cap a)) polyZero :=
  (angularDerivative_smul i j a polyOne).trans
    (((angularDerivative_one i j).smul a).trans (RatPolyCoeffEqv.smul_zero a))

private theorem affine_derivative (i j : Nat) (a b : Q') (x : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (polyAdd (cap a) (polyMul (cap b) x)))
      (polySmul b (angularDerivative i j x)) :=
  (angularDerivative_add i j _ _).trans
    (((cap_derivative i j a).add
      ((angularDerivative_congr i j (cap_mul_left b x)).trans
        (angularDerivative_smul i j b x))).trans (RatPolyCoeffEqv.zero_add _))

/-- Clear only the affine factor's coefficient comparison, not an inverse
of a whole heat polynomial. This applies to any signed scalar numerator. -/
private def affine_interval {blocks : Nat} {x y : RatPoly} {a b d r : Q'}
    (X : Certificate blocks x) (Y : Interval blocks y d)
    (_ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) (hr : (0 : Q') ≤ r)
    (hslope : b ≤ r*a) :
    RelativeInterval blocks (polyAdd (cap a) (polyMul (cap b) x))
      (polySmul b y) (d*r) := by
  let p := polyAdd (cap a) (polyMul (cap b) x)
  have capNeg : RatPolyCoeffEqv (polyNeg (cap b)) (cap (-b)) := by
    intro weight
    change Q'.eqv ((-(b*1))*weight []+0) (((-b)*1)*weight []+0)
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv b 1))) (Q'.eqv_refl _)
  have clearance : Certificate blocks (polyAdd (polyMul (cap r) p) (polyNeg (cap b))) := by
    refine .ofCoeff
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3)))) (.neg (.var 2)))
        (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))
          (.mul (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => cap r | 1 => cap a | 2 => cap b | _ => x)).trans
        ((((cap_mul r a).add capNeg).trans (cap_add (r*a) (-b))).add
          ((cap_mul r b).mul_right x))) ?_
    exact (Certificate.constant blocks (r*a + -b) (Q'.sub_nonneg_of_le hslope)).add
      ((Certificate.constant blocks (r*b) (Q'.mul_nonneg _ _ hr hb)).mul X)
  constructor
  · exact .ofCoeff
      ((((cap_mul d r).symm.mul_right p).add (cap_mul_left b y).symm).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 4)))
          (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
            (.mul (.var 3) (.add (.var 0) (.var 4))))
          (by decide) (fun | 0 => cap d | 1 => cap r | 2 => p | 3 => cap b | _ => y)))
      (((Certificate.constant blocks d Y.nonnegative).mul clearance).add
        ((Certificate.constant blocks b hb).mul Y.lower))
  · exact .ofCoeff
      ((((cap_mul d r).symm.mul_right p).add
        (RatPolyCoeffEqv.neg (cap_mul_left b y).symm)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.var 3) (.var 4))))
          (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
            (.mul (.var 3) (.add (.var 0) (.neg (.var 4)))))
          (by decide) (fun | 0 => cap d | 1 => cap r | 2 => p | 3 => cap b | _ => y)))
      (((Certificate.constant blocks d Y.nonnegative).mul clearance).add
        ((Certificate.constant blocks b hb).mul Y.upper))

private def affineMixedBound {blocks oi oj ii ij : Nat} {x : RatPoly}
    {a b d e m r : Q'} (X : Certificate blocks x)
    (DX : Interval blocks (angularDerivative oi oj x) d)
    (DY : Interval blocks (angularDerivative ii ij x) e)
    (DXY : Interval blocks (angularDerivative oi oj (angularDerivative ii ij x)) m)
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) (hr : (0 : Q') ≤ r)
    (hslope : b ≤ r*a) :
    MixedBound blocks oi oj ii ij (polyAdd (cap a) (polyMul (cap b) x))
      (d*r) (e*r) (m*r) where
  outer := RelativeBound.affine X DX ha hb hr hslope
  inner := RelativeBound.affine X DY ha hb hr hslope
  mixedNonnegative := Q'.mul_nonneg _ _ DXY.nonnegative hr
  mixed := RelativeInterval.ofCoeff
    ((angularDerivative_congr oi oj (affine_derivative ii ij a b x)).trans
      (angularDerivative_smul oi oj b (angularDerivative ii ij x)))
    (affine_interval X DXY ha hb hr hslope)

/-- Actual shifted Jacobi factor, with both first and ordered mixed scores. -/
def factorBound {blocks oi oj ii ij : Nat} {x : RatPoly} {q d e m : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (X : Certificate blocks x)
    (DX : Interval blocks (angularDerivative oi oj x) d)
    (DY : Interval blocks (angularDerivative ii ij x) e)
    (DXY : Interval blocks (angularDerivative oi oj (angularDerivative ii ij x)) m)
    (k : Nat) : MixedBound blocks oi oj ii ij (subst x (factor q k))
      (d*rate q k) (e*rate q k) (m*rate q k) :=
  .ofCoeff ((RatPolyCoeffEqv.refl _).add
    (((subst_singleton x (gFacDx q k)).mul_left x).trans (RatPolyCoeffEqv.mul_comm _ _)))
    (affineMixedBound X DX DY DXY (Q'.le_of_lt (base_pos hq0 hq1 k))
      (Q'.le_of_lt (slope_pos hq0 hq1 k)) (rate_nonnegative hq0 k)
      (slope_le_rate_mul_base hq0 hq1 k))

def mixedCost (d e m R : Q') : Q' := m*R + (d*e)*(R*R)
def mixedPrefixCost (q d e m : Q') (N : Nat) : Q' :=
  mixedCost d e m (finSum (rate q) N)
def mixedRelativeCost (q d e m : Q') : Q' := mixedCost d e m (budget q)

private theorem prefix_nonnegative {q : Q'} (hq0 : (0 : Q') < q) :
    ∀ N, (0 : Q') ≤ finSum (rate q) N
  | 0 => Q'.le_refl' _
  | N+1 => Q'.zero_le_add _ _ (prefix_nonnegative hq0 N) (rate_nonnegative hq0 N)

private theorem mixedCost_mono {d e m R S : Q'}
    (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e) (hm : (0 : Q') ≤ m)
    (hR : (0 : Q') ≤ R) (hRS : R ≤ S) : mixedCost d e m R ≤ mixedCost d e m S := by
  have hS := Q'.le_trans' _ _ _ hR hRS
  have hsq : R*R ≤ S*S := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hRS hR)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hRS hS)
  exact Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hRS hm)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hsq (Q'.mul_nonneg _ _ hd he))

private theorem prefix_succ (q d : Q') (N : Nat) :
    prefixCost q d N + d*rate q N ≈ prefixCost q d (N+1) := by
  change d*finSum (rate q) N + d*rate q N ≈ d*(finSum (rate q) N+rate q N)
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
    (.mul (.var 0) (.add (.var 1) (.var 2))) (by decide)
    (fun | 0 => d | 1 => finSum (rate q) N | _ => rate q N)

private theorem mixed_succ {q d e m : Q'}
    (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e) (N : Nat) :
    (mixedPrefixCost q d e m N + m*rate q N) +
      (prefixCost q d N*(e*rate q N)+prefixCost q e N*(d*rate q N)) ≤
      mixedPrefixCost q d e m (N+1) := by
  let R := finSum (rate q) N
  let r := rate q N
  have hn : (0 : Q') ≤ (d*e)*(r*r) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hd he) (SumOfSquares.q_mul_self_nonneg r)
  have hid :
      ((mixedCost d e m R + m*r) + (d*R*(e*r)+e*R*(d*r))) + (d*e)*(r*r) ≈
        mixedCost d e m (R+r) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.add (.add (.mul (.var 2) (.var 3))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 3))))
          (.mul (.var 2) (.var 4)))
          (.add (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4)))
            (.mul (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 4)))))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 4) (.var 4))))
      (.add (.mul (.var 2) (.add (.var 3) (.var 4)))
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.add (.var 3) (.var 4)) (.add (.var 3) (.var 4)))))
      (by decide) (fun | 0 => d | 1 => e | 2 => m | 3 => R | _ => r)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv hid)

/-- Simultaneous induction for the original product and its positive
Leibniz derivative. The latter, not the former, defines the actual heat. -/
def productDerivativeBounds {blocks oi oj ii ij : Nat} {x : RatPoly} {q d e m : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (X : Certificate blocks x)
    (DX : Interval blocks (angularDerivative oi oj x) d)
    (DY : Interval blocks (angularDerivative ii ij x) e)
    (DXY : Interval blocks (angularDerivative oi oj (angularDerivative ii ij x)) m) :
    (N : Nat) →
      MixedBound blocks oi oj ii ij (subst x (product q N))
        (prefixCost q d N) (prefixCost q e N) (mixedPrefixCost q d e m N) ×
      MixedBound blocks oi oj ii ij (subst x (derivative q N))
        (prefixCost q d N) (prefixCost q e N) (mixedPrefixCost q d e m N)
  | 0 => by
      have hd0 : (0 : Q') ≈ prefixCost q d 0 := (Q'.mul_zero_eqv d).symm
      have he0 : (0 : Q') ≈ prefixCost q e 0 := (Q'.mul_zero_eqv e).symm
      have hm0 : (0 : Q') ≈ mixedPrefixCost q d e m 0 := by
        exact Q'.eqv_symm (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.const 0)) (.mul (.var 1) (.mul (.const 0) (.const 0))))
          (.const 0) (by decide) (fun | 0 => m | _ => d*e))
      exact ⟨.ofCoeff (subst_singleton x 1)
          ((MixedBound.constant blocks oi oj ii ij 1 Q'.zero_le_one).changeCaps hd0 he0 hm0),
        (MixedBound.zero blocks oi oj ii ij).changeCaps hd0 he0 hm0⟩
  | N+1 => by
      let previous := productDerivativeBounds hq0 hq1 X DX DY DXY N
      let nextFactor := factorBound hq0 hq1 X DX DY DXY N
      have hR : finSum (rate q) N ≤ finSum (rate q) (N+1) :=
        Q'.add_le_self_of_nonneg _ _ (rate_nonnegative hq0 N)
      have hd := Q'.mul_le_mul_of_nonneg_left _ _ d hR DX.nonnegative
      have he := Q'.mul_le_mul_of_nonneg_left _ _ e hR DY.nonnegative
      have hm := mixedCost_mono DX.nonnegative DY.nonnegative DXY.nonnegative
        (prefix_nonnegative hq0 N) hR
      let step (P : MixedBound blocks oi oj ii ij (subst x (product q N))
          (prefixCost q d N) (prefixCost q e N) (mixedPrefixCost q d e m N)) :=
        ((P.mul nextFactor).changeCaps (prefix_succ q d N) (prefix_succ q e N)
          (Q'.eqv_refl _)).weaken (Q'.le_refl' _) (Q'.le_refl' _)
            (mixed_succ DX.nonnegative DY.nonnegative N)
      have hprod := step previous.1
      have hderiv := ((previous.2.mul nextFactor).changeCaps
        (prefix_succ q d N) (prefix_succ q e N) (Q'.eqv_refl _)).weaken
          (Q'.le_refl' _) (Q'.le_refl' _) (mixed_succ DX.nonnegative DY.nonnegative N)
      exact ⟨.ofCoeff (subst_pmul x _ _) hprod,
        .ofCoeff ((subst_padd x _ _).trans
          ((subst_pmul x _ _).add (subst_pscale x (gFacDx q N) _)))
          (hderiv.add ((previous.1.smul (gFacDx q N)
            (Q'.le_of_lt (slope_pos hq0 hq1 N))).weaken hd he hm))⟩

/-- Cutoff-independent mixed relative bound for the actual shifted heat,
including its original inverse-nome/half normalization. -/
def heatBound {blocks oi oj ii ij : Nat} {x : RatPoly} {q d e m : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (X : Certificate blocks x)
    (DX : Interval blocks (angularDerivative oi oj x) d)
    (DY : Interval blocks (angularDerivative ii ij x) e)
    (DXY : Interval blocks (angularDerivative oi oj (angularDerivative ii ij x)) m)
    (N : Nat) : MixedBound blocks oi oj ii ij (subst x (heat q N))
      (relativeCost q d) (relativeCost q e) (mixedRelativeCost q d e m) :=
  (MixedBound.ofCoeff (subst_pscale x _ _)
    (((productDerivativeBounds hq0 hq1 X DX DY DXY N).2).smul (inverseNome q * HalfPow.half)
      (Q'.mul_nonneg _ _ (inverseNome_nonnegative q) HalfPow.half_nonneg))).weaken
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (prefix_le_budget hq0 hq1 N) DX.nonnegative)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (prefix_le_budget hq0 hq1 N) DY.nonnegative)
    (mixedCost_mono DX.nonnegative DY.nonnegative DXY.nonnegative
      (prefix_nonnegative hq0 N) (prefix_le_budget hq0 hq1 N))

/-- On the SAME original quaternion carrier and the already identified
weighted character polynomial. No heat-minimum reciprocal in the cost. -/
def weightedHeatBound {blocks oi oj ii ij : Nat} {p : PolyQuaternion} {q d e m : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hoi : oi < 4*blocks) (hoj : oj < 4*blocks)
    (hii : ii < 4*blocks) (hij : ij < 4*blocks)
    (hp : Supported blocks p) (hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (DX : Interval blocks (angularDerivative oi oj p.scalar) d)
    (DY : Interval blocks (angularDerivative ii ij p.scalar) e)
    (DXY : Interval blocks (angularDerivative oi oj (angularDerivative ii ij p.scalar)) m)
    (N : Nat) :
    MixedBound blocks oi oj ii ij (JacobiWeightedHeatPolynomial.weightedPolynomial q N p.scalar)
      (relativeCost q d) (relativeCost q e) (mixedRelativeCost q d e m) := by
  have dt (i j : Nat) : RatPolyCoeffEqv
      (angularDerivative i j (polyAdd polyOne p.scalar)) (angularDerivative i j p.scalar) :=
    (angularDerivative_add i j polyOne p.scalar).trans
      (((angularDerivative_one i j).add (.refl _)).trans (RatPolyCoeffEqv.zero_add _))
  have hs := supported_add (supported_one blocks) hp.scalar
  let DT := Interval.ofCoeff (angularDerivative_supported_at hoi hoj hs) (dt oi oj) DX
  let DU := Interval.ofCoeff (angularDerivative_supported_at hii hij hs) (dt ii ij) DY
  let DTU := Interval.ofCoeff
    (angularDerivative_supported_at hoi hoj (angularDerivative_supported_at hii hij hs))
    (angularDerivative_congr oi oj (dt ii ij)) DXY
  exact .ofCoeff
    (JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial hq0 hq1 N p.scalar).symm
    (heatBound hq0 hq1 (oneAddScalar_certificate hp hu) DT DU DTU N)

#print axioms factorBound
#print axioms mixedCost
#print axioms mixedRelativeCost
#print axioms productDerivativeBounds
#print axioms heatBound
#print axioms weightedHeatBound

end YMGap.Continuum.JacobiHeatMixedRelativeAngularBound
