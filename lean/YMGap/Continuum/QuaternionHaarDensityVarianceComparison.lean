/-
# Raw variance under a certified change of Haar density

If `W - a*R` has an actual square certificate, the raw variance of every
supported observable under `W` dominates `a` times its raw variance under
`R`.  The two densities use their OWN means.  This is the elementary
comparison needed when an original terminal-message bracket is multiplied
into both ends of the original Wilson edge density.  No normalization,
partition comparison, or sign restriction on the observable is used.
-/

import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.QuaternionHaarDensityVarianceComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The positive mass is multiplied back into the SAME density's variance. -/
def rawVariance {blocks : Nat} {W : RatPoly}
    (hZ : (0 : Q') < H blocks W) (p : RatPoly) : Q' :=
  H blocks W * normalizedVariance blocks W p hZ

private theorem mass_cancel (Z X : Q') (hZ : (0 : Q') < Z) :
    Z*(X*Q'.recipPos Z hZ) ≈ X := by
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => Z | 1 => X | _ => Q'.recipPos Z hZ)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left X _ _ (Q'.mul_recipPos_eqv Z hZ))
    (Q'.mul_one_eqv X)

/-- Raw variance is the square at its OWN explicitly computed mean. -/
theorem rawVariance_own_mean {blocks : Nat} {W p : RatPoly}
    (P : Certificate blocks W) (hp : SupportedQuaternionBlocks blocks p)
    (hZ : (0 : Q') < H blocks W) :
    rawVariance hZ p ≈
      H blocks (polyMul W
        (polyMul (shifted p (normalizedMoment blocks W p hZ))
          (shifted p (normalizedMoment blocks W p hZ)))) := by
  let m := normalizedMoment blocks W p hZ
  have h := own_mean_pin P hp hZ
  unfold rawVariance
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (H blocks W) _ _ (Q'.eqv_symm h))
    (by
      unfold normalizedMoment
      exact mass_cancel (H blocks W)
        (H blocks (polyMul W (polyMul (shifted p m) (shifted p m)))) hZ)

/-- The OWN raw variance is at most the raw square at any rational center. -/
theorem rawVariance_le_shifted {blocks : Nat} {W p : RatPoly}
    (P : Certificate blocks W) (hp : SupportedQuaternionBlocks blocks p)
    (hZ : (0 : Q') < H blocks W) (c : Q') :
    rawVariance hZ p ≤
      H blocks (polyMul W (polyMul (shifted p c) (shifted p c))) := by
  have h := normalized_variance_le_shifted P hp hZ c
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (H blocks W) h (Q'.le_of_lt hZ)
  unfold rawVariance
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_of_eqv (by
      unfold normalizedMoment
      exact mass_cancel (H blocks W)
        (H blocks (polyMul W (polyMul (shifted p c) (shifted p c)))) hZ))

/-- The raw variance is positive because its own centered test is a square
under the original certified density. -/
theorem rawVariance_nonnegative {blocks : Nat} {W p : RatPoly}
    (P : Certificate blocks W) (hp : SupportedQuaternionBlocks blocks p)
    (hZ : (0 : Q') < H blocks W) :
    (0 : Q') ≤ rawVariance hZ p := by
  let m := normalizedMoment blocks W p hZ
  have hpos : (0 : Q') ≤
      H blocks (polyMul W (polyMul (shifted p m) (shifted p m))) :=
    (P.mul (Certificate.square (shifted p m) (shifted_supported hp m))).haar_nonnegative
  exact Q'.le_trans' _ _ _ hpos
    (Q'.le_of_eqv (Q'.eqv_symm (rawVariance_own_mean P hp hZ)))

private theorem negative_smul (a : Q') (R : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul a R)) (polySmul (-a) R) := by
  have ha : (-1 : Q')*a ≈ -a :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))
  exact (neg_smul (polySmul a R)).trans
    ((RatPolyCoeffEqv.smul_assoc (-1) a R).trans
      (RatPolyCoeffEqv.smul_coefficient ha R))

/-- A literal certificate `W-aR >= 0` compares every supported raw square.
The sign of `a` is irrelevant for this square-level statement. -/
theorem raw_square_comparison {blocks : Nat} {W R p : RatPoly} {a : Q'}
    (D : Certificate blocks (polyAdd W (polySmul (-a) R)))
    (hp : SupportedQuaternionBlocks blocks p) :
    a * H blocks (polyMul R (polyMul p p)) ≤
      H blocks (polyMul W (polyMul p p)) := by
  have D' : Certificate blocks (polyAdd W (polyNeg (polySmul a R))) :=
    Certificate.ofCoeff ((RatPolyCoeffEqv.refl W).add (negative_smul a R)) D
  have h := haar_order D' (Certificate.square p hp)
  have hs : H blocks (polyMul (polySmul a R) (polyMul p p)) ≈
      a * H blocks (polyMul R (polyMul p p)) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left a R (polyMul p p)))
      (quaternionHaar_polySmul blocks a (polyMul R (polyMul p p)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hs) h

/-- One density-order certificate compares the OWN raw variances.  The
minimizing centers can differ; no partition factor appears. -/
theorem raw_variance_comparison {blocks : Nat} {W R p : RatPoly} {a : Q'}
    (PW : Certificate blocks W) (PR : Certificate blocks R)
    (hW : (0 : Q') < H blocks W) (hR : (0 : Q') < H blocks R)
    (ha : (0 : Q') ≤ a)
    (D : Certificate blocks (polyAdd W (polySmul (-a) R)))
    (hp : SupportedQuaternionBlocks blocks p) :
    a * rawVariance hR p ≤ rawVariance hW p := by
  let c := normalizedMoment blocks W p hW
  have hmin := rawVariance_le_shifted PR hp hR c
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ a hmin ha
  have hc := raw_square_comparison D (shifted_supported hp c)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ hc
      (Q'.le_of_eqv (Q'.eqv_symm (rawVariance_own_mean PW hp hW))))

/-- A positive terminal bracket transports a raw energy/OWN-variance rate
without dividing by either variance or either partition.  In the original
application `Sm` is a certified raw variance, so its nonnegativity is supplied
by `rawVariance_nonnegative`.  Zero variances and zero `c` remain valid. -/
theorem energy_variance_ratio_transport {l u eta c En Em Sn Sm : Q'}
    (hl : (0 : Q') ≤ l) (hu : (0 : Q') ≤ u)
    (heta : (0 : Q') ≤ eta) (hc : (0 : Q') ≤ c)
    (hSm : (0 : Q') ≤ Sm)
    (hwidth : u + -l ≤ eta*l)
    (hen : En ≤ (u*u)*Em)
    (hvar : (l*l)*Sm ≤ Sn)
    (href : Em ≤ c*Sm) :
    En ≤ (c*((1+eta)*(1+eta)))*Sn := by
  let A := (1 : Q')+eta
  have hA : (0 : Q') ≤ A := Q'.zero_le_add 1 eta (by decide) heta
  have hAl : (0 : Q') ≤ A*l := Q'.mul_nonneg _ _ hA hl
  have hwidth_nonneg : (0 : Q') ≤ eta*l + -(u + -l) :=
    Q'.sub_nonneg_of_le hwidth
  have hwidth_pin : eta*l + -(u + -l) ≈ A*l + -u :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.neg (.add (.var 2) (.neg (.var 1)))))
      (.add (.mul (.add (.const 1) (.var 0)) (.var 1)) (.neg (.var 2)))
      (by decide) (fun | 0 => eta | 1 => l | _ => u)
  have hule : u ≤ A*l := Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hwidth_nonneg (Q'.le_of_eqv hwidth_pin))
  have hsq0 : u*u ≤ (A*l)*(A*l) :=
    Q'.mul_le_mul_of_nonneg hule hule hAl hu
  have hsq : u*u ≤ (A*A)*(l*l) :=
    Q'.le_trans' _ _ _ hsq0 (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => A | _ => l)))
  have hu2 : (0 : Q') ≤ u*u := Q'.mul_nonneg _ _ hu hu
  have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ (u*u) href hu2
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ Sm
    (Q'.mul_le_mul_of_nonneg_left _ _ c hsq hc) hSm
  have hleft : (u*u)*(c*Sm) ≈ (c*(u*u))*Sm :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.mul (.var 0) (.var 0))) (.var 2))
      (by decide) (fun | 0 => u | 1 => c | _ => Sm)
  have hright : (c*((A*A)*(l*l)))*Sm ≈ (c*(A*A))*((l*l)*Sm) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1))
        (.mul (.var 2) (.var 2)))) (.var 3))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 2) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => c | 1 => A | 2 => l | _ => Sm)
  have hmiddle : (u*u)*(c*Sm) ≤ (c*(A*A))*((l*l)*Sm) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hright))
  have hcA : (0 : Q') ≤ c*(A*A) :=
    Q'.mul_nonneg _ _ hc (Q'.mul_nonneg _ _ hA hA)
  have hlast := Q'.mul_le_mul_of_nonneg_left _ _ (c*(A*A)) hvar hcA
  exact Q'.le_trans' _ _ _ hen
    (Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hmiddle hlast))

#print axioms rawVariance
#print axioms rawVariance_own_mean
#print axioms rawVariance_le_shifted
#print axioms rawVariance_nonnegative
#print axioms raw_square_comparison
#print axioms raw_variance_comparison
#print axioms energy_variance_ratio_transport

end YMGap.Continuum.QuaternionHaarDensityVarianceComparison
