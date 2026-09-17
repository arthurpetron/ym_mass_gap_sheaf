/-
# Finite scalar centering in the same quaternion-Haar weight

The only inverse is the reciprocal of the explicit positive rational mass
H(W). Centering is an actual polynomial, preserves support and coordinate
independence, and removes the exact original weighted mean. Its second
moment is the original second moment minus the nonnegative scalar mean
correction. No polynomial reciprocal, completion, or new analytic budget is
used. Positivity of W itself is not needed for these algebraic identities;
the explicit hypothesis H(W)>0 suffices for the norm-reduction inequality.
-/

import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini

namespace YMGap.Continuum.QuaternionHaarNormalizedCenter

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_cap_mul (blocks : Nat) (c : Q') (p : RatPoly) :
    quaternionHaar blocks (polyMul (cap c) p) ≈ c*quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c p)) (quaternionHaar_polySmul blocks c p)

private theorem weighted_neg (blocks : Nat) (W f : RatPoly) :
    quaternionHaar blocks (polyMul W (polyNeg f)) ≈
      -(quaternionHaar blocks (polyMul W f)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
    (by decide) (fun | 0 => W | _ => f))) (haar_neg blocks _)

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1))*weight []+0 ≈ ((-c)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl _)

private theorem cap_supported (blocks : Nat) (c : Q') : SupportedQuaternionBlocks blocks (cap c) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one blocks s hs

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem scalar_sub_self (a : Q') : a + -a ≈ 0 :=
  poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide) (fun _ => a)

private theorem subtract_nonnegative (a b : Q') (hb : (0 : Q') ≤ b) : a + -b ≤ a :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (a + -b) b hb)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => a | _ => b)))

private theorem square_shift (blocks : Nat) (W f : RatPoly) (c : Q') :
    quaternionHaar blocks (polyMul W
      (polyMul (polyAdd f (polyNeg (cap c))) (polyAdd f (polyNeg (cap c))))) ≈
      quaternionHaar blocks (polyMul W (polyMul f f)) +
        -(c*quaternionHaar blocks (polyMul W f) + c*quaternionHaar blocks (polyMul W f)) +
        c*(c*quaternionHaar blocks W) := by
  have he := haar_of_coeff (blocks := blocks) (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))))
    (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
      (.neg (.add (.mul (.var 2) (.mul (.var 0) (.var 1)))
        (.mul (.var 2) (.mul (.var 0) (.var 1))))))
      (.mul (.var 2) (.mul (.var 2) (.var 0))))
    (by decide) (fun | 0 => W | 1 => f | _ => cap c))
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.eqv_trans _ _ _ (haar_neg blocks _)
              (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
                (Q'.add_eqv_congr' (haar_cap_mul blocks c _) (haar_cap_mul blocks c _)))))))
        (Q'.eqv_trans _ _ _ (haar_cap_mul blocks c _)
          (Q'.mul_eqv_congr_left _ _ _ (haar_cap_mul blocks c W)))))

variable (blocks : Nat) (W : RatPoly) (hZ : (0 : Q') < quaternionHaar blocks W)

/-- Subtract the explicit normalized mean in the SAME original weight. -/
def center (f : RatPoly) : RatPoly :=
  polyAdd f (polyNeg (cap (normalizedMoment blocks W f hZ)))

theorem center_supported {f : RatPoly} (hf : SupportedQuaternionBlocks blocks f) :
    SupportedQuaternionBlocks blocks (center blocks W hZ f) :=
  supported_add hf (neg_supported (cap_supported blocks _))

theorem center_independent {block : Nat} {f : RatPoly} (hf : QuaternionBlockIndependent block f) :
    QuaternionBlockIndependent block (center blocks W hZ f) :=
  quaternionBlockIndependent_polyAdd hf
    (quaternionBlockIndependent_polyNeg
      (quaternionBlockIndependent_polySmul _ (quaternionBlockIndependent_polyOne block)))

private theorem mean_mass (f : RatPoly) :
    normalizedMoment blocks W f hZ * quaternionHaar blocks W ≈
      quaternionHaar blocks (polyMul W f) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ hZ)))
      (Q'.mul_one_eqv _))

theorem center_mean_zero (f : RatPoly) :
    quaternionHaar blocks (polyMul W (center blocks W hZ f)) ≈ 0 := by
  have hc : quaternionHaar blocks (polyMul W (cap (normalizedMoment blocks W f hZ))) ≈
      quaternionHaar blocks (polyMul W f) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (haar_cap_mul blocks _ W) (mean_mass blocks W hZ f))
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right blocks W f _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (weighted_neg blocks W _) (Q'.neg_eqv_congr _ _ hc)))
      (scalar_sub_self _))

/-- Exact unnormalized second moment, with the original rational mass. -/
theorem center_norm_identity (f : RatPoly) :
    quaternionHaar blocks (polyMul W (polyMul (center blocks W hZ f) (center blocks W hZ f))) ≈
      quaternionHaar blocks (polyMul W (polyMul f f)) +
        -((quaternionHaar blocks (polyMul W f)*quaternionHaar blocks (polyMul W f))*
          Q'.recipPos (quaternionHaar blocks W) hZ) := by
  let a := quaternionHaar blocks (polyMul W f)
  let b := quaternionHaar blocks (polyMul W (polyMul f f))
  let c := normalizedMoment blocks W f hZ
  have he : b + -(c*a+c*a) + c*(c*quaternionHaar blocks W) ≈ b + -(c*a) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_eqv_congr_left _ _ _ (mean_mass blocks W hZ f)))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.add (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1)))))
          (.mul (.var 2) (.var 1)))
        (.add (.var 0) (.neg (.mul (.var 2) (.var 1)))) (by decide)
        (fun | 0 => b | 1 => a | _ => c))
  have hc : c*a ≈ (a*a)*Q'.recipPos (quaternionHaar blocks W) hZ :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 0))
      (.mul (.mul (.var 0) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => a | _ => Q'.recipPos (quaternionHaar blocks W) hZ)
  exact Q'.eqv_trans _ _ _ (square_shift blocks W f c)
    (Q'.eqv_trans _ _ _ he (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hc)))

/-- Centering loses no multiplicative constant in the original second moment. -/
theorem center_norm_le (f : RatPoly) :
    quaternionHaar blocks (polyMul W (polyMul (center blocks W hZ f) (center blocks W hZ f))) ≤
      quaternionHaar blocks (polyMul W (polyMul f f)) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (center_norm_identity blocks W hZ f))
    (subtract_nonnegative _ _ (Q'.mul_nonneg _ _
      (SumOfSquares.q_mul_self_nonneg _) (Q'.le_of_lt (Q'.recipPos_pos _ hZ))))

theorem center_congr {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (center blocks W hZ f) (center blocks W hZ g) := by
  have hm : normalizedMoment blocks W f hZ ≈ normalizedMoment blocks W g hZ :=
    Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (h.mul_left W))
  exact h.add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.smul_coefficient hm polyOne))

theorem center_add (f g : RatPoly) :
    RatPolyCoeffEqv (center blocks W hZ (polyAdd f g))
      (polyAdd (center blocks W hZ f) (center blocks W hZ g)) := by
  have hm : normalizedMoment blocks W (polyAdd f g) hZ ≈
      normalizedMoment blocks W f hZ + normalizedMoment blocks W g hZ :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (quaternionHaar_polyMul_add_right blocks W f g))
      (Q'.add_mul_eqv _ _ _)
  have hc : RatPolyCoeffEqv (cap (normalizedMoment blocks W (polyAdd f g) hZ))
      (polyAdd (cap (normalizedMoment blocks W f hZ)) (cap (normalizedMoment blocks W g hZ))) :=
    (RatPolyCoeffEqv.smul_coefficient hm polyOne).trans (cap_add _ _).symm
  exact ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hc)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide) (fun
        | 0 => f | 1 => g | 2 => cap (normalizedMoment blocks W f hZ)
        | _ => cap (normalizedMoment blocks W g hZ)))

theorem center_neg (f : RatPoly) :
    RatPolyCoeffEqv (center blocks W hZ (polyNeg f)) (polyNeg (center blocks W hZ f)) := by
  have hm : normalizedMoment blocks W (polyNeg f) hZ ≈ -(normalizedMoment blocks W f hZ) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (weighted_neg blocks W f))
      (Q'.neg_mul_eqv _ _)
  have hc : RatPolyCoeffEqv (cap (normalizedMoment blocks W (polyNeg f) hZ))
      (polyNeg (cap (normalizedMoment blocks W f hZ))) :=
    (RatPolyCoeffEqv.smul_coefficient hm polyOne).trans (cap_neg _).symm
  exact ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hc)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.neg (.var 0)) (.neg (.neg (.var 1))))
      (.neg (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => f | _ => cap (normalizedMoment blocks W f hZ)))

theorem center_fixed (f : RatPoly) (hf : quaternionHaar blocks (polyMul W f) ≈ 0) :
    RatPolyCoeffEqv (center blocks W hZ f) f := by
  have hm : normalizedMoment blocks W f hZ ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hf) (Q'.zero_mul_eqv _)
  have hc : RatPolyCoeffEqv (cap (normalizedMoment blocks W f hZ)) polyZero :=
    (RatPolyCoeffEqv.smul_coefficient hm polyOne).trans (RatPolyCoeffEqv.zero_smul polyOne)
  exact ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hc)).trans (RatPolyCoeffEqv.add_zero f)

end YMGap.Continuum.QuaternionHaarNormalizedCenter

#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_supported
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_independent
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_mean_zero
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_norm_identity
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_norm_le
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_congr
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_add
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_neg
#print axioms YMGap.Continuum.QuaternionHaarNormalizedCenter.center_fixed
