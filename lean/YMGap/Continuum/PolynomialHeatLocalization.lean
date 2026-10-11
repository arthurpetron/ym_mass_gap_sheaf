/-
# Finite polynomial localization from a positive floor and a linear deficit

For an actual scalar weight h with positive floor eta, and u in [0,1],
the linear estimate 1-h <= c*(1-u) pays the explicitly computed polynomial
(1/2)*u^(D(c)*n(eta)). D is value-based rounding and n is binary search.
Neither exponent depends on a count of action factors. This is scalar
arithmetic, not an assumed partition, entropy, response, or physical estimate.
-/

import YMGap.Continuum.PolynomialHeatLocalizationParameters
import YMGap.Continuum.ReciprocalBernoulliUpper
import YMGap.Continuum.RouteDHigherRepTail
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.PolynomialHeatLocalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.HeatKernelRGStep (qpow_qpow)
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RouteDHigherRepTail (qpow_base_mono sub_le_self')
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)
open YMGap.Continuum.PolynomialHeatLocalizationParameters
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩

private theorem qr (a b : PE) (h :
    RingNormaliser.normalize a = RingNormaliser.normalize b) (rho : Nat → Q') :
    RingNormaliser.eval rho a ≈ RingNormaliser.eval rho b :=
  poly_identity_of_normal_eq a b h rho

private theorem power_congr {a b : Q'} (h : a ≈ b) :
    ∀ k, qpow a k ≈ qpow b k
  | 0 => Q'.eqv_refl 1
  | k+1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (power_congr h k))
      (Q'.mul_eqv_congr_left _ _ _ h)

private theorem le_of_not_le {a b : Q'} (h : ¬ a ≤ b) : b ≤ a := by
  change ¬ a.num * (b.den : Int) ≤ b.num * (a.den : Int) at h
  change b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  omega

private theorem power_le_one {u : Q'} (hu0 : (0 : Q') ≤ u)
    (hu1 : u ≤ (1 : Q')) : ∀ k, qpow u k ≤ (1 : Q')
  | 0 => Q'.le_refl' 1
  | k+1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg (power_le_one hu0 hu1 k) hu1 (by decide) hu0)
      (Q'.le_of_eqv (by decide : (1 : Q') * 1 ≈ 1))

private theorem block_le_half {c u : Q'} (hc : (0 : Q') ≤ c)
    (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q'))
    (hfar : half ≤ c*(1 + -u)) : qpow u (D c) ≤ half := by
  let delta := (1 : Q') + -u
  have hd0 : (0 : Q') ≤ delta := Q'.sub_nonneg_of_le hu1
  have hd1 : delta ≤ (1 : Q') := sub_le_self' 1 hu0
  have hdouble := Q'.mul_le_mul_of_nonneg_left _ _ 2 hfar (by decide)
  have hpin : (2 : Q') * (c*delta) ≈ (2*c)*delta :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hpaid : (1 : Q') ≤ Q'.ofNat (D c)*delta :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (1 : Q') ≈ 2*half))
      (Q'.le_trans' _ _ _ hdouble
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
          (Q'.mul_le_mul_of_nonneg_right _ _ delta (D_lower c hc) hd0)))
  have hden : (2 : Q') ≤ bernDen delta (D c) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (2 : Q') ≈ 1+1))
      (Q'.add_le_add_left 1 _ _ hpaid)
  have hcomp : oneSub delta ≈ u :=
    qr (.var 1 + -(.var 1 + -(.var 0))) (.var 0) (by decide)
      (fun | 0 => u | _ => 1)
  have hbern := oneSub_pow_mul_bernDen_le hd0 hd1 (D c)
  have hbern' : qpow u (D c)*bernDen delta (D c) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv
      (Q'.mul_eqv_congr_right _ _ _ (power_congr hcomp (D c)))) hbern
  have htwice : qpow u (D c)*2 ≤ half*2 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hden (qpow_nonneg u hu0 (D c)))
      (Q'.le_trans' _ _ _ hbern' (Q'.ge_of_eqv (by decide : half*2 ≈ (1 : Q'))))
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide) htwice

/-- Explicit positive localization exponent, retaining both computed inputs. -/
def degree (c eta : Q') (heta : (0 : Q') < eta) : Nat := D c * n eta heta

theorem degree_positive (c eta : Q') (heta : (0 : Q') < eta) :
    0 < degree c eta heta :=
  Nat.mul_pos (D_positive c) (n_positive eta heta)

/-- The computed polynomial lies below the SAME supplied scalar weight.
The floor and deficit are ordinary finite arithmetic premises, not a new
analytic interface; the original-action consumer must produce them. -/
theorem half_mul_power_le {c eta h u : Q'} (heta : (0 : Q') < eta)
    (hc : (0 : Q') ≤ c) (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q'))
    (hfloor : eta ≤ h) (hdef : (1 : Q') + -h ≤ c*(1 + -u)) :
    half*qpow u (degree c eta heta) ≤ h := by
  by_cases hnear : c*(1 + -u) ≤ half
  · have hz := Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ hdef hnear)
    have hpin : half + -((1 : Q') + -h) ≈ h + -half :=
      Q'.eqv_trans _ _ _
        (qr (.var 0 + -(.var 2 + -(.var 1)))
          (.var 1 + -(.var 2 + -(.var 0))) (by decide)
          (fun | 0 => half | 1 => h | _ => 1))
        (Q'.add_eqv_congr_left h _ _
          (Q'.neg_eqv_congr _ _ (by decide : (1 : Q') + -half ≈ half)))
    have hh : half ≤ h := Q'.le_of_sub_nonneg
      (Q'.le_trans' _ _ _ hz (Q'.le_of_eqv hpin))
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ half
          (power_le_one hu0 hu1 _) (by decide))
        (Q'.le_of_eqv (Q'.mul_one_eqv half))) hh
  · have hb := block_le_half hc hu0 hu1 (le_of_not_le hnear)
    have hp : qpow u (degree c eta heta) ≤ eta :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qpow_qpow u (D c) (n eta heta)))
        (Q'.le_trans' _ _ _
          (qpow_base_mono (qpow_nonneg u hu0 (D c)) hb (n eta heta))
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_eqv_pow half _))
            (half_pow_n_le eta heta)))
    have hhalf : half*qpow u (degree c eta heta) ≤ qpow u (degree c eta heta) :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : half ≤ (1 : Q'))
          (qpow_nonneg u hu0 _)) (Q'.le_of_eqv (Q'.one_mul_eqv _))
    exact Q'.le_trans' _ _ _ hhalf (Q'.le_trans' _ _ _ hp hfloor)

#print axioms degree
#print axioms degree_positive
#print axioms half_mul_power_le

end YMGap.Continuum.PolynomialHeatLocalization
