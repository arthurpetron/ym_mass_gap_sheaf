/-
# Centered susceptibility on an original weighted Haar carrier

The weight is an actual square-certified polynomial, including all shared
coordinates. A zero-mean response polynomial pairs only with the centered
observable. Cauchy--Schwarz therefore retains its variance rather than an
uncentered sup norm. No independence, OS-norm identification or spatial
summability is asserted. The consumer is the normalized two-nome face score.
-/
import YMGap.Continuum.QuaternionHaarNormalizedMomentLinear

namespace YMGap.Continuum.QuaternionHaarCenteredResponse

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem normalized_pair {n : Nat} {W : RatPoly}
    (hW : (0 : Q') < quaternionHaar n W) (p q : RatPoly) :
    weightedPair n W p q * Q'.recipPos (quaternionHaar n W) hW ≈
      normalizedMoment n W (polyMul p q) hW :=
  Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))

/-- Sharp Cauchy--Schwarz after dividing by the SAME actual positive mass. -/
theorem normalized_cauchySchwarz {n : Nat} {W p q : RatPoly}
    (H : Certificate n W) (hW : (0 : Q') < quaternionHaar n W)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    normalizedMoment n W (polyMul p q) hW * normalizedMoment n W (polyMul p q) hW ≤
      normalizedMoment n W (polyMul p p) hW * normalizedMoment n W (polyMul q q) hW := by
  let r := Q'.recipPos (quaternionHaar n W) hW
  have shuffle (a b : Q') : (a*r)*(b*r) ≈ (a*b)*(r*r) := by
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (r*r)
    (weighted_cauchySchwarz n W p q H hp hq)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos _ hW))
      (Q'.le_of_lt (Q'.recipPos_pos _ hW)))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (qmul (normalized_pair hW p q) (normalized_pair hW p q)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (shuffle _ _))
      (Q'.le_trans' _ _ _ hm (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (shuffle _ _))
        (Q'.le_of_eqv (qmul (normalized_pair hW p p) (normalized_pair hW q q))))))

/-- Centering the probe costs nothing when the response has actual mean zero. -/
theorem centered_pair_pin {n : Nat} {W p q : RatPoly}
    (hW : (0 : Q') < quaternionHaar n W)
    (hq : normalizedMoment n W q hW ≈ 0) (c : Q') :
    normalizedMoment n W (polyMul (shifted p c) q) hW ≈
      normalizedMoment n W (polyMul p q) hW := by
  have hc : RatPolyCoeffEqv (polyMul (shifted p c) q)
      (polyAdd (polySmul 1 (polyMul p q)) (polySmul (-c) q)) := by
    unfold shifted
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.polyMul_smul_left 1 p q).add
        ((RatPolyCoeffEqv.polyMul_smul_left (-c) polyOne q).trans
          ((RatPolyCoeffEqv.one_mul q).smul (-c)))
  have he := QuaternionHaarNormalizedMomentCongruence.normalizedMoment_congr hW hW
    (RatPolyCoeffEqv.refl W) hc
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ (normalizedMoment_add hW)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (normalizedMoment_smul hW) (Q'.one_mul_eqv _))
        (Q'.eqv_trans _ _ _ (normalizedMoment_smul hW)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hq) (Q'.mul_zero_eqv _))))
      (Q'.eqv_of_eq (Q'.add_zero' _))))

/-- Both sides are on the retained background, with the exact observable
variance. In particular, a constant observable has zero response. -/
theorem centered_response_square_bound {n : Nat} {W p q : RatPoly}
    (H : Certificate n W) (hW : (0 : Q') < quaternionHaar n W)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (hq0 : normalizedMoment n W q hW ≈ 0) :
    normalizedMoment n W (polyMul p q) hW * normalizedMoment n W (polyMul p q) hW ≤
      normalizedVariance n W p hW * normalizedMoment n W (polyMul q q) hW := by
  have hpair := centered_pair_pin (p := p) hW hq0 (normalizedMoment n W p hW)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hpair hpair))
    (Q'.le_trans' _ _ _
      (normalized_cauchySchwarz H hW (shifted_supported hp _) hq)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (own_mean_pin H hp hW))))

/-- The actual local factor divided by its expectation in the retained background.
Only scalar positive Haar masses are inverted, never a polynomial. -/
def normalizedFactor (n : Nat) (B V : RatPoly)
    (hV : (0 : Q') < quaternionHaar n (polyMul B V)) : RatPoly :=
  polySmul (quaternionHaar n B * Q'.recipPos (quaternionHaar n (polyMul B V)) hV) V

/-- Signed normalized-factor contrast. Its background mean is exactly zero. -/
def responsePolynomial (n : Nat) (B U V : RatPoly)
    (hU : (0 : Q') < quaternionHaar n (polyMul B U))
    (hV : (0 : Q') < quaternionHaar n (polyMul B V)) : RatPoly :=
  polyAdd (normalizedFactor n B V hV) (polySmul (-1) (normalizedFactor n B U hU))

private theorem support_smul {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem responsePolynomial_supported {n : Nat} {B U V : RatPoly}
    (hU : (0 : Q') < quaternionHaar n (polyMul B U))
    (hV : (0 : Q') < quaternionHaar n (polyMul B V))
    (hu : SupportedQuaternionBlocks n U) (hv : SupportedQuaternionBlocks n V) :
    SupportedQuaternionBlocks n (responsePolynomial n B U V hU hV) :=
  supported_add (support_smul hv _) (support_smul (support_smul hu _) (-1))

private theorem factor_pair {n : Nat} {B V : RatPoly}
    (hB : (0 : Q') < quaternionHaar n B)
    (hV : (0 : Q') < quaternionHaar n (polyMul B V)) (p : RatPoly) :
    normalizedMoment n B (polyMul p (normalizedFactor n B V hV)) hB ≈
      normalizedMoment n (polyMul B V) p hV := by
  let z := quaternionHaar n B
  let r := Q'.recipPos (quaternionHaar n (polyMul B V)) hV
  have he := QuaternionHaarNormalizedMomentCongruence.normalizedMoment_congr hB hB
    (RatPolyCoeffEqv.refl B) (RatPolyCoeffEqv.polyMul_smul_right (z*r) p V)
  have hs : (z*r)*normalizedMoment n B (polyMul p V) hB ≈
      (normalizedMoment n B (polyMul V p) hB*z)*r := by
    have hc : (z*r)*normalizedMoment n B (polyMul p V) hB ≈
        (normalizedMoment n B (polyMul p V) hB*z)*r := by
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.mul_num_cast, Q'.mul_den_cast]
      ac_rfl
    exact Q'.eqv_trans _ _ _ hc
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (normalizedMoment_mul_symm hB)))
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ (normalizedMoment_smul hB)
    (Q'.eqv_trans _ _ _ hs normalizedMoment_reweight))

/-- Exact two-density response, before taking an absolute value or replacing
the signed contrast by separate endpoint bounds. Every partition is retained. -/
theorem response_pin {n : Nat} {B U V : RatPoly}
    (hB : (0 : Q') < quaternionHaar n B)
    (hU : (0 : Q') < quaternionHaar n (polyMul B U))
    (hV : (0 : Q') < quaternionHaar n (polyMul B V)) (p : RatPoly) :
    normalizedMoment n B (polyMul p (responsePolynomial n B U V hU hV)) hB ≈
      normalizedMoment n (polyMul B V) p hV +
        -(normalizedMoment n (polyMul B U) p hU) := by
  have hc := QuaternionHaarNormalizedMomentCongruence.normalizedMoment_congr hB hB
    (RatPolyCoeffEqv.refl B) ((RatPolyCoeffEqv.mul_add_right p
      (normalizedFactor n B V hV) (polySmul (-1) (normalizedFactor n B U hU))).trans
      ((RatPolyCoeffEqv.refl (polyMul p (normalizedFactor n B V hV))).add
        (RatPolyCoeffEqv.polyMul_smul_right (-1) p (normalizedFactor n B U hU))))
  have hneg : (-1 : Q')*normalizedMoment n B (polyMul p (normalizedFactor n B U hU)) hB ≈
      -(normalizedMoment n (polyMul B U) p hU) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (factor_pair hB hU p))
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => normalizedMoment n (polyMul B U) p hU))
  exact Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ (normalizedMoment_add hB)
    (Q'.add_eqv_congr' (factor_pair hB hV p)
      (Q'.eqv_trans _ _ _ (normalizedMoment_smul hB) hneg)))

theorem response_centered {n : Nat} {B U V : RatPoly}
    (hB : (0 : Q') < quaternionHaar n B)
    (hU : (0 : Q') < quaternionHaar n (polyMul B U))
    (hV : (0 : Q') < quaternionHaar n (polyMul B V)) :
    normalizedMoment n B (responsePolynomial n B U V hU hV) hB ≈ 0 := by
  have hc := QuaternionHaarNormalizedMomentCongruence.normalizedMoment_congr hB hB
    (RatPolyCoeffEqv.refl B) (RatPolyCoeffEqv.one_mul (responsePolynomial n B U V hU hV))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hc)
    (Q'.eqv_trans _ _ _ (response_pin hB hU hV polyOne)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (normalizedMoment_one hV)
        (Q'.neg_eqv_congr _ _ (normalizedMoment_one hU))) (by decide)))

/-- An actual finite two-density estimate: the centered score is constructed,
and its retained-background second moment is its variance. No analytic
response bound is an input. Summability of these local costs remains separate. -/
theorem reweighting_variance_bound {n : Nat} {B U V p : RatPoly}
    (H : Certificate n B) (hB : (0 : Q') < quaternionHaar n B)
    (hU : (0 : Q') < quaternionHaar n (polyMul B U))
    (hV : (0 : Q') < quaternionHaar n (polyMul B V))
    (hp : SupportedQuaternionBlocks n p)
    (hu : SupportedQuaternionBlocks n U) (hv : SupportedQuaternionBlocks n V) :
    let d := normalizedMoment n (polyMul B V) p hV +
      -(normalizedMoment n (polyMul B U) p hU)
    let s := responsePolynomial n B U V hU hV
    d*d ≤ normalizedVariance n B p hB * normalizedMoment n B (polyMul s s) hB := by
  have hpq := response_pin hB hU hV p
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hpq hpq))
    (centered_response_square_bound H hB hp (responsePolynomial_supported hU hV hu hv)
      (response_centered hB hU hV))

end YMGap.Continuum.QuaternionHaarCenteredResponse

#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.normalized_cauchySchwarz
#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.centered_pair_pin
#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.centered_response_square_bound
#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.normalizedFactor
#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.responsePolynomial
#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.responsePolynomial_supported
#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.response_pin
#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.response_centered
#print axioms YMGap.Continuum.QuaternionHaarCenteredResponse.reweighting_variance_bound
