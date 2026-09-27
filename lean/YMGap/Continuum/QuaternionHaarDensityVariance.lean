/-
# A normalized variance floor from an actual Haar density certificate

The density W and its positive mass Z = H(W) remain unchanged throughout.
A certificate for W - delta*Z gives normalized domination of every supported
polynomial square by delta times its bare quaternion-Haar integral. Testing
at the explicitly computed W-mean proves the corresponding variance floor.

The density comparison is an explicit certificate input, to be supplied by
the actual finite-density producer. No alternative probability law,
independence hypothesis, choice of center, or reflected-norm identification
is introduced here. In particular a supported Haar-centered polynomial of
bare second moment one has normalized W-variance at least delta.
-/

import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.RationalVarianceComparison
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.QuaternionHaarDensityVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-- The raw W-moment divided by the SAME actual Haar mass of W. -/
def normalizedMoment (blocks : Nat) (W p : RatPoly)
    (hZ : (0 : Q') < quaternionHaar blocks W) : Q' :=
  quaternionHaar blocks (polyMul W p) * Q'.recipPos (quaternionHaar blocks W) hZ

/-- Variance centered at the actual explicitly computed normalized W-mean. -/
def normalizedVariance (blocks : Nat) (W p : RatPoly)
    (hZ : (0 : Q') < quaternionHaar blocks W) : Q' :=
  normalizedMoment blocks W (polyMul p p) hZ +
    -(normalizedMoment blocks W p hZ * normalizedMoment blocks W p hZ)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one blocks))
    (Q'.eqv_refl _)) (Q'.eqv_of_eq (Q'.add_zero' 1))

private def densityCertificate {blocks : Nat} {W : RatPoly} {delta : Q'}
    (hZ : (0 : Q') < quaternionHaar blocks W) (hd : (0 : Q') ≤ delta)
    (D : Certificate blocks
      (polyAdd W (polyNeg (cap (delta*quaternionHaar blocks W))))) :
    Certificate blocks W :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => W | _ => cap (delta*quaternionHaar blocks W)))
    (D.add (.constant blocks (delta*quaternionHaar blocks W)
      (Q'.mul_nonneg _ _ hd (Q'.le_of_lt hZ))))

/-- An actual density-floor certificate dominates every supported square. -/
theorem raw_square_floor {blocks : Nat} {W p : RatPoly} {c : Q'}
    (D : Certificate blocks (polyAdd W (polyNeg (cap c))))
    (hp : SupportedQuaternionBlocks blocks p) :
    c * quaternionHaar blocks (polyMul p p) ≤
      quaternionHaar blocks (polyMul W (polyMul p p)) := by
  let s := polyMul p p
  have hpos := D.square_insertion_nonnegative p hp
  have hcap : quaternionHaar blocks (polyMul (cap c) s) ≈ c*quaternionHaar blocks s :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c s))
      (quaternionHaar_polySmul blocks c s)
  have he : quaternionHaar blocks (polyMul s (polyAdd W (polyNeg (cap c)))) ≈
      quaternionHaar blocks (polyMul W s) + -(c*quaternionHaar blocks s) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 2) (.var 0))))
      (by decide) (fun | 0 => s | 1 => W | _ => cap c)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (haar_neg blocks _) (Q'.neg_eqv_congr _ _ hcap))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))

/-- Normalized domination of every supported square. Only the actual mass
Z is inverted, using its supplied positive-mass proof. -/
theorem normalized_square_floor {blocks : Nat} {W : RatPoly} {delta : Q'}
    (hZ : (0 : Q') < quaternionHaar blocks W) (_hd : (0 : Q') ≤ delta)
    (D : Certificate blocks
      (polyAdd W (polyNeg (cap (delta*quaternionHaar blocks W)))))
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    delta * quaternionHaar blocks (polyMul p p) ≤
      normalizedMoment blocks W (polyMul p p) hZ := by
  let Z := quaternionHaar blocks W
  let r := Q'.recipPos Z hZ
  let s := quaternionHaar blocks (polyMul p p)
  have he : ((delta*Z)*s)*r ≈ delta*s :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => delta | 1 => Z | 2 => s | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_right _ _ r (raw_square_floor D hp)
      (Q'.le_of_lt (Q'.recipPos_pos Z hZ)))

/-- Subtract a rational constant without changing the original polynomial carrier. -/
def shifted (p : RatPoly) (c : Q') : RatPoly :=
  polyAdd (polySmul 1 p) (polySmul (-c) polyOne)

private theorem supported_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem shifted_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (shifted p c) :=
  supported_add (supported_smul hp 1) (supported_smul (supported_one blocks) (-c))

private theorem shifted_square_pin {blocks : Nat} {W p : RatPoly}
    (P : Certificate blocks W) (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    quaternionHaar blocks (polyMul W (polyMul (shifted p c) (shifted p c))) ≈
      quaternionHaar blocks (polyMul W (polyMul p p)) +
        -(2*c*quaternionHaar blocks (polyMul W p)) +
        c*c*quaternionHaar blocks W := by
  let G := weightedGNSData blocks W P
  have h := G.diag_expand 1 (-c) ⟨p,hp⟩ ⟨polyOne,supported_one blocks⟩
  have hb : weightedPair blocks W p p ≈ quaternionHaar blocks (polyMul W (polyMul p p)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have ha : weightedPair blocks W p polyOne ≈ quaternionHaar blocks (polyMul W p) :=
    haar_of_coeff (((RatPolyCoeffEqv.mul_one p).mul_right W).trans
      (RatPolyCoeffEqv.mul_comm _ _))
  have hz : weightedPair blocks W polyOne polyOne ≈ quaternionHaar blocks W :=
    haar_of_coeff (((RatPolyCoeffEqv.one_mul polyOne).mul_right W).trans
      (RatPolyCoeffEqv.one_mul W))
  have ht := Q'.eqv_trans _ _ _ h (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl 1) (qmul (Q'.eqv_refl 1) hb))
      (qmul (Q'.eqv_refl 1) (qmul (Q'.eqv_refl (-c)) ha)))
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl (-c)) (qmul (Q'.eqv_refl 1) ha))
      (qmul (Q'.eqv_refl (-c)) (qmul (Q'.eqv_refl (-c)) hz))))
  have hs : quaternionHaar blocks (polyMul W (polyMul (shifted p c) (shifted p c))) ≈
      weightedPair blocks W (shifted p c) (shifted p c) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  exact Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _ ht
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
        (.mul (.const 1) (.mul (.neg (.var 3)) (.var 1))))
        (.add (.mul (.neg (.var 3)) (.mul (.const 1) (.var 1)))
          (.mul (.neg (.var 3)) (.mul (.neg (.var 3)) (.var 2)))))
      (.add (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 3)) (.var 1))))
        (.mul (.mul (.var 3) (.var 3)) (.var 2))) (by decide)
      (fun
        | 0 => quaternionHaar blocks (polyMul W (polyMul p p))
        | 1 => quaternionHaar blocks (polyMul W p)
        | 2 => quaternionHaar blocks W
        | _ => c)))

/-- Exact shifted-square expansion in the SAME certified density. This public
adapter exposes the existing algebra without assuming a variance estimate. -/
theorem shifted_moment_expansion {blocks : Nat} {W p : RatPoly}
    (P : Certificate blocks W) (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    quaternionHaar blocks (polyMul W (polyMul (shifted p c) (shifted p c))) ≈
      quaternionHaar blocks (polyMul W (polyMul p p)) +
        -(2*c*quaternionHaar blocks (polyMul W p)) +
        c*c*quaternionHaar blocks W := shifted_square_pin P hp c

/-- The actual normalized W-variance is no larger than the W-square
centered at any supplied rational constant. -/
theorem normalized_variance_le_shifted {blocks : Nat} {W p : RatPoly}
    (P : Certificate blocks W) (hp : SupportedQuaternionBlocks blocks p)
    (hZ : (0 : Q') < quaternionHaar blocks W) (c : Q') :
    normalizedVariance blocks W p hZ ≤
      normalizedMoment blocks W (polyMul (shifted p c) (shifted p c)) hZ := by
  let z := quaternionHaar blocks W
  let a := quaternionHaar blocks (polyMul W p)
  let b := quaternionHaar blocks (polyMul W (polyMul p p))
  let s := Q'.recipPos z hZ
  have h := RationalVarianceComparison.variance_le_quadratic z a b s c
    (Q'.mul_recipPos_eqv z hZ)
  change normalizedVariance blocks W p hZ ≤
    RationalVarianceComparison.quadratic z a b s c at h
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ s
      (Q'.eqv_symm (shifted_square_pin P hp c))))

/-- Any rational center has bare squared norm at least the bare variance. -/
theorem bare_variance_le_shifted {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    quaternionHaar blocks (polyMul p p) +
        -(quaternionHaar blocks p * quaternionHaar blocks p) ≤
      quaternionHaar blocks (polyMul (shifted p c) (shifted p c)) := by
  let a := quaternionHaar blocks p
  let b := quaternionHaar blocks (polyMul p p)
  have he : quaternionHaar blocks (polyMul (shifted p c) (shifted p c)) ≈
      b + -(2*c*a) + c*c*1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
      (Q'.eqv_trans _ _ _ (shifted_square_pin (Certificate.one blocks) hp c)
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (haar_of_coeff (RatPolyCoeffEqv.one_mul _))
            (Q'.neg_eqv_congr _ _
              (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul p)))))
          (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks))))
  have hvar : RationalVarianceComparison.variance a b 1 ≈ b + -(a*a) :=
    Q'.add_eqv_congr' (Q'.mul_one_eqv b)
      (Q'.neg_eqv_congr _ _ (qmul (Q'.mul_one_eqv a) (Q'.mul_one_eqv a)))
  have hquad : RationalVarianceComparison.quadratic 1 a b 1 c ≈
      quaternionHaar blocks (polyMul (shifted p c) (shifted p c)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.eqv_symm he)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hvar)
    (Q'.le_trans' _ _ _
      (RationalVarianceComparison.variance_le_quadratic 1 a b 1 c (by decide))
      (Q'.le_of_eqv hquad))

/-- Centering at the bare Haar mean gives exactly the bare variance. -/
theorem bare_mean_pin {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    quaternionHaar blocks
        (polyMul (shifted p (quaternionHaar blocks p))
          (shifted p (quaternionHaar blocks p))) ≈
      quaternionHaar blocks (polyMul p p) +
        -(quaternionHaar blocks p * quaternionHaar blocks p) := by
  let a := quaternionHaar blocks p
  let b := quaternionHaar blocks (polyMul p p)
  have he : quaternionHaar blocks (polyMul (shifted p a) (shifted p a)) ≈
      b + -(2*a*a) + a*a*1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
      (Q'.eqv_trans _ _ _ (shifted_square_pin (Certificate.one blocks) hp a)
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (haar_of_coeff (RatPolyCoeffEqv.one_mul _))
            (Q'.neg_eqv_congr _ _
              (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul p)))))
          (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks))))
  have hquad : b + -(2*a*a) + a*a*1 ≈
      RationalVarianceComparison.quadratic 1 a b 1 (a*1) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 1)) (.var 1))))
        (.mul (.mul (.var 1) (.var 1)) (.const 1)))
      (.mul
        (.add (.add (.var 0)
          (.neg (.mul (.mul (.const 2) (.mul (.var 1) (.const 1))) (.var 1))))
          (.mul (.mul (.mul (.var 1) (.const 1)) (.mul (.var 1) (.const 1)))
            (.const 1)))
        (.const 1))
      (by decide) (fun | 0 => b | _ => a)
  have hvar : RationalVarianceComparison.variance a b 1 ≈ b + -(a*a) :=
    Q'.add_eqv_congr' (Q'.mul_one_eqv b)
      (Q'.neg_eqv_congr _ _ (qmul (Q'.mul_one_eqv a) (Q'.mul_one_eqv a)))
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _ hquad
      (Q'.eqv_trans _ _ _
        (RationalVarianceComparison.quadratic_minimizer 1 a b 1 (by decide)) hvar))

/-- The original centered square is exactly its normalized variance. -/
theorem own_mean_pin {blocks : Nat} {W p : RatPoly}
    (P : Certificate blocks W) (hp : SupportedQuaternionBlocks blocks p)
    (hZ : (0 : Q') < quaternionHaar blocks W) :
    normalizedMoment blocks W
        (polyMul (shifted p (normalizedMoment blocks W p hZ))
          (shifted p (normalizedMoment blocks W p hZ))) hZ ≈
      normalizedVariance blocks W p hZ :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.recipPos (quaternionHaar blocks W) hZ)
      (shifted_square_pin P hp (normalizedMoment blocks W p hZ)))
    (RationalVarianceComparison.quadratic_minimizer
      (quaternionHaar blocks W) (quaternionHaar blocks (polyMul W p))
      (quaternionHaar blocks (polyMul W (polyMul p p)))
      (Q'.recipPos (quaternionHaar blocks W) hZ)
      (Q'.mul_recipPos_eqv _ hZ))

/-- General lower comparison with bare Haar variance. The center tested on
both sides is the explicit mean of the actual normalized density W. -/
theorem normalized_variance_comparison {blocks : Nat} {W : RatPoly} {delta : Q'}
    (hZ : (0 : Q') < quaternionHaar blocks W) (hd : (0 : Q') ≤ delta)
    (D : Certificate blocks
      (polyAdd W (polyNeg (cap (delta*quaternionHaar blocks W)))))
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    delta * (quaternionHaar blocks (polyMul p p) +
        -(quaternionHaar blocks p * quaternionHaar blocks p)) ≤
      normalizedVariance blocks W p hZ := by
  let mean := normalizedMoment blocks W p hZ
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ delta (bare_variance_le_shifted hp mean) hd)
    (Q'.le_trans' _ _ _ (normalized_square_floor hZ hd D (shifted_supported hp mean))
      (Q'.le_of_eqv (own_mean_pin (densityCertificate hZ hd D) hp hZ)))

/-- A Haar-centered unit-second-moment probe has actual normalized W-variance
at least delta. These are exact Haar moments of p, not a substitute law. -/
theorem normalized_variance_floor {blocks : Nat} {W : RatPoly} {delta : Q'}
    (hZ : (0 : Q') < quaternionHaar blocks W) (hd : (0 : Q') ≤ delta)
    (D : Certificate blocks
      (polyAdd W (polyNeg (cap (delta*quaternionHaar blocks W)))))
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p)
    (hp0 : quaternionHaar blocks p ≈ 0)
    (hp2 : quaternionHaar blocks (polyMul p p) ≈ 1) :
    delta ≤ normalizedVariance blocks W p hZ := by
  have hv : quaternionHaar blocks (polyMul p p) +
      -(quaternionHaar blocks p * quaternionHaar blocks p) ≈ 1 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hp2 (Q'.neg_eqv_congr _ _ (qmul hp0 hp0))) (by decide)
  have hdv : delta * (quaternionHaar blocks (polyMul p p) +
      -(quaternionHaar blocks p * quaternionHaar blocks p)) ≈ delta :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hv) (Q'.mul_one_eqv delta)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hdv)
    (normalized_variance_comparison hZ hd D hp)

end YMGap.Continuum.QuaternionHaarDensityVariance

#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.raw_square_floor
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.shifted_moment_expansion
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.normalized_variance_le_shifted
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.bare_variance_le_shifted
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.bare_mean_pin
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.normalizedMoment
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.normalizedVariance
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.shifted
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.shifted_supported
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.own_mean_pin
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.normalized_square_floor
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.normalized_variance_comparison
#print axioms YMGap.Continuum.QuaternionHaarDensityVariance.normalized_variance_floor
