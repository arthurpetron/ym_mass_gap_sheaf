/-
# A nontrivial antipodal-averaged heat kernel on the original Haar carrier

Average the actual finite relative heat packet over the sign of its source
quaternion. The result is invariant under EITHER endpoint sign, has both
original Haar marginals equal to one, and inherits the existing late-cutoff
headFloor by transporting actual square certificates. The same computed
kernelMap is contractive; its centered bound uses the existing nome-dependent
squaredHeatRate. An explicit even quadratic has input norm 1/24 and output
norm (w^8)^2/24, proved by its pairing with arbitrary retained polynomials.

This is a different finite kernel from the full SU(2) packet. It is suitable
for antipodally invariant polynomial observables, but is not descent of the
unchanged interacting SU(2) action: averaging shared link signs in a product
is not the product of independent face averages. No compact SO(3), topology,
interacting/OS gap, continuum theory, or every-group Yang--Mills result is
asserted. All positivity and normalization refer to the SAME quaternionHaar.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatContraction
import YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission
import YMGap.Continuum.SU2QuaternionProductHeatCenterSign

namespace YMGap.Continuum.SU2QuaternionAntipodalHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (quaternionHaar_partialHaarHeads)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission
open YMGap.Continuum.SU2QuaternionProductHeatCenterSign
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHeadChainComposition (head_pairing)
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private def sourceSelector (i : Nat) : Bool := if i < 1 then true else false
private def targetSelector (i : Nat) : Bool := if i < 1 then false else true

/-- Negate the four original source coordinates, leaving the target unchanged. -/
def sourceSign (p : RatPoly) : RatPoly := blockSign 2 sourceSelector p

/-- Negate the four target coordinates, leaving the source unchanged. -/
def targetSign (p : RatPoly) : RatPoly := blockSign 2 targetSelector p

private theorem flip_add (s : Nat → Bool) (p q : RatPoly) :
    blockSign 2 s (polyAdd p q) = polyAdd (blockSign 2 s p) (blockSign 2 s q) :=
  signSelectedPolynomial_add _ _ _ _

private theorem flip_neg (s : Nat → Bool) (p : RatPoly) :
    blockSign 2 s (polyNeg p) = polyNeg (blockSign 2 s p) :=
  signSelectedPolynomial_neg _ _ _

private theorem flip_mul (s : Nat → Bool) (p q : RatPoly) :
    RatPolyCoeffEqv (blockSign 2 s (polyMul p q))
      (polyMul (blockSign 2 s p) (blockSign 2 s q)) :=
  signSelectedPolynomial_mul_coeffEqv _ _ p q

private theorem flip_smul (s : Nat → Bool) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (blockSign 2 s (polySmul c p)) (polySmul c (blockSign 2 s p)) :=
  signSelectedPolynomial_smul_coeffEqv _ _ c p

private theorem flip_congr (s : Nat → Bool) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockSign 2 s p) (blockSign 2 s q) :=
  signSelectedPolynomial_coeffEqv _ _ h

private theorem flip_involutive (s : Nat → Bool) : ∀ p : RatPoly,
    RatPolyCoeffEqv (blockSign 2 s (blockSign 2 s p)) p
  | [] => .refl _
  | term :: rest => by
      intro weight
      simp only [blockSign, signSelectedPolynomial, List.map_cons]
      simp only [signSelectedTerm, ratWeightedSum]
      generalize hp : selectedExponentParity 8 (fun k => s (k/4)) term.1 = parity
      cases parity
      · simp only [Bool.false_eq_true, if_false]
        exact Q'.add_eqv_congr' (Q'.eqv_refl _) (flip_involutive s rest weight)
      · simp only [if_true]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_neg_eqv term.2))
          (flip_involutive s rest weight)

private theorem flips_commute (s t : Nat → Bool) (p : RatPoly) :
    blockSign 2 s (blockSign 2 t p) = blockSign 2 t (blockSign 2 s p) := by
  unfold blockSign signSelectedPolynomial
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro term _
  change signSelectedTerm 8 (fun k => s (k/4))
      (signSelectedTerm 8 (fun k => t (k/4)) term) =
    signSelectedTerm 8 (fun k => t (k/4))
      (signSelectedTerm 8 (fun k => s (k/4)) term)
  simp only [signSelectedTerm]
  cases hs : selectedExponentParity 8 (fun k => s (k/4)) term.1 <;>
    cases ht : selectedExponentParity 8 (fun k => t (k/4)) term.1 <;> rfl

private theorem flip_haar_pair (s : Nat → Bool) (p r : RatPoly) :
    quaternionHaar 2 (polyMul (blockSign 2 s p) r) ≈
      quaternionHaar 2 (polyMul p (blockSign 2 s r)) := by
  have h := (flip_mul s p (blockSign 2 s r)).trans
    ((RatPolyCoeffEqv.refl _).mul (flip_involutive s r))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff h))
    (quaternionHaar_signSelected 2 (fun k => s (k/4)) _)

private theorem flip_carrier (s : Nat → Bool) {p q : RatPoly}
    (h : HaarCarrierEqv 2 p q) : HaarCarrierEqv 2 (blockSign 2 s p) (blockSign 2 s q) := by
  intro r
  have left := Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm r _))
    (Q'.eqv_trans _ _ _ (flip_haar_pair s p r)
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm p _)))
  have right := Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm r _))
    (Q'.eqv_trans _ _ _ (flip_haar_pair s q r)
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm q _)))
  exact Q'.eqv_trans _ _ _ left (Q'.eqv_trans _ _ _ (h (blockSign 2 s r)) (Q'.eqv_symm right))

private def flip_certificate (s : Nat → Bool) : {p : RatPoly} → Certificate 2 p →
    Certificate 2 (blockSign 2 s p)
  | _, .square p hp => .ofCoeff (flip_mul s p p) (.square _ (blockSign_supported s hp))
  | _, .add P Q => by rw [flip_add]; exact .add (flip_certificate s P) (flip_certificate s Q)
  | _, .smul c hc P => .ofCoeff (flip_smul s c _) (.smul c hc (flip_certificate s P))
  | _, .transport h P => .transport (flip_carrier s h) (flip_certificate s P)

private theorem flip_cap (s : Nat → Bool) (c : Q') :
    RatPolyCoeffEqv (blockSign 2 s (cap c)) (cap c) := by
  exact (flip_smul s c polyOne).trans (by rw [blockSign_one]; exact .refl _)

private theorem flip_character (s : Nat → Bool) (p : RatPoly) : ∀ spin,
    RatPolyCoeffEqv (blockSign 2 s (characterPolynomial p spin))
      (characterPolynomial (blockSign 2 s p) spin)
  | 0 => by rw [characterPolynomial, blockSign_one]; exact .refl _
  | 1 => flip_smul s 2 p
  | n+2 => by
      change RatPolyCoeffEqv
        (blockSign 2 s (polyAdd
          (polyMul (polySmul 2 p) (characterPolynomial p (n+1)))
          (polySmul (-1) (characterPolynomial p n)))) _
      rw [flip_add]
      exact ((flip_mul s _ _).trans
        ((flip_smul s 2 p).mul (flip_character s p (n+1)))).add
        ((flip_smul s (-1) _).trans ((flip_character s p n).smul (-1)))

private theorem endpoint_scalar_pin :
    RatPolyCoeffEqv (targetSign relativeScalar) (sourceSign relativeScalar) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem endpoint_heat_pin (w : Q') (K : Nat) :
    RatPolyCoeffEqv (targetSign (relativeHeat w K)) (sourceSign (relativeHeat w K)) := by
  unfold relativeHeat
  induction List.range (K+1) with
  | nil => exact .refl _
  | cons spin spins ih =>
      change RatPolyCoeffEqv (blockSign 2 targetSelector (polyAdd _ _))
        (blockSign 2 sourceSelector (polyAdd _ _))
      rw [flip_add, flip_add]
      refine (RatPolyCoeffEqv.trans (flip_smul targetSelector _ _) ?_).add ih
      refine RatPolyCoeffEqv.trans ?_ (flip_smul sourceSelector _ _).symm
      exact ((flip_character targetSelector relativeScalar spin).trans
        ((characterPolynomial_coeffEqv endpoint_scalar_pin spin).trans
          (flip_character sourceSelector relativeScalar spin).symm)).smul _

/-- The finite center average of the literal original two-link heat packet. -/
def antipodalHeat (w : Q') (K : Nat) : RatPoly :=
  polySmul HalfPow.half (polyAdd (relativeHeat w K) (sourceSign (relativeHeat w K)))

theorem supported (w : Q') (K : Nat) : SupportedQuaternionBlocks 2 (antipodalHeat w K) :=
  by
    intro term ht
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
    exact (supported_add (relativeHeat_supported w K)
      (blockSign_supported sourceSelector (relativeHeat_supported w K))) source hs

/-- The lower endpoint may change representative independently. -/
theorem sourceSign_invariant (w : Q') (K : Nat) :
    RatPolyCoeffEqv (sourceSign (antipodalHeat w K)) (antipodalHeat w K) := by
  unfold antipodalHeat
  refine (flip_smul sourceSelector _ _).trans ?_
  rw [flip_add]
  exact (((RatPolyCoeffEqv.refl _).add (flip_involutive sourceSelector _)).trans
    (RatPolyCoeffEqv.add_comm _ _)).smul _

/-- The upper endpoint may change representative independently as well. -/
theorem targetSign_invariant (w : Q') (K : Nat) :
    RatPolyCoeffEqv (targetSign (antipodalHeat w K)) (antipodalHeat w K) := by
  have hs : RatPolyCoeffEqv (targetSign (sourceSign (relativeHeat w K))) (relativeHeat w K) := by
    change RatPolyCoeffEqv (blockSign 2 targetSelector (blockSign 2 sourceSelector _)) _
    rw [flips_commute]
    exact (flip_congr sourceSelector (endpoint_heat_pin w K)).trans
      (flip_involutive sourceSelector _)
  unfold antipodalHeat
  refine (flip_smul targetSelector _ _).trans ?_
  rw [flip_add]
  exact (((endpoint_heat_pin w K).add hs).trans (RatPolyCoeffEqv.add_comm _ _)).smul _

private theorem half_double (a : Q') : HalfPow.half * (a+a) ≈ a :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.var 0) (.add (.var 1) (.var 1)))
      (.mul (.add (.var 0) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => HalfPow.half | _ => a))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a (by decide : HalfPow.half+HalfPow.half ≈ 1))
      (Q'.one_mul_eqv a))

private theorem average_pair (w : Q') (K : Nat) (r : RatPoly) :
    quaternionHaar 2 (polyMul (antipodalHeat w K) r) ≈
      HalfPow.half * (quaternionHaar 2 (polyMul (relativeHeat w K) r) +
        quaternionHaar 2 (polyMul (sourceSign (relativeHeat w K)) r)) := by
  unfold antipodalHeat
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_)
  rw [polyMul_add_left_exact]
  exact Q'.mul_eqv_congr_left _ _ _ (quaternionHaar_append 2 _ _)

private theorem average_pair_of_source_invariant (w : Q') (K : Nat) (r : RatPoly)
    (hr : RatPolyCoeffEqv (sourceSign r) r) :
    quaternionHaar 2 (polyMul (antipodalHeat w K) r) ≈
      quaternionHaar 2 (polyMul (relativeHeat w K) r) :=
  Q'.eqv_trans _ _ _ (average_pair w K r)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (flip_haar_pair sourceSelector _ r)
          (haar_of_coeff (hr.mul_left _))))) (half_double _))

private theorem source_lift (r : RatPoly) : sourceSign (liftBoundary 1 r) = liftBoundary 1 r :=
  lowerSign_lift 1 (fun _ => true) r

/-- Lower marginal one for every original supported polynomial, at EVERY cutoff. -/
theorem lower_marginal (w : Q') (K : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks 1 f) :
    quaternionHaar 2 (polyMul (antipodalHeat w K) f) ≈ quaternionHaar 1 f := by
  have hs : sourceSign f = blockSign 1 (fun _ => true) f :=
    lowerSign_lower 1 (fun _ => true) hf
  have hfs : SupportedQuaternionBlocks 1 (sourceSign f) := by
    rw [hs]
    exact blockSign_supported _ hf
  have hm : quaternionHaar 2 (polyMul (sourceSign (relativeHeat w K)) f) ≈ quaternionHaar 1 f :=
    Q'.eqv_trans _ _ _ (flip_haar_pair sourceSelector _ f)
      (Q'.eqv_trans _ _ _ (relativeHeat_lower_marginal w K _ hfs) (by
        change quaternionHaar 1 (sourceSign f) ≈ quaternionHaar 1 f
        rw [hs]
        exact quaternionHaar_signSelected 1 (fun _ => true) f))
  exact Q'.eqv_trans _ _ _ (average_pair w K f)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr' (relativeHeat_lower_marginal w K f hf) hm)) (half_double _))

/-- Upper marginal one on the SAME original Haar functional. -/
theorem upper_marginal (w : Q') (K : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks 1 f) :
    quaternionHaar 2 (polyMul (antipodalHeat w K) (liftBoundary 1 f)) ≈ quaternionHaar 1 f :=
  Q'.eqv_trans _ _ _ (average_pair_of_source_invariant w K _ (by rw [source_lift]; exact .refl _))
    (relativeHeat_upper_marginal w K f hf)

private theorem half_double_poly (p : RatPoly) :
    RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p := by
  have hmap : polySmul HalfPow.half (polyAdd p p) =
      polyAdd (polySmul HalfPow.half p) (polySmul HalfPow.half p) := List.map_append
  rw [hmap]
  exact (RatPolyCoeffEqv.add_smul_same _ _ p).trans
    ((RatPolyCoeffEqv.smul_coefficient (by decide : HalfPow.half+HalfPow.half ≈ 1) p).trans
      (RatPolyCoeffEqv.one_smul p))

private theorem average_sub (p q a : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polySmul HalfPow.half (polyAdd p q)) (polyNeg a))
      (polySmul HalfPow.half (polyAdd (polyAdd p (polyNeg a)) (polyAdd q (polyNeg a)))) := by
  have ring := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
      (.neg (.mul (.var 0) (.add (.var 3) (.var 3)))))
    (.mul (.var 0) (.add (.add (.var 1) (.neg (.var 3))) (.add (.var 2) (.neg (.var 3)))))
    (by decide) (fun | 0 => cap HalfPow.half | 1 => p | 2 => q | _ => a)
  exact ((cap_mul_left HalfPow.half _).add
    (RatPolyCoeffEqv.neg ((cap_mul_left HalfPow.half _).trans (half_double_poly a)))).symm.trans
      (ring.trans (cap_mul_left HalfPow.half _))

/-- Constructed positive remainder above the SAME computed headFloor.
No pointwise-positivity axiom, new cutoff, or inverse normalizer is used. -/
def floorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) :
    Certificate 2 (polyAdd (antipodalHeat w K) (polyNeg (cap (headFloor w)))) := by
  let P := relativeHeat_floorCertificate hw0 hw1 K hK
  have he : RatPolyCoeffEqv
      (sourceSign (polyAdd (relativeHeat w K) (polyNeg (cap (headFloor w)))))
      (polyAdd (sourceSign (relativeHeat w K)) (polyNeg (cap (headFloor w)))) := by
    change RatPolyCoeffEqv (blockSign 2 sourceSelector (polyAdd _ _)) _
    rw [flip_add, flip_neg]
    exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (flip_cap sourceSelector _))
  let Q := Certificate.ofCoeff he.symm (flip_certificate sourceSelector P)
  exact .ofCoeff (average_sub _ _ _) (.smul HalfPow.half (by decide) (P.add Q))

def certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) : Certificate 2 (antipodalHeat w K) :=
  .smul HalfPow.half (by decide)
    ((relativeHeat_certificate hw0 hw1 K hK).add
      (flip_certificate sourceSelector (relativeHeat_certificate hw0 hw1 K hK)))

/-- Computed source integration against this averaged kernel, not the interacting transfer. -/
def antipodalMap (w : Q') (K : Nat) (f : RatPoly) : RatPoly := kernelMap 1 (antipodalHeat w K) f

theorem map_supported (w : Q') (K : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks 1 f) :
    SupportedQuaternionBlocks 1 (antipodalMap w K f) := kernelMap_supported (supported w K) hf

/-- The computed map preserves the SAME Haar mean before any positivity guard. -/
theorem map_mean (w : Q') (K : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks 1 f) :
    quaternionHaar 1 (antipodalMap w K f) ≈ quaternionHaar 1 f :=
  Q'.eqv_trans _ _ _ (quaternionHaar_partialHaarHeads 1 1 _)
    (lower_marginal w K f hf)

/-- The exact marginals give the cap-one ordinary Haar bound. -/
theorem map_square_contraction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) {f : RatPoly} (hf : SupportedQuaternionBlocks 1 f) :
    quaternionHaar 1 (polyMul (antipodalMap w K f) (antipodalMap w K f)) ≤
      quaternionHaar 1 (polyMul f f) :=
  kernelMap_square_contraction (lower_marginal w K) (upper_marginal w K)
    (certificate hw0 hw1 K hK) (supported w K) hf

/-- Same supplied nome-dependent rate, applied to this actual centered map. -/
theorem map_centered_square_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) {f : RatPoly} (hf : SupportedQuaternionBlocks 1 f)
    (hc : quaternionHaar 1 f ≈ 0) :
    quaternionHaar 1 (polyMul (antipodalMap w K f) (antipodalMap w K f)) ≤
      squaredHeatRate w * quaternionHaar 1 (polyMul f f) :=
  kernelMap_centered_square_bound (lower_marginal w K) (upper_marginal w K)
    (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide))
    (floorCertificate hw0 hw1 K hK) (supported w K) hf hc

/-- Explicit nonzero antipodally even polynomial on the original one-link carrier. -/
def evenMode : RatPoly := quadratic 0 1

theorem evenMode_supported : SupportedQuaternionBlocks 1 evenMode := by
  have hb : evenMode.all (fun term => decide (term.1.length ≤ 4)) = true := by decide +kernel
  intro term ht
  exact of_decide_eq_true ((List.all_eq_true.mp hb) term ht)

theorem evenMode_sourceSign : RatPolyCoeffEqv (sourceSign evenMode) evenMode := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

theorem evenMode_haar_norm :
    quaternionHaar 1 (polyMul evenMode evenMode) ≈ Q'.mkPos 1 24 (by decide) :=
  off_diagonal_haar_norm

theorem evenMode_haar_mean_zero : quaternionHaar 1 evenMode ≈ 0 := by decide +kernel

/-- The surviving quadratic image is centered in the original Haar law. -/
theorem evenMode_map_mean_zero (w : Q') (K : Nat) :
    quaternionHaar 1 (antipodalMap w K evenMode) ≈ 0 :=
  Q'.eqv_trans _ _ _ (map_mean w K evenMode_supported) evenMode_haar_mean_zero

/-- Full retained insertion and exact w^8 image at every cutoff containing label two. -/
theorem evenMode_transmission (w : Q') (K : Nat) (hK : 2 ≤ K) (r : RatPoly) :
    quaternionHaar 2 (polyMul (polyMul (antipodalHeat w K) evenMode) (liftBoundary 1 r)) ≈
      qpow w 8 * quaternionHaar 1 (polyMul evenMode r) := by
  have hi : RatPolyCoeffEqv (sourceSign (polyMul evenMode (liftBoundary 1 r)))
      (polyMul evenMode (liftBoundary 1 r)) := by
    refine (flip_mul sourceSelector _ _).trans ?_
    exact evenMode_sourceSign.mul (by
      change RatPolyCoeffEqv (sourceSign (liftBoundary 1 r)) (liftBoundary 1 r)
      rw [source_lift]
      exact .refl _)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
    (Q'.eqv_trans _ _ _ (average_pair_of_source_invariant w K _ hi)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
        (quadratic_heat_transmission 1 (by decide) w K hK 0 1 r)))

private theorem map_pairing (w : Q') (K : Nat) (f r : RatPoly) :
    quaternionHaar 1 (polyMul (antipodalMap w K f) r) ≈
      quaternionHaar 2 (polyMul (polyMul (antipodalHeat w K) f) (liftBoundary 1 r)) :=
  Q'.eqv_symm (head_pairing 1 1 (polyMul (antipodalHeat w K) f) r)

/-- Actual OUTPUT norm: the average has not collapsed to the constant kernel.
The displayed coefficient is w^16/24, kept in the existing qpow convention. -/
theorem evenMode_map_norm (w : Q') (K : Nat) (hK : 2 ≤ K) :
    quaternionHaar 1 (polyMul (antipodalMap w K evenMode) (antipodalMap w K evenMode)) ≈
      (qpow w 8 * qpow w 8) * Q'.mkPos 1 24 (by decide) := by
  have pair (r : RatPoly) :
      quaternionHaar 1 (polyMul (antipodalMap w K evenMode) r) ≈
        qpow w 8 * quaternionHaar 1 (polyMul evenMode r) :=
    Q'.eqv_trans _ _ _ (map_pairing w K evenMode r) (evenMode_transmission w K hK r)
  have hcross := Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm evenMode _))
    (Q'.eqv_trans _ _ _ (pair evenMode) (Q'.mul_eqv_congr_left _ _ _ evenMode_haar_norm))
  exact Q'.eqv_trans _ _ _ (pair (antipodalMap w K evenMode))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hcross)
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))

private theorem power_positive {w : Q'} (hw : (0 : Q') < w) : ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_positive hw n) hw

theorem evenMode_map_norm_positive {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (hK : 2 ≤ K) :
    (0 : Q') < quaternionHaar 1
      (polyMul (antipodalMap w K evenMode) (antipodalMap w K evenMode)) :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos (Q'.mul_pos (power_positive hw 8) (power_positive hw 8))
      (by decide : (0 : Q') < Q'.mkPos 1 24 (by decide)))
    (Q'.ge_of_eqv (evenMode_map_norm w K hK))

end YMGap.Continuum.SU2QuaternionAntipodalHeat

#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.sourceSign
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.targetSign
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.antipodalHeat
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.supported
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.sourceSign_invariant
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.targetSign_invariant
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.lower_marginal
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.upper_marginal
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.floorCertificate
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.certificate
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.antipodalMap
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.map_supported
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.map_mean
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.map_square_contraction
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.map_centered_square_bound
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode_supported
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode_sourceSign
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode_haar_norm
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode_haar_mean_zero
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode_map_mean_zero
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode_transmission
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode_map_norm
#print axioms YMGap.Continuum.SU2QuaternionAntipodalHeat.evenMode_map_norm_positive
