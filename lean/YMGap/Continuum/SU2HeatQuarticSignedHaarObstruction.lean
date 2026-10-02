/-
# An original-Haar signed quadratic witness at the finite cutoff edge

The endpoint is an explicitly specialized original solid character of degree
K+2. Its one-link Haar norm is one, proved from original harmonic reproduction
and retained-coefficient specialization. No free character-packet Haar model
is substituted. The original relative heat prefix annihilates this endpoint,
but its squared-chord product has the strictly positive top coefficient.

For arbitrary affine coefficients c,e, the SAME-cutoff squared-nome majorant
therefore has a negative ORIGINAL two-link quadratic pairing. This prunes a
universal signed-source transport rule, not a bound for the particular Wilson
endpoint source, its OWN variance, the actual response, or continuum survival.
-/

import YMGap.Continuum.SU2HeatQuarticSignedCoefficientObstruction
import YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
import YMGap.Continuum.SU2QuaternionHeatQuarticMoment

namespace YMGap.Continuum.SU2HeatQuarticSignedHaarObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionHaarSparseEquality
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection
open YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionTailEvaluation
open YMGap.Continuum.SU2QuaternionTailEvaluationDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionHeatQuarticMoment
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion (defect)
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup
open YMGap.Continuum.SU2HeatQuarticSignedCoefficientObstruction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RGTransport (dimQ)
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr const_mul_finSum)

local infix:50 " ≈ " => Q'.eqv

private def raw (n : Nat) : RatPoly :=
  evaluateTail 8 auxiliaryUnits (exposedSolidZonalCharacter false true false false n)

/-- An explicit real one-link endpoint; the specialized auxiliary links are
coefficients only. The actual two links of the quadratic pairing remain Haar
variables. -/
def endpoint (n : Nat) : RatPoly := evaluateTail 4 auxiliaryUnits (raw n)

theorem endpoint_supported (n : Nat) : SupportedQuaternionBlocks 1 (endpoint n) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact Nat.le_trans (List.length_take_le _ _) (by decide)

private theorem raw_degree (n : Nat) : HasQuaternionBlockDegree 0 n (raw n) :=
  evaluate_headDegree 8 auxiliaryUnits (by decide)
    (exposedSolidZonalCharacter_blockDegree false true false false 0 (by decide) n)

private theorem raw_harmonic (n : Nat) :
    RatPolyCoeffEqv (headLaplacian (raw n)) polyZero :=
  (evaluate_headLaplacian 8 auxiliaryUnits (by decide) _).trans
    (evaluate_congr 8 auxiliaryUnits
      (laplacian_exposedSolidZonalCharacter_zero false true false false n))

theorem endpoint_degree (n : Nat) : HasQuaternionBlockDegree 0 n (endpoint n) :=
  evaluate_headDegree 4 auxiliaryUnits (by decide) (raw_degree n)

theorem endpoint_harmonic (n : Nat) :
    RatPolyCoeffEqv (headLaplacian (endpoint n)) polyZero :=
  (evaluate_headLaplacian 4 auxiliaryUnits (by decide) _).trans
    (evaluate_congr 4 auxiliaryUnits (raw_harmonic n))

private theorem solid_congr {s s' r r' : RatPoly}
    (hs : RatPolyCoeffEqv s s') (hr : RatPolyCoeffEqv r r') : ∀ n,
    RatPolyCoeffEqv (solidZonalCharacterPolynomial s r n)
      (solidZonalCharacterPolynomial s' r' n)
  | 0 => .refl _
  | 1 => hs.smul 2
  | n+2 => ((hs.smul 2).mul (solid_congr hs hr (n+1))).add
      ((hr.mul (solid_congr hs hr n)).smul (-1))

private theorem solid_carrier_congr {blocks : Nat} {s s' r r' : RatPoly}
    (hs : QuaternionHaarCarrierEqv blocks s s')
    (hr : QuaternionHaarCarrierEqv blocks r r') : ∀ n,
    QuaternionHaarCarrierEqv blocks (solidZonalCharacterPolynomial s r n)
      (solidZonalCharacterPolynomial s' r' n)
  | 0 => QuaternionHaarCarrierEqv.refl blocks _
  | 1 => hs.smul 2
  | n+2 => ((hs.smul 2).mul (solid_carrier_congr hs hr (n+1))).add
      ((hr.mul (solid_carrier_congr hs hr n)).smul (-1))

private theorem evaluate_solid (keep : Nat) (rho : Nat → Q') (s r : RatPoly) : ∀ n,
    RatPolyCoeffEqv (evaluateTail keep rho (solidZonalCharacterPolynomial s r n))
      (solidZonalCharacterPolynomial (evaluateTail keep rho s) (evaluateTail keep rho r) n)
  | 0 => evaluate_one keep rho
  | 1 => evaluate_smul keep rho 2 s
  | n+2 => by
      change RatPolyCoeffEqv (evaluateTail keep rho (polyAdd
        (polyMul (polySmul 2 s) (solidZonalCharacterPolynomial s r (n+1)))
        (polySmul (-1) (polyMul r (solidZonalCharacterPolynomial s r n))))) _
      rw [evaluate_add]
      exact ((evaluate_mul keep rho _ _).trans
        ((evaluate_smul keep rho 2 s).mul (evaluate_solid keep rho s r (n+1)))).add
        ((evaluate_smul keep rho (-1) _).trans
          (((evaluate_mul keep rho _ _).trans
            ((RatPolyCoeffEqv.refl _).mul (evaluate_solid keep rho s r n))).smul (-1)))

private theorem substitute_one : RatPolyCoeffEqv (substituteRetained polyOne) polyOne := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem substitute_solid (s r : RatPoly) : ∀ n,
    RatPolyCoeffEqv (substituteRetained (solidZonalCharacterPolynomial s r n))
      (solidZonalCharacterPolynomial (substituteRetained s) (substituteRetained r) n)
  | 0 => substitute_one
  | 1 => substituteRetained_smul 2 s
  | n+2 => (substituteRetained_add _ _).trans
      (((substituteRetained_mul _ _).trans
        ((substituteRetained_smul 2 s).mul (substitute_solid s r (n+1)))).add
        ((substituteRetained_smul (-1) _).trans
          (((substituteRetained_mul _ _).trans
            ((RatPolyCoeffEqv.refl _).mul (substitute_solid s r n))).smul (-1))))

private def paddedScalar : RatPoly := evaluateTail 4 auxiliaryUnits specializedScalar

private def paddedRadius : RatPoly := evaluateTail 4 auxiliaryUnits specializedRadius

private theorem endpoint_solid (n : Nat) : RatPolyCoeffEqv (endpoint n)
    (solidZonalCharacterPolynomial paddedScalar paddedRadius n) :=
  (evaluate_congr 4 auxiliaryUnits (solid_specialization n)).trans
    (evaluate_solid 4 auxiliaryUnits specializedScalar specializedRadius n)

private theorem substituted_scalar :
    QuaternionHaarCarrierEqv 1 (substituteRetained paddedScalar) paddedScalar := by
  apply carrier_of_canon_check
  decide +kernel

private theorem substituted_radius :
    QuaternionHaarCarrierEqv 1 (substituteRetained paddedRadius) paddedRadius := by
  apply carrier_of_canon_check
  decide +kernel

private theorem endpoint_substitute (n : Nat) :
    QuaternionHaarCarrierEqv 1 (substituteRetained (endpoint n)) (endpoint n) :=
  (RatPolyCoeffEqv.haarCarrier (substituteRetained_congr (endpoint_solid n))).trans
    ((RatPolyCoeffEqv.haarCarrier (substitute_solid _ _ n)).trans
      ((solid_carrier_congr substituted_scalar substituted_radius n).trans
        (RatPolyCoeffEqv.haarCarrier (endpoint_solid n)).symm))

private theorem evaluate_character (keep : Nat) (rho : Nat → Q') (s : RatPoly) : ∀ n,
    RatPolyCoeffEqv (evaluateTail keep rho (characterPolynomial s n))
      (characterPolynomial (evaluateTail keep rho s) n)
  | 0 => evaluate_one keep rho
  | 1 => evaluate_smul keep rho 2 s
  | n+2 => by
      change RatPolyCoeffEqv (evaluateTail keep rho (polyAdd
        (polyMul (polySmul 2 s) (characterPolynomial s (n+1)))
        (polySmul (-1) (characterPolynomial s n)))) _
      rw [evaluate_add]
      exact ((evaluate_mul keep rho _ _).trans
        ((evaluate_smul keep rho 2 s).mul (evaluate_character keep rho s (n+1)))).add
        ((evaluate_smul keep rho (-1) _).trans ((evaluate_character keep rho s n).smul (-1)))

private theorem evaluated_relative_scalar :
    RatPolyCoeffEqv paddedScalar (evaluateTail 4 auxiliaryUnits relativeScalar) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem padded_radius_carrier :
    QuaternionHaarCarrierEqv 1 paddedRadius polyOne := by
  have hr : QuaternionHaarCarrierEqv 1 paddedRadius (quaternionRadiusPolynomial 0) := by
    apply carrier_of_canon_check
    decide +kernel
  exact hr.trans (quaternionRadiusPolynomial_carrier_one (by decide : 0 < 1))

private theorem endpoint_character (n : Nat) :
    QuaternionHaarCarrierEqv 1 (endpoint n)
      (evaluateTail 4 auxiliaryUnits (relativeCharacter n)) :=
  (RatPolyCoeffEqv.haarCarrier (endpoint_solid n)).trans
    ((solidZonalCharacterPolynomial_eq_character_of_radius_eq_one _ _
      padded_radius_carrier n).trans
      (RatPolyCoeffEqv.haarCarrier
        ((characterPolynomial_coeffEqv evaluated_relative_scalar n).trans
          (evaluate_character 4 auxiliaryUnits relativeScalar n).symm)))

private theorem diagonal_scalar :
    RatPolyCoeffEqv (evaluateTail 0 auxiliaryUnits (substituteRetained specializedScalar)) polyOne := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem diagonal_radius :
    RatPolyCoeffEqv (evaluateTail 0 auxiliaryUnits (substituteRetained specializedRadius)) polyOne := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem dimension_recurrence (n : Nat) :
    2*Q'.ofNat (n+2) + (-1)*Q'.ofNat (n+1) ≈ Q'.ofNat (n+3) := by
  change ((2*((n+2 : Nat) : Int))*1 + ((-1)*((n+1 : Nat) : Int))*1)*1 =
    ((n+3 : Nat) : Int)*1
  simp only [Int.mul_one, Int.natCast_add]
  omega

private theorem solid_unit_value : ∀ n,
    RatPolyCoeffEqv (solidZonalCharacterPolynomial polyOne polyOne n)
      (polySmul (Q'.ofNat (n+1)) polyOne)
  | 0 => (RatPolyCoeffEqv.one_smul _).symm
  | 1 => .refl _
  | n+2 => by
      have ha := ((RatPolyCoeffEqv.refl (polySmul 2 polyOne)).mul (solid_unit_value (n+1))).trans
        ((RatPolyCoeffEqv.polyMul_smul_left 2 polyOne _).trans
          (((RatPolyCoeffEqv.one_mul _).smul 2).trans (RatPolyCoeffEqv.smul_assoc _ _ _)))
      have hb := (((RatPolyCoeffEqv.refl polyOne).mul (solid_unit_value n)).smul (-1)).trans
        (((RatPolyCoeffEqv.one_mul _).smul (-1)).trans (RatPolyCoeffEqv.smul_assoc _ _ _))
      exact (ha.add hb).trans
        ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
          (RatPolyCoeffEqv.smul_coefficient (dimension_recurrence n) _))

private theorem diagonal_value (n : Nat) :
    RatPolyCoeffEqv (evaluateTail 0 auxiliaryUnits (substituteRetained (raw n)))
      (polySmul (Q'.ofNat (n+1)) polyOne) :=
  (evaluate_congr 0 auxiliaryUnits (substituteRetained_congr (solid_specialization n))).trans
    ((evaluate_congr 0 auxiliaryUnits (substitute_solid _ _ n)).trans
      ((evaluate_solid 0 auxiliaryUnits _ _ n).trans
        ((solid_congr diagonal_scalar diagonal_radius n).trans (solid_unit_value n))))

/-- Exact positive norm of the constructed endpoint, in the ORIGINAL
one-quaternion Haar functional. -/
theorem endpoint_norm (n : Nat) :
    quaternionHaar 1 (polyMul (endpoint n) (endpoint n)) ≈ 1 := by
  let p := polyMul (relativeCharacter n) (raw n)
  let c := Q'.ofNat (n+1)
  have hr := character_harmonic_reproduction n (raw n) (raw_degree n) (raw_harmonic n)
  have hscaled : c * quaternionHaar 0
      (evaluateTail 0 auxiliaryUnits (partialHaarHead p)) ≈ c := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul 0 c _)) ?_
    refine Q'.eqv_trans _ _ _ (haar_of_coeff
      ((evaluate_smul 0 auxiliaryUnits c _).symm.trans
        (evaluate_congr 0 auxiliaryUnits hr))) ?_
    refine Q'.eqv_trans _ _ _ (haar_of_coeff (diagonal_value n)) ?_
    exact Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 0 c polyOne)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (by decide +kernel : quaternionHaar 0 polyOne ≈ 1)) (Q'.mul_one_eqv c))
  have hvalue : quaternionHaar 1 (polyMul (endpoint n) (endpoint n)) ≈
      quaternionHaar 0 (evaluateTail 0 auxiliaryUnits (partialHaarHead p)) := by
    refine Q'.eqv_trans _ _ _ (haar_of_carrier ((endpoint_character n).mul_right (endpoint n))) ?_
    refine Q'.eqv_trans _ _ _ (haar_of_coeff (evaluate_mul 4 auxiliaryUnits _ _).symm) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead 0 _)) ?_
    exact haar_of_coeff (partialHaarHead_evaluate 0 auxiliaryUnits p)
  apply Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos n)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ hvalue)
    (Q'.eqv_trans _ _ _ hscaled (Q'.eqv_symm (Q'.mul_one_eqv c)))

theorem endpoint_norm_positive (n : Nat) :
    (0 : Q') < quaternionHaar 1 (polyMul (endpoint n) (endpoint n)) :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (Q'.ge_of_eqv (endpoint_norm n))

/-- The original bilateral character response of the explicitly constructed
degree-n endpoint. Both endpoint links remain original Haar variables. -/
def gamma (n j : Nat) : Q' := response 1 polyOne (endpoint n) relativeScalar j

private theorem gamma_pairing (n j : Nat) : gamma n j ≈
    quaternionHaar 2 (polyMul (polyMul (relativeCharacter j) (endpoint n))
      (liftHead (endpoint n))) := by
  unfold gamma response insertion
  refine Q'.eqv_trans _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.one_mul _).mul_right (relativeCharacter j))) ?_
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
    (fun | 0 => endpoint n | 1 => liftHead (endpoint n) | _ => relativeCharacter j))

private theorem gamma_off_diagonal (n j : Nat) (hne : j ≠ n) : gamma n j ≈ 0 :=
  Q'.eqv_trans _ _ _ (gamma_pairing n j)
    (character_harmonic_boundary_zero 1 (by decide)
      (endpoint_degree n) (endpoint_harmonic n) hne (endpoint n))

private theorem gamma_diagonal (n : Nat) : Q'.ofNat (n+1) * gamma n n ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (gamma_pairing n n))
    (Q'.eqv_trans _ _ _
      (character_harmonic_boundary_reproduction 1 n (endpoint n)
        (endpoint_degree n) (endpoint_harmonic n) (endpoint n))
      (Q'.eqv_trans _ _ _ (haar_of_carrier ((endpoint_substitute n).mul_right _)) (endpoint_norm n)))

/-- General original two-link selection, with its exact dimension factor.
The source degree and the character label are arbitrary and independent. -/
theorem character_response_pin (n j : Nat) :
    Q'.ofNat (n+1) * gamma n j ≈ (if j = n then 1 else 0) := by
  by_cases h : j = n
  · subst j
    simpa only [if_pos rfl] using gamma_diagonal n
  · rw [if_neg h]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (gamma_off_diagonal n j h)) (Q'.mul_zero_eqv _)

private theorem sum_pick (a : Nat → Q') (n : Nat) : ∀ N,
    finSum (fun j => if j = n then a n else 0) N ≈ (if n < N then a n else 0)
  | 0 => by
      rw [if_neg (Nat.not_lt_zero n)]
      exact Q'.eqv_refl _
  | N+1 => by
      change finSum (fun j => if j = n then a n else 0) N +
        (if N = n then a n else 0) ≈ (if n < N+1 then a n else 0)
      by_cases hn : n < N
      · have hne : N ≠ n := by omega
        have hn' : n < N+1 := by omega
        rw [if_neg hne, if_pos hn']
        have h := sum_pick a n N
        rw [if_pos hn] at h
        exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ 0 h)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · by_cases he : N = n
        · subst N
          rw [if_pos rfl, if_pos (Nat.lt_succ_self n)]
          have h := sum_pick a n n
          rw [if_neg (Nat.lt_irrefl n)] at h
          exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (a n) h)
            (Q'.eqv_of_eq (Q'.zero_add' _))
        · have hn' : ¬ n < N+1 := by omega
          rw [if_neg he, if_neg hn']
          have h := sum_pick a n N
          rw [if_neg hn] at h
          exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ 0 h)
            (Q'.eqv_of_eq (Q'.add_zero' _))

/-- An actual finite original relative-character polynomial, with no sign
restriction on its rational coefficients. N is the exclusive row length. -/
def characterRow (a : Nat → Q') (N : Nat) : RatPoly :=
  finitePolySum (fun j => polySmul (a j) (relativeCharacter j)) (List.range N)

/-- The ORIGINAL Haar quadratic of any actual finite character row extracts
its n-th coefficient, or zero when that coefficient lies beyond the row.
This allows a fixed endpoint to test all later prefix cutoffs. -/
theorem characterRow_quadratic_pin (a : Nat → Q') (N n : Nat) :
    Q'.ofNat (n+1) * insertion 1 polyOne (endpoint n) (characterRow a N) ≈
      (if n < N then a n else 0) := by
  have hr : insertion 1 polyOne (endpoint n) (characterRow a N) ≈
      finSum (fun j => a j * gamma n j) N :=
    Q'.eqv_trans _ _ _ (insertion_sum_range 1 polyOne (endpoint n) _ N)
      (finSum_eqv_congr _ _ (fun j => insertion_smul 1 polyOne (endpoint n) _ (a j)) N)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) ?_
  refine Q'.eqv_trans _ _ _ (const_mul_finSum _ (Q'.ofNat (n+1)) N) ?_
  refine Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _ (fun j => ?_) N) (sum_pick a n N)
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => Q'.ofNat (n+1) | 1 => a j | _ => gamma n j)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (character_response_pin n j)) ?_
  by_cases h : j = n
  · subst j
    simpa only [if_pos rfl] using Q'.mul_one_eqv (a n)
  · simp only [if_neg h]
    exact Q'.mul_zero_eqv _

private theorem sum_zero (f : Nat → Q') : ∀ N,
    (∀ j, j < N → f j ≈ 0) → finSum f N ≈ 0
  | 0, _ => Q'.eqv_refl _
  | N+1, h => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (sum_zero f N (fun j hj => h j (by omega))) (h N (by omega)))
      (Q'.eqv_of_eq (Q'.add_zero' 0))

private theorem heat_pairing_zero (q : Q') (K : Nat) :
    insertion 1 polyOne (endpoint (K+2)) (heatPrefix q K relativeScalar) ≈ 0 :=
  Q'.eqv_trans _ _ _ (prefix_value 1 polyOne (endpoint (K+2)) relativeScalar q K)
    (sum_zero _ (K+1) (fun j hj => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (gamma_off_diagonal (K+2) j (by omega))) (Q'.mul_zero_eqv _)))

private theorem constant_pairing_zero (K : Nat) (e : Q') :
    insertion 1 polyOne (endpoint (K+2)) (cap e) ≈ 0 := by
  have he : RatPolyCoeffEqv (cap e) (polySmul e (relativeCharacter 0)) := .refl _
  exact Q'.eqv_trans _ _ _ (insertion_coeff _ _ _ he)
    (Q'.eqv_trans _ _ _ (insertion_smul _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (gamma_off_diagonal (K+2) 0 (by omega))) (Q'.mul_zero_eqv _)))

private theorem quartic_pairing (q : Q') (K : Nat) :
    insertion 1 polyOne (endpoint (K+2))
      (polyMul (polyMul (defect relativeScalar) (defect relativeScalar))
        (heatPrefix q K relativeScalar)) ≈ coeffW q K * gamma (K+2) (K+2) := by
  refine Q'.eqv_trans _ _ _ (quartic_value_regrouped 1 polyOne (endpoint (K+2)) relativeScalar q K) ?_
  change finSum _ (K+2) + quarticCoeff (cutCoeff q K) (K+2)*gamma (K+2) (K+2) ≈ _
  have hz := sum_zero
    (fun j => quarticCoeff (cutCoeff q K) j * gamma (K+2) j) (K+2)
    (fun j hj => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (gamma_off_diagonal (K+2) j (by omega))) (Q'.mul_zero_eqv _))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    hz (Q'.mul_eqv_congr_right _ _ _ (quarticCoeff_top_eqv q K))) (Q'.eqv_of_eq (Q'.zero_add' _))

/-- Literal original relative kernel residual: SAME inclusive heat cutoff,
actual squared nome, and a constant error in spin zero only. -/
def affineResidual (q : Q') (K : Nat) (c e : Q') : RatPoly :=
  polyAdd (polyAdd (polySmul c (heatPrefix (q*q) K relativeScalar)) (cap e))
    (polyNeg (polyMul (polyMul (defect relativeScalar) (defect relativeScalar))
      (heatPrefix q K relativeScalar)))

/-- The actual two-link Haar quadratic pairing with the same explicit real
endpoint at both ends. No positivity of the signed endpoint is assumed. -/
def affineQuadratic (q : Q') (K : Nat) (c e : Q') : Q' :=
  insertion 1 polyOne (endpoint (K+2)) (affineResidual q K c e)

private theorem insertion_negative (a p : RatPoly) :
    insertion 1 polyOne a (polyNeg p) ≈ -(insertion 1 polyOne a p) := by
  have hp : RatPolyCoeffEqv (polyNeg p) (polySmul (-1) p) :=
    (coeffEvalExpr_eqv_of_normalize_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
      (by decide) (fun _ => p)).trans
      (YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left (-1) p)
  exact Q'.eqv_trans _ _ _ (insertion_coeff _ _ _ hp)
    (Q'.eqv_trans _ _ _ (insertion_smul _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

/-- Cleared exact ORIGINAL Haar obstruction, including K=0 and arbitrary
c/e. The source has norm one and degree K+2, not an assumed harmonic mode. -/
theorem affineQuadratic_cleared_pin (q : Q') (K : Nat) (c e : Q') :
    Q'.ofNat (K+3) * affineQuadratic q K c e ≈ -(coeffW q K) := by
  have hz : insertion 1 polyOne (endpoint (K+2))
      (polyAdd (polySmul c (heatPrefix (q*q) K relativeScalar)) (cap e)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (insertion_add _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (insertion_smul _ _ _ _ _)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (heat_pairing_zero (q*q) K))
            (Q'.mul_zero_eqv c))) (constant_pairing_zero K e)) (Q'.eqv_of_eq (Q'.add_zero' 0)))
  have hp : affineQuadratic q K c e ≈ -(coeffW q K * gamma (K+2) (K+2)) :=
    Q'.eqv_trans _ _ _ (insertion_add _ _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hz
        (Q'.eqv_trans _ _ _ (insertion_negative _ _)
          (Q'.neg_eqv_congr _ _ (quartic_pairing q K)))) (Q'.eqv_of_eq (Q'.zero_add' _)))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp) ?_
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.neg (.mul (.var 1) (.var 2))))
    (.neg (.mul (.var 1) (.mul (.var 0) (.var 2)))) (by decide)
    (fun | 0 => Q'.ofNat (K+3) | 1 => coeffW q K | _ => gamma (K+2) (K+2))) ?_
  exact Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (gamma_diagonal (K+2))) (Q'.mul_one_eqv _))

private theorem product_negative {d x : Q'} (hd : (0 : Q') < d)
    (hprod : d*x < (0 : Q')) : x < (0 : Q') := by
  have hn : (0 : Int) < d.num := Q'.num_pos_of_pos hd
  have hp : d.num*x.num < 0 := by
    change (d*x).num*1 < 0*(d*x).den at hprod
    simpa only [Int.mul_one, Int.zero_mul] using hprod
  have hx : x.num < 0 := by
    by_cases h : x.num < 0
    · exact h
    · have hnn : 0 ≤ x.num := by omega
      have hmul := Int.mul_nonneg (Int.le_of_lt hn) hnn
      omega
  change x.num*1 < 0*x.den
  simpa only [Int.mul_one, Int.zero_mul] using hx

/-- A negative ORIGINAL Haar quadratic value. This is a generic signed test,
not the actual original Wilson endpoint source and not its response. -/
theorem affineQuadratic_negative {q : Q'} (hq : (0 : Q') < q)
    (K : Nat) (c e : Q') : affineQuadratic q K c e < (0 : Q') := by
  have he : Q'.ofNat (K+3) * affineQuadratic q K c e ≈
      affineResidualCoeff q K c e (K+2) :=
    Q'.eqv_trans _ _ _ (affineQuadratic_cleared_pin q K c e)
      (Q'.eqv_symm (affineResidual_top_eqv q K c e))
  exact product_negative (Q'.ofNat_succ_pos (K+2))
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv he) (affineResidual_top_negative hq K c e))

#print axioms endpoint
#print axioms endpoint_supported
#print axioms endpoint_degree
#print axioms endpoint_harmonic
#print axioms endpoint_norm
#print axioms endpoint_norm_positive
#print axioms gamma
#print axioms character_response_pin
#print axioms characterRow
#print axioms characterRow_quadratic_pin
#print axioms affineResidual
#print axioms affineQuadratic
#print axioms affineQuadratic_cleared_pin
#print axioms affineQuadratic_negative

end YMGap.Continuum.SU2HeatQuarticSignedHaarObstruction
