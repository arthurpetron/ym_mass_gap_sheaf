/-
# Actual regularized entropy under the original finite quaternion Haar

The approximants are the original Haar integrals of the existing entropy
polynomials, with no replacement functional. Pointwise densities in [0,1]
give the explicit uniform denominator modulus, including zero density and
zero blocks. Finite Jensen retains the OWN partition Z=Haar(W).

For positive Z, the checked scalar-series identification supplies the actual
computed logarithmic upper bound, with its cutoff as Type-level data. This
does not divide W by Z, identify identity normalization with probability
normalization, assert a conditional log-integral formula, or pay a signed
late-response, scaling, or spectral estimate.
-/

import YMGap.Continuum.QuaternionHaarFiniteEntropy
import YMGap.Continuum.RegularizedLogRationalAlgebra
import YMGap.Continuum.RegularizedLogBinaryIdentification
import YMGap.Constructive.CRealExplicitSqueeze

namespace YMGap.Continuum.QuaternionHaarRegularizedEntropy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_one evalRatPoly_smul)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_append quaternionHaar_polySmul)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one supported_add)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder
open YMGap.Continuum.QuaternionHaarFiniteEntropy
open YMGap.Continuum.RegularizedLogPolynomial (partialSum modulus)
open YMGap.Continuum.RegularizedLogBinaryReduction (binaryReduction)
open YMGap.Continuum.RebasedExpShiftSupportReduction (dyadicLogValue)

local infix:50 " ≈ " => Q'.eqv

private theorem supported_scale {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem eval_constant (rho : Nat → Q') (c : Q') :
    evalRatPoly rho (polySmul c polyOne) ≈ c :=
  Q'.eqv_trans _ _ _ (evalRatPoly_smul rho c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (evalRatPoly_one rho))
      (Q'.mul_one_eqv c))

private theorem haar_constant (blocks : Nat) (c : Q') :
    quaternionHaar blocks (polySmul c polyOne) ≈ c :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks))
      (Q'.mul_one_eqv c))

private theorem haar_slack (blocks : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (c : Q') (h : ∀ qs : Nat → UnitNorm,
      evalRatPoly (environment qs) p ≤ evalRatPoly (environment qs) q+c) :
    quaternionHaar blocks p ≤ quaternionHaar blocks q+c := by
  have he (qs : Nat → UnitNorm) :
      evalRatPoly (environment qs) (polyAdd q (polySmul c polyOne)) ≈
        evalRatPoly (environment qs) q+c :=
    Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (eval_constant _ c))
  have hh := haar_mono blocks p (polyAdd q (polySmul c polyOne)) hp
    (supported_add hq (supported_scale (supported_one blocks) c))
    (fun qs => Q'.le_trans' _ _ _ (h qs) (Q'.ge_of_eqv (he qs)))
  exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (quaternionHaar_append blocks q (polySmul c polyOne))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_constant blocks c))))

/-- Literal original Haar entropy-polynomial approximants. -/
def entropyApprox (blocks : Nat) (W : RatPoly) (n : Nat) : Q' :=
  quaternionHaar blocks (entropyStage n W)

theorem entropyApprox_bounds (blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (hlower : ∀ qs : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment qs) W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q'))
    (n : Nat) : (0 : Q') ≤ entropyApprox blocks W n ∧ entropyApprox blocks W n ≤ 1 := by
  exact ⟨haar_lower_bound blocks _ (entropyStage_supported hW n) 0 (fun qs =>
      Q'.le_trans' _ _ _ (RegularizedLogPolynomial.partial_nonnegative _ (hlower qs) (hupper qs) n)
        (Q'.ge_of_eqv (entropyStage_eval n W (environment qs)))),
    haar_upper_bound blocks _ (entropyStage_supported hW n) 1 (fun qs =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (entropyStage_eval n W (environment qs)))
        (RegularizedLogPolynomial.partial_le_one _ (hlower qs) (hupper qs) n))⟩

/-- The actual integrated tail retains the scalar constant, without a volume factor. -/
theorem entropy_tail (blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (hlower : ∀ qs : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment qs) W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q'))
    {m n : Nat} (hmn : m ≤ n) :
    entropyApprox blocks W n ≤ entropyApprox blocks W m+Q'.invSucc m := by
  apply haar_slack blocks _ _ (entropyStage_supported hW n) (entropyStage_supported hW m)
  intro qs
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (entropyStage_eval n W (environment qs)))
    (Q'.le_trans' _ _ _ (RegularizedLogPolynomial.partial_tail _ (hlower qs) (hupper qs) hmn)
      (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (entropyStage_eval m W (environment qs)))))

/-- Recoverable denominator modulus, uniform in the number of blocks and W. -/
theorem entropy_uniformCauchy (blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (hlower : ∀ qs : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment qs) W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : modulus epsilon ≤ m) (hn : modulus epsilon ≤ n) :
    entropyApprox blocks W m ≤ entropyApprox blocks W n+epsilon ∧
      entropyApprox blocks W n ≤ entropyApprox blocks W m+epsilon := by
  have hp (qs : Nat → UnitNorm) := RegularizedLogPolynomial.partial_uniformCauchy
    epsilon he m n hm hn _ (hlower qs) (hupper qs)
  have integrate (i j : Nat) (h : ∀ qs : Nat → UnitNorm,
      partialSum (evalRatPoly (environment qs) W) i ≤
        partialSum (evalRatPoly (environment qs) W) j+epsilon) :
      entropyApprox blocks W i ≤ entropyApprox blocks W j+epsilon := by
    apply haar_slack blocks _ _ (entropyStage_supported hW i) (entropyStage_supported hW j)
    intro qs
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (entropyStage_eval i W (environment qs)))
      (Q'.le_trans' _ _ _ (h qs)
        (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (entropyStage_eval j W (environment qs)))))
  exact ⟨integrate m n (fun qs => (hp qs).1), integrate n m (fun qs => (hp qs).2)⟩

/-- Limit of the SAME actual original Haar stages, not an assumed log integral. -/
def entropyValue (blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (hlower : ∀ qs : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment qs) W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q')) : CReal where
  approx := entropyApprox blocks W
  cauchy := fun epsilon he => ⟨modulus epsilon,
    fun m n hm hn => entropy_uniformCauchy blocks W hW hlower hupper epsilon he m n hm hn⟩

def entropyRegularity (blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (hlower : ∀ qs : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment qs) W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q')) :
    CReal.InnerRegularity (entropyValue blocks W hW hlower hupper) where
  rate := modulus
  regular := entropy_uniformCauchy blocks W hW hlower hupper

/-- Jensen for every original index, including zero, based at the OWN partition. -/
theorem entropy_jensen (blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q'))
    (n : Nat) : entropyApprox blocks W n ≤ partialSum (quaternionHaar blocks W) n := by
  cases n with
  | zero => change (0 : Q') ≤ 0; exact Q'.le_refl' _
  | succ n => exact haar_partial_jensen n blocks W hW hupper

/-- Actual log comparison at the SAME approximation index, with computed cutoff. -/
theorem haar_entropy_log_approx (blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (_hlower : ∀ qs : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment qs) W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q'))
    (hZ0 : (0 : Q') < quaternionHaar blocks W)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : RegularizedLogBinaryIdentification.identificationRate epsilon ≤ n) :
    entropyApprox blocks W n ≤
      (CReal.neg (CReal.mul (CReal.ofQ' (quaternionHaar blocks W))
        (dyadicLogValue (binaryReduction (quaternionHaar blocks W) hZ0
          (haar_upper_bound blocks W hW 1 hupper))))).approx n+epsilon :=
  Q'.le_trans' _ _ _ (entropy_jensen blocks W hW hupper n)
    (RegularizedLogBinaryIdentification.value_binaryLog_approx (quaternionHaar blocks W)
      hZ0 (haar_upper_bound blocks W hW 1 hupper) epsilon he n hn).1

/-- Sound eventual order with a recoverable modulus, not one-slack CReal order. -/
def haar_entropy_log_bound (blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (hlower : ∀ qs : Nat → UnitNorm, (0 : Q') ≤ evalRatPoly (environment qs) W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q'))
    (hZ0 : (0 : Q') < quaternionHaar blocks W) :
    CReal.ExplicitLeEv (entropyValue blocks W hW hlower hupper)
      (CReal.neg (CReal.mul (CReal.ofQ' (quaternionHaar blocks W))
        (dyadicLogValue (binaryReduction (quaternionHaar blocks W) hZ0
          (haar_upper_bound blocks W hW 1 hupper))))) where
  modulus := RegularizedLogBinaryIdentification.identificationRate
  bound := haar_entropy_log_approx blocks W hW hlower hupper hZ0

end YMGap.Continuum.QuaternionHaarRegularizedEntropy

#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.entropyApprox
#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.entropyApprox_bounds
#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.entropy_tail
#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.entropy_uniformCauchy
#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.entropyValue
#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.entropyRegularity
#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.entropy_jensen
#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.haar_entropy_log_approx
#print axioms YMGap.Continuum.QuaternionHaarRegularizedEntropy.haar_entropy_log_bound
