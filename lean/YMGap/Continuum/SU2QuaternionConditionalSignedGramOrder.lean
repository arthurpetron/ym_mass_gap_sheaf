/-
# Signed conditional Gram order from actual THREE-head replicas

The original positive kernel windows cancel only INSIDE the full Haar
expectation. The exact replica pin yields nonnegativity of the signed
moment determinant under every certified surviving insertion. The
centered score bound retains the signed Hessian and negative score-mean
square; no positivity certificate for the determinant or uncleared
replica is asserted. The marginal is multiplied, never inverted.
The signed jet polynomials d/dd are precomputed: their moments are NOT
identified with derivatives of the marginal when q or frozen coefficients
depend on the integrated heads.

The observable phi is an actual polynomial. An arbitrary incoming c is
not silently identified with q*phi; its reconstruction/error and the
original interacting-action instance remain separate. No completed OS,
scaling or physical gap is claimed.
-/

import YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica
import YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration (partialHaarHeads_certificate)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (head_pairing)
open YMGap.Continuum.SU2QuaternionTripleHeadReplica
open YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow (tripleKernelWindow)
open YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct (positiveFromLowerWindow)
open YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection (haar_nonnegative_of_positive_multiplier)
open YMGap.Continuum.QuaternionHaarClearedThreeGram
open YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica

def conditionalDeterminant (heads : Nat) (q P d dd phi : RatPoly) : RatPoly :=
  momentDeterminant (momentA heads q P) (momentB heads q P phi) (momentD heads q d)
    (momentV heads q P phi) (momentE heads q d phi) (momentG heads q dd)

def conditionalNoise (heads : Nat) (q P phi : RatPoly) : RatPoly :=
  centeredNoise (momentA heads q P) (momentB heads q P phi) (momentV heads q P phi)

def conditionalScore (heads : Nat) (q P d phi : RatPoly) : RatPoly :=
  centeredScore (momentA heads q P) (momentB heads q P phi)
    (momentD heads q d) (momentE heads q d phi)

def conditionalFisher (heads : Nat) (q P d dd : RatPoly) : RatPoly :=
  centeredFisher (momentA heads q P) (momentD heads q d) (momentG heads q dd)

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem three_supported {blocks : Nat} {f : Fin 3 → RatPoly}
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (threeSum f) :=
  supported_add (hf 0) (supported_add (hf 1) (hf 2))

private theorem replica_supported {blocks : Nat} (P d dd f : Fin 3 → RatPoly)
    (hP : ∀ i, SupportedQuaternionBlocks blocks (P i))
    (hd : ∀ i, SupportedQuaternionBlocks blocks (d i))
    (hdd : ∀ i, SupportedQuaternionBlocks blocks (dd i))
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (replicaPolynomial P d dd f) := by
  have hb (i : Fin 3) : SupportedQuaternionBlocks blocks (complementProduct P i) := by
    unfold complementProduct
    split
    · exact supported_polyMul (hP 1) (hP 2)
    · exact supported_polyMul (hP 0) (hP 2)
    · exact supported_polyMul (hP 0) (hP 1)
  have hh (i : Fin 3) : SupportedQuaternionBlocks blocks (cyclicDifference f i) := by
    unfold cyclicDifference
    split
    · exact supported_add (hf 1) (neg_supported (hf 2))
    · exact supported_add (hf 2) (neg_supported (hf 0))
    · exact supported_add (hf 0) (neg_supported (hf 1))
  have hx (i j k : Fin 3) : SupportedQuaternionBlocks blocks
      (polyMul (polyMul (P k) (polyMul (d i) (d j)))
        (polyMul (cyclicDifference f i) (cyclicDifference f j))) :=
    supported_polyMul (supported_polyMul (hP k) (supported_polyMul (hd i) (hd j)))
      (supported_polyMul (hh i) (hh j))
  exact supported_add
    (three_supported (fun i => supported_polyMul (supported_polyMul (hb i) (hdd i))
      (supported_polyMul (hh i) (hh i))))
    (supported_polyMul (polySmul_supported (supported_one blocks) 2)
      (supported_add (hx 0 1 2) (supported_add (hx 0 2 1) (hx 1 2 0))))

private theorem haar_neg (blocks : Nat) (p : RatPoly) :
    Q'.eqv (quaternionHaar blocks (polyNeg p)) (-quaternionHaar blocks p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => quaternionHaar blocks p)))

private theorem haar_difference (blocks : Nat) (R p q : RatPoly) :
    Q'.eqv (quaternionHaar blocks (polyMul R (polyAdd p (polyNeg q))))
      (quaternionHaar blocks (polyMul R p) + -quaternionHaar blocks (polyMul R q)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => R | 1 => p | _ => q)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg blocks (polyMul R q))))

/-- Signed determinant order under EVERY certified surviving insertion.
Only the actual three-copy kernel is reflected inside the Haar expectation. -/
theorem conditional_determinant_nonnegative (tail heads : Nat) (q P d dd phi R : RatPoly)
    {ell upper : Q'}
    (hq : SupportedQuaternionBlocks (tail+heads) q)
    (hP : SupportedQuaternionBlocks (tail+heads) P)
    (hd : SupportedQuaternionBlocks (tail+heads) d)
    (hdd : SupportedQuaternionBlocks (tail+heads) dd)
    (hphi : SupportedQuaternionBlocks (tail+heads) phi)
    (Qcert : Certificate (tail+heads) q)
    (Ccert : Certificate (tail+heads) (polyAdd (polyMul P dd) (polyNeg (polyMul d d))))
    (Rcert : Certificate tail R)
    (hell : (0 : Q') < ell) (hupper : (0 : Q') < upper) (hle : ell ≤ upper)
    (L : Certificate (tail+heads) (polyAdd P (polyNeg (cap ell))))
    (U : Certificate (tail+heads) (polyAdd (cap upper) (polyNeg P))) :
    (0 : Q') ≤ quaternionHaar tail (polyMul R (conditionalDeterminant heads q P d dd phi)) := by
  let H := heads+(heads+heads)
  let p := fun i => tripleCopy heads i P
  let a := fun i => tripleCopy heads i d
  let b := fun i => tripleCopy heads i dd
  let f := fun i => tripleCopy heads i phi
  let z := fun i => tripleCopy heads i q
  let T := replicaPolynomial p a b f
  have hp (i : Fin 3) := tripleCopy_supported tail heads hP i
  have ha (i : Fin 3) := tripleCopy_supported tail heads hd i
  have hb (i : Fin 3) := tripleCopy_supported tail heads hdd i
  have hf (i : Fin 3) := tripleCopy_supported tail heads hphi i
  have hT : SupportedQuaternionBlocks (tail+H) T := replica_supported p a b f hp ha hb hf
  have hC : SupportedQuaternionBlocks (tail+heads)
      (polyAdd (polyMul P dd) (polyNeg (polyMul d d))) :=
    supported_add (supported_polyMul hP hdd) (neg_supported (supported_polyMul hd hd))
  let C : ∀ i, Certificate (tail+H) (rowCurvature p a b i) := fun i => by
    simpa only [rowCurvature, tripleCopy_add, tripleCopy_mul, tripleCopy_neg] using
      tripleCopy_certificate tail heads hC Ccert i
  let cleared := cleared_replica_certificate p a b f hp ha hf C
  let W := tripleKernelWindow tail heads P hP hell hupper hle L U
  let background := polyMul (kernelProduct z) (liftBoundary H R)
  let B : Certificate (tail+H) background :=
    (((tripleCopy_certificate tail heads hq Qcert 0).mul
      (tripleCopy_certificate tail heads hq Qcert 1)).mul
        (tripleCopy_certificate tail heads hq Qcert 2)).mul (lift_certificate H Rcert)
  have h := haar_nonnegative_of_positive_multiplier W.support hT
    W.lowerPositive W.upperPositive W.endpointsOrdered W.lowerCertificate W.upperCertificate B cleared
  have hmove : RatPolyCoeffEqv (polyMul background T)
      (polyMul (weightedReplica heads q P d dd phi) (liftBoundary H R)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => kernelProduct z | 1 => liftBoundary H R | _ => T)
  have hscale : RatPolyCoeffEqv
      (polyMul (polyMul (cap 6) (conditionalDeterminant heads q P d dd phi)) R)
      (polySmul 6 (polyMul R (conditionalDeterminant heads q P d dd phi))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => cap 6 | 1 => conditionalDeterminant heads q P d dd phi | _ => R)).trans
        (cap_mul_left 6 _)
  have hint : Q'.eqv (quaternionHaar (tail+H) (polyMul background T))
      (6*quaternionHaar tail (polyMul R (conditionalDeterminant heads q P d dd phi))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hmove)
      (Q'.eqv_trans _ _ _ (head_pairing tail H (weightedReplica heads q P d dd phi) R)
        (Q'.eqv_trans _ _ _
          (haar_of_coeff ((weighted_replica_integral_pin heads q P d dd phi).mul_right R))
          (Q'.eqv_trans _ _ _ (haar_of_coeff hscale) (quaternionHaar_polySmul tail 6 _))))
  have hnonnegative : (0 : Q') ≤
      6*quaternionHaar tail (polyMul R (conditionalDeterminant heads q P d dd phi)) :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv hint)
  have hscaled : (6 : Q')*0 ≤
      6*quaternionHaar tail (polyMul R (conditionalDeterminant heads q P d dd phi)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv 6)) hnonnegative
  exact Q'.le_of_mul_le_mul_left hscaled (by decide : (0 : Q') < 6)

/-- Conditional integrated Gram inequality for the precomputed signed jet
moments. The signed second moment and negative score-mean square remain;
no marginal-derivative interpretation or marginal inverse is formed. -/
theorem conditional_signed_score_bound (tail heads : Nat) (q P d dd phi R : RatPoly)
    {ell upper : Q'}
    (hq : SupportedQuaternionBlocks (tail+heads) q)
    (hP : SupportedQuaternionBlocks (tail+heads) P)
    (hd : SupportedQuaternionBlocks (tail+heads) d)
    (hdd : SupportedQuaternionBlocks (tail+heads) dd)
    (hphi : SupportedQuaternionBlocks (tail+heads) phi)
    (Qcert : Certificate (tail+heads) q)
    (Ccert : Certificate (tail+heads) (polyAdd (polyMul P dd) (polyNeg (polyMul d d))))
    (Rcert : Certificate tail R)
    (hell : (0 : Q') < ell) (hupper : (0 : Q') < upper) (hle : ell ≤ upper)
    (L : Certificate (tail+heads) (polyAdd P (polyNeg (cap ell))))
    (U : Certificate (tail+heads) (polyAdd (cap upper) (polyNeg P))) :
    quaternionHaar tail (polyMul R
      (polyMul (conditionalScore heads q P d phi) (conditionalScore heads q P d phi))) ≤
    quaternionHaar tail (polyMul R
      (polyMul (conditionalNoise heads q P phi) (conditionalFisher heads q P d dd))) := by
  let A := momentA heads q P
  let Pcert := positiveFromLowerWindow L (Q'.le_of_lt hell)
  let Acert : Certificate tail A := partialHaarHeads_certificate tail heads (Qcert.mul Pcert)
  have h := conditional_determinant_nonnegative tail heads q P d dd phi (polyMul R A)
    hq hP hd hdd hphi Qcert Ccert (Rcert.mul Acert) hell hupper hle L U
  have hpin : RatPolyCoeffEqv
      (polyMul R (polyAdd
        (polyMul (conditionalNoise heads q P phi) (conditionalFisher heads q P d dd))
        (polyNeg (polyMul (conditionalScore heads q P d phi) (conditionalScore heads q P d phi)))))
      (polyMul (polyMul R A) (conditionalDeterminant heads q P d dd phi)) :=
    ((centered_difference_pin (momentA heads q P) (momentB heads q P phi) (momentD heads q d)
      (momentV heads q P phi) (momentE heads q d phi) (momentG heads q dd)).mul_left R).trans
        ((RatPolyCoeffEqv.mul_assoc R A (conditionalDeterminant heads q P d dd phi)).symm)
  have hdiff : (0 : Q') ≤
      quaternionHaar tail (polyMul R
        (polyMul (conditionalNoise heads q P phi) (conditionalFisher heads q P d dd))) +
      -quaternionHaar tail (polyMul R
        (polyMul (conditionalScore heads q P d phi) (conditionalScore heads q P d phi))) :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (haar_of_coeff hpin.symm)
        (haar_difference tail R _ _)))
  exact Q'.le_of_sub_nonneg hdiff

end YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder

#print axioms YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder.conditional_determinant_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder.conditional_signed_score_bound
