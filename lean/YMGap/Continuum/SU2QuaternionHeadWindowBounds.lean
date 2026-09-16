/-
# Certified relative bounds after integrating an observed time window

Retain the half-open action: every window transition carries its original
kernel and head spatial weight, but the last spatial weight is not inserted
until the terminal pairing. Positive step and input certificates construct
the complete background certificate, including all overlapping variables.
Partial Haar integration carries C - P and C + P to C*D - F and C*D + F, where
F is the observed window message and D is the SAME unobserved iterate.
No division by a message, pointwise positivity oracle or changed action is
used. This is finite input for cylinder boundary forgetting, not an OS state.
-/

import YMGap.Continuum.SU2QuaternionHeadWindowContraction
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
import YMGap.Continuum.SU2QuaternionHaarKernelBound
import YMGap.Continuum.QuaternionHaarPolynomialInterval

namespace YMGap.Continuum.SU2QuaternionHeadWindowBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 h)

private def certificate_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large)
    (P : Certificate small p) : Certificate large p := by
  have he : small + (large-small) = large := by omega
  exact he ▸ certificate_extend (large-small) hp P

/-- Construct the actual complete half-open action certificate from one
supported positive K*V step. No terminal V is added by this construction. -/
def halfOpenAction_certificate {blocks : Nat} {kernel weight : RatPoly}
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight)
    (S : Certificate (blocks+blocks) (polyMul kernel weight)) :
    (L : Nat) → Certificate ((L+1)*blocks) (halfOpenAction blocks kernel weight L)
  | 0 => by
      simpa only [Nat.zero_add, Nat.one_mul, halfOpenAction] using Certificate.one blocks
  | L+1 => by
      have hb : blocks ≤ (L+1)*blocks := by rw [Nat.succ_mul]; omega
      have hs : Certificate ((L+1+1)*blocks) (polyMul kernel weight) :=
        certificate_mono (supported_polyMul hk (support_mono hw (by omega)))
          (by simp only [Nat.succ_mul]; omega) S
      have ht : Certificate ((L+1+1)*blocks)
          (liftBoundary blocks (halfOpenAction blocks kernel weight L)) := by
        simpa only [Nat.succ_mul] using
          lift_certificate blocks (halfOpenAction_certificate hk hw S L)
      exact Certificate.ofCoeff (RatPolyCoeffEqv.mul_assoc kernel weight _).symm (hs.mul ht)

private theorem windowMessage_kernelMap (blocks : Nat) (kernel weight : RatPoly)
    (L : Nat) (f p : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight L f p)
      (kernelMap (L*blocks) (polyMul f (halfOpenAction blocks kernel weight L)) p) :=
  partialHaarHeads_congr (L*blocks)
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => f | 1 => p | _ => halfOpenAction blocks kernel weight L))

theorem windowMessage_add (blocks : Nat) (kernel weight : RatPoly)
    (L : Nat) (f p q : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight L f (polyAdd p q))
      (polyAdd (windowMessage blocks kernel weight L f p) (windowMessage blocks kernel weight L f q)) :=
  (windowMessage_kernelMap blocks kernel weight L f _).trans
    ((kernelMap_add _ _ p q).trans
      ((windowMessage_kernelMap blocks kernel weight L f p).symm.add
        (windowMessage_kernelMap blocks kernel weight L f q).symm))

theorem windowMessage_smul (blocks : Nat) (kernel weight : RatPoly)
    (L : Nat) (f : RatPoly) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (windowMessage blocks kernel weight L f (polySmul c p))
      (polySmul c (windowMessage blocks kernel weight L f p)) :=
  (windowMessage_kernelMap blocks kernel weight L f _).trans
    ((kernelMap_smul _ _ c p).trans
      ((windowMessage_kernelMap blocks kernel weight L f p).symm.smul c))

/-- Integrate an actual certified insertion against the same certified
window background. The input support is used for enlargement, not dropped. -/
def windowMessage_certificate {blocks : Nat} {kernel weight : RatPoly}
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight)
    (S : Certificate (blocks+blocks) (polyMul kernel weight))
    (L : Nat) {f p : RatPoly} (hf : SupportedQuaternionBlocks blocks f)
    (F : Certificate blocks f) (P : Certificate ((L+1)*blocks) p) :
    Certificate blocks (windowMessage blocks kernel weight L f p) := by
  have hb : blocks ≤ (L+1)*blocks := by rw [Nat.succ_mul]; omega
  have H := ((certificate_mono hf hb F).mul P).mul (halfOpenAction_certificate hk hw S L)
  have he : (L+1)*blocks = blocks + L*blocks := by rw [Nat.succ_mul]; omega
  exact partialHaarHeads_certificate blocks (L*blocks) (he ▸ H)

private theorem smul_neg (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem image_linear (blocks : Nat) (kernel weight : RatPoly)
    (L : Nat) (f p : RatPoly) (a b : Q') :
    RatPolyCoeffEqv
      (windowMessage blocks kernel weight L f (polyAdd (polySmul a polyOne) (polySmul b p)))
      (polyAdd (polySmul a (iterateStep blocks kernel weight L f))
        (polySmul b (windowMessage blocks kernel weight L f p))) :=
  (windowMessage_add blocks kernel weight L f _ _).trans
    (((windowMessage_smul blocks kernel weight L f a polyOne).trans
      ((windowMessage_one blocks kernel weight L f).smul a)).add
      (windowMessage_smul blocks kernel weight L f b p))

/-- The observed message lies below C times the ORIGINAL unobserved iterate. -/
def windowMessage_upper_certificate {blocks : Nat} {kernel weight : RatPoly}
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight)
    (S : Certificate (blocks+blocks) (polyMul kernel weight))
    (L : Nat) {f p : RatPoly} {c : Q'} (hf : SupportedQuaternionBlocks blocks f)
    (F : Certificate blocks f) (I : Interval ((L+1)*blocks) p c) :
    Certificate blocks (polyAdd (polySmul c (iterateStep blocks kernel weight L f))
      (polySmul (-1) (windowMessage blocks kernel weight L f p))) :=
  Certificate.ofCoeff (image_linear blocks kernel weight L f p c (-1)).symm
    (windowMessage_certificate hk hw S L hf F
      (Certificate.ofCoeff ((RatPolyCoeffEqv.refl (cap c)).add (smul_neg p)) I.upper))

/-- The opposite signed bound uses the SAME unobserved iterate. -/
def windowMessage_lower_certificate {blocks : Nat} {kernel weight : RatPoly}
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight)
    (S : Certificate (blocks+blocks) (polyMul kernel weight))
    (L : Nat) {f p : RatPoly} {c : Q'} (hf : SupportedQuaternionBlocks blocks f)
    (F : Certificate blocks f) (I : Interval ((L+1)*blocks) p c) :
    Certificate blocks (polyAdd (windowMessage blocks kernel weight L f p)
      (polySmul c (iterateStep blocks kernel weight L f))) := by
  have he := (windowMessage_add blocks kernel weight L f (cap c) p).trans
    (((windowMessage_smul blocks kernel weight L f c polyOne).trans
      ((windowMessage_one blocks kernel weight L f).smul c)).add (RatPolyCoeffEqv.refl _))
  exact Certificate.ofCoeff
    ((RatPolyCoeffEqv.add_comm _ _).trans he.symm)
    (windowMessage_certificate hk hw S L hf F I.lower)

end YMGap.Continuum.SU2QuaternionHeadWindowBounds

#print axioms YMGap.Continuum.SU2QuaternionHeadWindowBounds.halfOpenAction_certificate
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowBounds.windowMessage_add
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowBounds.windowMessage_smul
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowBounds.windowMessage_certificate
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowBounds.windowMessage_upper_certificate
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowBounds.windowMessage_lower_certificate
