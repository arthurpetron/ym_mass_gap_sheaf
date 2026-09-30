/-
Explicitly retain a supported polynomial representative of an SOS certificate.
Transport nodes may themselves have unsupported source polynomials, so the
recursion follows the certificate constructors rather than assuming support
of every intermediate expression.
-/

import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.QuaternionHaarSquareCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem polySmul_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

namespace Certificate

/-- A recursively constructed supported polynomial with the same arbitrary-
insertion Haar functional as the certified polynomial. In particular,
`transport` never assumes its source is supported. -/
def supportedRepresentative {blocks : Nat} {p : RatPoly}
    (P : Certificate blocks p) :
    {q : RatPoly // SupportedQuaternionBlocks blocks q ∧ HaarCarrierEqv blocks p q} :=
  match P with
  | .square q hq =>
      ⟨polyMul q q, supported_polyMul hq hq, HaarCarrierEqv.refl _ _⟩
  | .add P Q =>
      let r := supportedRepresentative P
      let s := supportedRepresentative Q
      ⟨polyAdd r.val s.val,
        supported_add r.property.1 s.property.1,
        HaarCarrierEqv.add r.property.2 s.property.2⟩
  | .smul c _ P =>
      let r := supportedRepresentative P
      ⟨polySmul c r.val,
        polySmul_supported r.property.1 c,
        HaarCarrierEqv.smul c r.property.2⟩
  | .transport h P =>
      let r := supportedRepresentative P
      ⟨r.val, r.property.1, h.trans r.property.2⟩

end Certificate

#print axioms Certificate.supportedRepresentative

end YMGap.Continuum.QuaternionHaarSquareCertificate
