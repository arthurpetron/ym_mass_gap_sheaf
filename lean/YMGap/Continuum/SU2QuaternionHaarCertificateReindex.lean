/-
# Positive certificates under finite quaternion-coordinate involutions

The final polynomial must be supported. Intermediate certificate transports
need not be: recursion keeps an explicit supported square representative.
Arbitrary insertion equality is recovered from supported insertion equality
by actual tail integration, not by truncating an unsupported insertion.

The consumer is positive conditional integration at an arbitrary selected
coordinate of the actual finite marginal. No gap or uniform estimate is
asserted here.
-/

import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

namespace YMGap.Continuum.SU2QuaternionHaarCertificateReindex

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Supported insertion equality suffices when both compared polynomials
are supported; arbitrary insertions are integrated, not silently clipped. -/
theorem carrier_of_supported {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : SupportedHaarEqv blocks p q) : HaarCarrierEqv blocks p q := by
  intro r
  exact Q'.eqv_trans _ _ _ (tail_pairing blocks 0 r p hp)
    (Q'.eqv_trans _ _ _ (h (tailMarginal blocks 0 r) (tailMarginal_supported blocks 0 r))
      (Q'.eqv_symm (tail_pairing blocks 0 r q hq)))

theorem reindex_supported {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (p : RatPoly) : SupportedQuaternionBlocks blocks (reindexQuaternionPolynomial s p) := by
  intro t ht
  obtain ⟨r, _, hr⟩ := List.mem_map.mp ht
  rw [← hr]
  exact Nat.le_of_eq (reindexQuaternionExponents_length s r.1)

theorem reindex_twice_prefix {blocks : Nat} (s : QuaternionBlockInvolution blocks) :
    ∀ p : RatPoly, QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s (reindexQuaternionPolynomial s p)) p
  | [] => .nil
  | t::ts => by
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro coordinate hc
        change exponentAt (reindexQuaternionExponents s (reindexQuaternionExponents s t.1))
          coordinate = exponentAt t.1 coordinate
        rw [exponentAt_reindexQuaternionExponents s _ hc]
        have hb : coordinate / 4 < blocks := by omega
        have hm := s.map_lt (coordinate / 4) hb
        rw [exponentAt_reindexQuaternionExponents s _ (by omega)]
        have hd : (4*s.map (coordinate/4)+coordinate%4)/4 = s.map (coordinate/4) := by omega
        have hr : (4*s.map (coordinate/4)+coordinate%4)%4 = coordinate%4 := by omega
        rw [hd, hr, s.involutive _ hb]
        congr 1
        omega
      · exact reindex_twice_prefix s ts

/-- Move an insertion through the same explicit involution. -/
theorem reindex_pair {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (r p : RatPoly) (hr : SupportedQuaternionBlocks blocks r)
    (hp : SupportedQuaternionBlocks blocks p) :
    quaternionHaar blocks (polyMul r (reindexQuaternionPolynomial s p)) ≈
      quaternionHaar blocks (polyMul (reindexQuaternionPolynomial s r) p) := by
  have hs := quaternionHaar_reindex s (polyMul r (reindexQuaternionPolynomial s p))
    (supported_polyMul hr (reindex_supported s p))
  rw [reindexQuaternionPolynomial_mul] at hs
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
    (quaternionHaar_prefixPolynomialEqv blocks
      ((QuaternionPrefixPolynomialEqv.refl blocks _).mul (reindex_twice_prefix s p))
      (supported_polyMul (reindex_supported s r) (reindex_supported s _))
      (supported_polyMul (reindex_supported s r) hp))

theorem reindex_carrier {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    {p q : RatPoly} (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (reindexQuaternionPolynomial s p) (reindexQuaternionPolynomial s q) := by
  apply carrier_of_supported (reindex_supported s p) (reindex_supported s q)
  intro r hr
  exact Q'.eqv_trans _ _ _ (reindex_pair s r p hr hp)
    (Q'.eqv_trans _ _ _ (h (reindexQuaternionPolynomial s r))
      (Q'.eqv_symm (reindex_pair s r q hr hq)))

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private structure ReindexedRepresentative {blocks : Nat}
    (s : QuaternionBlockInvolution blocks) (p : RatPoly) where
  polynomial : RatPoly
  supported : SupportedQuaternionBlocks blocks polynomial
  certificate : Certificate blocks (reindexQuaternionPolynomial s polynomial)
  pin : HaarCarrierEqv blocks p polynomial

private def representative {blocks : Nat} (s : QuaternionBlockInvolution blocks) :
    {p : RatPoly} → Certificate blocks p → ReindexedRepresentative s p
  | _, .square p hp => by
      refine ⟨polyMul p p, supported_polyMul hp hp, ?_, .refl _ _⟩
      rw [reindexQuaternionPolynomial_mul]
      exact .square _ (reindex_supported s p)
  | _, .add P Q => by
      let r := representative s P
      let t := representative s Q
      refine ⟨polyAdd r.polynomial t.polynomial, supported_add r.supported t.supported,
        ?_, HaarCarrierEqv.add r.pin t.pin⟩
      rw [reindexQuaternionPolynomial_add]
      exact .add r.certificate t.certificate
  | _, .smul c hc P => by
      let r := representative s P
      refine ⟨polySmul c r.polynomial, support_smul r.supported c, ?_, HaarCarrierEqv.smul c r.pin⟩
      rw [reindexQuaternionPolynomial_smul]
      exact .smul c hc r.certificate
  | _, .transport h P =>
      let r := representative s P
      ⟨r.polynomial, r.supported, r.certificate, h.trans r.pin⟩

/-- Reindex a supported positive polynomial with every square witness retained. -/
def reindex_certificate {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) (P : Certificate blocks p) :
    Certificate blocks (reindexQuaternionPolynomial s p) :=
  let r := representative s P
  .transport (reindex_carrier s hp r.supported r.pin) r.certificate

end YMGap.Continuum.SU2QuaternionHaarCertificateReindex

#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateReindex.carrier_of_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_twice_prefix
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_pair
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_carrier
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_certificate
