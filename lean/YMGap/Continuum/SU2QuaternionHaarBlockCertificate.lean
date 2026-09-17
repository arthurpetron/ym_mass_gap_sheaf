/-
# Positive conditional integration at an original selected quaternion block

Move the selected coordinate to the head, integrate its existing positive
certificate, restore the empty coordinate, and move it back. The resulting
polynomial is pinned to the in-place conditional projection before any
spectator is integrated. Only the final input polynomial needs support;
arbitrary intermediate Haar-carrier transports are handled by the checked
certificate constructors.

The consumer is the finite-regulator weighted-residual approximation: its
conditional marginal and error interval need actual positive certificates.
No uniform inverse, weighted decomposition, OS bound, or gap follows here.
-/

import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.SU2QuaternionHaarBlockProjection
import YMGap.Continuum.QuaternionHaarPolynomialInterval

namespace YMGap.Continuum.SU2QuaternionHaarBlockCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
  (clearQuaternionBlock exponentAt_clearQuaternionBlock coordinateInQuaternionBlock)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

private theorem exponent_restore_head (m : List Nat) (k : Nat) :
    exponentAt (0 :: 0 :: 0 :: 0 :: m.drop 4) k =
      if k < 4 then 0 else exponentAt m k := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        cases k with
        | zero => rfl
        | succ k =>
          change exponentAt (m.drop 4) k =
            if k+1+1+1+1 < 4 then 0 else exponentAt m (k+1+1+1+1)
          rw [if_neg (by omega), exponentAt_drop]
          congr 1
          omega

private theorem restored_prefix (blocks i : Nat) (hi : i < blocks) :
    ∀ p : RatPoly, QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial (headSwapBlockInvolution blocks i hi)
        (liftHead (partialHaarHead
          (reindexQuaternionPolynomial (headSwapBlockInvolution blocks i hi) p))))
      (project i p)
  | [] => .nil
  | t :: ts => by
      let s := headSwapBlockInvolution blocks i hi
      have hz : s.map 0 = i := headSwapBlockInvolution_map_zero blocks i hi
      have hs : s.map i = 0 := headSwapBlockInvolution_map_selected blocks i hi
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · have hm := quaternionBlockMoment_reindex s t.1 (block := 0) (by omega)
          rw [hz] at hm
          change headQuaternionMoment (reindexQuaternionExponents s t.1) =
            SU2QuaternionFiniteProductHaarCarrier.quaternionBlockMoment i t.1 at hm
          change Q'.eqv (t.2 * headQuaternionMoment (reindexQuaternionExponents s t.1))
            (t.2 * SU2QuaternionFiniteProductHaarCarrier.quaternionBlockMoment i t.1)
          rw [hm]
          exact Q'.eqv_refl _
        · intro k hk
          change exponentAt (reindexQuaternionExponents s
              (0 :: 0 :: 0 :: 0 :: (reindexQuaternionExponents s t.1).drop 4)) k =
            exponentAt (clearQuaternionBlock i t.1) k
          rw [exponentAt_reindexQuaternionExponents s _ hk,
            exponent_restore_head, exponentAt_clearQuaternionBlock]
          have hb : k / 4 < blocks := by omega
          have hr : k % 4 < 4 := Nat.mod_lt _ (by decide)
          by_cases he : k / 4 = i
          · have hin : coordinateInQuaternionBlock i k := by
              unfold coordinateInQuaternionBlock
              exact ⟨by omega, by omega⟩
            rw [he, hs, if_pos hin, if_pos (by omega)]
          · have hout : ¬ coordinateInQuaternionBlock i k := by
              unfold coordinateInQuaternionBlock
              omega
            have hn : s.map (k / 4) ≠ 0 := by
              intro h
              have hh := congrArg s.map h
              rw [s.involutive _ hb, hz] at hh
              exact he hh
            rw [if_neg (by omega), if_neg hout]
            have hm := s.map_lt (k / 4) hb
            rw [exponentAt_reindexQuaternionExponents s _ (by omega)]
            have hd : (4*s.map (k/4)+k%4)/4 = s.map (k/4) := by omega
            have hmod : (4*s.map (k/4)+k%4)%4 = k%4 := by omega
            rw [hd, hmod, s.involutive _ hb]
            congr 1
            omega
      · exact restored_prefix blocks i hi ts

private theorem restored_head_supported {blocks : Nat} (hb : 0 < blocks)
    (s : QuaternionBlockInvolution blocks) (p : RatPoly) :
    SupportedQuaternionBlocks blocks
      (liftHead (partialHaarHead (reindexQuaternionPolynomial s p))) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
  change (0 :: 0 :: 0 :: 0 :: (reindexQuaternionExponents s w.1).drop 4).length ≤ 4*blocks
  simp only [List.length_cons, List.length_drop, reindexQuaternionExponents_length]
  omega

/-- A supplied positive polynomial remains positive after integrating only
the selected original quaternion coordinate; every spectator is retained. -/
def project_certificate (blocks i : Nat) (hi : i < blocks) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (P : Certificate blocks p) :
    Certificate blocks (project i p) := by
  cases blocks with
  | zero => exact False.elim (Nat.not_lt_zero i hi)
  | succ tail =>
      let s := headSwapBlockInvolution (tail+1) i hi
      have hrest := restored_head_supported (by omega : 0 < tail+1) s p
      have C : Certificate (tail+1)
          (reindexQuaternionPolynomial s
            (liftHead (partialHaarHead (reindexQuaternionPolynomial s p)))) :=
        reindex_certificate s hrest
          (lift_certificate 1 (partialHaarHead_certificate tail (reindex_certificate s hp P)))
      have he := SupportedHaarEqv.of_padded
        (PaddedPolynomialCoeffEqv.of_prefix (restored_prefix (tail+1) i hi p))
        (reindex_supported s _) (project_supported i hp)
      exact .transport
        (carrier_of_supported (project_supported i hp) (reindex_supported s _) he.symm) C

/-- Rational constant polynomials are fixed before any other integration. -/
theorem project_cap (i : Nat) (c : Q') :
    RatPolyCoeffEqv (project i (cap c)) (cap c) := by
  apply project_fixed
  intro t ht
  have ht' : t = ([], c * (1 : Q')) := by
    simpa only [cap, polySmul, polyOne, List.map_cons, List.map_nil,
      List.mem_singleton] using ht
  subst t
  rfl

private theorem cap_supported (blocks : Nat) (c : Q') :
    SupportedQuaternionBlocks blocks (cap c) := by
  intro t ht
  have ht' : t = ([], c * (1 : Q')) := by
    simpa only [cap, polySmul, polyOne, List.map_cons, List.map_nil,
      List.mem_singleton] using ht
  subst t
  exact Nat.zero_le _

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

/-- Conditional integration preserves the same rational two-sided interval;
the certificates are constructed, not assumed bounds on the projection. -/
def project_interval (blocks i : Nat) (hi : i < blocks) {p : RatPoly} {c : Q'}
    (P : Interval blocks p c) : Interval blocks (project i p) c where
  support := project_supported i P.support
  nonnegative := P.nonnegative
  upper := by
    have C := project_certificate blocks i hi
      (supported_add (cap_supported blocks c) (neg_supported P.support)) P.upper
    rw [project_add] at C
    exact .ofCoeff ((project_cap i c).add (project_neg i p)).symm C
  lower := by
    have C := project_certificate blocks i hi
      (supported_add (cap_supported blocks c) P.support) P.lower
    rw [project_add] at C
    exact .ofCoeff ((project_cap i c).add (RatPolyCoeffEqv.refl _)).symm C

end YMGap.Continuum.SU2QuaternionHaarBlockCertificate

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockCertificate.project_certificate
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockCertificate.project_cap
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockCertificate.project_interval
