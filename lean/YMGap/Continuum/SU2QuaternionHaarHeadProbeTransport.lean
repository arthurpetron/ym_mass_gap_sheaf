/-
# Transport tail probes to the original quaternion Haar carrier

A supported polynomial in the remaining blocks is lifted past the head and
pulled back by the same explicit block involution used for head integration.
Pairing this actual original-carrier probe against any supported insertion
equals pairing the tail probe against the partial Haar integral of that
insertion. The square specialization preserves the same original Haar law.

All pins are finite polynomial/Haar identities. They do not assert pointwise
conditional positivity, a normalized conditional kernel, or spatial decay.
-/

import YMGap.Continuum.SU2QuaternionHeadLinearHaar
import YMGap.Continuum.BF4CompactActionCPOrder
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem reindex_supported {blocks : Nat} (swap : QuaternionBlockInvolution blocks)
    (p : RatPoly) : SupportedQuaternionBlocks blocks (reindexQuaternionPolynomial swap p) := by
  intro t ht
  obtain ⟨s, _, hs⟩ := List.mem_map.mp ht
  rw [← hs]
  exact Nat.le_of_eq (reindexQuaternionExponents_length swap s.1)

private theorem lift_supported {blocks : Nat} (hb : 0 < blocks) {r : RatPoly}
    (hr : SupportedQuaternionBlocks (blocks-1) r) : SupportedQuaternionBlocks blocks (liftHead r) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have h := hr s hs
  simp only [List.length_cons]
  omega

private theorem reindex_twice_prefix {blocks : Nat} (swap : QuaternionBlockInvolution blocks) :
    ∀ p : RatPoly, QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial swap (reindexQuaternionPolynomial swap p)) p
  | [] => .nil
  | t :: ts => by
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro coordinate hcoordinate
        change exponentAt (reindexQuaternionExponents swap (reindexQuaternionExponents swap t.1)) coordinate =
          exponentAt t.1 coordinate
        rw [exponentAt_reindexQuaternionExponents swap _ hcoordinate]
        have hb : coordinate / 4 < blocks := by omega
        have hm := swap.map_lt (coordinate / 4) hb
        rw [exponentAt_reindexQuaternionExponents swap _ (by omega)]
        have hd : (4 * swap.map (coordinate / 4) + coordinate % 4) / 4 = swap.map (coordinate / 4) := by omega
        have hr : (4 * swap.map (coordinate / 4) + coordinate % 4) % 4 = coordinate % 4 := by omega
        rw [hd, hr, swap.involutive _ hb]
        congr 1
        omega
      · exact reindex_twice_prefix swap ts

private theorem partial_lift (r : RatPoly) : RatPolyCoeffEqv (partialHaarHead (liftHead r)) r := by
  have ht : RatPolyTermwiseEqv (partialHaarHead (liftHead r)) r := by
    induction r with
    | nil => exact True.intro
    | cons t ts ih =>
        refine ⟨rfl, ?_, ih⟩
        have h : headQuaternionMoment (0::0::0::0::t.1) ≈ 1 := by
          change sphereMoment4 0 0 0 0 ≈ 1
          decide +kernel
        exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left t.2 _ _ h) (Q'.mul_one_eqv t.2)
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

/-- The tail probe is pulled back to the original finite block carrier. -/
def headProbe {blocks : Nat} (swap : QuaternionBlockInvolution blocks) (r : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial swap (liftHead r)

theorem headProbe_supported {blocks : Nat} (swap : QuaternionBlockInvolution blocks) (r : RatPoly) :
    SupportedQuaternionBlocks blocks (headProbe swap r) := reindex_supported swap _

theorem headProbe_mul {blocks : Nat} (swap : QuaternionBlockInvolution blocks) (r s : RatPoly) :
    headProbe swap (polyMul r s) = polyMul (headProbe swap r) (headProbe swap s) := by
  simp only [headProbe, liftHead_mul, reindexQuaternionPolynomial_mul]

/-- Arbitrary-block form avoids transporting the involution across a
dependent equality identifying the original block count with a successor. -/
theorem headProbe_pair {blocks : Nat} (hb : 0 < blocks) (swap : QuaternionBlockInvolution blocks)
    (r p : RatPoly) (hr : SupportedQuaternionBlocks (blocks-1) r)
    (hp : SupportedQuaternionBlocks blocks p) :
    quaternionHaar blocks (polyMul (headProbe swap r) p) ≈
      quaternionHaar (blocks-1) (polyMul r (partialHaarHead (reindexQuaternionPolynomial swap p))) := by
  have hswap := quaternionHaar_reindex swap (polyMul (headProbe swap r) p)
    (supported_polyMul (headProbe_supported swap r) hp)
  rw [reindexQuaternionPolynomial_mul] at hswap
  have hprefix := quaternionHaar_prefixPolynomialEqv blocks
    ((reindex_twice_prefix swap (liftHead r)).mul
      (QuaternionPrefixPolynomialEqv.refl blocks (reindexQuaternionPolynomial swap p)))
    (supported_polyMul (reindex_supported swap _) (reindex_supported swap p))
    (supported_polyMul (lift_supported hb hr) (reindex_supported swap p))
  have hn : (blocks-1)+1 = blocks := by omega
  have hf := Q'.eqv_symm (quaternionHaar_partialHaarHead (blocks-1)
    (polyMul (reindexQuaternionPolynomial swap p) (liftHead r)))
  rw [hn] at hf
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hswap)
    (Q'.eqv_trans _ _ _ hprefix
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _ hf
          (haar_of_coeff ((partialHaarHead_mul_lift _ _).trans (RatPolyCoeffEqv.mul_comm _ _))))))

theorem headProbe_square_pair {blocks : Nat} (hb : 0 < blocks) (swap : QuaternionBlockInvolution blocks)
    (r p : RatPoly) (hr : SupportedQuaternionBlocks (blocks-1) r)
    (hp : SupportedQuaternionBlocks blocks p) :
    quaternionHaar blocks (polyMul (polyMul (headProbe swap r) (headProbe swap r)) p) ≈
      quaternionHaar (blocks-1)
        (polyMul (polyMul r r) (partialHaarHead (reindexQuaternionPolynomial swap p))) := by
  rw [← headProbe_mul]
  exact headProbe_pair hb swap (polyMul r r) p (supported_polyMul hr hr) hp

theorem headProbe_haar {blocks : Nat} (hb : 0 < blocks) (swap : QuaternionBlockInvolution blocks)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (blocks-1) r) :
    quaternionHaar blocks (headProbe swap r) ≈ quaternionHaar (blocks-1) r := by
  have hn : (blocks-1)+1 = blocks := by omega
  have hf := Q'.eqv_symm (quaternionHaar_partialHaarHead (blocks-1) (liftHead r))
  rw [hn] at hf
  exact Q'.eqv_trans _ _ _ (quaternionHaar_reindex swap (liftHead r) (lift_supported hb hr))
    (Q'.eqv_trans _ _ _ hf (haar_of_coeff (partial_lift r)))

theorem headProbe_square_haar {blocks : Nat} (hb : 0 < blocks) (swap : QuaternionBlockInvolution blocks)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (blocks-1) r) :
    quaternionHaar blocks (polyMul (headProbe swap r) (headProbe swap r)) ≈
      quaternionHaar (blocks-1) (polyMul r r) := by
  rw [← headProbe_mul]
  exact headProbe_haar hb swap (polyMul r r) (supported_polyMul hr hr)

private theorem headProbe_reindex_pair {blocks : Nat} (hb : 0 < blocks)
    (swap : QuaternionBlockInvolution blocks) (r p : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks-1) r)
    (hp : SupportedQuaternionBlocks blocks p) :
    quaternionHaar blocks (polyMul (headProbe swap r) p) ≈
      quaternionHaar blocks (polyMul (liftHead r) (reindexQuaternionPolynomial swap p)) := by
  have hswap := quaternionHaar_reindex swap (polyMul (headProbe swap r) p)
    (supported_polyMul (headProbe_supported swap r) hp)
  rw [reindexQuaternionPolynomial_mul] at hswap
  have hprefix := quaternionHaar_prefixPolynomialEqv blocks
    ((reindex_twice_prefix swap (liftHead r)).mul
      (QuaternionPrefixPolynomialEqv.refl blocks (reindexQuaternionPolynomial swap p)))
    (supported_polyMul (reindex_supported swap _) (reindex_supported swap p))
    (supported_polyMul (lift_supported hb hr) (reindex_supported swap p))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hswap) hprefix

/-- Retain an actual head-independent weight instead of replacing it by Haar. -/
theorem headProbe_independent_pair {blocks : Nat} (hb : 0 < blocks)
    (swap : QuaternionBlockInvolution blocks) (r p : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks-1) r)
    (hp : SupportedQuaternionBlocks blocks p)
    (hind : HeadQuaternionIndependent (reindexQuaternionPolynomial swap p)) :
    quaternionHaar blocks (polyMul (headProbe swap r) p) ≈
      quaternionHaar (blocks-1)
        (polyMul r (dropHeadPolynomial (reindexQuaternionPolynomial swap p))) := by
  have hn : (blocks-1)+1 = blocks := by omega
  have hf := quaternionHaar_polyMul_headIndependent (blocks-1) (liftHead r)
    (reindexQuaternionPolynomial swap p) hind
  rw [hn] at hf
  exact Q'.eqv_trans _ _ _ (headProbe_reindex_pair hb swap r p hr hp)
    (Q'.eqv_trans _ _ _ hf (haar_of_coeff ((partial_lift r).mul_right _)))

/-- Integrate the insertion while retaining every factor of the independent
complement in the tail pairing. This is an exact identity, not an inverse or
a positivity estimate for either the insertion or the complement. -/
theorem headProbe_product_pair {blocks : Nat} (hb : 0 < blocks)
    (swap : QuaternionBlockInvolution blocks) (r p q : RatPoly)
    (hr : SupportedQuaternionBlocks (blocks-1) r)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hind : HeadQuaternionIndependent (reindexQuaternionPolynomial swap q)) :
    quaternionHaar blocks (polyMul (headProbe swap r) (polyMul p q)) ≈
      quaternionHaar (blocks-1)
        (polyMul (polyMul r (partialHaarHead (reindexQuaternionPolynomial swap p)))
          (dropHeadPolynomial (reindexQuaternionPolynomial swap q))) := by
  have hs := headProbe_reindex_pair hb swap r (polyMul p q) hr (supported_polyMul hp hq)
  rw [reindexQuaternionPolynomial_mul] at hs
  have horder : RatPolyCoeffEqv
      (polyMul (liftHead r)
        (polyMul (reindexQuaternionPolynomial swap p) (reindexQuaternionPolynomial swap q)))
      (polyMul (polyMul (reindexQuaternionPolynomial swap p) (liftHead r))
        (reindexQuaternionPolynomial swap q)) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
      ((RatPolyCoeffEqv.mul_comm _ _).mul_right _)
  have hn : (blocks-1)+1 = blocks := by omega
  have hf := quaternionHaar_polyMul_headIndependent (blocks-1)
    (polyMul (reindexQuaternionPolynomial swap p) (liftHead r))
    (reindexQuaternionPolynomial swap q) hind
  rw [hn] at hf
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _ (haar_of_coeff horder)
      (Q'.eqv_trans _ _ _ hf
        (haar_of_coeff
          (((partialHaarHead_mul_lift _ _).trans (RatPolyCoeffEqv.mul_comm _ _)).mul_right _))))

end YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport

#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe_pair
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe_square_pair
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe_haar
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe_square_haar
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe_independent_pair
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport.headProbe_product_pair
