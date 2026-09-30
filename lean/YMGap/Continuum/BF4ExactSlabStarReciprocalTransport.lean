/-
# Transport of the finite star reciprocal through the actual head swap

The original head-coordinate normalizer and its in-place link projection are
already equal under arbitrary Haar insertions. The finite geometric inverse
is a polynomial in that normalizer, so the same equality persists after its
corrector recursion. This module retains the original link permutation and
does not infer a pointwise reciprocal or a limiting conditional state.
-/

import YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.BF4ExactSlabStarReciprocalTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarBandCertificate
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem probe_add {n : Nat} (s : QuaternionBlockInvolution n)
    (p q : RatPoly) :
    headProbe s (polyAdd p q) = polyAdd (headProbe s p) (headProbe s q) := by
  change reindexQuaternionPolynomial s (liftBoundary 1 (polyAdd p q)) =
    polyAdd (reindexQuaternionPolynomial s (liftBoundary 1 p))
      (reindexQuaternionPolynomial s (liftBoundary 1 q))
  rw [lift_add, reindexQuaternionPolynomial_add]

private theorem probe_smul {n : Nat} (s : QuaternionBlockInvolution n)
    (a : Q') (p : RatPoly) :
    headProbe s (polySmul a p) = polySmul a (headProbe s p) := by
  change reindexQuaternionPolynomial s (liftBoundary 1 (polySmul a p)) =
    polySmul a (reindexQuaternionPolynomial s (liftBoundary 1 p))
  rw [lift_smul, reindexQuaternionPolynomial_smul]

private theorem probe_coeff {n : Nat} (s : QuaternionBlockInvolution n)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (headProbe s p) (headProbe s q) := by
  simpa only [headProbe, liftBoundary] using
    (RatPolyCoeffEqv.reindex s (lift_coeff 1 h))

private theorem probe_neg {n : Nat} (s : QuaternionBlockInvolution n)
    (p : RatPoly) :
    RatPolyCoeffEqv (headProbe s (polyNeg p)) (polyNeg (headProbe s p)) := by
  have hsmul : RatPolyCoeffEqv (headProbe s (polySmul (-1) p))
      (polySmul (-1) (headProbe s p)) := by
    rw [probe_smul]
    exact RatPolyCoeffEqv.refl _
  exact (probe_coeff s (neg_smul p)).trans
    (hsmul.trans
      (neg_smul (headProbe s p)).symm)

private theorem cap_supported (n : Nat) (c : Q') :
    SupportedQuaternionBlocks n (cap c) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact supported_one n u hu

private theorem probe_cap {n : Nat} (s : QuaternionBlockInvolution n)
    (c : Q') : HaarCarrierEqv n (headProbe s (cap c)) (cap c) := by
  have hz : ∀ m j : Nat, exponentAt (List.replicate m 0) j = 0 := by
    intro m
    induction m with
    | zero => intro j; rfl
    | succ m ih =>
        intro j
        cases j with
        | zero => rfl
        | succ j => exact ih j
  have hbase : QuaternionPrefixPolynomialEqv n
      (reindexQuaternionPolynomial s (liftHead polyOne)) polyOne := by
    change QuaternionPrefixPolynomialEqv n
      [(reindexQuaternionExponents s [0,0,0,0], (1 : Q'))] [([], (1 : Q'))]
    apply QuaternionPrefixPolynomialEqv.cons
    · refine ⟨Q'.eqv_refl _, ?_⟩
      intro coordinate hcoordinate
      rw [exponentAt_reindexQuaternionExponents s _ hcoordinate]
      change exponentAt (List.replicate 4 0)
        (4 * s.map (coordinate / 4) + coordinate % 4) = exponentAt [] coordinate
      rw [hz]
      rfl
    · exact .nil
  have hp : SupportedQuaternionBlocks n (headProbe s (cap c)) :=
    headProbe_supported s (cap c)
  have hq := cap_supported n c
  apply carrierOfPrefix hp hq
  change QuaternionPrefixPolynomialEqv n
    (reindexQuaternionPolynomial s (liftBoundary 1 (polySmul c polyOne)))
    (polySmul c polyOne)
  rw [lift_smul, reindexQuaternionPolynomial_smul]
  exact QuaternionPrefixPolynomialEqv.smul c hbase

private theorem probe_one {n : Nat} (s : QuaternionBlockInvolution n) :
    HaarCarrierEqv n (headProbe s polyOne) polyOne := by
  have h : RatPolyCoeffEqv polyOne (cap 1) :=
    (RatPolyCoeffEqv.one_smul polyOne).symm
  exact (RatPolyCoeffEqv.haarCarrier (probe_coeff s h)).trans
    ((probe_cap s 1).trans (RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.one_smul polyOne)))

private theorem probe_remainder {n : Nat} (s : QuaternionBlockInvolution n)
    (p q : RatPoly) (U : Q') (hU : (0 : Q') < U)
    (h : HaarCarrierEqv n (headProbe s p) q) :
    HaarCarrierEqv n
      (headProbe s (remainder p U hU)) (remainder q U hU) := by
  let a := scale U hU
  change HaarCarrierEqv n
    (headProbe s (polyAdd (polySmul a p) (polyNeg polyOne)))
    (polyAdd (polySmul a q) (polyNeg polyOne))
  rw [probe_add, probe_smul]
  exact HaarCarrierEqv.add (HaarCarrierEqv.smul a h)
    ((RatPolyCoeffEqv.haarCarrier (probe_neg s polyOne)).trans
      (HaarCarrierEqv.neg (probe_one s)))

private theorem probe_corrector {n : Nat} (s : QuaternionBlockInvolution n)
    (p q : RatPoly) (h : HaarCarrierEqv n (headProbe s p) q) :
    ∀ k : Nat, HaarCarrierEqv n
      (headProbe s (corrector p k)) (corrector q k)
  | 0 => by
      change HaarCarrierEqv n (headProbe s polyZero) polyZero
      exact HaarCarrierEqv.refl _ _
  | k+1 => by
      change HaarCarrierEqv n
        (headProbe s (polyAdd polyOne (polyMul (polyNeg p) (corrector p k))))
        (polyAdd polyOne (polyMul (polyNeg q) (corrector q k)))
      rw [probe_add, headProbe_mul]
      exact HaarCarrierEqv.add (probe_one s)
        (HaarCarrierEqv.mul
          ((RatPolyCoeffEqv.haarCarrier (probe_neg s p)).trans
            (HaarCarrierEqv.neg h))
          (probe_corrector s p q h k))

/-- Literal original-coordinate finite reciprocal equals the transported
head reciprocal under every supported Haar insertion. The two denominators
are the already pinned original normalizer, not replacement weights. -/
theorem inPlace_headReciprocal_carrier {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (k : Nat) :
    HaarCarrierEqv (blocks extent)
      (reciprocal (inPlaceNormalizer w K extent link) (starUpper w extent link)
        (starUpper_positive hw0 hw1 extent link) k)
      (headProbe (linkHeadSwap extent link hl)
        (headReciprocal hw0 hw1 K extent link hl k)) := by
  let s := linkHeadSwap extent link hl
  let p := normalizer w K extent link hl
  let q := inPlaceNormalizer w K extent link
  let U := starUpper w extent link
  let hU := starUpper_positive hw0 hw1 extent link
  have hp : HaarCarrierEqv (blocks extent) (headProbe s p) q :=
    (inPlaceNormalizer_head_pin w K extent hl).symm
  have hR := probe_remainder s p q U hU hp
  have hG := probe_corrector s (remainder p U hU) (remainder q U hU) hR k
  have hrec : HaarCarrierEqv (blocks extent)
      (headProbe s (reciprocal p U hU k)) (reciprocal q U hU k) := by
    change HaarCarrierEqv (blocks extent)
      (headProbe s (polySmul (scale U hU) (corrector (remainder p U hU) k)))
      (polySmul (scale U hU) (corrector (remainder q U hU) k))
    rw [probe_smul]
    exact HaarCarrierEqv.smul (scale U hU) hG
  exact hrec.symm

#print axioms inPlace_headReciprocal_carrier

end YMGap.Continuum.BF4ExactSlabStarReciprocalTransport
