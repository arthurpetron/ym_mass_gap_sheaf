/-
# Relative angular bound for the literal odd marginal

This keeps the original spatial action and both adjacent terminal messages.
The local cap is the sum of the endpoint-source and next-message caps; no
heat-floor factor enters it (the late cutoff remains explicit).
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard
import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.SU2QuaternionHaarHeadFubini
import YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalRelativeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.ClusterCount4DProgress

local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight

private theorem cap_supported (blocks : Nat) (c : Q') :
    SupportedQuaternionBlocks blocks (cap c) := by
  unfold cap
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact supported_one blocks u hu

private theorem neg_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

private theorem reindex_one_prefix {blocks : Nat} (s : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s polyOne) polyOne := by
  change QuaternionPrefixPolynomialEqv blocks
    [(reindexQuaternionExponents s [], 1)] [([], 1)]
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro coordinate hcoordinate
      rw [exponentAt_reindexQuaternionExponents s [] hcoordinate]
      simp [exponentAt]
  · exact .nil

private theorem reindex_cap_prefix {blocks : Nat}
    (s : QuaternionBlockInvolution blocks) (c : Q') :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s (cap c)) (cap c) := by
  unfold cap
  rw [reindexQuaternionPolynomial_smul]
  exact .smul c (reindex_one_prefix s)

/-- A selected block relative bound is transported to its frame coordinate
by genuine same-carrier endpoint equalities, not raw padded coefficient
identification. -/
private def reindexRelativeBound {blocks source i j : Nat}
    (s : QuaternionBlockInvolution blocks) (hsource : source < blocks)
    (hmap : s.map 0 = source) (hi : i < 4) (hj : j < 4)
    {p : RatPoly} {c : Q'} (hp : SupportedQuaternionBlocks blocks p)
    (P : RelativeBound blocks (4*source+i) (4*source+j) p c) :
    RelativeBound blocks i j (reindexQuaternionPolynomial s p) c := by
  have hD := reindex_blockAngularDerivative_prefix (block := 0) s (by omega) hi hj p
  have hcarD : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (angularDerivative (4*source+i) (4*source+j) p))
      (angularDerivative i j (reindexQuaternionPolynomial s p)) := by
    simpa [blockAngularDerivative, hmap] using
      (carrierOfPrefix (reindex_supported s _)
        (angularDerivative_supported_at (by omega) (by omega) (reindex_supported s p)) hD)
  have hcap := reindex_cap_prefix s c
  have hupper : QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s
        (polyAdd (polyMul (cap c) p)
          (polyNeg (angularDerivative (4*source+i) (4*source+j) p))))
      (polyAdd (polyMul (cap c) (reindexQuaternionPolynomial s p))
        (polyNeg (angularDerivative i j (reindexQuaternionPolynomial s p)))) := by
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_mul,
      reindexQuaternionPolynomial_neg]
    exact (hcap.mul (.refl blocks (reindexQuaternionPolynomial s p))).append
      (by simpa [blockAngularDerivative, hmap, Nat.mul_zero, Nat.zero_add] using hD.neg)
  have hlower : QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s
        (polyAdd (polyMul (cap c) p)
          (angularDerivative (4*source+i) (4*source+j) p)))
      (polyAdd (polyMul (cap c) (reindexQuaternionPolynomial s p))
        (angularDerivative i j (reindexQuaternionPolynomial s p))) := by
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_mul]
    exact (hcap.mul (.refl blocks (reindexQuaternionPolynomial s p))).append
      (by simpa [blockAngularDerivative, hmap, Nat.mul_zero, Nat.zero_add] using hD)
  have hupCar : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (polyAdd (polyMul (cap c) p)
          (polyNeg (angularDerivative (4*source+i) (4*source+j) p))))
      (polyAdd (polyMul (cap c) (reindexQuaternionPolynomial s p))
        (polyNeg (angularDerivative i j (reindexQuaternionPolynomial s p)))) := by
    apply carrierOfPrefix
    · exact reindex_supported s _
    · exact supported_add
        (supported_polyMul (cap_supported blocks c) (reindex_supported s p))
        (neg_supported (angularDerivative_supported_at (by omega) (by omega)
          (reindex_supported s p)))
    · exact hupper
  have hloCar : HaarCarrierEqv blocks
      (reindexQuaternionPolynomial s
        (polyAdd (polyMul (cap c) p)
          (angularDerivative (4*source+i) (4*source+j) p)))
      (polyAdd (polyMul (cap c) (reindexQuaternionPolynomial s p))
        (angularDerivative i j (reindexQuaternionPolynomial s p))) := by
    apply carrierOfPrefix
    · exact reindex_supported s _
    · exact supported_add
        (supported_polyMul (cap_supported blocks c) (reindex_supported s p))
        (angularDerivative_supported_at (by omega) (by omega) (reindex_supported s p))
    · exact hlower
  exact {
    positive := reindex_certificate s hp P.positive
    nonnegative := P.nonnegative
    upper := .transport hupCar.symm
      (reindex_certificate s
        (supported_add (supported_polyMul (cap_supported blocks c) hp)
          (neg_supported (angularDerivative_supported_at (by omega) (by omega) hp))) P.upper)
    lower := .transport hloCar.symm
      (reindex_certificate s
        (supported_add (supported_polyMul (cap_supported blocks c) hp)
          (angularDerivative_supported_at (by omega) (by omega) hp)) P.lower)
  }

/-- The literal marginal `V*g_n*g_(n+1)` has the sum of the six-face
spatial-source cap and one terminal-message cap. -/
def marginalRelativeBound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : endpointRelativeCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (N width) (4*(baseLinks width).idxOf selected+i)
      (4*(baseLinks width).idxOf selected+j)
      (marginalWeight w K width n)
      (6 * relativeCap w 4096 + 2 * relativeCap w 32) := by
  have h32 : relativeCutoff w 32 ≤ K :=
    Nat.le_trans (Nat.le_max_right _ _) hK
  have P := (endpointSourceRelativeBound hw0 hw1 K width hK n selected hl hs hi hj).mul
    (terminalMessageRelativeBound hw0 hw1 K width h32 n
      ((baseLinks width).idxOf selected) hs hi hj)
  have heq : Q'.eqv (endpointRelativeCap w + relativeCap w 32)
      (6 * relativeCap w 4096 + 2 * relativeCap w 32) := by
    unfold endpointRelativeCap
    exact poly_identity_of_normal_eq
      (.add (.add (.mul (.const 6) (.var 0)) (.var 1)) (.var 1))
      (.add (.mul (.const 6) (.var 0)) (.mul (.const 2) (.var 1)))
      (by decide) (fun | 0 => relativeCap w 4096 | _ => relativeCap w 32)
  have P' := P.changeCap heq
  exact RelativeBound.ofCoeff (by
    unfold marginalWeight endpointSource
    exact RatPolyCoeffEqv.refl _) P'

/-- Move the selected active link to the frame head, preserving the same
original marginal and the cap from `marginalRelativeBound`. -/
def frameRelativeBound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : endpointRelativeCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (N width) i j
      (frameWeight w K width n
        (headSwapBlockInvolution (N width) ((baseLinks width).idxOf selected)
          (List.idxOf_lt_length_of_mem hl)))
      (6 * relativeCap w 4096 + 2 * relativeCap w 32) := by
  let s := headSwapBlockInvolution (N width) ((baseLinks width).idxOf selected)
    (List.idxOf_lt_length_of_mem hl)
  have hmap : s.map 0 = (baseLinks width).idxOf selected := by
    exact headSwapBlockInvolution_map_zero _ _ _
  have P := marginalRelativeBound hw0 hw1 K width n hK selected hl hs hi hj
  simpa [frameWeight, marginalWeight, s] using
    (reindexRelativeBound s (List.idxOf_lt_length_of_mem hl) hmap hi hj
      (marginalWeight_supported w K width n) P)

#print axioms marginalRelativeBound
#print axioms frameRelativeBound

end YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalRelativeBound
