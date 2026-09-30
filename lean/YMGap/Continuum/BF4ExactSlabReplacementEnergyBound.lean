/-
# Independent full-replica replacement is bounded by actual conditional energy

Pass the fully pinned finite cross-exterior inequality through the existing
explicit-modulus replica limit. The result uses the ORIGINAL partition and
the residual of the EXISTING conditional projection on full-action weighted
L2. It applies to every supported original polynomial. It is not a global
Poincare inequality, OS-transfer estimate, or spatial/scaling theorem.
-/

import YMGap.Continuum.BF4ExactSlabCrossExteriorEnergyFubini
import YMGap.Continuum.BF4ExactSlabReciprocalVarianceLimit
import YMGap.Continuum.GeometricCorrectedLimitOrder

namespace YMGap.Continuum.BF4ExactSlabReplacementEnergyBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabReplicaPathVariance
open YMGap.Continuum.BF4ExactSlabCrossExteriorReplacement
open YMGap.Continuum.BF4ExactSlabCrossExteriorEnergyFubini
open YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
open YMGap.Continuum.BF4ExactSlabReciprocalVarianceLimit
open YMGap.Continuum.GeometricCorrectedLimitOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionReplicaPairBounds
open YMGap.Continuum.SU2QuaternionReplicaPathTelescope
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK

private theorem replacement_nonnegative (p : (F).V) :
    (0 : Q') ≤ replacementIntegral w K extent link p.val := by
  have hf : SupportedQuaternionBlocks (blocks extent) p.val := p.property
  have hf2 : SupportedQuaternionBlocks (blocks extent + blocks extent) p.val :=
    fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))
  have hd := difference_supported (reindex_supported (headExchange extent link) p.val) hf2
  exact ((pairCertificate (blocks extent) (fullWeight_supported w K extent)
    (fullWeight_certificate hw0 hw1 K extent hK)).mul (.square _ hd)).haar_nonnegative

/-- The completed conditional residual is the one already constructed from
the same action and link. The constant is explicit and nome-dependent. -/
theorem original_replacement_energy_bound (p : (F).V) :
    RCle
      (Quotient.mk crealSetoid (ofQ'
        ((starLower w extent link * starLower w extent link) *
          replacementIntegral w K extent link p.val)))
      (RCmul
        (Quotient.mk crealSetoid (ofQ'
          ((starUpper w extent link * starUpper w extent link) *
            quaternionHaar (blocks extent) (fullWeight w K extent))))
        (RCadd
          (normSq ((projections hw0 hw1 K extent hK).residual ⟨link,hl⟩ (embedV F p)))
          (normSq ((projections hw0 hw1 K extent hK).residual ⟨link,hl⟩ (embedV F p))))) := by
  have h := geometric_corrected_limit_order
    (starRadius hw0 hw1 extent link)
    (starLower w extent link * starLower w extent link)
    (replacementIntegral w K extent link p.val)
    ((starUpper w extent link * starUpper w extent link) *
      quaternionHaar (blocks extent) (fullWeight w K extent))
    (starRadius_nonnegative hw0 hw1 extent link) (starRadius_lt_one hw0 hw1 extent link)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (starLower_positive hw0 hw1 extent link))
      (Q'.le_of_lt (starLower_positive hw0 hw1 extent link)))
    (replacement_nonnegative hw0 hw1 K extent hK link p)
    (replicaIntegral hw0 hw1 K extent hK link hl p)
    (replicaCauchy hw0 hw1 K extent hK link hl p)
    (original_replacement_finite_energy_bound hw0 hw1 K extent link hl hK p)
  change RCle _ (RCmul _ (Quotient.mk crealSetoid
    (replicaReal hw0 hw1 K extent hK link hl p))) at h
  rw [replica_limit_eq_twice_residual_norm hw0 hw1 K extent hK link hl p] at h
  exact h

#print axioms original_replacement_energy_bound

end YMGap.Continuum.BF4ExactSlabReplacementEnergyBound
