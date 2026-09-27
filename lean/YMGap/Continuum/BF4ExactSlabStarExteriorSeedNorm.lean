/-
# Original-action norm of an exterior-modulated polynomial

The inserted square is certified before any normalizer division.  Its
exterior multiplication retains the complete original heat action.  The
norm identities below are exact finite-action Haar identities, not a
coercive or continuum estimate.
-/

import YMGap.Continuum.BF4ExactSlabStarExteriorResidual
import YMGap.Continuum.BF4ExactSlabStarVarianceReplica
import YMGap.Continuum.GNSDenseCompletionLaws

namespace YMGap.Continuum.BF4ExactSlabStarExteriorSeedNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarVarianceReplica
open YMGap.Continuum.BF4ExactSlabStarExteriorResidual
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) := (boundaryCompleteSlabLinks extent).length

private theorem embed_pair (D : GNSData) (a b : D.V) :
    D.cinnerCompl (embedV D a) (embedV D b) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (D.B a b)) := D.cinnerCompl_embed a b

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "E" => exteriorSeed hw0 hw1 K extent hK i

private theorem headInput_support (p : (F).V) :
    SupportedQuaternionBlocks ((blocks extent-1)+1)
      (headInput extent i.val i.property p.val) := by
  have hc : blocks extent = (blocks extent-1)+1 := by
    have hlt := List.idxOf_lt_length_of_mem i.property
    dsimp only [blocks]
    omega
  rw [← hc]
  exact reindex_supported _ _

private theorem inserted_square_pin (p : (F).V) :
    RatPolyCoeffEqv
      (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val))
      (partialHaarHead (polyMul
        (headWeight w K extent i.val i.property)
        (polyMul (headInput extent i.val i.property p.val)
          (headInput extent i.val i.property p.val)))) := by
  unfold insertedNormalizer headWeight headInput
  simp only [reindexQuaternionPolynomial_mul]
  exact partialHaarHead_congr (RatPolyCoeffEqv.mul_comm _ _)

/-- The actual inserted square has a finite witness-bearing tail certificate. -/
def insertedSquare_certificate (p : (F).V) :
    Certificate (blocks extent-1)
      (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val)) := by
  let hp := headWeight_certificate K extent i.val i.property hw0 hw1 hK
  let hq : Certificate ((blocks extent-1)+1)
      (polyMul (headInput extent i.val i.property p.val)
        (headInput extent i.val i.property p.val)) :=
    .square _ (headInput_support hw0 hw1 K extent hK i p)
  exact .ofCoeff (inserted_square_pin hw0 hw1 K extent hK i p)
    (partialHaarHead_certificate (blocks extent-1) (Certificate.mul hp hq))

/-- The same inserted square retains every complementary action factor. -/
def tailSquare_certificate (p : (F).V) :
    Certificate (blocks extent-1)
      (polyMul
        (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val))
        (exterior w K extent i.val i.property)) :=
  Certificate.mul (insertedSquare_certificate hw0 hw1 K extent hK i p)
    (exterior_certificate K extent i.val i.property hw0 hw1 hK)

/-- The full-action squared norm is the exact inserted square with exterior heat. -/
theorem original_norm_pin (p : (F).V) :
    (F).B p p ≈ quaternionHaar (blocks extent-1)
      (polyMul
        (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val))
        (exterior w K extent i.val i.property)) := by
  change quaternionHaar (blocks extent)
    (polyMul (polyMul p.val p.val)
      (polynomialProduct (faceHeatPolynomial w K extent)
        (slabPhysicalFaceEdges extent))) ≈ _
  exact full_insertion_pin w K extent i.val i.property
    (polyMul p.val p.val) (supported_polyMul p.property p.property)

/-- Multiplying a full-action polynomial by an exterior test costs precisely
the inserted square weighted by that test's square. -/
theorem exteriorSeed_norm_pin (r : (G).V) (p : (F).V) :
    (F).B (E r p) (E r p) ≈ quaternionHaar (blocks extent-1)
      (polyMul
        (polyMul (polyMul r.val r.val)
          (insertedNormalizer w K extent i.val i.property (polyMul p.val p.val)))
        (exterior w K extent i.val i.property)) := by
  let rr : (G).V :=
    ⟨polyMul r.val r.val, supported_polyMul r.property r.property⟩
  let pp : (F).V :=
    ⟨polyMul p.val p.val, supported_polyMul p.property p.property⟩
  have hJ : (J rr).val = polyMul (J r).val (J r).val :=
    headProbe_mul (linkHeadSwap extent i.val i.property) r.val r.val
  have he : (F).B (E r p) (E r p) ≈ (F).B (J rr) pp := by
    change weightedPair _ _ _ _ ≈ weightedPair _ _ _ _
    rw [hJ]
    exact haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => (J r).val | _ => p.val)).mul_right _)
  have ht : (F).B (J rr) pp ≈ quaternionHaar (blocks extent-1)
      (polyMul (polyMul rr.val
        (insertedNormalizer w K extent i.val i.property pp.val))
        (exterior w K extent i.val i.property)) := by
    change quaternionHaar (blocks extent)
      (polyMul (polyMul (J rr).val pp.val)
        (polynomialProduct (faceHeatPolynomial w K extent)
          (slabPhysicalFaceEdges extent))) ≈ _
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
      (full_test_pin w K extent i.val i.property rr.val pp.val rr.property pp.property)
  exact Q'.eqv_trans _ _ _ he ht

/-- A padded lift of the exterior constant acts as the identity in the
original full-action completion.  It need not be coefficientwise identical
to the unpadded polynomial constant. -/
theorem exteriorSeed_one_completed (p : (F).V) :
    embedV F (E ⟨polyOne, supported_one (blocks extent-1)⟩ p) = embedV F p := by
  apply GNSDenseCompletionLaws.eq_of_dense_pairings
  intro f
  rw [embed_pair, embed_pair]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  let q : (F).V :=
    ⟨polyMul p.val f.val, supported_polyMul p.property f.property⟩
  have hreshape : (F).B (E ⟨polyOne, supported_one (blocks extent-1)⟩ p) f ≈
      quaternionHaar (blocks extent)
        (polyMul
          (headProbe (linkHeadSwap extent i.val i.property) polyOne)
          (polyMul q.val
            (polynomialProduct (faceHeatPolynomial w K extent)
              (slabPhysicalFaceEdges extent)))) := by
    change weightedPair _ _ _ _ ≈ _
    exact haar_of_coeff
      (((RatPolyCoeffEqv.mul_assoc _ _ _).mul_right _).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _))
  have htest := full_test_pin w K extent i.val i.property
    polyOne q.val (supported_one (blocks extent-1)) q.property
  have hbase : (F).B p f ≈ quaternionHaar (blocks extent-1)
      (polyMul (insertedNormalizer w K extent i.val i.property q.val)
        (exterior w K extent i.val i.property)) := by
    change quaternionHaar (blocks extent)
      (polyMul q.val
        (polynomialProduct (faceHeatPolynomial w K extent)
          (slabPhysicalFaceEdges extent))) ≈ _
    exact full_insertion_pin w K extent i.val i.property q.val q.property
  exact Q'.eqv_trans _ _ _ hreshape
    (Q'.eqv_trans _ _ _ htest
      (Q'.eqv_trans _ _ _
        (haar_of_coeff ((RatPolyCoeffEqv.one_mul _).mul_right _))
        (Q'.eqv_symm hbase)))

#print axioms insertedSquare_certificate
#print axioms tailSquare_certificate
#print axioms original_norm_pin
#print axioms exteriorSeed_norm_pin
#print axioms exteriorSeed_one_completed

end YMGap.Continuum.BF4ExactSlabStarExteriorSeedNorm
