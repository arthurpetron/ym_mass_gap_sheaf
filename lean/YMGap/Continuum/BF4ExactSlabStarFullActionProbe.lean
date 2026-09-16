/-
# Exterior probes in the original full-action polynomial space

The full carrier is weighted by the actual heat product over every physical
face. A supported exterior polynomial is lifted by the selected-link Haar
block involution. Its full-action pairing is exactly the exterior B-weighted
pairing with the actual integrated star D retained.

These finite identities and the nome-dependent norm ceiling support a lift
to completions. They do not assert a completed conditional update, spatial
contraction, an OS estimate or a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabStarInverseApproximation

namespace YMGap.Continuum.BF4ExactSlabStarFullActionProbe

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInsertedNumerator
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- The certified polynomial form uses the complete original slab action. -/
def fullData {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) : GNSData :=
  weightedGNSData (blocks extent)
    (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))
    (headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ hi => hi))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "F" => fullData hw0 hw1 K extent hK
local notation "M" => normalizerMap hw0 hw1 K extent hK link hl

/-- Lift the same exterior polynomial to the original shared-link carrier. -/
def probeMap (r : (G).V) : (F).V :=
  ⟨headProbe (linkHeadSwap extent link hl) r.val, headProbe_supported _ _⟩

local notation "J" => probeMap hw0 hw1 K extent hK link hl

theorem probeMap_sub (a b : (G).V) :
    (F).veq (J ((G).sub a b)) ((F).sub (J a) (J b)) := by
  change RatPolyCoeffEqv
    (headProbe (linkHeadSwap extent link hl) (polyAdd a.val (polySmul (-1) b.val)))
    (polyAdd (headProbe (linkHeadSwap extent link hl) a.val)
      (polySmul (-1) (headProbe (linkHeadSwap extent link hl) b.val)))
  have he : headProbe (linkHeadSwap extent link hl) (polyAdd a.val (polySmul (-1) b.val)) =
      polyAdd (headProbe (linkHeadSwap extent link hl) a.val)
        (polySmul (-1) (headProbe (linkHeadSwap extent link hl) b.val)) := by
    simp [headProbe, liftHead, reindexQuaternionPolynomial, polyAdd, polySmul,
      List.map_map, Function.comp_def]
  rw [he]
  exact RatPolyCoeffEqv.refl _

/-- Full-action norm control retains the complementary exterior weight. -/
theorem probeMap_norm (a : (G).V) :
    (F).B (J a) (J a) ≤ upperFactor w * (G).B a a :=
  headProbe_full_norm_bound hw0 hw1 K extent hK link hl a.val a.property

/-- The induced exterior pairing is the ORIGINAL D*B marginal form. -/
theorem probeMap_pair (a b : (G).V) :
    (F).B (J a) (J b) ≈ (G).B a (M b) := by
  let swap := linkHeadSwap extent link hl
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have he := headProbe_product_pair hb swap (polyMul a.val b.val)
    (incidentHeat w K extent link) (complementHeat w K extent link)
    (supported_polyMul a.property b.property)
    (incidentHeat_supported w K extent link) (complementHeat_supported w K extent link)
    (complementHeat_headIndependent w K extent link hl)
  rw [headProbe_mul] at he
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.refl _).mul (heatProduct_partition w K extent link)))
    (Q'.eqv_trans _ _ _ he
      (haar_of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).mul_right _)))

/-- Pairing against an original observable retains its actual inserted numerator. -/
theorem probeMap_test (a : (G).V) (p : (F).V) :
    (F).B (J a) p ≈ (G).B a
      ⟨insertedNormalizer w K extent link hl p.val,
        insertedNormalizer_supported w K extent link hl p.val p.property⟩ :=
  insertedNormalizer_pair_pin w K extent link hl a.val p.val a.property p.property

/-- The actual integrated numerator, with its proved exterior support. -/
def numeratorMap (p : (F).V) : (G).V :=
  ⟨insertedNormalizer w K extent link hl p.val,
    insertedNormalizer_supported w K extent link hl p.val p.property⟩

local notation "N" => numeratorMap hw0 hw1 K extent hK link hl

/-- Original full-action null classes induce the same B-weighted numerator
class. Exact test pairings suffice; no numerator linearity is assumed. -/
theorem numerator_rad (p q : (F).V) (h : (F).rad p q) :
    (G).rad (N p) (N q) := by
  have he (a : (G).V) : (G).B a (N p) ≈ (G).B a (N q) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (probeMap_test hw0 hw1 K extent hK link hl a p))
      (Q'.eqv_trans _ _ _ ((F).B_welldef ((F).rad_refl (J a)) h)
        (probeMap_test hw0 hw1 K extent hK link hl a q))
  let a := (G).sub (N p) (N q)
  change (G).B a a ≈ 0
  exact Q'.eqv_trans _ _ _ ((G).B_add_right a (N p) ((G).neg (N q)))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (he a) ((G).B_neg_right a (N q)))
      (OSReconstructionProgress.q_add_neg_self ((G).B a (N q))))

end YMGap.Continuum.BF4ExactSlabStarFullActionProbe

#print axioms YMGap.Continuum.BF4ExactSlabStarFullActionProbe.fullData
#print axioms YMGap.Continuum.BF4ExactSlabStarFullActionProbe.probeMap
#print axioms YMGap.Continuum.BF4ExactSlabStarFullActionProbe.probeMap_sub
#print axioms YMGap.Continuum.BF4ExactSlabStarFullActionProbe.probeMap_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarFullActionProbe.probeMap_pair
#print axioms YMGap.Continuum.BF4ExactSlabStarFullActionProbe.probeMap_test
#print axioms YMGap.Continuum.BF4ExactSlabStarFullActionProbe.numeratorMap
#print axioms YMGap.Continuum.BF4ExactSlabStarFullActionProbe.numerator_rad
