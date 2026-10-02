/-
# Condition the COMPLETE original central edge on a signed family's footprint

Both copies of every spectator link are integrated from the literal original
K(x,y)V(x)V(y)g(x)g(y), with g the actual terminal message. This constructs
one JOINT density; it does not factor it into independent endpoint sources.
The original positive certificate, partition, endpoint moments, OWN variance
and full signed squared temporal increment are preserved exactly.

At most eight quaternion blocks per supplied face remain relevant. This is a
variable-support bound, NOT a bound on degree, coefficient size, construction
cost or runtime. Nome, cutoff, width and terminal-depth dependence remain in
the integrated coefficients. The projected finite margin feeds the existing
original reference checker; no accepted small-rate instance is supplied.
Scaling survival, physical mass, continuum QFT and every group remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint
import YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionHaarBlockCompression
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor
import YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalEnergyComparison
  (edgeMass_positive edgeMoment_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFootprint
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression family_within)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondFloor
  (finite_family_energy_pin finite_family_variance_pin)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit (finiteEnergy)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit (finiteVariance)
open YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin
  (referenceMargin referenceCutoff check)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
  (exponentAt_clearQuaternionBlock_self)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage

/-- Integrate the complement of the COMMON family footprint at BOTH ends. -/
def spectatorCopies (width : Nat) (qs : List Z4Plaq) : List Nat :=
  familySpectatorBlocks width qs ++
    (familySpectatorBlocks width qs).map (fun i => N width+i)

/-- The two copies of the deduplicated observable footprint. -/
def observableCopies (width : Nat) (qs : List Z4Plaq) : List Nat :=
  familyObservableBlocks width qs ++
    (familyObservableBlocks width qs).map (fun i => N width+i)

theorem observableCopies_length (width : Nat) (qs : List Z4Plaq) :
    (observableCopies width qs).length ≤ 8*qs.length := by
  have h := familyObservableBlocks_length_le_four width qs
  simp only [observableCopies, List.length_append, List.length_map]
  omega

private theorem observableCopies_nodup (width : Nat) (qs : List Z4Plaq) :
    (observableCopies width qs).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨familyObservableBlocks_nodup width qs,
    YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn _ _
      (familyObservableBlocks_nodup width qs) (fun _ _ _ _ h => by omega), ?_⟩
  intro a ha b hb heq
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
  have h := familyObservableBlocks_lt width qs a ha
  omega

private theorem observableCopies_lt (width : Nat) (qs : List Z4Plaq) (i : Nat)
    (hi : i ∈ observableCopies width qs) : i < N width+N width := by
  rcases List.mem_append.mp hi with hi | hi
  · have h := familyObservableBlocks_lt width qs i hi
    omega
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have h := familyObservableBlocks_lt width qs j hj
    omega

/-- Explicit placement of the smaller two-endpoint carrier in the original one. -/
def footprintEmbedding (width : Nat) (qs : List Z4Plaq) :
    BlockEmbedding (observableCopies width qs).length (N width+N width) where
  image := observableCopies width qs
  length := rfl
  nodup := observableCopies_nodup width qs
  physical := observableCopies_lt width qs

theorem spectatorCopies_lt (width : Nat) (qs : List Z4Plaq) (i : Nat)
    (hi : i ∈ spectatorCopies width qs) : i < N width+N width := by
  rcases List.mem_append.mp hi with hi | hi
  · have h := familySpectatorBlocks_lt width qs i hi
    omega
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have h := familySpectatorBlocks_lt width qs j hj
    omega

private theorem spectator_of_not_observable (width : Nat) (qs : List Z4Plaq)
    (i : Nat) (hi : i < N width) (hnot : i ∉ familyObservableBlocks width qs) :
    i ∈ familySpectatorBlocks width qs := by
  have h := (familySpectator_observable_cover width qs).mem_iff.mpr
    (List.mem_range.mpr hi)
  exact (List.mem_append.mp h).resolve_right hnot

private theorem copies_cover (width : Nat) (qs : List Z4Plaq) (i : Nat)
    (hi : i < N width+N width) (hnot : i ∉ observableCopies width qs) :
    i ∈ spectatorCopies width qs := by
  by_cases hlow : i < N width
  · exact List.mem_append_left _ (spectator_of_not_observable width qs i hlow
      (fun h => hnot (List.mem_append_left _ h)))
  · have hj : i-N width < N width := by omega
    have heq : N width+(i-N width) = i := by omega
    have hs := spectator_of_not_observable width qs (i-N width) hj (by
      intro h
      exact hnot (List.mem_append_right _ (List.mem_map.mpr ⟨_, h, heq⟩)))
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hs, heq⟩)

private theorem lower_independent (width : Nat) (qs : List Z4Plaq)
    (coeff : Z4Plaq → Q') (i : Nat) (hi : i ∈ spectatorCopies width qs) :
    QuaternionBlockIndependent i (spatialSpan width coeff qs) := by
  rcases List.mem_append.mp hi with hi | hi
  · exact spatialSpan_familySpectator_independent width coeff qs i hi
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact supported_upper_independent (spatialSpan_supported width coeff qs) j

private theorem upper_independent (width : Nat) (qs : List Z4Plaq)
    (coeff : Z4Plaq → Q') (i : Nat) (hi : i ∈ spectatorCopies width qs) :
    QuaternionBlockIndependent i (liftBoundary (N width) (spatialSpan width coeff qs)) := by
  rcases List.mem_append.mp hi with hi | hi
  · exact lift_lower_independent (N width) _ i (familySpectatorBlocks_lt width qs i hi)
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact lift_upper_independent (N width)
      (spatialSpan_familySpectator_independent width coeff qs j hj)

private theorem square_independent (width : Nat) (qs : List Z4Plaq)
    (coeff : Z4Plaq → Q') (i : Nat) (hi : i ∈ spectatorCopies width qs) :
    QuaternionBlockIndependent i
      (polyMul (jump width (spatialSpan width coeff qs))
        (jump width (spatialSpan width coeff qs))) := by
  have h := quaternionBlockIndependent_polyAdd (lower_independent width qs coeff i hi)
    (quaternionBlockIndependent_polyNeg (upper_independent width qs coeff i hi))
  exact quaternionBlockIndependent_polyMul h h

/-- One actual JOINT polynomial, with all action and terminal factors integrated. -/
def density (w : Q') (K width depth : Nat) (qs : List Z4Plaq) : RatPoly :=
  familyProject (spectatorCopies width qs)
    (edgeDensity w K width (terminalMessage w K width depth))

theorem density_supported (w : Q') (K width depth : Nat) (qs : List Z4Plaq) :
    SupportedQuaternionBlocks (N width+N width) (density w K width depth qs) :=
  familyProject_supported _
    (edgeDensity_supported w K width (terminalMessage_supported w K width depth))

/-- Every in-range block outside the explicit <=8|qs| list is literally absent. -/
theorem density_local (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (i : Nat) (hi : i < N width+N width) (hnot : i ∉ observableCopies width qs) :
    QuaternionBlockIndependent i (density w K width depth qs) :=
  familyProject_independent _ _ i (copies_cover width qs i hi hnot)

private theorem blockZero_of_independent {i : Nat} {p : RatPoly}
    (hp : QuaternionBlockIndependent i p) {term : RatTerm} (ht : term ∈ p) :
    BlockZero term.1 i := by
  intro component hc
  have h := exponentAt_clearQuaternionBlock_self term.1 i component hc
  rw [hp term ht] at h
  exact h

/-- Preserve arbitrary signed tests on the COMMON two-endpoint footprint. -/
theorem pairing_pin (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (p : RatPoly) (hp : ∀ i, i ∈ spectatorCopies width qs → QuaternionBlockIndependent i p) :
    quaternionHaar (N width+N width) (polyMul (density w K width depth qs) p) ≈
      quaternionHaar (N width+N width)
        (polyMul (edgeDensity w K width (terminalMessage w K width depth)) p) :=
  Q'.eqv_trans _ _ _
    (familyProject_selfAdjoint _ _ (spectatorCopies_lt width qs) _ p)
    (haar_of_coeff ((RatPolyCoeffEqv.refl _).mul (familyProject_fixed _ p hp)))

/-- Evaluate on the computed SMALLER carrier, retaining every signed term. -/
def compressedPairing (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (p : RatPoly) : Q' :=
  quaternionHaar (observableCopies width qs).length
    ((footprintEmbedding width qs).compress (polyMul (density w K width depth qs) p))

/-- Exact reduced evaluation of the original joint insertion; no runtime bound. -/
theorem compressedPairing_pin (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width+N width) p)
    (hi : ∀ i, i ∈ spectatorCopies width qs → QuaternionBlockIndependent i p) :
    compressedPairing w K width depth qs p ≈
      quaternionHaar (N width+N width)
        (polyMul (edgeDensity w K width (terminalMessage w K width depth)) p) := by
  have hlocal : BlockLocal (N width+N width)
      (fun b => b ∈ (footprintEmbedding width qs).image)
      (polyMul (density w K width depth qs) p) := by
    intro term ht b hb hout
    exact blockZero_of_independent (quaternionBlockIndependent_polyMul
      (density_local w K width depth qs b hb hout)
      (hi b (copies_cover width qs b hb hout))) ht
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm ((footprintEmbedding width qs).haar_compress _
      (supported_polyMul (density_supported w K width depth qs) hp) hlocal))
    (pairing_pin w K width depth qs p hi)

/-- Positivity is constructed from the ORIGINAL finite terminal messages. -/
def density_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (qs : List Z4Plaq) :
    Certificate (N width+N width) (density w K width depth qs) :=
  familyProject_certificate _ _ (spectatorCopies_lt width qs)
    (edgeDensity_supported w K width (terminalMessage_supported w K width depth))
    (edgeCertificate hw0 hw1 K width hK (terminalMessage_supported w K width depth)
      (terminalMessage_certificate hw0 hw1 K width hK depth))

theorem mass_pin (w : Q') (K width depth : Nat) (qs : List Z4Plaq) :
    quaternionHaar (N width+N width) (density w K width depth qs) ≈
      oddMass w K width depth :=
  Q'.eqv_trans _ _ _ (familyProject_mean _ _ (spectatorCopies_lt width qs) _)
    (edge_total_mass w K width depth)

theorem mass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (qs : List Z4Plaq) :
    (0 : Q') < quaternionHaar (N width+N width) (density w K width depth qs) :=
  HeatKernelRGStep.lt_of_lt_of_le (oddMass_positive hw0 hw1 K width hK depth)
    (Q'.ge_of_eqv (mass_pin w K width depth qs))

theorem compressedMass_pin (w : Q') (K width depth : Nat) (qs : List Z4Plaq) :
    compressedPairing w K width depth qs polyOne ≈ oddMass w K width depth :=
  Q'.eqv_trans _ _ _
    (compressedPairing_pin w K width depth qs polyOne (supported_one _)
      (fun i _ => quaternionBlockIndependent_polyOne i))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _))
      (edge_total_mass w K width depth))

theorem compressedMass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (qs : List Z4Plaq) :
    (0 : Q') < compressedPairing w K width depth qs polyOne :=
  HeatKernelRGStep.lt_of_lt_of_le (oddMass_positive hw0 hw1 K width hK depth)
    (Q'.ge_of_eqv (compressedMass_pin w K width depth qs))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (qs : List Z4Plaq)

/-- Numerator AND actual mass are evaluated on the computed smaller carrier. -/
def moment (p : RatPoly) : Q' :=
  compressedPairing w K width depth qs p *
    Q'.recipPos (compressedPairing w K width depth qs polyOne)
      (compressedMass_positive hw0 hw1 K width hK depth qs)

theorem moment_pin (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width+N width) p)
    (hi : ∀ i, i ∈ spectatorCopies width qs → QuaternionBlockIndependent i p) :
    moment hw0 hw1 K width hK depth qs p ≈
      quaternionHaar (N width+N width)
        (polyMul (edgeDensity w K width (terminalMessage w K width depth)) p) *
        Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (compressedPairing_pin w K width depth qs p hp hi))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _
      (compressedMass_positive hw0 hw1 K width hK depth qs)
      (oddMass_positive hw0 hw1 K width hK depth) (compressedMass_pin w K width depth qs)))

private theorem lower_moment_pin (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p)
    (hi : ∀ i, i ∈ spectatorCopies width qs → QuaternionBlockIndependent i p) :
    moment hw0 hw1 K width hK depth qs p ≈
      middleRatio hw0 hw1 K width hK (depth+1) depth p :=
  Q'.eqv_trans _ _ _ (moment_pin hw0 hw1 K width hK depth qs p
    (fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))) hi)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (edge_marginal_pairing w K width (terminalMessage_supported w K width depth) hp))
      (marginal_middleRatio hw0 hw1 K width hK depth p))

/-- Center at the projected law's OWN mean, retaining the entire signed family. -/
def variance (coeff : Z4Plaq → Q') : Q' :=
  moment hw0 hw1 K width hK depth qs
      (polyMul (spatialSpan width coeff qs) (spatialSpan width coeff qs)) +
    -(moment hw0 hw1 K width hK depth qs (spatialSpan width coeff qs) *
      moment hw0 hw1 K width hK depth qs (spatialSpan width coeff qs))

theorem variance_pin (coeff : Z4Plaq → Q') :
    variance hw0 hw1 K width hK depth qs coeff ≈
      oddVariance hw0 hw1 K width hK depth (spatialSpan width coeff qs) := by
  have hm := lower_moment_pin hw0 hw1 K width hK depth qs _
    (spatialSpan_supported width coeff qs) (lower_independent width qs coeff)
  have hs := lower_moment_pin hw0 hw1 K width hK depth qs _
    (supported_polyMul (spatialSpan_supported width coeff qs) (spatialSpan_supported width coeff qs))
    (fun i hi => quaternionBlockIndependent_polyMul
      (lower_independent width qs coeff i hi) (lower_independent width qs coeff i hi))
  exact Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm) (Q'.mul_eqv_congr_left _ _ _ hm)))

/-- Half the COMPLETE signed squared increment, not a diagonal-face sum. -/
def temporalEnergy (coeff : Z4Plaq → Q') : Q' :=
  HalfPow.half * moment hw0 hw1 K width hK depth qs
    (polyMul (jump width (spatialSpan width coeff qs)) (jump width (spatialSpan width coeff qs)))

theorem temporalEnergy_pin (coeff : Z4Plaq → Q') :
    temporalEnergy hw0 hw1 K width hK depth qs coeff ≈
      normalizedEnergy hw0 hw1 K width hK depth (spatialSpan width coeff qs) := by
  have hj := jump_supported width (spatialSpan_supported width coeff qs)
  have hm := moment_pin hw0 hw1 K width hK depth qs _
    (supported_polyMul hj hj) (square_independent width qs coeff)
  have he := Q'.eqv_symm (energy_identity w K width (terminalMessage_supported w K width depth)
    (spatialSpan_supported width coeff qs))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left HalfPow.half _ _ hm)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.mul_eqv_congr_right _ _ _ he))
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
        (.mul (.mul (.var 0) (.const 2)) (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => HalfPow.half
          | 1 => energy w K width (terminalMessage w K width depth) (spatialSpan width coeff qs)
          | _ => Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : HalfPow.half*2 ≈ (1 : Q')))
          (Q'.one_mul_eqv _))))

/-- The computable signed margin of the actual conditioned JOINT law. -/
def margin (coeff : Z4Plaq → Q') (c : Q') : Q' :=
  c*variance hw0 hw1 K width hK depth qs coeff + -(temporalEnergy hw0 hw1 K width hK depth qs coeff)

variable {base : Nat} (hwidth : base < width) (coeff : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)

local notation "wideFaces" =>
  (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
local notation "e" => familyExpression width qs coeff wideFaces
local notation "he" => family_within width qs coeff wideFaces

/-- The conditioned signed margin is the existing ORIGINAL certificate input. -/
theorem finite_margin_pin (stage t : Nat) (c : Q') :
    margin hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t qs coeff c ≈
      referenceMargin hw0 hw1 e c stage t := by
  have hv := Q'.eqv_trans _ _ _
    (variance_pin hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t qs coeff)
    (Q'.eqv_symm (finite_family_variance_pin hw0 hw1 hwidth qs coeff hqs stage t))
  have hE := Q'.eqv_trans _ _ _
    (temporalEnergy_pin hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t qs coeff)
    (Q'.eqv_symm (finite_family_energy_pin hw0 hw1 hwidth qs coeff hqs stage t))
  exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_left c _ _ hv) (Q'.neg_eqv_congr _ _ hE)

#print axioms observableCopies_length
#print axioms footprintEmbedding
#print axioms density_supported
#print axioms density_local
#print axioms density_certificate
#print axioms pairing_pin
#print axioms compressedPairing_pin
#print axioms mass_pin
#print axioms mass_positive
#print axioms compressedMass_pin
#print axioms compressedMass_positive
#print axioms moment_pin
#print axioms variance_pin
#print axioms temporalEnergy_pin
#print axioms finite_margin_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDensity
