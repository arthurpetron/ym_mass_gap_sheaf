/-
# Free-link averaging with the actual complementary action retained

Deleting the incident star leaves a weight independent of the selected
physical link. Its normalized Haar average is computed by the original
block swap and partial Haar integral. Every supported exterior probe pairs
with this exact polynomial-valued average.

When that average is coefficient-equivalent to zero, the original
polynomial is orthogonal to every exterior probe in the star-deleted form.
Subtracting such a probe can only increase the star-deleted squared norm.
The hypothesis is conditional polynomial centering, not a scalar mean-zero
claim. Independently, subtracting the lifted free average constructs an
orthogonal residual for every original polynomial, proved directly in the
form without a coefficient-level padding identification. No completed free
projection, spatial or OS gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabStarFullActionProbe

namespace YMGap.Continuum.BF4ExactSlabStarFreeCentering

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- Only the incident factors are deleted; the original carrier and the
complete complementary shared-link action are unchanged. -/
def deletedData {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (_hl : link ∈ boundaryCompleteSlabLinks extent) : GNSData :=
  weightedGNSData (blocks extent) (complementHeat w K extent link)
    (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
      (fun _ hi => complementIds_physical hi))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "F" => fullData hw0 hw1 K extent hK
local notation "D" => deletedData hw0 hw1 K extent hK link hl
local notation "J" => probeMap hw0 hw1 K extent hK link hl

/-- Exact normalized Haar integration of the selected link, before any
incident heat factor is inserted. -/
def freeAverage (p : (F).V) : (G).V := by
  refine ⟨partialHaarHead (reindexQuaternionPolynomial (linkHeadSwap extent link hl) p.val), ?_⟩
  have hlt := List.idxOf_lt_length_of_mem hl
  have hn : blocks extent = (blocks extent-1)+1 := by dsimp only [blocks]; omega
  apply BF4ExactPhysicalCenteredVacuumTransmittedMarginal.partialHaarHead_supported
  rw [← hn]
  exact BF4ExactPhysicalCenteredVacuumTransmittedMarginal.reindexQuaternionPolynomial_supported _ _

local notation "A" => freeAverage hw0 hw1 K extent hK link hl

/-- Exact free conditional pairing, with the actual complementary weight. -/
theorem deleted_probe_pair (r : (G).V) (p : (F).V) :
    (D).B (J r) p ≈ (G).B r (A p) := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
    (headProbe_product_pair hb (linkHeadSwap extent link hl) r.val p.val
      (complementHeat w K extent link) r.property p.property
      (complementHeat_supported w K extent link) (complementHeat_headIndependent w K extent link hl))

/-- Polynomial-valued free centering annihilates every exterior probe. -/
theorem deleted_pair_zero (r : (G).V) (p : (F).V)
    (hcenter : (G).veq (A p) (G).zero) :
    (D).B p (J r) ≈ 0 :=
  Q'.eqv_trans _ _ _ ((D).B_symm p (J r))
    (Q'.eqv_trans _ _ _ (deleted_probe_pair hw0 hw1 K extent hK link hl r p)
      (Q'.eqv_trans _ _ _ ((G).B_congr_right r hcenter)
        (Q'.eqv_trans _ _ _ ((G).B_symm r (G).zero) ((G).B_zero_left r))))

/-- Subtracting a star-deleted-orthogonal exterior probe cannot lower the
star-deleted squared norm. No coefficient-representation equality is needed. -/
theorem deleted_sub_norm_lower (p : (F).V) (r : (G).V)
    (horth : (D).B p (J r) ≈ 0) :
    (D).B p p ≤ (D).B ((D).sub p (J r)) ((D).sub p (J r)) := by
  have hz : -((D).B p (J r)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ horth)
      (by decide : Q'.eqv (-(0 : Q')) 0)
  have he : (D).B ((D).sub p (J r)) ((D).sub p (J r)) ≈
      (D).B p p + (D).B (J r) (J r) :=
    Q'.eqv_trans _ _ _ ((D).B_sub_diag_expand p (J r))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (Q'.eqv_refl _) hz)
          (Q'.add_eqv_congr' hz (Q'.eqv_refl _)))
        (Q'.eqv_of_eq (by rw [Q'.add_zero', Q'.zero_add'])))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ ((D).self_nonneg (J r))) (Q'.ge_of_eqv he)

/-- A free-centered original input cannot lose star-deleted norm by
subtracting an arbitrary supported exterior probe. -/
theorem deleted_residual_norm_lower (p : (F).V) (r : (G).V)
    (hcenter : (G).veq (A p) (G).zero) :
    (D).B p p ≤ (D).B ((D).sub p (J r)) ((D).sub p (J r)) :=
  deleted_sub_norm_lower hw0 hw1 K extent hK link hl p r
    (deleted_pair_zero hw0 hw1 K extent hK link hl r p hcenter)

/-- Explicit free centering on the SAME original supported carrier. -/
def freeResidual (p : (F).V) : (F).V := (F).sub p (J (A p))

private theorem deleted_probe_probe_pair (r a : (G).V) :
    (D).B (J a) (J r) ≈ (G).B r a := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have he := headProbe_independent_pair hb (linkHeadSwap extent link hl)
    (polyMul r.val a.val) (complementHeat w K extent link)
    (supported_polyMul r.property a.property)
    (complementHeat_supported w K extent link) (complementHeat_headIndependent w K extent link hl)
  rw [headProbe_mul] at he
  exact Q'.eqv_trans _ _ _ ((D).B_symm (J a) (J r)) he

/-- Every original polynomial has a constructed free residual orthogonal
to every exterior probe. The proof compares Haar pairings directly; it
does not identify padded and unpadded coefficient representations. -/
theorem freeResidual_pair_zero (p : (F).V) (r : (G).V) :
    (D).B (freeResidual hw0 hw1 K extent hK link hl p) (J r) ≈ 0 := by
  have hleft : (D).B p (J r) ≈ (G).B r (A p) :=
    Q'.eqv_trans _ _ _ ((D).B_symm p (J r))
      (deleted_probe_pair hw0 hw1 K extent hK link hl r p)
  have hright : (D).B (J (A p)) (J r) ≈ (G).B r (A p) :=
    deleted_probe_probe_pair hw0 hw1 K extent hK link hl r (A p)
  have hsame : (D).B p (J r) ≈ (D).B (J (A p)) (J r) :=
    Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)
  change (D).B ((D).sub p (J (A p))) (J r) ≈ 0
  exact Q'.eqv_trans _ _ _ ((D).B_add_left p ((D).neg (J (A p))) (J r))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hsame ((D).B_neg_left (J (A p)) (J r)))
      (OSReconstructionProgress.q_add_neg_self ((D).B (J (A p)) (J r))))

end YMGap.Continuum.BF4ExactSlabStarFreeCentering

#print axioms YMGap.Continuum.BF4ExactSlabStarFreeCentering.deletedData
#print axioms YMGap.Continuum.BF4ExactSlabStarFreeCentering.freeAverage
#print axioms YMGap.Continuum.BF4ExactSlabStarFreeCentering.deleted_probe_pair
#print axioms YMGap.Continuum.BF4ExactSlabStarFreeCentering.deleted_pair_zero
#print axioms YMGap.Continuum.BF4ExactSlabStarFreeCentering.deleted_sub_norm_lower
#print axioms YMGap.Continuum.BF4ExactSlabStarFreeCentering.deleted_residual_norm_lower
#print axioms YMGap.Continuum.BF4ExactSlabStarFreeCentering.freeResidual
#print axioms YMGap.Continuum.BF4ExactSlabStarFreeCentering.freeResidual_pair_zero
