/-
# Computed localization floor for the SAME ORIGINAL conditional normalizer

The actual selected-link schedule integrates the original incident collar,
at EVERY remaining unit-quaternion assignment. Wholly selected faces pay
half; all crossing collar faces retain their eta cost. The test Haar mass
uses only selected original links, not the full ambient carrier.

For Fi internal faces, Fb remaining collar faces and L selected links the
identity-normalized conditional normalizer is at least
2^(-Fi) * eta(w,K)^Fb * kernelMoment(6*M(w,K))^L, hence at least
2^(-Fi) * eta(w,K)^Fb * (1/(6*M(w,K)+1)^2)^L.
The exact original full-marginal pin retains the detached background.

The floor is independent of the remaining assignment, NOT uniform in
coupling, cutoff or selected volume. No entropy/log identification, signed
response-relative estimate, physical-family calibration or mass gap follows
from this finite lower bound alone.
-/

import YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization
import YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder
import YMGap.Continuum.QuaternionHaarSelectedKernelLocalization
import YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier

namespace YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.RepTheory.RationalQuaternionFourKernelProduct (base)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.RingNormaliser (evalMono)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_smul)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (quaternionBlockIndependent_polyOne quaternionBlockIndependent_polySmul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder (familyProject_pointwise_mono)
open YMGap.Continuum.QuaternionHaarSelectedKernelLocalization
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration (kernelMoment)
open YMGap.Continuum.SU2QuaternionKernelMomentLower (localizationFloor localizationFloor_positive)
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison (collar background fullWeight)
open YMGap.Continuum.BF4ExactSlabBlockNormalizer (slots slots_valid collarHeat normalizer full_marginal_pin)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit (linkValue)
open YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization (eta eta_positive localizationDegree)
open YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization (scalarProduct)
open YMGap.Continuum.BF4ExactSlabKernelProductRecoding (linkPowerProduct)
open YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier
  (chainLinks chainLinks_nodup chainLinks_physical)
open YMGap.Continuum.CayleyPruferInjection (nodup_map_of_injOn)
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff)
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*evalMono rho t.1+z) (weighted_eval rho p)

private theorem eval_congr (rho : Nat → Q') {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    evalRatPoly rho p ≈ evalRatPoly rho q := by
  simpa only [weighted_eval] using h (evalMono rho)

private theorem family_smul (ids : List Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (polySmul c p))
      (polySmul c (familyProject ids p)) :=
  (familyProject_congr ids (cap_mul_left c p).symm).trans
    ((familyProject_mul_of_independent ids (cap c) p
      (fun b _ => quaternionBlockIndependent_polySmul c (quaternionBlockIndependent_polyOne b))).trans
        (cap_mul_left c (familyProject ids p)))

private theorem projected_smul_eval (ids : List Nat) (c : Q') (p : RatPoly) (rho : Nat → Q') :
    evalRatPoly rho (familyProject ids (polySmul c p)) ≈
      c*evalRatPoly rho (familyProject ids p) :=
  Q'.eqv_trans _ _ _ (eval_congr rho (family_smul ids c p)) (evalRatPoly_smul rho c _)

private theorem scalar_map {A B : Type} (f : B → Q') (g : A → B) : ∀ xs,
    scalarProduct f (xs.map g) = scalarProduct (fun a => f (g a)) xs
  | [] => rfl
  | a::xs => congrArg (fun z => f (g a)*z) (scalar_map f g xs)

private theorem scalar_congr {A : Type} {f g : A → Q'} : ∀ xs : List A,
    (∀ a, a ∈ xs → f a ≈ g a) → scalarProduct f xs ≈ scalarProduct g xs
  | [], _ => Q'.eqv_refl _
  | a::xs, h => mc (h a List.mem_cons_self)
      (scalar_congr xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem assigned_value (carrier : List Z4Link) (qs : Nat → UnitNorm)
    (link : Z4Link) (hl : link ∈ carrier) :
    (if link ∈ carrier then qs (carrier.idxOf link) else
      YMGap.RepTheory.RationalQuaternion.unitOne) = qs (carrier.idxOf link) := if_pos hl

/-- Opaque carrier recoding keeps actual original indices, without unfolding
the ambient slab enumeration or substituting a different quaternion carrier. -/
private theorem original_slot_product_pin (extent m : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) (qs : Nat → UnitNorm) :
    linkPowerProduct extent qs m links ≈
      scalarProduct (fun b => qpow (base (qs b)) m) (slots extent links) := by
  have hmap := scalar_map (fun b => qpow (base (qs b)) m)
    (fun link => (boundaryCompleteSlabLinks extent).idxOf link) links
  change _ ≈ scalarProduct (fun b => qpow (base (qs b)) m)
    (links.map (fun link => (boundaryCompleteSlabLinks extent).idxOf link))
  rw [hmap]
  apply scalar_congr
  intro link hm
  have hv : linkValue extent qs link = qs ((boundaryCompleteSlabLinks extent).idxOf link) :=
    assigned_value (boundaryCompleteSlabLinks extent) qs link (hl link hm)
  rw [hv]
  exact Q'.eqv_refl _

private theorem slots_nodup (extent : Nat) (links : List Z4Link) (hn : links.Nodup)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) :
    (slots extent links).Nodup :=
  nodup_map_of_injOn _ links hn
    (fun _ ha _ hb => idxOf_injective_on_members (hl _ ha) (hl _ hb))

/-- Every original collar face contributes exactly one half or eta cost. -/
def collarCost (w : Q') (hw0 : (0 : Q') < w) (K extent : Nat) (links : List Z4Link) : Q' :=
  half^(insideIds extent links (collar extent links)).length *
    (eta w hw0 K)^(boundaryIds extent links (collar extent links)).length

theorem collarCost_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) : (0 : Q') < collarCost w hw0 K extent links :=
  Q'.mul_pos (HKPos.pow_pos (by decide) _) (HKPos.pow_pos (eta_positive hw0 hw1 K) _)

/-- Polynomial test on literal selected original slots, below the entire
identity-normalized incident collar for every original unit assignment. -/
theorem original_conditional_test_le_density {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (links : List Z4Link)
    (hn : links.Nodup) (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (hK : finiteCutoff w ≤ K+1) (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs)
      (polySmul (collarCost w hw0 K extent links)
        (selectedKernel (slots extent links) (6*localizationDegree w hw0 hw1 K))) ≤
      evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent (collar extent links)) := by
  have he := Q'.eqv_trans _ _ _
    (evalRatPoly_smul (environment qs) (collarCost w hw0 K extent links)
      (selectedKernel (slots extent links) (6*localizationDegree w hw0 hw1 K)))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
      (selectedKernel_eval (slots extent links) (6*localizationDegree w hw0 hw1 K) qs)
      (Q'.eqv_symm (original_slot_product_pin extent (6*localizationDegree w hw0 hw1 K) links hl qs))))
  have hr : collarCost w hw0 K extent links *
      linkPowerProduct extent qs (6*localizationDegree w hw0 hw1 K) links ≈
      (half^(insideIds extent links (collar extent links)).length *
        linkPowerProduct extent qs (6*localizationDegree w hw0 hw1 K) links) *
          (eta w hw0 K)^(boundaryIds extent links (collar extent links)).length :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he hr))
    (original_collar_localization hw0 hw1 K extent links hn hK qs)

private theorem normalized_collar_project_eval {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (links : List Z4Link) (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs)
      (familyProject (slots extent links) (normalizedHeatProduct w hw0 K extent (collar extent links))) ≈
      normalizingFactor w hw0 K (collar extent links)*evalRatPoly (environment qs) (normalizer w K extent links) :=
  projected_smul_eval (slots extent links) _ (collarHeat w K extent links) (environment qs)

/-- Exact selected-link Haar moment below the EXISTING original normalizer
at EVERY boundary assignment, not merely after full Haar integration. -/
theorem original_normalizer_moment_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (links : List Z4Link)
    (hn : links.Nodup) (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (hK : finiteCutoff w ≤ K+1) (qs : Nat → UnitNorm) :
    collarCost w hw0 K extent links * (kernelMoment (6*localizationDegree w hw0 hw1 K))^links.length ≤
      normalizingFactor w hw0 K (collar extent links)*evalRatPoly (environment qs) (normalizer w K extent links) := by
  have ho := familyProject_pointwise_mono (slots extent links) _ _
    (original_conditional_test_le_density hw0 hw1 K extent links hn hl hK) qs
  have hp := Q'.eqv_trans _ _ _ (projected_smul_eval (slots extent links)
    (collarCost w hw0 K extent links)
    (selectedKernel (slots extent links) (6*localizationDegree w hw0 hw1 K)) (environment qs))
    (Q'.mul_eqv_congr_left _ _ _ (selectedKernel_project_eval (blocks extent) (slots extent links)
      (6*localizationDegree w hw0 hw1 K) (slots_valid extent links hl) (slots_nodup extent links hn hl) qs))
  simp only [slots, List.length_map] at hp
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp)
    (Q'.le_trans' _ _ _ ho (Q'.le_of_eqv (normalized_collar_project_eval hw0 K extent links qs)))

/-- Computed rational finite floor; every coupling/cutoff/local-volume
dependence remains explicit data. No ambient-carrier exponent is charged. -/
def conditionalFloor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) : Q' :=
  collarCost w hw0 K extent links * (localizationFloor (6*localizationDegree w hw0 hw1 K))^links.length

theorem conditionalFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) : (0 : Q') < conditionalFloor w hw0 hw1 K extent links :=
  Q'.mul_pos (collarCost_positive hw0 hw1 K extent links)
    (HKPos.pow_pos (localizationFloor_positive _) _)

/-- Computed finite floor at every boundary assignment on the SAME
normalizer; no interacting conditional law or analytic premise is supplied. -/
theorem original_normalizer_normalized_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (links : List Z4Link)
    (hn : links.Nodup) (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (hK : finiteCutoff w ≤ K+1) (qs : Nat → UnitNorm) :
    conditionalFloor w hw0 hw1 K extent links ≤
      normalizingFactor w hw0 K (collar extent links)*evalRatPoly (environment qs) (normalizer w K extent links) := by
  have ho := familyProject_pointwise_mono (slots extent links) _ _
    (original_conditional_test_le_density hw0 hw1 K extent links hn hl hK) qs
  have hsel := selectedKernel_project_lower (blocks extent) (slots extent links)
    (6*localizationDegree w hw0 hw1 K) (slots_valid extent links hl) (slots_nodup extent links hn hl) qs
  simp only [slots, List.length_map] at hsel
  have hp := projected_smul_eval (slots extent links) (collarCost w hw0 K extent links)
    (selectedKernel (slots extent links) (6*localizationDegree w hw0 hw1 K)) (environment qs)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hsel (Q'.le_of_lt (collarCost_positive hw0 hw1 K extent links)))
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp)
      (Q'.le_trans' _ _ _ ho (Q'.le_of_eqv (normalized_collar_project_eval hw0 K extent links qs))))

/-- Undo identity normalization: an actual positive lower bound on the
original selected-link conditional normalizer, with all collar factors. -/
theorem original_normalizer_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (links : List Z4Link)
    (hn : links.Nodup) (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (hK : finiteCutoff w ≤ K+1) (qs : Nat → UnitNorm) :
    productCeiling w K (collar extent links)*conditionalFloor w hw0 hw1 K extent links ≤
      evalRatPoly (environment qs) (normalizer w K extent links) := by
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ _
    (original_normalizer_normalized_lower hw0 hw1 K extent links hn hl hK qs)
    (Q'.le_of_lt (productCeiling_positive (Q'.le_of_lt hw0) K (collar extent links)))
  have he : productCeiling w K (collar extent links) *
      (normalizingFactor w hw0 K (collar extent links)*evalRatPoly (environment qs) (normalizer w K extent links)) ≈
      evalRatPoly (environment qs) (normalizer w K extent links) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv _ _))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv he)

theorem original_normalizer_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (links : List Z4Link)
    (hn : links.Nodup) (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (hK : finiteCutoff w ≤ K+1) (qs : Nat → UnitNorm) :
    (0 : Q') < evalRatPoly (environment qs) (normalizer w K extent links) :=
  HeatKernelRGStep.lt_of_lt_of_le
    (Q'.mul_pos (productCeiling_positive (Q'.le_of_lt hw0) K (collar extent links))
      (conditionalFloor_positive hw0 hw1 K extent links))
    (original_normalizer_lower hw0 hw1 K extent links hn hl hK qs)

/-- The bound's normalizer is the actual full-action marginal factor;
the existing detached original background remains EXACTLY in this pin. -/
theorem original_full_marginal_evaluate (w : Q') (K extent : Nat) (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs) (familyProject (slots extent links) (fullWeight w K extent)) ≈
      evalRatPoly (environment qs) (background w K extent links)*
        evalRatPoly (environment qs) (normalizer w K extent links) :=
  Q'.eqv_trans _ _ _ (eval_congr (environment qs) (full_marginal_pin w K extent links hl))
    (evalRatPoly_mul (environment qs) _ _)

/-- Actual chronological spatial-link chain, including its final slice,
inside the SAME original slab. This is NOT a gauge-fixed action replacement. -/
theorem chronological_chain_original_normalizer_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent width start steps : Nat)
    (hw : width ≤ extent) (ht : start+steps ≤ extent) (hK : finiteCutoff w ≤ K+1)
    (qs : Nat → UnitNorm) :
    productCeiling w K (collar extent (chainLinks width start steps))*
      conditionalFloor w hw0 hw1 K extent (chainLinks width start steps) ≤
        evalRatPoly (environment qs) (normalizer w K extent (chainLinks width start steps)) :=
  original_normalizer_lower hw0 hw1 K extent (chainLinks width start steps)
    (chainLinks_nodup width start steps) (fun _ hl => chainLinks_physical hw ht hl) hK qs

end YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower

#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.collarCost
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.collarCost_positive
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.original_conditional_test_le_density
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.original_normalizer_moment_lower
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.conditionalFloor
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.conditionalFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.original_normalizer_normalized_lower
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.original_normalizer_lower
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.original_normalizer_positive
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.original_full_marginal_evaluate
#print axioms YMGap.Continuum.BF4ExactSlabConditionalPolynomialPartitionLower.chronological_chain_original_normalizer_lower
