/-
# Localized ORIGINAL collar, with EVERY crossing factor retained

The existing incident collar is split by the actual four-edge membership
test: wholly selected faces receive the produced polynomial localization;
all other collar faces receive their actual eta floor. Detached faces stay
in the existing original background, not in either localization cost.

This pointwise producer feeds the original familyProject normalizer. No
independence of interacting faces, conditional integration, entropy/log
identification, response-relative payment, scaling or mass gap is assumed.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower
import YMGap.Continuum.BF4ExactSlabBlockNormalizer

namespace YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.RepTheory.RationalQuaternionFourKernelProduct (base base_bounds)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion (collarIds)
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison (collar collar_physical)
open YMGap.Continuum.BF4ExactSlabBlockNormalizer (slots normalizer)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (faceLinks)
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit (linkValue)
open YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization
open YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization
open YMGap.Continuum.BF4ExactSlabKernelProductRecoding
open YMGap.Continuum.BF4ExactSlabKernelIncidence (faceLinks_count_le_six)
open YMGap.Continuum.FiniteProductMultiplicityBound (scalarProduct_multiplicity_bound)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds (normalizedHeatProduct)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.HeatKernelRGStep (qpow_qpow)

local infix:50 " ≈ " => Q'.eqv

/-- EVERY boundary slot, not just a face base or one selected edge. -/
def insideFace (extent : Nat) (links : List Z4Link) (id : Nat) : Bool :=
  (edgesOf (slabPlaquetteAt extent id)).all (fun link => decide (link ∈ links))

def insideIds (extent : Nat) (links : List Z4Link) (ids : List Nat) : List Nat :=
  ids.filter (insideFace extent links)

def boundaryIds (extent : Nat) (links : List Z4Link) (ids : List Nat) : List Nat :=
  ids.filter (fun id => !(insideFace extent links id))

theorem inside_slots (extent : Nat) (links : List Z4Link) (ids : List Nat) :
    ∀ link, link ∈ faceLinks extent (insideIds extent links ids) → link ∈ links := by
  intro link hl
  obtain ⟨id,hid,hedge⟩ := List.mem_flatMap.mp hl
  exact of_decide_eq_true (List.all_eq_true.mp (List.mem_filter.mp hid).2 link hedge)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem swap_front (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
      (Q'.mul_assoc_eqv _ _ _))

private theorem scalar_congr {A : Type} {f g : A → Q'} : ∀ xs : List A,
    (∀ a, a ∈ xs → f a ≈ g a) → scalarProduct f xs ≈ scalarProduct g xs
  | [], _ => Q'.eqv_refl 1
  | a::xs,h => mc (h a List.mem_cons_self)
      (scalar_congr xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem power_bounds (x : Q') (hx : (0 : Q') ≤ x ∧ x ≤ 1) : ∀ m,
    (0 : Q') ≤ qpow x m ∧ qpow x m ≤ 1
  | 0 => ⟨by change (0 : Q') ≤ 1; decide, Q'.le_refl' _⟩
  | m+1 => ⟨qpow_nonneg x hx.1 _, Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg (power_bounds x hx m).2 hx.2 (by decide) hx.1)
      (Q'.le_of_eqv (by decide : (1 : Q')*1 ≈ 1))⟩

/-- Half and eta costs separated without dropping or duplicating a face. -/
def mixedProduct (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) (qs : Nat → UnitNorm) (ids : List Nat) : Q' :=
  scalarProduct (fun id => if insideFace extent links id then
    half*qpow (faceKernelProduct extent id qs) (localizationDegree w hw0 hw1 K)
    else eta w hw0 K) ids

private theorem mixed_recoding {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) (qs : Nat → UnitNorm) : ∀ ids,
    mixedProduct w hw0 hw1 K extent links qs ids ≈
      localizedProduct w hw0 hw1 K extent qs (insideIds extent links ids)*
        (eta w hw0 K)^(boundaryIds extent links ids).length
  | [] => by change (1 : Q') ≈ 1*1; decide
  | id::ids => by
      cases hi : insideFace extent links id with
      | true =>
          simp only [mixedProduct,scalarProduct,hi,if_true,insideIds,boundaryIds,
            List.filter_cons,Bool.not_true] at *
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (mixed_recoding hw0 hw1 K extent links qs ids))
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      | false =>
          simp only [mixedProduct,scalarProduct,hi,if_false,insideIds,boundaryIds,
            List.filter_cons,Bool.false_eq_true,Bool.not_false,if_true,if_false,List.length_cons] at *
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (mixed_recoding hw0 hw1 K extent links qs ids))
            (swap_front _ _ _)

private theorem mixed_factor_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) (qs : Nat → UnitNorm)
    (hK : finiteCutoff w ≤ K+1) (id : Nat) :
    (0 : Q') ≤ (if insideFace extent links id then
      half*qpow (faceKernelProduct extent id qs) (localizationDegree w hw0 hw1 K)
      else eta w hw0 K) ∧
    (if insideFace extent links id then
      half*qpow (faceKernelProduct extent id qs) (localizationDegree w hw0 hw1 K)
      else eta w hw0 K) ≤ normalizedFace w hw0 K extent id qs := by
  cases hi : insideFace extent links id with
  | true => exact ⟨Q'.mul_nonneg _ _ (by decide) (qpow_nonneg _ (faceKernelProduct_bounds _ _ _).1 _),
      original_face_localization hw0 hw1 K extent id qs hK⟩
  | false => exact ⟨Q'.le_of_lt (eta_positive hw0 hw1 K),
      normalizedFace_floor hw0 hw1 K extent id qs hK⟩

private theorem mixed_le_original {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) (qs : Nat → UnitNorm)
    (hK : finiteCutoff w ≤ K+1) : ∀ ids,
    mixedProduct w hw0 hw1 K extent links qs ids ≤
      scalarProduct (fun id => normalizedFace w hw0 K extent id qs) ids
  | [] => Q'.le_refl' _
  | id::ids => HKConv.mul_le_mul'
      (mixed_factor_bounds hw0 hw1 K extent links qs hK id).1
      (scalarProduct_nonnegative _ (fun i => Q'.le_trans' _ _ _
        (Q'.le_of_lt (eta_positive hw0 hw1 K)) (normalizedFace_floor hw0 hw1 K extent i qs hK)) ids)
      (mixed_factor_bounds hw0 hw1 K extent links qs hK id).2
      (mixed_le_original hw0 hw1 K extent links qs hK ids)

/-- The selected carrier pays ONLY internal faces and the remaining collar
boundary faces. All four selected slots are counted, with the cap six. -/
theorem selected_product_le_internal (extent M : Nat) (links : List Z4Link) (ids : List Nat)
    (hn : links.Nodup) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hni : ids.Nodup) (qs : Nat → UnitNorm) :
    linkPowerProduct extent qs (6*M) links ≤
      linkPowerProduct extent qs M (faceLinks extent (insideIds extent links ids)) := by
  have hm := scalarProduct_multiplicity_bound
    (fun link => qpow (base (linkValue extent qs link)) M) 6 links
    (faceLinks extent (insideIds extent links ids)) hn (inside_slots extent links ids)
    (fun link _ => faceLinks_count_le_six extent _
      (fun id hi => hids id (List.mem_filter.mp hi).1) (List.filter_sublist.nodup hni) link)
    (fun link _ => power_bounds _ (base_bounds _) M)
  have he : scalarProduct (fun link => qpow (qpow (base (linkValue extent qs link)) M) 6) links ≈
      linkPowerProduct extent qs (6*M) links := by
    apply scalar_congr
    intro link _
    simpa only [Nat.mul_comm] using qpow_qpow (base (linkValue extent qs link)) M 6
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hm

/-- Pointwise original collar localization on EVERY boundary assignment.
No detached original factor is charged an eta cost or discarded. -/
theorem original_collar_localization {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (links : List Z4Link) (hn : links.Nodup)
    (hK : finiteCutoff w ≤ K+1) (qs : Nat → UnitNorm) :
    (half^(insideIds extent links (collar extent links)).length *
      linkPowerProduct extent qs (6*localizationDegree w hw0 hw1 K) links) *
        (eta w hw0 K)^(boundaryIds extent links (collar extent links)).length ≤
      evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent (collar extent links)) := by
  have hc : (collar extent links).Nodup :=
    List.filter_sublist.nodup (CayleyParentInj.range_nodup _)
  have hm := selected_product_le_internal extent (localizationDegree w hw0 hw1 K)
    links (collar extent links) hn
    (fun _ hi => collar_physical hi) hc qs
  have hl : half^(insideIds extent links (collar extent links)).length *
      linkPowerProduct extent qs (6*localizationDegree w hw0 hw1 K) links ≤
      localizedProduct w hw0 hw1 K extent qs (insideIds extent links (collar extent links)) :=
    Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hm
      (Q'.pow_nonneg half (by decide) _))
    (Q'.ge_of_eqv (localizedProduct_recoding hw0 hw1 K extent qs _))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hl
      (Q'.pow_nonneg _ (Q'.le_of_lt (eta_positive hw0 hw1 K)) _))
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mixed_recoding hw0 hw1 K extent links qs _))
      (Q'.le_trans' _ _ _ (mixed_le_original hw0 hw1 K extent links qs hK _)
        (Q'.le_of_eqv (normalized_product_pin hw0 K extent _ qs))))

end YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization

#print axioms YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization.insideFace
#print axioms YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization.insideIds
#print axioms YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization.boundaryIds
#print axioms YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization.inside_slots
#print axioms YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization.mixedProduct
#print axioms YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization.selected_product_le_internal
#print axioms YMGap.Continuum.BF4ExactSlabCollarPolynomialLocalization.original_collar_localization
