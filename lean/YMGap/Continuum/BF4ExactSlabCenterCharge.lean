/-
# Original all-spin shared-link center-charge filter

Compute the charge from the actual oriented face incidences and actual
original slab link indices. Quaternion word order is unchanged. The
ordinary all-spin character contributes spin times incidence count modulo
two, and ALL selected faces contribute at a shared link. An odd charge
annihilates the EXISTING exactCorrectedSlabHaarCoefficient, at every extent.

The filter also permits charged insertions, rather than requiring them to
be independent. Passing the filter asserts neither a nonzero coefficient
nor connected support: two disconnected endpoint caps pass it. Combining
this filter with connected cancellation, classifying minimal surviving
terms, and bounding the signed response remainder remain open.
-/

import YMGap.Continuum.SU2QuaternionBlockCenterCharge
import YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

namespace YMGap.Continuum.BF4ExactSlabCenterCharge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionBlockCenterCharge
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "N" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Count the actual coordinate block, retaining repeated incidences. -/
def entryCharge (extent block : Nat) (entry : OrientedBF4Link) : Nat :=
  if block = (boundaryCompleteSlabLinks extent).idxOf entry.link then 1 else 0

def wordCharge (extent block : Nat) : List OrientedBF4Link → Nat
  | [] => 0
  | e::es => entryCharge extent block e + wordCharge extent block es

def faceDegree (extent block : Nat) (face : Z4Plaq) : Nat :=
  wordCharge extent block (orientedPlaquetteBoundary face)

theorem entry_degree (extent block : Nat) (entry : OrientedBF4Link)
    (he : entry.link ∈ boundaryCompleteSlabLinks extent) :
    HasPolyQuaternionBlockDegree block (entryCharge extent block entry)
      (orientedCorrectedSlabLinkPolynomial extent entry) := by
  have h := hasPolyQuaternionBlockDegree_coordinateVariable
    ((boundaryCompleteSlabLinks extent).idxOf entry.link) block
  unfold orientedCorrectedSlabLinkPolynomial
  rw [correctedSlabLinkPolynomial_of_mem he]
  cases hr : entry.reverse with
  | false => exact h
  | true => exact h.conj

theorem word_degree (extent block : Nat) : ∀ (es : List OrientedBF4Link) (q : PolyQuaternion) (d : Nat),
    HasPolyQuaternionBlockDegree block d q →
    (∀ e, e ∈ es → e.link ∈ boundaryCompleteSlabLinks extent) →
    HasPolyQuaternionBlockDegree block (d + wordCharge extent block es)
      (es.foldl (fun p e => PolyQuaternion.mul p (orientedCorrectedSlabLinkPolynomial extent e)) q)
  | [], _, _, h, _ => h
  | e::es, _, _, h, hp =>
    HasPolyQuaternionBlockDegree.relabel (Nat.add_assoc _ _ _)
      (word_degree extent block es _ _ (h.mul (entry_degree extent block e (hp e List.mem_cons_self)))
        (fun f hf => hp f (List.mem_cons_of_mem e hf)))

theorem face_degree (extent block : Nat) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HasQuaternionBlockDegree block (faceDegree extent block face)
      (correctedSlabPlaquettePolynomial extent face).scalar := by
  have hunit : HasPolyQuaternionBlockDegree block 0 PolyQuaternion.one :=
    ⟨hasQuaternionBlockDegree_one block, hasQuaternionBlockDegree_zero block 0,
      hasQuaternionBlockDegree_zero block 0, hasQuaternionBlockDegree_zero block 0⟩
  have h := word_degree extent block (orientedPlaquetteBoundary face) PolyQuaternion.one 0 hunit
    (fun _ he => orientedPlaquetteBoundary_link_mem_slab hf he)
  exact HasQuaternionBlockDegree.relabel (Nat.zero_add _) h.scalar

theorem face_character_charge (extent block : Nat) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    HasCharge block (spin * faceDegree extent block face)
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) :=
  (HasCharge.of_degree (face_degree extent block face hf)).character spin

def selectedCharge (extent block : Nat) (labels : EdgeLabelling) : List Z4Plaq → Nat
  | [] => 0
  | f::fs => labels ((boundaryCompleteSlabPlaquettes extent).idxOf f) * faceDegree extent block f +
      selectedCharge extent block labels fs

theorem faceList_charge (extent block : Nat) (labels : EdgeLabelling) : ∀ faces : List Z4Plaq,
    (∀ f, f ∈ faces → f ∈ boundaryCompleteSlabPlaquettes extent) →
    HasCharge block (selectedCharge extent block labels faces)
      (faces.foldr (fun f p => polyMul (correctedSlabPlaquetteSpinFactor extent labels f) p) polyOne)
  | [], _ => HasCharge.one block
  | f::fs, hp =>
    (face_character_charge extent block f (hp f List.mem_cons_self) _).mul
      (faceList_charge extent block labels fs (fun g hg => hp g (List.mem_cons_of_mem f hg)))

/-- Whole-action label charge; no independent-face replacement. -/
def totalCharge (extent block : Nat) (labels : EdgeLabelling) : Nat :=
  selectedCharge extent block labels (boundaryCompleteSlabPlaquettes extent)

theorem integrand_charge (extent block : Nat) (labels : EdgeLabelling) :
    HasCharge block (totalCharge extent block labels) (exactCorrectedSlabSpinNetworkIntegrand extent labels) :=
  faceList_charge extent block labels _ (fun _ h => h)

theorem inserted_coefficient_zero (extent block charge : Nat) (labels : EdgeLabelling) (p : RatPoly)
    (hb : block < N extent) (hp : HasCharge block charge p)
    (ho : (charge + totalCharge extent block labels) % 2 = 1) :
    quaternionHaar (N extent) (polyMul p (exactCorrectedSlabSpinNetworkIntegrand extent labels)) ≈ 0 :=
  haar_insert_zero hb hp (integrand_charge extent block labels) ho

/-- Rejection theorem for the pre-existing signed physical Haar coefficient. -/
theorem coefficient_zero (extent block : Nat) (labels : EdgeLabelling) (hb : block < N extent)
    (ho : totalCharge extent block labels % 2 = 1) : exactCorrectedSlabHaarCoefficient extent labels ≈ 0 :=
  haar_zero hb (integrand_charge extent block labels) ho

/-- A finite incidence-only test: never expand the quaternion polynomial. -/
def chargeCheck (extent : Nat) (labels : EdgeLabelling) : Bool :=
  (List.range (N extent)).all (fun block => decide (totalCharge extent block labels % 2 = 0))

private theorem all_false_witness (f : Nat → Bool) : ∀ xs : List Nat,
    xs.all f = false → ∃ b, b ∈ xs ∧ f b = false
  | [], h => by cases h
  | b::bs, h => by
    cases hb : f b with
    | false => exact ⟨b,List.mem_cons_self,hb⟩
    | true =>
      have ht : bs.all f = false := by simpa only [List.all_cons, hb, Bool.true_and] using h
      obtain ⟨c,hc,hf⟩ := all_false_witness f bs ht
      exact ⟨c,List.mem_cons_of_mem b hc,hf⟩

theorem rejected_zero (extent : Nat) (labels : EdgeLabelling) (h : chargeCheck extent labels = false) :
    exactCorrectedSlabHaarCoefficient extent labels ≈ 0 := by
  unfold chargeCheck at h
  obtain ⟨block,hb,ho⟩ := all_false_witness _ _ h
  have hn := of_decide_eq_false ho
  exact coefficient_zero extent block labels (List.mem_range.mp hb) (by omega)

/-- Observable charge participates in the incidence test, on the same links. -/
def insertionCheck (extent : Nat) (labels : EdgeLabelling) (charges : Nat → Nat) : Bool :=
  (List.range (N extent)).all (fun block => decide ((charges block + totalCharge extent block labels) % 2 = 0))

theorem inserted_rejected_zero (extent : Nat) (labels : EdgeLabelling) (charges : Nat → Nat) (p : RatPoly)
    (hp : ∀ block, HasCharge block (charges block) p) (h : insertionCheck extent labels charges = false) :
    quaternionHaar (N extent) (polyMul p (exactCorrectedSlabSpinNetworkIntegrand extent labels)) ≈ 0 := by
  unfold insertionCheck at h
  obtain ⟨block,hb,ho⟩ := all_false_witness _ _ h
  have hn := of_decide_eq_false ho
  exact inserted_coefficient_zero extent block (charges block) labels p (List.mem_range.mp hb) (hp block) (by omega)

/-- Passing the test does NOT assert a nonzero or positive coefficient. -/
theorem coefficient_filter (extent : Nat) (labels : EdgeLabelling) :
    exactCorrectedSlabHaarCoefficient extent labels ≈
      (if chargeCheck extent labels then exactCorrectedSlabHaarCoefficient extent labels else 0) := by
  cases h : chargeCheck extent labels with
  | false => exact rejected_zero extent labels h
  | true => exact Q'.eqv_refl _

theorem dual_term_rejected (w : Q') (K extent : Nat) (labels : EdgeLabelling)
    (h : chargeCheck extent labels = false) : exactCorrectedSlabDualTerm w K extent labels ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (rejected_zero extent labels h)) (Q'.mul_zero_eqv _)

/-- Delete rejected labels from any original finite heat sum BEFORE estimates. -/
theorem dual_sum_filter (w : Q') (K extent : Nat) : ∀ labels : List EdgeLabelling,
    listQSum (exactCorrectedSlabDualTerm w K extent) labels ≈
      listQSum (exactCorrectedSlabDualTerm w K extent) (labels.filter (chargeCheck extent))
  | [] => Q'.eqv_refl _
  | l::ls => by
    cases h : chargeCheck extent l with
    | false =>
      simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (dual_term_rejected w K extent l h) (dual_sum_filter w K extent ls))
        (Q'.eqv_of_eq (Q'.zero_add' _))
    | true =>
      simp only [List.filter_cons, h, ↓reduceIte]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (dual_sum_filter w K extent ls)

end YMGap.Continuum.BF4ExactSlabCenterCharge

#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.entry_degree
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.word_degree
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.face_degree
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.face_character_charge
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.faceList_charge
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.integrand_charge
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.inserted_coefficient_zero
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.coefficient_zero
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.chargeCheck
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.rejected_zero
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.insertionCheck
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.inserted_rejected_zero
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.coefficient_filter
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.dual_term_rejected
#print axioms YMGap.Continuum.BF4ExactSlabCenterCharge.dual_sum_filter
