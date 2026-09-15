/-
# The included original action has the original normalized expectation

The coordinate inclusion maps every source face and observable together.
Its physical target mask keeps exactly those faces. The full target action
splits into this heat product and its actual exterior product; no exterior
factor is discarded in a claim about the full target law.

Exact finite Haar transport passes to the existing explicit-modulus cutoff
limits. Cancellation of the SAME partitions then identifies the masked
normalized expectation with the original source expectation. This works
across slab parity, in particular from odd to adjacent even. Comparing with
the full even action still requires the checked boundary-response estimate.
-/

import YMGap.Continuum.BF4ExactSlabCoordinateInclusion
import YMGap.Continuum.BF4ExactSlabFaceSetExpectation
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabCoordinateAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabCoordinateInclusion
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

def includedIds (source target : Nat) : List Nat :=
  (slabPhysicalFaceEdges source).map (faceId source target)

def keep (source target id : Nat) : Bool := decide (id ∈ includedIds source target)

def keptIds (source target : Nat) : List Nat := (slabPhysicalFaceEdges target).filter (keep source target)

theorem included_physical {source target id : Nat} (h : source ≤ target)
    (hi : id ∈ includedIds source target) : id ∈ slabPhysicalFaceEdges target := by
  obtain ⟨i, hs, rfl⟩ := List.mem_map.mp hi
  exact faceId_physical h hs

theorem kept_physical (source target id : Nat) (hi : id ∈ keptIds source target) :
    id ∈ slabPhysicalFaceEdges target := (List.mem_filter.mp hi).1

theorem kept_perm {source target : Nat} (h : source ≤ target) :
    (keptIds source target).Perm (includedIds source target) := by
  apply perm_of_nodup_mem_iff _ _ (List.filter_sublist.nodup (CayleyParentInj.range_nodup _))
    (nodup_map_of_injOn _ _ (CayleyParentInj.range_nodup _) (fun _ hi _ hj => faceId_injective h hi hj))
  intro id
  constructor
  · intro hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  · intro hi
    exact List.mem_filter.mpr ⟨included_physical h hi, decide_eq_true hi⟩

/-- The complement remains an actual heat factor, including shared links. -/
theorem full_action_split (source target : Nat) (w : Q') (K : Nat) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K target) (slabPhysicalFaceEdges target))
      (polyMul (polynomialProduct (faceHeatPolynomial w K target) (keptIds source target))
        (polynomialProduct (faceHeatPolynomial w K target)
          ((slabPhysicalFaceEdges target).filter (fun id => !(keep source target id))))) :=
  (polynomialProduct_perm _ (List.filter_append_perm (keep source target) _).symm).trans
    (polynomialProduct_append _ _ _)

private theorem imageSum {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (finitePolySum f xs)) (finitePolySum g xs)
  | [], _ => .nil
  | a :: xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyAdd (f a) (finitePolySum f xs))) _
      rw [E.polynomial_add]
      exact (h a List.mem_cons_self).append (imageSum E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem imageProduct {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (polynomialProduct f xs)) (polynomialProduct g xs)
  | [], _ => E.polynomial_one_prefix
  | a :: xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyMul (f a) (polynomialProduct f xs))) _
      rw [E.polynomial_mul]
      exact (h a List.mem_cons_self).mul (imageProduct E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem heatFactor_pin {source target : Nat} (h : source ≤ target) (w : Q') (K : Nat) {id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges source) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks target).length
      ((embedding h).polynomial (faceHeatPolynomial w K source id))
      (faceHeatPolynomial w K target (faceId source target id)) := by
  apply imageSum (embedding h) (localFaceTerm w K source id)
    (localFaceTerm w K target (faceId source target id)) (List.range (K+1))
  intro spin _
  unfold localFaceTerm
  rw [BlockEmbedding.polynomial_smul]
  rw [faceId_pin h hi]
  exact (character_pin h (slabPlaquetteAt_mem hi) spin).smul _

theorem heatProduct_pin {source target : Nat} (h : source ≤ target) (w : Q') (K : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks target).length
      ((embedding h).polynomial (polynomialProduct (faceHeatPolynomial w K source) (slabPhysicalFaceEdges source)))
      (polynomialProduct (faceHeatPolynomial w K target) (includedIds source target)) := by
  simpa only [includedIds, polynomialProduct, List.foldr_map] using
    (imageProduct (embedding h) _ _ _ (fun _ hi => heatFactor_pin h w K hi))

theorem numerator_pin {source target : Nat} (h : source ≤ target) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks source).length p) :
    numerator w (boundaryCompleteSlabLinks target).length target (keptIds source target)
      ((embedding h).polynomial p) K ≈
      numerator w (boundaryCompleteSlabLinks source).length source (slabPhysicalFaceEdges source) p K := by
  have himage : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks target).length
      ((embedding h).polynomial (polyMul p
        (polynomialProduct (faceHeatPolynomial w K source) (slabPhysicalFaceEdges source))))
      (polyMul ((embedding h).polynomial p)
        (polynomialProduct (faceHeatPolynomial w K target) (includedIds source target))) := by
    rw [BlockEmbedding.polynomial_mul]
    exact (QuaternionPrefixPolynomialEqv.refl _ _).mul (heatProduct_pin h w K)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
    ((polynomialProduct_perm _ (kept_perm h)).mul_left _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv _ himage
      ((embedding h).polynomial_supported _)
      (supported_polyMul ((embedding h).polynomial_supported p) (heatProduct_supported w K _ _))))
      ((embedding h).haar _ (supported_polyMul hp (heatProduct_supported w K _ _))))

private theorem numerator_prefix (w : Q') (K extent : Nat) (ids : List Nat) {p q : RatPoly}
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q) :
    numerator w (boundaryCompleteSlabLinks extent).length extent ids p K ≈
      numerator w (boundaryCompleteSlabLinks extent).length extent ids q K :=
  quaternionHaar_prefixPolynomialEqv _ (he.mul (.refl _ _))
    (supported_polyMul hp (heatProduct_supported w K _ _))
    (supported_polyMul hq (heatProduct_supported w K _ _))

theorem partition_pin {source target : Nat} (h : source ≤ target) (w : Q') (K : Nat) :
    heatProductHaar w (boundaryCompleteSlabLinks target).length target (keptIds source target) K ≈
      heatProductHaar w (boundaryCompleteSlabLinks source).length source (slabPhysicalFaceEdges source) K := by
  have hone := numerator_prefix w K target (keptIds source target) (embedding h).polynomial_one_prefix
    ((embedding h).polynomial_supported polyOne) (supported_one _)
  have ht := haar_of_coeff_eqv (boundaryCompleteSlabLinks target).length (RatPolyCoeffEqv.one_mul
    (polynomialProduct (faceHeatPolynomial w K target) (keptIds source target)))
  have hs := haar_of_coeff_eqv (boundaryCompleteSlabLinks source).length (RatPolyCoeffEqv.one_mul
    (polynomialProduct (faceHeatPolynomial w K source) (slabPhysicalFaceEdges source)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm ht)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hone) (Q'.eqv_trans _ _ _ (numerator_pin h w K polyOne (supported_one _)) hs))

variable {source target : Nat} (h : source ≤ target)
  (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

theorem numeratorLimit_pin (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks source).length p) :
    Equiv (numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks target).length target
      (keptIds source target) ((embedding h).polynomial p))
      (numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks source).length source (slabPhysicalFaceEdges source) p) :=
  Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 _ _ _ _) (numerator_converges w hw0 hw1 _ _ _ p)
    (fun epsilon he => ⟨0, fun K _ => eqv_close (numerator_pin h w K p hp) epsilon he⟩)

include h in
theorem partitionLimit_pin :
    Equiv (heatProductHaarLimit w hw0 hw1 (boundaryCompleteSlabLinks target).length target (keptIds source target))
      (heatProductHaarLimit w hw0 hw1 (boundaryCompleteSlabLinks source).length source (slabPhysicalFaceEdges source)) :=
  Equiv_of_ofQ'_limit_close (heatProductHaar_converges w hw0 hw1 _ _ _) (heatProductHaar_converges w hw0 hw1 _ _ _)
    (fun epsilon he => ⟨0, fun K _ => eqv_close (partition_pin h w K) epsilon he⟩)

/-- The kept target law is the source law, with its original normalization. -/
theorem expectation_pin (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks source).length p) :
    Equiv (expectation w hw0 hw1 hsmall hd target (keptIds source target) (kept_physical source target)
      ((embedding h).polynomial p))
      (expectation w hw0 hw1 hsmall hd source (slabPhysicalFaceEdges source) (fun _ hi => hi) p) := by
  let e := expectation w hw0 hw1 hsmall hd target (keptIds source target) (kept_physical source target)
    ((embedding h).polynomial p)
  have hrecovery := (Pivot2.mul_congr_right (A := e) (partitionLimit_pin h w hw0 hw1).symm).trans
    ((expectation_recover w hw0 hw1 hsmall hd target (keptIds source target) (kept_physical source target) _).trans
      (numeratorLimit_pin h w hw0 hw1 p hp))
  exact (CRealAlg.cmul_cone e).symm.trans
    ((Pivot2.mul_congr_right (partition_cancellation w hw0 hw1 hsmall hd source
      (slabPhysicalFaceEdges source) (fun _ hi => hi)).symm).trans
      ((CRealAlg.cmul_assoc _ _ _).symm.trans (Pivot2.mul_congr_left hrecovery)))

/-- A supported literal target insertion can replace the mapped polynomial. -/
theorem expectation_pin_of_prefix (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks source).length p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks target).length q)
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks target).length ((embedding h).polynomial p) q) :
    Equiv (expectation w hw0 hw1 hsmall hd target (keptIds source target) (kept_physical source target) q)
      (expectation w hw0 hw1 hsmall hd source (slabPhysicalFaceEdges source) (fun _ hi => hi) p) := by
  have hn := Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 _ target (keptIds source target) q)
    (numerator_converges w hw0 hw1 _ target (keptIds source target) ((embedding h).polynomial p))
    (fun epsilon ht => ⟨0, fun K _ => eqv_close (Q'.eqv_symm
      (numerator_prefix w K target (keptIds source target) he ((embedding h).polynomial_supported p) hq)) epsilon ht⟩)
  exact (Pivot2.mul_congr_left hn).trans (expectation_pin h w hw0 hw1 hsmall hd p hp)

end YMGap.Continuum.BF4ExactSlabCoordinateAction

#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.includedIds
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.keep
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.keptIds
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.included_physical
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.kept_physical
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.kept_perm
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.full_action_split
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.heatFactor_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.heatProduct_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.numerator_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.partition_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.numeratorLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.partitionLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.expectation_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateAction.expectation_pin_of_prefix
