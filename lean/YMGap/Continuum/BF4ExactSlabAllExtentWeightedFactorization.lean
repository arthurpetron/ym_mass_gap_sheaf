/-
# Original signed heat-weighted factorization at every slab extent

The existing exactCorrectedSlabDualTerm is retained, including its complete
signed Haar-network coefficient and every original face heat weight. Literal
face-index lookup and the lower/fixed/upper partition turn it into the Haar
integral of three polynomial factors at every odd extent. No new law, rank
product, positivity premise or numerical enumeration replaces the source.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity

namespace YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem slabFaceIds_map (extent : Nat) :
    (slabPhysicalFaceEdges extent).map (slabPlaquetteAt extent) = boundaryCompleteSlabPlaquettes extent := by
  apply List.ext_getElem
  · simp [slabPhysicalFaceEdges]
  · intro i hi hj
    simp only [List.getElem_map, slabPhysicalFaceEdges, List.getElem_range]
    exact (List.getElem_eq_getD (h := hj) fallbackPlaquette).symm

theorem idxOf_slabPlaquetteAt {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) :
    (boundaryCompleteSlabPlaquettes extent).idxOf (slabPlaquetteAt extent id) = id := by
  have hm := slabPlaquetteAt_mem hi
  have hb := List.idxOf_lt_length_of_mem hm
  apply slabPlaquetteAt_injective_on_physical (List.mem_range.mpr hb) hi
  exact (List.getElem_eq_getD (h := hb) fallbackPlaquette).symm.trans
    (LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hb)))

def polynomialProduct {A : Type} (factor : A → RatPoly) (ids : List A) : RatPoly :=
  ids.foldr (fun id p => polyMul (factor id) p) polyOne

theorem polynomialProduct_congr {A : Type} (f g : A → RatPoly) : ∀ ids : List A,
    (∀ id, id ∈ ids → f id = g id) → polynomialProduct f ids = polynomialProduct g ids
  | [], _ => rfl
  | id :: ids, h => by
      change polyMul (f id) (polynomialProduct f ids) = polyMul (g id) (polynomialProduct g ids)
      rw [h id List.mem_cons_self, polynomialProduct_congr f g ids (fun j hj => h j (List.mem_cons_of_mem id hj))]

theorem polynomialProduct_append {A : Type} (f : A → RatPoly) : ∀ left right : List A,
    RatPolyCoeffEqv (polynomialProduct f (left ++ right))
      (polyMul (polynomialProduct f left) (polynomialProduct f right))
  | [], _ => (RatPolyCoeffEqv.one_mul _).symm
  | _ :: ids, right =>
      ((polynomialProduct_append f ids right).mul_left _).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm

theorem polynomialProduct_perm {A : Type} (f : A → RatPoly) {left right : List A}
    (h : left.Perm right) : RatPolyCoeffEqv (polynomialProduct f left) (polynomialProduct f right) := by
  induction h with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons id _ ih => exact ih.mul_left (f id)
  | swap a b ids =>
      exact (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
        (((RatPolyCoeffEqv.mul_comm _ _).mul_right _).trans (RatPolyCoeffEqv.mul_assoc _ _ _))
  | trans _ _ ih ih' => exact ih.trans ih'

private theorem weighted_product (weight : Nat → Q') (factor : Nat → RatPoly) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polynomialProduct (fun id => polySmul (weight id) (factor id)) ids)
      (polySmul (eliminateLinks weight ids) (polynomialProduct factor ids))
  | [] => (RatPolyCoeffEqv.one_smul _).symm
  | _ :: ids =>
      ((weighted_product weight factor ids).mul_left _).trans
        ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
          (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul _).trans (RatPolyCoeffEqv.smul_assoc _ _ _)))

theorem central_product_factorization (half : Nat) (f : Nat → RatPoly) :
    RatPolyCoeffEqv (polynomialProduct f (slabPhysicalFaceEdges (centralExtent half)))
      (polyMul (polynomialProduct f (centralLowerFaceIds half))
        (polyMul (polynomialProduct f (centralFixedFaceIds half))
          (polynomialProduct f (centralUpperFaceIds half)))) :=
  (polynomialProduct_perm f (by
    have h := centralSlabFaceIdParts_perm half
    -- Reassociate explicitly; at symbolic extent these lists cannot be computed.
    rw [List.append_assoc] at h
    exact h.symm)).trans
      ((polynomialProduct_append f (centralLowerFaceIds half) (centralFixedFaceIds half ++ centralUpperFaceIds half)).trans
        ((polynomialProduct_append f (centralFixedFaceIds half) (centralUpperFaceIds half)).mul_left _))

def weightedFacePolynomial (w : Q') (K extent : Nat) (state : EdgeLabelling) (id : Nat) : RatPoly :=
  polySmul (coeffAt (heatKernelPacket K w) (state id))
    (characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar (state id))

def lowerPolynomial (w : Q') (K half : Nat) (state : EdgeLabelling) : RatPoly :=
  polynomialProduct (weightedFacePolynomial w K (centralExtent half) state) (centralLowerFaceIds half)

def interfaceLabelPolynomial (w : Q') (K half : Nat) (boundary : EdgeLabelling) : RatPoly :=
  polynomialProduct (weightedFacePolynomial w K (centralExtent half) boundary) (centralFixedFaceIds half)

def upperPolynomial (w : Q') (K half : Nat) (state : EdgeLabelling) : RatPoly :=
  polynomialProduct (weightedFacePolynomial w K (centralExtent half)
    (fun id => state (slabFaceReflectId (centralExtent half) id))) (centralUpperFaceIds half)

/-- Original full face weight times the ORIGINAL signed network polynomial. -/
def weightedIntegrand (w : Q') (K extent : Nat) (state : EdgeLabelling) : RatPoly :=
  polySmul (slabParametricKPhysicalFaceFactor w K extent state)
    (exactCorrectedSlabSpinNetworkIntegrand extent state)

theorem weighted_integrand_eq_product (w : Q') (K extent : Nat) (state : EdgeLabelling) :
    RatPolyCoeffEqv (weightedIntegrand w K extent state)
      (polynomialProduct (weightedFacePolynomial w K extent state) (slabPhysicalFaceEdges extent)) := by
  let spin : Nat → RatPoly := fun id =>
    characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar (state id)
  have hspin : polynomialProduct spin (slabPhysicalFaceEdges extent) = exactCorrectedSlabSpinNetworkIntegrand extent state := by
    rw [polynomialProduct_congr spin (fun id => correctedSlabPlaquetteSpinFactor extent state (slabPlaquetteAt extent id))
      (slabPhysicalFaceEdges extent) (fun id hi => by
        unfold correctedSlabPlaquetteSpinFactor
        dsimp only [spin]
        rw [idxOf_slabPlaquetteAt hi])]
    unfold polynomialProduct exactCorrectedSlabSpinNetworkIntegrand
    rw [← slabFaceIds_map extent, List.foldr_map]
  have h := weighted_product (fun id => coeffAt (heatKernelPacket K w) (state id)) spin (slabPhysicalFaceEdges extent)
  rw [hspin] at h
  exact h.symm

theorem weighted_integrand_factorization (w : Q') (K half : Nat) (left boundary right : EdgeLabelling) :
    RatPolyCoeffEqv (weightedIntegrand w K (centralExtent half) (assembleReflectedSlabLabelling half left boundary right))
      (polyMul (lowerPolynomial w K half left)
        (polyMul (interfaceLabelPolynomial w K half boundary) (upperPolynomial w K half right))) := by
  let assembled := assembleReflectedSlabLabelling half left boundary right
  let f := weightedFacePolynomial w K (centralExtent half) assembled
  have hl : polynomialProduct f (centralLowerFaceIds half) = lowerPolynomial w K half left := by
    apply polynomialProduct_congr
    intro id hi
    unfold f weightedFacePolynomial assembled
    rw [assembleReflectedSlabLabelling_lower (mem_centralLowerFaceIds.mp hi).1 (mem_centralLowerFaceIds.mp hi).2]
  have hb : polynomialProduct f (centralFixedFaceIds half) = interfaceLabelPolynomial w K half boundary := by
    apply polynomialProduct_congr
    intro id hi
    unfold f weightedFacePolynomial assembled
    rw [assembleReflectedSlabLabelling_fixed (mem_centralFixedFaceIds.mp hi).1 (mem_centralFixedFaceIds.mp hi).2]
  have hr : polynomialProduct f (centralUpperFaceIds half) = upperPolynomial w K half right := by
    apply polynomialProduct_congr
    intro id hi
    unfold f weightedFacePolynomial assembled
    rw [assembleReflectedSlabLabelling_upper (mem_centralUpperFaceIds.mp hi).1 (mem_centralUpperFaceIds.mp hi).2]
  have hp := central_product_factorization half f
  rw [hl, hb, hr] at hp
  exact (weighted_integrand_eq_product w K (centralExtent half) assembled).trans hp

private theorem haar_eq_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: rest => by unfold quaternionHaar ratWeightedSum; rw [haar_eq_weighted blocks rest]

theorem haar_of_coeff_eqv (blocks : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  rw [haar_eq_weighted, haar_eq_weighted]
  exact h _

/-- Exact same-source signed dual summand at every odd extent. -/
theorem dualTerm_eq_threeFactorHaar (w : Q') (K half : Nat) (left boundary right : EdgeLabelling) :
    exactCorrectedSlabDualTerm w K (centralExtent half) (assembleReflectedSlabLabelling half left boundary right) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (polyMul (lowerPolynomial w K half left)
          (polyMul (interfaceLabelPolynomial w K half boundary) (upperPolynomial w K half right))) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul _ _ _))
    (haar_of_coeff_eqv _ (weighted_integrand_factorization w K half left boundary right))

end YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.slabFaceIds_map
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.idxOf_slabPlaquetteAt
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.polynomialProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.polynomialProduct_congr
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.polynomialProduct_append
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.polynomialProduct_perm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.central_product_factorization
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.weightedFacePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.lowerPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.interfaceLabelPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.upperPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.weightedIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.weighted_integrand_eq_product
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.weighted_integrand_factorization
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.haar_of_coeff_eqv
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.dualTerm_eq_threeFactorHaar
