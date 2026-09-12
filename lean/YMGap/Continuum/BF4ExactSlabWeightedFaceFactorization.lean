/-
# Literal heat-weighted signed-Haar factorization across the BF4 plane

The complete 72-face/116-link network factors into its 24 lower, 24 fixed,
and 24 upper face polynomials, with the actual heat coefficient on EVERY
face. This is coefficient-probe equality of polynomials, before Haar
integration, and remains valid with any polynomial insertion.

The upper factor uses the literal reflected face labels. No link projector
is replaced by its rank, no sign is dropped, and no positivity or spectral
estimate is assumed. The reflection-positive cross-plane resolution and
physical time-translation construction are still separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
import YMGap.Continuum.SU2QuaternionRatPolyDifferential

namespace YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private def faceProduct (factor : Nat → RatPoly) : List Nat → RatPoly
  | [] => polyOne
  | id :: rest => polyMul (factor id) (faceProduct factor rest)

private theorem one_smul (p : RatPoly) : RatPolyCoeffEqv (polySmul 1 p) p := by
  intro weight
  exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight 1 p) (Q'.one_mul_eqv _)

private theorem one_mul (p : RatPoly) : RatPolyCoeffEqv (polyMul polyOne p) p := by
  have h : polyMul polyOne p = polySmul 1 p := by
    simp [polyMul, polyOne, polySmul, monoMul]
  rw [h]
  exact one_smul p

private theorem product_append (factor : Nat → RatPoly) :
    ∀ left right : List Nat,
      RatPolyCoeffEqv (faceProduct factor (left ++ right))
        (polyMul (faceProduct factor left) (faceProduct factor right))
  | [], right => (one_mul _).symm
  | id :: rest, right => by
    change RatPolyCoeffEqv
      (polyMul (factor id) (faceProduct factor (rest ++ right)))
      (polyMul (polyMul (factor id) (faceProduct factor rest)) (faceProduct factor right))
    exact ((product_append factor rest right).mul_left (factor id)).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm

private theorem product_perm (factor : Nat → RatPoly) {left right : List Nat}
    (h : left.Perm right) : RatPolyCoeffEqv (faceProduct factor left) (faceProduct factor right) := by
  induction h with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons id _ ih => exact ih.mul_left (factor id)
  | swap a b rest =>
    exact (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
      (((RatPolyCoeffEqv.mul_comm _ _).mul_right _).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem product_congr (left right : Nat → RatPoly) :
    ∀ ids : List Nat, (∀ id, id ∈ ids → left id = right id) →
      faceProduct left ids = faceProduct right ids
  | [], _ => rfl
  | id :: rest, h => by
    change polyMul (left id) (faceProduct left rest) = polyMul (right id) (faceProduct right rest)
    rw [h id List.mem_cons_self, product_congr left right rest
      (fun j hj => h j (List.mem_cons_of_mem id hj))]

private theorem weighted_product (weight : Nat → Q') (factor : Nat → RatPoly) :
    ∀ ids : List Nat,
      RatPolyCoeffEqv (faceProduct (fun id => polySmul (weight id) (factor id)) ids)
        (polySmul (eliminateLinks weight ids) (faceProduct factor ids))
  | [] => (one_smul _).symm
  | id :: rest => by
    change RatPolyCoeffEqv
      (polyMul (polySmul (weight id) (factor id))
        (faceProduct (fun j => polySmul (weight j) (factor j)) rest))
      (polySmul (weight id * eliminateLinks weight rest)
        (polyMul (factor id) (faceProduct factor rest)))
    exact ((weighted_product weight factor rest).mul_left _).trans
      ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
        (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul _).trans
          (RatPolyCoeffEqv.smul_assoc _ _ _)))

/-- Actual heat-weighted character on the named literal slab face. -/
def weightedFacePolynomial (w : Q') (K : Nat) (state : EdgeLabelling) (id : Nat) : RatPoly :=
  polySmul (coeffAt (heatKernelPacket K w) (state id))
    (characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar (state id))

def lowerPolynomial (w : Q') (K : Nat) (state : EdgeLabelling) : RatPoly :=
  faceProduct (weightedFacePolynomial w K state) (centralLowerFaceIds 0)

def interfacePolynomial (w : Q') (K : Nat) (boundary : EdgeLabelling) : RatPoly :=
  faceProduct (weightedFacePolynomial w K boundary) (centralFixedFaceIds 0)

/-- The right label is pulled back by the existing physical face reflection. -/
def upperPolynomial (w : Q') (K : Nat) (state : EdgeLabelling) : RatPoly :=
  faceProduct (weightedFacePolynomial w K (fun id => state (slabFaceReflectId 1 id)))
    (centralUpperFaceIds 0)

private theorem spin_factor_id (state : EdgeLabelling) {id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges 1) :
    correctedSlabPlaquetteSpinFactor 1 state (slabPlaquetteAt 1 id) =
      characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar (state id) := by
  unfold correctedSlabPlaquetteSpinFactor
  rw [idxOf_slabPlaquetteAt_one hid]

private theorem product_eq_fold (factor : Nat → RatPoly) (ids : List Nat) :
    faceProduct factor ids = ids.foldr (fun id p => polyMul (factor id) p) polyOne := by
  induction ids with
  | nil => rfl
  | cons id ids ih => simp only [faceProduct, List.foldr, ih]

/-- The product of weighted face polynomials is the original signed-network
integrand with its original full heat coefficient, not a rank product. -/
theorem weighted_integrand_eq_faceProduct (w : Q') (K : Nat) (state : EdgeLabelling) :
    RatPolyCoeffEqv (exactCorrectedSlabWeightedIntegrand w K state)
      (faceProduct (weightedFacePolynomial w K state) (slabPhysicalFaceEdges 1)) := by
  let spin : Nat → RatPoly := fun id =>
    characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar (state id)
  have hspin : faceProduct spin (slabPhysicalFaceEdges 1) = exactCorrectedSlabSpinNetworkIntegrand 1 state := by
    rw [product_congr spin (fun id => correctedSlabPlaquetteSpinFactor 1 state (slabPlaquetteAt 1 id))
      (slabPhysicalFaceEdges 1) (fun id hid => (spin_factor_id state hid).symm), product_eq_fold]
    have hmap : (slabPhysicalFaceEdges 1).map (slabPlaquetteAt 1) = boundaryCompleteSlabPlaquettes 1 := by decide
    unfold exactCorrectedSlabSpinNetworkIntegrand
    rw [← hmap, List.foldr_map]
  have h := weighted_product (fun id => coeffAt (heatKernelPacket K w) (state id)) spin
    (slabPhysicalFaceEdges 1)
  rw [hspin] at h
  exact h.symm

/-- Exact lower/interface/upper factorization before integration. The three
parts use disjoint face labels but retain the SAME 116 link coordinates. -/
theorem weighted_integrand_factorization (w : Q') (K : Nat)
    (left boundary right : EdgeLabelling) :
    RatPolyCoeffEqv
      (exactCorrectedSlabWeightedIntegrand w K (assembleReflectedSlabLabelling 0 left boundary right))
      (polyMul (lowerPolynomial w K left)
        (polyMul (interfacePolynomial w K boundary) (upperPolynomial w K right))) := by
  let assembled := assembleReflectedSlabLabelling 0 left boundary right
  let factor := weightedFacePolynomial w K assembled
  have hl : faceProduct factor (centralLowerFaceIds 0) = lowerPolynomial w K left := by
    apply product_congr
    intro id hid
    have hp := mem_centralLowerFaceIds.mp hid
    unfold factor weightedFacePolynomial assembled
    rw [assembleReflectedSlabLabelling_lower hp.1 hp.2]
  have hb : faceProduct factor (centralFixedFaceIds 0) = interfacePolynomial w K boundary := by
    apply product_congr
    intro id hid
    have hp := mem_centralFixedFaceIds.mp hid
    unfold factor weightedFacePolynomial assembled
    rw [assembleReflectedSlabLabelling_fixed hp.1 hp.2]
  have hr : faceProduct factor (centralUpperFaceIds 0) = upperPolynomial w K right := by
    apply product_congr
    intro id hid
    have hp := mem_centralUpperFaceIds.mp hid
    unfold factor weightedFacePolynomial assembled
    rw [assembleReflectedSlabLabelling_upper hp.1 hp.2]
    rfl
  have hparts := (product_perm factor (centralSlabFaceIdParts_perm 0).symm).trans
    ((product_append factor (centralLowerFaceIds 0)
      (centralFixedFaceIds 0 ++ centralUpperFaceIds 0)).trans
      ((product_append factor (centralFixedFaceIds 0) (centralUpperFaceIds 0)).mul_left _))
  rw [hl, hb, hr] at hparts
  exact (weighted_integrand_eq_faceProduct w K assembled).trans hparts

private theorem haar_eq_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: rest => by
    unfold quaternionHaar ratWeightedSum
    rw [haar_eq_weighted blocks rest]

/-- Coefficient-probe equality can be consumed by the original product Haar
with any further polynomial insertion; no positivity assumption is needed. -/
theorem weighted_integrand_factorization_insert (w : Q') (K : Nat)
    (left boundary right : EdgeLabelling) (insertion : RatPoly) :
    quaternionHaar 116 (polyMul insertion
      (exactCorrectedSlabWeightedIntegrand w K (assembleReflectedSlabLabelling 0 left boundary right))) ≈
    quaternionHaar 116 (polyMul insertion
      (polyMul (lowerPolynomial w K left)
        (polyMul (interfacePolynomial w K boundary) (upperPolynomial w K right)))) := by
  rw [haar_eq_weighted, haar_eq_weighted]
  exact ((weighted_integrand_factorization w K left boundary right).mul_left insertion)
    (quaternionHaarMono 116)

/-- The actual signed dual term is the Haar integral of these three literal
heat-weighted pieces. This is the scalar consumer used in finite resummation. -/
theorem dualTerm_eq_threeFactorHaar (w : Q') (K : Nat)
    (left boundary right : EdgeLabelling) :
    exactCorrectedSlabDualTerm w K 1 (assembleReflectedSlabLabelling 0 left boundary right) ≈
      quaternionHaar 116 (polyMul (lowerPolynomial w K left)
        (polyMul (interfacePolynomial w K boundary) (upperPolynomial w K right))) := by
  refine Q'.eqv_trans _ _ _ (exactCorrectedSlabDualTerm_eq_weightedHaar w K _) ?_
  rw [haar_eq_weighted, haar_eq_weighted]
  exact weighted_integrand_factorization w K left boundary right (quaternionHaarMono 116)

end YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization

#print axioms YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization.weightedFacePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization.lowerPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization.interfacePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization.upperPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization.weighted_integrand_eq_faceProduct
#print axioms YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization.weighted_integrand_factorization
#print axioms YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization.weighted_integrand_factorization_insert
#print axioms YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization.dualTerm_eq_threeFactorHaar
