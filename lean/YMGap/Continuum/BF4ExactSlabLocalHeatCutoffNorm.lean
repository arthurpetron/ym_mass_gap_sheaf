/-
# Changing local heat cutoffs in the ORIGINAL normalized OS norm

Multiply an actual source expression by a finite source-region heat product.
Differences between cutoffs K and K+L have squared OS norm at most
bound(e)*(S(w,|region|)*2^(-K))^2, at every bulk padding and allowed lag.
The complete original action and its own normalization stay unchanged.
The estimate passes to the EXISTING thermodynamic form with an explicit
source-dependent cutoff modulus, not a changing-observable limit inference.

The heat-region nome has an explicit smallness guard. The thermodynamic
action is the existing nome 1/1024 at fixed spacing. This is not a bounded
OS multiplication operator, a changed-action comparison or a T2 preimage.
-/

import YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval
import YMGap.Continuum.BF4ExactSlabBulkCollarApproximation
import YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm

namespace YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm (form)
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient (subtract)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (correctionOrder correctionOrder_budget)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def dressed (w : Q') (K : Nat) {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) : PlaquetteExpression half :=
  .mul e (regionExpression w K half ids hi)

def difference (w : Q') (K L : Nat) {half : Nat} (ids : List Nat)
    (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) : PlaquetteExpression half :=
  subtract (dressed w (K+L) ids hi e) (dressed w K ids hi e)

private def faceGenerator (extent : Nat) (phi : Nat → Nat) (id spin : Nat) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent (phi id))).scalar spin

private theorem sum_eval {half : Nat} (F : Nat → Nat → RatPoly) (f : Nat → PlaquetteExpression half) : ∀ ids,
    RatPolyCoeffEqv (evaluate F (sumExpression f ids)) (finitePolySum (fun i => evaluate F (f i)) ids)
  | [] => RatPolyCoeffEqv.zero_smul _
  | _::ids => (RatPolyCoeffEqv.refl _).add (sum_eval F f ids)

private theorem region_eval (w : Q') (K half extent : Nat) (phi : Nat → Nat) :
    (ids : List Nat) → (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) →
      RatPolyCoeffEqv (evaluate (faceGenerator extent phi) (regionExpression w K half ids hi))
        (polynomialProduct (faceHeatPolynomial w K extent) (ids.map phi))
  | [], _ => RatPolyCoeffEqv.refl _
  | id::ids, hi => by
      have hf : RatPolyCoeffEqv (evaluate (faceGenerator extent phi) (faceExpression w K (hi id List.mem_cons_self)))
          (faceHeatPolynomial w K extent (phi id)) := by
        rw [faceHeatPolynomial_eq_sum]
        exact sum_eval _ _ _
      exact hf.mul (region_eval w K half extent phi ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

private theorem difference_eval (w : Q') (K L extent : Nat) (phi : Nat → Nat) {half : Nat}
    (ids : List Nat) (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) :
    RatPolyCoeffEqv (evaluate (faceGenerator extent phi) (difference w K L ids hi e))
      (polyMul (evaluate (faceGenerator extent phi) e) (heatProductRemainder w extent K L (ids.map phi))) := by
  let p := evaluate (faceGenerator extent phi) e
  let H := polynomialProduct (faceHeatPolynomial w K extent) (ids.map phi)
  let R := heatProductRemainder w extent K L (ids.map phi)
  have hl := (RatPolyCoeffEqv.refl p).mul ((region_eval w (K+L) half extent phi ids hi).trans
    (heatProduct_cutoff_append w extent K L (ids.map phi)))
  have hr := (((RatPolyCoeffEqv.refl p).mul (region_eval w K half extent phi ids hi)).smul (-1)).trans
    (cap_mul_left (-1) (polyMul p H)).symm
  exact (hl.add hr).trans (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.mul (.const (-1)) (.mul (.var 0) (.var 1))))
    (.mul (.var 0) (.var 2)) (by decide) (fun | 0 => p | 1 => H | _ => R))

private def mappedSquare {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (K L extent : Nat) (phi : Nat → Nat) {half : Nat}
    (ids : List Nat) (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half)
    (hphi : ∀ id,id ∈ ids → phi id ∈ slabPhysicalFaceEdges extent)
    (hs : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (evaluate (faceGenerator extent phi) (difference w K L ids hi e)))
    (P : SquareBound (boundaryCompleteSlabLinks extent).length (evaluate (faceGenerator extent phi) e) (bound e)) :
    SquareBound (boundaryCompleteSlabLinks extent).length
      (evaluate (faceGenerator extent phi) (difference w K L ids hi e))
      (bound e * ((tailConstant w ids.length * HalfPow.half^K)*(tailConstant w ids.length * HalfPow.half^K))) := by
  let R := productTailInterval hw0 hw1 hsmall K L extent (ids.map phi) (fun _ h => by
    obtain ⟨id,hid,rfl⟩ := List.mem_map.mp h
    exact hphi id hid)
  have hc : (ids.map phi).length = ids.length := List.length_map _
  rw [hc] at R
  exact .ofCoeff hs (difference_eval w K L extent phi ids hi e)
    (P.mul ⟨R.support,Q'.mul_nonneg _ _ R.nonnegative R.nonnegative,(R.mul R).upper⟩)

def bulkLowerSquare {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (padding : Nat) (s : Fin (padding+1))
    (K L : Nat) (ids : List Nat) (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) :
    SquareBound (blocks (half+padding)) (lower (bulkAtTime padding s (difference w K L ids hi e)))
      (bound e * ((tailConstant w ids.length * HalfPow.half^K)*(tailConstant w ids.length * HalfPow.half^K))) := by
  let phi := bulkFaceId half padding s.val
  have hs : ∀ q : PlaquetteExpression half, SupportedQuaternionBlocks (blocks (half+padding))
      (evaluate (faceGenerator (centralExtent (half+padding)) phi) q) := by
    intro q
    simpa only [lower,evaluate_bulkAtTime] using lower_supported (bulkAtTime padding s q)
  have P : SquareBound (blocks (half+padding)) (evaluate (faceGenerator (centralExtent (half+padding)) phi) e) (bound e) := by
    simpa only [lower,evaluate_bulkAtTime,bound_bulkAtTime] using lowerBound (bulkAtTime padding s e)
  unfold lower
  rw [evaluate_bulkAtTime]
  exact mappedSquare hw0 hw1 hsmall K L _ phi ids hi e
    (fun id hid => bulkFaceId_physical (mem_centralLowerFaceIds.mp (hi id hid)).1) (hs _) P

def bulkUpperSquare {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (padding : Nat) (s : Fin (padding+1))
    (K L : Nat) (ids : List Nat) (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) :
    SquareBound (blocks (half+padding)) (upper (bulkAtTime padding s (difference w K L ids hi e)))
      (bound e * ((tailConstant w ids.length * HalfPow.half^K)*(tailConstant w ids.length * HalfPow.half^K))) := by
  let phi := fun id => slabFaceReflectId (centralExtent (half+padding)) (bulkFaceId half padding s.val id)
  have hs : ∀ q : PlaquetteExpression half, SupportedQuaternionBlocks (blocks (half+padding))
      (evaluate (faceGenerator (centralExtent (half+padding)) phi) q) := by
    intro q
    simpa only [upper,evaluate_bulkAtTime] using upper_supported (bulkAtTime padding s q)
  have P : SquareBound (blocks (half+padding)) (evaluate (faceGenerator (centralExtent (half+padding)) phi) e) (bound e) := by
    simpa only [upper,evaluate_bulkAtTime,bound_bulkAtTime] using upperBound (bulkAtTime padding s e)
  unfold upper
  rw [evaluate_bulkAtTime]
  exact mappedSquare hw0 hw1 hsmall K L _ phi ids hi e
    (fun id hid => slabFaceReflectId_physical (bulkFaceId_physical (mem_centralLowerFaceIds.mp (hi id hid)).1)) (hs _) P

/-- The action nome v is independent of the nome w used in the test region. -/
theorem bulk_norm_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (v : Q') (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q'))
    {half : Nat} (padding : Nat) (s : Fin (padding+1)) (K L : Nat)
    (ids : List Nat) (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) :
    leEv (form v hv0 hv1 (bulkAtTime padding s (difference w K L ids hi e)) (bulkAtTime padding s (difference w K L ids hi e)))
      (ofQ' (bound e * ((tailConstant w ids.length * HalfPow.half^K)*(tailConstant w ids.length * HalfPow.half^K)))) :=
  expectation_upper v hv0 hv1 (half+padding) _ _
    ((bulkUpperSquare hw0 hw1 hsmall padding s K L ids hi e).cross (bulkLowerSquare hw0 hw1 hsmall padding s K L ids hi e))

theorem thermodynamic_norm_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) {half : Nat} (K L : Nat)
    (ids : List Nat) (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) (e : PlaquetteExpression half) :
    leEv (formLimit (difference w K L ids hi e) (difference w K L ids hi e))
      (ofQ' (bound e * ((tailConstant w ids.length * HalfPow.half^K)*(tailConstant w ids.length * HalfPow.half^K)))) :=
  leEv_of_convergesTo_le (form_converges _ _) (convergesTo_const _)
    (fun padding => bulk_norm_bound hw0 hw1 hsmall nome nome_pos nome_lt_one padding ⟨0,Nat.zero_lt_succ _⟩ K L ids hi e)

end YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm

#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm.dressed
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm.difference
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm.bulkLowerSquare
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm.bulkUpperSquare
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm.bulk_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm.thermodynamic_norm_bound
