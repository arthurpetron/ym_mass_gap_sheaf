/-
# The SAME source collar approximation survives actual bulk enlargement

Embedding a source collar changes its physical face IDs, not its number
of factors. The existing at-most-24-face heat remainder certificate thus
applies to both the embedded source collar and its actual reflection.
The original signed geometric identity gives the same squared OS error
bound(e)*2^(-2n), independent of padding and the allowed time lag.

No newly chosen target-volume collar replaces the embedded source collar.
The correction order is computed at the source. The bound is evaluated
in the actual normalized finite-slab action, with any 0<w<1; it is a
size/approximation estimate, not a coupling-uniform spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabCollarTestNorm

namespace YMGap.Continuum.BF4ExactSlabBulkCollarApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression
open YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector
open YMGap.Continuum.BF4ExactSlabCollarTestNorm
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient (subtract)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion (collar_mem)
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection (collar_cap_half)
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

private def faceGenerator (extent : Nat) (phi : Nat → Nat) (id spin : Nat) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent (phi id))).scalar spin

private theorem sum_eval {half : Nat} (F : Nat → Nat → RatPoly) (f : Nat → PlaquetteExpression half) : ∀ ids,
    RatPolyCoeffEqv (evaluate F (sumExpression f ids)) (finitePolySum (fun i => evaluate F (f i)) ids)
  | [] => RatPolyCoeffEqv.zero_smul _
  | i :: ids => (RatPolyCoeffEqv.refl (evaluate F (f i))).add (sum_eval F f ids)

private theorem region_eval (K half extent : Nat) (phi : Nat → Nat) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralLowerFaceIds half) →
    RatPolyCoeffEqv (evaluate (faceGenerator extent phi) (regionExpression nome K half ids hi))
      (polynomialProduct (faceHeatPolynomial nome K extent) (ids.map phi))
  | [], _ => RatPolyCoeffEqv.refl _
  | id :: ids, hi => by
      have hf : RatPolyCoeffEqv (evaluate (faceGenerator extent phi) (faceExpression nome K (hi id List.mem_cons_self)))
          (faceHeatPolynomial nome K extent (phi id)) := by
        rw [faceHeatPolynomial_eq_sum]
        exact sum_eval _ _ _
      exact hf.mul (region_eval K half extent phi ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

private def mappedRemainderInterval (K half extent : Nat) (phi : Nat → Nat)
    (hphi : ∀ id, id ∈ lowerCollar half → phi id ∈ slabPhysicalFaceEdges extent)
    (hs : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (evaluate (faceGenerator extent phi) (collarRExpression K half))) :
    Interval (boundaryCompleteSlabLinks extent).length
      (evaluate (faceGenerator extent phi) (collarRExpression K half)) (productErrorCap nome 24) := by
  have hp := (region_eval K half extent phi (lowerCollar half) (fun _ hi => collar_mem hi)).trans
    (product_eq_one_add nome extent K ((lowerCollar half).map phi))
  have hr : RatPolyCoeffEqv (evaluate (faceGenerator extent phi) (collarRExpression K half))
      (productPerturbation nome extent K ((lowerCollar half).map phi)) :=
    (hp.add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq (.add (.add (.const 1) (.var 0)) (.const (-1))) (.var 0)
        (by decide) (fun _ => productPerturbation nome extent K ((lowerCollar half).map phi)))
  exact .ofCoeff hs hr ((productErrorInterval (Q'.le_of_lt nome_pos) (Q'.le_of_lt nome_lt_one)
    existingNome_guards.1 K extent _ (fun _ hi => by
      obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hi
      exact hphi id hid)).weaken (productErrorCap_mono (Q'.le_of_lt nome_pos)
        (by simpa only [List.length_map] using lowerCollar_length_le half)))

private def errorSquare {half blockCount : Nat} (F : Nat → Nat → RatPoly) (K n : Nat) (e : PlaquetteExpression half)
    (hs : ∀ q : PlaquetteExpression half, SupportedQuaternionBlocks blockCount (evaluate F q))
    (P : SquareBound blockCount (evaluate F e) (bound e))
    (R : Interval blockCount (evaluate F (collarRExpression K half)) (productErrorCap nome 24)) :
    SquareBound blockCount (evaluate F (approximationError K n e)) (bound e * (HalfPow.half^n * HalfPow.half^n)) := by
  let H := evaluate F (collarExpression nome K half)
  let r := evaluate F (collarRExpression K half)
  have hH : RatPolyCoeffEqv H (polyAdd polyOne r) :=
    coeffEvalExpr_eqv_of_normalize_eq (.var 0) (.add (.const 1) (.add (.var 0) (.const (-1))))
      (by decide) (fun _ => H)
  have hg := evaluate_geometric F (collarRExpression K half) n
  have he : RatPolyCoeffEqv (evaluate F (approximationError K n e)) (polyMul (evaluate F e) (defect H r n)) :=
    (((RatPolyCoeffEqv.refl _).mul ((RatPolyCoeffEqv.refl _).mul hg)).add (cap_mul_left (-1) (evaluate F e)).symm).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 1) (.mul (.var 0) (.var 2))) (.mul (.const (-1)) (.var 0)))
        (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.const 1))))
        (by decide) (fun | 0 => evaluate F e | 1 => H | _ => corrector r n))
  let E := defectInterval hH (hs _) R collar_cap_half n
  exact .ofCoeff (hs _) he (P.mul ⟨E.support, Q'.mul_nonneg _ _ E.nonnegative E.nonnegative, (E.mul E).upper⟩)

def bulkLowerErrorSquare {half : Nat} (padding : Nat) (s : Fin (padding+1)) (K n : Nat) (e : PlaquetteExpression half) :
    SquareBound (blocks (half+padding)) (lower (bulkAtTime padding s (approximationError K n e)))
      (bound e * (HalfPow.half^n * HalfPow.half^n)) := by
  let phi := bulkFaceId half padding s.val
  have hs : ∀ q : PlaquetteExpression half,
      SupportedQuaternionBlocks (blocks (half+padding)) (evaluate (faceGenerator (centralExtent (half+padding)) phi) q) := by
    intro q
    simpa only [lower, evaluate_bulkAtTime] using lower_supported (bulkAtTime padding s q)
  have P : SquareBound (blocks (half+padding)) (evaluate (faceGenerator (centralExtent (half+padding)) phi) e) (bound e) := by
    simpa only [lower, evaluate_bulkAtTime, bound_bulkAtTime] using lowerBound (bulkAtTime padding s e)
  unfold lower
  rw [evaluate_bulkAtTime]
  exact errorSquare _ K n e hs P (mappedRemainderInterval K half _ phi
    (fun _ hi => bulkFaceId_physical (lowerCollar_physical hi)) (hs _))

def bulkUpperErrorSquare {half : Nat} (padding : Nat) (s : Fin (padding+1)) (K n : Nat) (e : PlaquetteExpression half) :
    SquareBound (blocks (half+padding)) (upper (bulkAtTime padding s (approximationError K n e)))
      (bound e * (HalfPow.half^n * HalfPow.half^n)) := by
  let phi := fun id => slabFaceReflectId (centralExtent (half+padding)) (bulkFaceId half padding s.val id)
  have hs : ∀ q : PlaquetteExpression half,
      SupportedQuaternionBlocks (blocks (half+padding)) (evaluate (faceGenerator (centralExtent (half+padding)) phi) q) := by
    intro q
    simpa only [upper, evaluate_bulkAtTime] using upper_supported (bulkAtTime padding s q)
  have P : SquareBound (blocks (half+padding)) (evaluate (faceGenerator (centralExtent (half+padding)) phi) e) (bound e) := by
    simpa only [upper, evaluate_bulkAtTime, bound_bulkAtTime] using upperBound (bulkAtTime padding s e)
  unfold upper
  rw [evaluate_bulkAtTime]
  exact errorSquare _ K n e hs P (mappedRemainderInterval K half _ phi
    (fun _ hi => slabFaceReflectId_physical (bulkFaceId_physical (lowerCollar_physical hi))) (hs _))

theorem bulk_approximation_error_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {half : Nat} (padding : Nat) (s : Fin (padding+1)) (K n : Nat) (e : PlaquetteExpression half) :
    leEv (form w hw0 hw1 (bulkAtTime padding s (approximationError K n e)) (bulkAtTime padding s (approximationError K n e)))
      (ofQ' (bound e * (HalfPow.half^n * HalfPow.half^n))) :=
  expectation_upper w hw0 hw1 (half+padding) _ _ ((bulkUpperErrorSquare padding s K n e).cross (bulkLowerErrorSquare padding s K n e))

/-- One source-derived order works at EVERY padding and allowed time lag. -/
theorem bulk_approximation_error_atOrder (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {half : Nat} (padding : Nat) (s : Fin (padding+1)) (K : Nat) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    leEv (form w hw0 hw1 (bulkAtTime padding s (approximationError K (approximationOrder e epsilon) e))
      (bulkAtTime padding s (approximationError K (approximationOrder e epsilon) e))) (ofQ' epsilon) :=
  leEv_trans (bulk_approximation_error_bound w hw0 hw1 padding s K _ e)
    (leEv_ofQ'_of_approx_ge (fun _ => approximation_order_budget e epsilon he))

end YMGap.Continuum.BF4ExactSlabBulkCollarApproximation

#print axioms YMGap.Continuum.BF4ExactSlabBulkCollarApproximation.bulkLowerErrorSquare
#print axioms YMGap.Continuum.BF4ExactSlabBulkCollarApproximation.bulkUpperErrorSquare
#print axioms YMGap.Continuum.BF4ExactSlabBulkCollarApproximation.bulk_approximation_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkCollarApproximation.bulk_approximation_error_atOrder
