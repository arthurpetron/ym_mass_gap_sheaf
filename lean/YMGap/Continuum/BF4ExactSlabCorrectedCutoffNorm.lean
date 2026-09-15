/-
# Joint heat-cutoff and correction-order control in the ORIGINAL OS norm

The samples are the existing correctedExpression K K e. A single signed
identity compares samples K+L and K, with squared OS error bounded by
bound(e)*((4*S(nome,|source collar|)+4)*2^(-K))^2. Both parameters vary;
the actual source collar is embedded, not recomputed at the larger volume.

The full original normalized action remains unchanged. This supplies the
missing diagonal corrected-state estimate, not a bounded OS multiplier,
changed-action comparison, actual T2 identity, or physical mass gap.
-/

import YMGap.Continuum.QuaternionHaarPolynomialCorrectorStability
import YMGap.Continuum.BF4ExactSlabLocalHeatCutoffNorm

namespace YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm

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
open YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector
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
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion (collar_mem)
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection (collar_cap_half)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarPolynomialCorrectorStability (differenceInterval)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "hw0" => Q'.le_of_lt nome_pos
local notation "hw1" => Q'.le_of_lt nome_lt_one

def tailCap (half : Nat) : Q' := 4*tailConstant nome (lowerCollar half).length+4

theorem tailCap_nonnegative (half : Nat) : (0 : Q') ≤ tailCap half :=
  Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (by decide) (tailConstant_nonnegative hw0 _)) (by decide)

def correctedDifference (K L : Nat) {half : Nat} (e : PlaquetteExpression half) : PlaquetteExpression half :=
  subtract (correctedExpression (K+L) (K+L) e) (correctedExpression K K e)

private def faceGenerator (extent : Nat) (phi : Nat → Nat) (id spin : Nat) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent (phi id))).scalar spin

private theorem sum_eval {half : Nat} (F : Nat → Nat → RatPoly) (f : Nat → PlaquetteExpression half) : ∀ ids,
    RatPolyCoeffEqv (evaluate F (sumExpression f ids)) (finitePolySum (fun i => evaluate F (f i)) ids)
  | [] => RatPolyCoeffEqv.zero_smul _
  | _::ids => (RatPolyCoeffEqv.refl _).add (sum_eval F f ids)

private theorem region_eval (K half extent : Nat) (phi : Nat → Nat) :
    (ids : List Nat) → (hi : ∀ id,id ∈ ids → id ∈ centralLowerFaceIds half) →
      RatPolyCoeffEqv (evaluate (faceGenerator extent phi) (regionExpression nome K half ids hi))
        (polynomialProduct (faceHeatPolynomial nome K extent) (ids.map phi))
  | [], _ => RatPolyCoeffEqv.refl _
  | id::ids, hi => by
      have hf : RatPolyCoeffEqv (evaluate (faceGenerator extent phi) (faceExpression nome K (hi id List.mem_cons_self)))
          (faceHeatPolynomial nome K extent (phi id)) := by
        rw [faceHeatPolynomial_eq_sum]
        exact sum_eval _ _ _
      exact hf.mul (region_eval K half extent phi ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

private def remainderInterval (K half extent : Nat) (phi : Nat → Nat)
    (hphi : ∀ id,id ∈ lowerCollar half → phi id ∈ slabPhysicalFaceEdges extent)
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
  exact .ofCoeff hs hr ((productErrorInterval hw0 hw1 existingNome_guards.1 K extent _ (fun _ hi => by
    obtain ⟨id,hid,rfl⟩ := List.mem_map.mp hi
    exact hphi id hid)).weaken (productErrorCap_mono hw0
      (by simpa only [List.length_map] using lowerCollar_length_le half)))

private def heatDifferenceInterval (K L half extent : Nat) (phi : Nat → Nat)
    (hphi : ∀ id,id ∈ lowerCollar half → phi id ∈ slabPhysicalFaceEdges extent)
    (hs : ∀ q : PlaquetteExpression half, SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (evaluate (faceGenerator extent phi) q)) :
    Interval (boundaryCompleteSlabLinks extent).length
      (polyAdd (evaluate (faceGenerator extent phi) (collarRExpression (K+L) half))
        (polyNeg (evaluate (faceGenerator extent phi) (collarRExpression K half))))
      (tailConstant nome (lowerCollar half).length * HalfPow.half^K) := by
  let ids := (lowerCollar half).map phi
  let H := polynomialProduct (faceHeatPolynomial nome K extent) ids
  let R := heatProductRemainder nome extent K L ids
  have hp := ((region_eval (K+L) half extent phi (lowerCollar half) (fun _ hi => collar_mem hi)).trans
    (heatProduct_cutoff_append nome extent K L ids)).add (RatPolyCoeffEqv.refl (polySmul (-1) polyOne))
  have hq := (region_eval K half extent phi (lowerCollar half) (fun _ hi => collar_mem hi)).add
    (RatPolyCoeffEqv.refl (polySmul (-1) polyOne))
  have hd := (hp.add (RatPolyCoeffEqv.neg hq)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.add (.var 0) (.var 2))))
      (.var 1) (by decide) (fun | 0 => H | 1 => R | _ => polySmul (-1) polyOne))
  let P := productTailInterval hw0 hw1 existingNome_guards.1 K L extent ids (fun _ hi => by
    obtain ⟨id,hid,rfl⟩ := List.mem_map.mp hi
    exact hphi id hid)
  have hlen : ids.length = (lowerCollar half).length := List.length_map _
  rw [hlen] at P
  exact .ofCoeff ((remainderInterval (K+L) half extent phi hphi (hs _)).add
    (negInterval (remainderInterval K half extent phi hphi (hs _)))).support hd P

private def correctionDifferenceInterval (K L half extent : Nat) (phi : Nat → Nat)
    (hphi : ∀ id,id ∈ lowerCollar half → phi id ∈ slabPhysicalFaceEdges extent)
    (hs : ∀ q : PlaquetteExpression half, SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (evaluate (faceGenerator extent phi) q)) :
    Interval (boundaryCompleteSlabLinks extent).length
      (QuaternionHaarPolynomialCorrectorStability.difference
        (evaluate (faceGenerator extent phi) (collarRExpression (K+L) half))
        (evaluate (faceGenerator extent phi) (collarRExpression K half)) (K+L) K)
      (tailCap half * HalfPow.half^K) := by
  let D := heatDifferenceInterval K L half extent phi hphi hs
  let P := differenceInterval (remainderInterval (K+L) half extent phi hphi (hs _))
    (remainderInterval K half extent phi hphi (hs _)) collar_cap_half collar_cap_half D (K+L) K
  have hpow : HalfPow.half^(K+L) ≤ HalfPow.half^K := half_pow_antitone K (K+L) (Nat.le_add_right _ _)
  have hc := Q'.add_le_add_left (4*(tailConstant nome (lowerCollar half).length*HalfPow.half^K)) _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 (Q'.add_le_add_right _ _ (HalfPow.half^K) hpow) (by decide))
  exact P.weaken (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.mul (.const 4) (.mul (.var 0) (.var 1))) (.mul (.const 2) (.add (.var 1) (.var 1))))
      (.mul (.add (.mul (.const 4) (.var 0)) (.const 4)) (.var 1))
      (by decide) (fun | 0 => tailConstant nome (lowerCollar half).length | _ => HalfPow.half^K))))

private def mappedSquare (K L half extent : Nat) (phi : Nat → Nat) (e : PlaquetteExpression half)
    (hphi : ∀ id,id ∈ lowerCollar half → phi id ∈ slabPhysicalFaceEdges extent)
    (hs : ∀ q : PlaquetteExpression half, SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (evaluate (faceGenerator extent phi) q))
    (P : SquareBound (boundaryCompleteSlabLinks extent).length (evaluate (faceGenerator extent phi) e) (bound e)) :
    SquareBound (boundaryCompleteSlabLinks extent).length
      (evaluate (faceGenerator extent phi) (correctedDifference K L e))
      (bound e*((tailCap half*HalfPow.half^K)*(tailCap half*HalfPow.half^K))) := by
  let F := faceGenerator extent phi
  let p := evaluate F e
  let G := corrector (evaluate F (collarRExpression (K+L) half)) (K+L)
  let J := corrector (evaluate F (collarRExpression K half)) K
  have hg := evaluate_geometric F (collarRExpression (K+L) half) (K+L)
  have hj := evaluate_geometric F (collarRExpression K half) K
  have hp := ((RatPolyCoeffEqv.refl p).mul hg).add
    ((((RatPolyCoeffEqv.refl p).mul hj).smul (-1)).trans (cap_mul_left (-1) (polyMul p J)).symm)
  have hd := hp.trans (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1)) (.mul (.const (-1)) (.mul (.var 0) (.var 2))))
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide) (fun | 0 => p | 1 => G | _ => J))
  let D := correctionDifferenceInterval K L half extent phi hphi hs
  exact .ofCoeff (hs _) hd (P.mul ⟨D.support,Q'.mul_nonneg _ _ D.nonnegative D.nonnegative,(D.mul D).upper⟩)

def bulkLowerSquare {half : Nat} (padding : Nat) (s : Fin (padding+1)) (K L : Nat) (e : PlaquetteExpression half) :
    SquareBound (blocks (half+padding)) (lower (bulkAtTime padding s (correctedDifference K L e)))
      (bound e*((tailCap half*HalfPow.half^K)*(tailCap half*HalfPow.half^K))) := by
  let phi := bulkFaceId half padding s.val
  have hs : ∀ q : PlaquetteExpression half, SupportedQuaternionBlocks (blocks (half+padding))
      (evaluate (faceGenerator (centralExtent (half+padding)) phi) q) := by
    intro q
    simpa only [lower,evaluate_bulkAtTime] using lower_supported (bulkAtTime padding s q)
  have P : SquareBound (blocks (half+padding)) (evaluate (faceGenerator (centralExtent (half+padding)) phi) e) (bound e) := by
    simpa only [lower,evaluate_bulkAtTime,bound_bulkAtTime] using lowerBound (bulkAtTime padding s e)
  unfold lower
  rw [evaluate_bulkAtTime]
  exact mappedSquare K L half _ phi e (fun _ hi => bulkFaceId_physical (lowerCollar_physical hi)) hs P

def bulkUpperSquare {half : Nat} (padding : Nat) (s : Fin (padding+1)) (K L : Nat) (e : PlaquetteExpression half) :
    SquareBound (blocks (half+padding)) (upper (bulkAtTime padding s (correctedDifference K L e)))
      (bound e*((tailCap half*HalfPow.half^K)*(tailCap half*HalfPow.half^K))) := by
  let phi := fun id => slabFaceReflectId (centralExtent (half+padding)) (bulkFaceId half padding s.val id)
  have hs : ∀ q : PlaquetteExpression half, SupportedQuaternionBlocks (blocks (half+padding))
      (evaluate (faceGenerator (centralExtent (half+padding)) phi) q) := by
    intro q
    simpa only [upper,evaluate_bulkAtTime] using upper_supported (bulkAtTime padding s q)
  have P : SquareBound (blocks (half+padding)) (evaluate (faceGenerator (centralExtent (half+padding)) phi) e) (bound e) := by
    simpa only [upper,evaluate_bulkAtTime,bound_bulkAtTime] using upperBound (bulkAtTime padding s e)
  unfold upper
  rw [evaluate_bulkAtTime]
  exact mappedSquare K L half _ phi e
    (fun _ hi => slabFaceReflectId_physical (bulkFaceId_physical (lowerCollar_physical hi))) hs P

theorem bulk_norm_bound (v : Q') (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q'))
    {half : Nat} (padding : Nat) (s : Fin (padding+1)) (K L : Nat) (e : PlaquetteExpression half) :
    leEv (form v hv0 hv1 (bulkAtTime padding s (correctedDifference K L e)) (bulkAtTime padding s (correctedDifference K L e)))
      (ofQ' (bound e*((tailCap half*HalfPow.half^K)*(tailCap half*HalfPow.half^K)))) :=
  expectation_upper v hv0 hv1 (half+padding) _ _ ((bulkUpperSquare padding s K L e).cross (bulkLowerSquare padding s K L e))

theorem thermodynamic_norm_bound {half : Nat} (K L : Nat) (e : PlaquetteExpression half) :
    leEv (formLimit (correctedDifference K L e) (correctedDifference K L e))
      (ofQ' (bound e*((tailCap half*HalfPow.half^K)*(tailCap half*HalfPow.half^K)))) :=
  leEv_of_convergesTo_le (form_converges _ _) (convergesTo_const _)
    (fun padding => bulk_norm_bound nome nome_pos nome_lt_one padding ⟨0,Nat.zero_lt_succ _⟩ K L e)

end YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm

#print axioms YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm.tailCap
#print axioms YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm.tailCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm.correctedDifference
#print axioms YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm.bulkLowerSquare
#print axioms YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm.bulkUpperSquare
#print axioms YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm.bulk_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabCorrectedCutoffNorm.thermodynamic_norm_bound
