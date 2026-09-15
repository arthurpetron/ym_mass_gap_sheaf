/-
# The ORIGINAL interacting scalar numerator is a plaquette pairing /128

The common all-link Haar change is applied to the whole original integrand.
Its full-action/observable factor is preserved; only then are the three
auxiliary gauges integrated. The result uses the existing numerator with the
same original heat coefficients, cutoff, physical face list and observable.

The existing cutoff limits and SAME partition reciprocal give the normalized
cutoff-removed identity. These identities do not identify the completed test or prove
separation, actual-transfer range density, a physical gap or continuum closure.
-/

import YMGap.Continuum.BF4ExactSlabVertexGaugeAction
import YMGap.Continuum.BF4ExactSlabBulkScalarVertexImage
import YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
import YMGap.Continuum.BF4ExactSlabPolynomialExpectation

namespace YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals
open YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage
open YMGap.Continuum.BF4ExactSlabBulkScalarVertexImage
open YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge
open YMGap.Continuum.BF4ExactSlabVertexGaugeAction
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
open YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain

local infix:50 " ≈ " => Q'.eqv

private theorem haar_coeff {p q : RatPoly} (h : RatPolyCoeffEqv p q) (blocks : Nat) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  have pin : ∀ r : RatPoly, quaternionHaar blocks r = ratWeightedSum (quaternionHaarMono blocks) r := by
    intro r
    induction r with
    | nil => rfl
    | cons t ts ih => simp only [quaternionHaar, ratWeightedSum, ih]
  rw [pin, pin]
  exact h _

private theorem partial_lift (p : RatPoly) : RatPolyCoeffEqv (partialHaarHead (liftHead p)) p := by
  have ht : RatPolyTermwiseEqv (partialHaarHead (liftHead p)) p := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih =>
        refine ⟨rfl, ?_, ih⟩
        have h : headQuaternionMoment (0::0::0::0::t.1) ≈ 1 := by
          change sphereMoment4 0 0 0 0 ≈ 1
          decide +kernel
        exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left t.2 _ _ h) (Q'.mul_one_eqv t.2)
  exact fun w => ratWeightedSum_termwise_eqv w ht

private theorem haar_lift_head (blocks : Nat) (p : RatPoly) :
    quaternionHaar (blocks+1) (liftHead p) ≈ quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead blocks (liftHead p)))
    (haar_coeff (partial_lift p) blocks)

private theorem haar_lift : ∀ (n blocks : Nat) (p : RatPoly),
    quaternionHaar (blocks+n) (liftBoundary n p) ≈ quaternionHaar blocks p
  | 0, _, _ => Q'.eqv_refl _
  | n+1, blocks, p => Q'.eqv_trans _ _ _ (haar_lift_head (blocks+n) (liftBoundary n p)) (haar_lift n blocks p)

private theorem haar_average (blocks : Nat) (p : RatPoly) :
    quaternionHaar (blocks+3) p ≈ quaternionHaar blocks (averageThree p) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead (blocks+2) p))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead (blocks+1) (partialHaarHead p)))
      (Q'.eqv_symm (quaternionHaar_partialHaarHead blocks (partialHaarHead (partialHaarHead p)))))

/-- Explicit support of the previously computed literal scalar image. -/
theorem bulkScalarVertexImage_supported (half : Nat) :
    SupportedQuaternionBlocks (linkCount (centralExtent half)+3) (bulkScalarVertexImage half) := by
  have link (edge : Z4Plaq → Z4Link) := lifted_link_support (centralExtent half) (edge (probeFace half))
  have g0 : QuaternionSupported (linkCount (centralExtent half)+3) (PolyQuaternion.coordinateVariable 0) := .coordinate (by omega)
  have g1 : QuaternionSupported (linkCount (centralExtent half)+3) (PolyQuaternion.coordinateVariable 1) := .coordinate (by omega)
  have g2 : QuaternionSupported (linkCount (centralExtent half)+3) (PolyQuaternion.coordinateVariable 2) := .coordinate (by omega)
  exact supported_polyMul (supported_polyMul (supported_polyMul
    ((link faceLinkA).mul g0).scalar ((g0.conj.mul (link faceLinkB)).mul g1).scalar)
    ((g2.conj.mul (link faceLinkC)).mul g1).scalar) ((link faceLinkD).mul g2).scalar

/-- Any proved invariant tail on the ORIGINAL links is retained. The full
action/upper-observable instance is supplied below, not assumed away. -/
theorem bulkScalar_invariant_tail {half : Nat} (tail : RatPoly)
    (h : Invariant (centralExtent half) (probeTags half) tail) :
    quaternionHaar (linkCount (centralExtent half)) (polyMul (bulkScalar half) tail) ≈
      characterFraction * quaternionHaar (linkCount (centralExtent half))
        (polyMul (lower (bulkProbe half)) tail) := by
  let blocks := linkCount (centralExtent half)
  let tags := probeTags half
  let g := slabGaugePolynomial (centralExtent half) tags
  let p := polyMul (bulkScalar half) tail
  have hp : SupportedQuaternionBlocks blocks p := supported_polyMul (bulkScalarInterval half).support h.support
  have hg := slabGauge_haar (centralExtent half) tags (liftBoundary 3 p) (lift_supported hp 3)
  have image : PaddedPolynomialCoeffEqv (blocks+3) (g (liftBoundary 3 p))
      (polyMul (bulkScalarVertexImage half) (g (liftBoundary 3 tail))) := by
    change PaddedPolynomialCoeffEqv _ (g (liftBoundary 3 (polyMul (bulkScalar half) tail))) _
    rw [lift_product]
    exact (PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_mul _ _ _ _)).trans
      ((bulkScalar_global_vertex_image half).mul (PaddedPolynomialCoeffEqv.refl _ _))
  have himage := image.haar (gaugePolynomial_supported _ _ _ (lift_supported hp 3))
    (supported_polyMul (bulkScalarVertexImage_supported half) h.image_support)
  have htail := h.image (bulkScalarVertexImage half) (bulkScalarVertexImage_supported half)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_lift 3 blocks p))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hg)
      (Q'.eqv_trans _ _ _ himage
        (Q'.eqv_trans _ _ _ htail
          (Q'.eqv_trans _ _ _ (haar_average blocks (polyMul (bulkScalarVertexImage half) (liftBoundary 3 tail)))
            (Q'.eqv_trans _ _ _ (haar_coeff (bulkScalar_vertex_average_with_tail half tail) blocks)
              (quaternionHaar_polySmul blocks characterFraction _))))))

private theorem swap_first (a b c : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a b) c) (polyMul b (polyMul a c)) :=
  ((RatPolyCoeffEqv.mul_comm a b).mul_right c).trans (RatPolyCoeffEqv.mul_assoc b a c)

/-- Exact original interacting numerator, for every rational coupling,
cutoff and half-size. This is an identity, not a coupling-uniform estimate. -/
theorem scalar_numerator_eq_plaquette (w : Q') (K half : Nat) (e : PlaquetteExpression half) :
    numerator w (linkCount (centralExtent half)) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
        (polyMul (upper e) (bulkScalar half)) K ≈
      characterFraction * numerator w (linkCount (centralExtent half)) (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) (lower (bulkProbe half))) K := by
  let action := polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (slabPhysicalFaceEdges (centralExtent half))
  have h := bulkScalar_invariant_tail (polyMul (upper e) action) (fullActionInsertion_invariant (probeTags half) w K e)
  exact Q'.eqv_trans _ _ _ (haar_coeff (swap_first (upper e) (bulkScalar half) action) _)
    (Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left characterFraction _ _
      (Q'.eqv_symm (haar_coeff (swap_first (upper e) (lower (bulkProbe half)) action) _))))

private theorem scaled_limit {s t : Nat → Q'} {x y : CReal} (a : Q')
    (h : ∀ n, s n ≈ a * t n)
    (hs : CReal.ConvergesTo (fun n => CReal.ofQ' (s n)) x)
    (ht : CReal.ConvergesTo (fun n => CReal.ofQ' (t n)) y) :
    CReal.Equiv x (CReal.mul (CReal.ofQ' a) y) :=
  CReal.Equiv_of_limit_of_equal
    (fun n => (SumOfSquares.Equiv_of_approx_eqv (fun _ => h n)).trans (CRealAlg.ofQ'_mul a (t n)))
    hs (CReal.convergesTo_const_mul (CReal.ofQ' a) ht)

/-- The SAME original cutoff limits, with their previously supplied moduli. -/
theorem scalar_numeratorLimit_eq_plaquette (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (e : PlaquetteExpression half) :
    CReal.Equiv
      (numeratorLimit w hw0 hw1 (linkCount (centralExtent half)) (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) (bulkScalar half)))
      (CReal.mul (CReal.ofQ' characterFraction)
        (numeratorLimit w hw0 hw1 (linkCount (centralExtent half)) (centralExtent half)
          (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) (lower (bulkProbe half))))) :=
  scaled_limit characterFraction (fun K => scalar_numerator_eq_plaquette w K half e)
    (numerator_converges w hw0 hw1 (linkCount (centralExtent half)) (centralExtent half)
      (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) (bulkScalar half)))
    (numerator_converges w hw0 hw1 (linkCount (centralExtent half)) (centralExtent half)
      (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) (lower (bulkProbe half))))

/-- The partition reciprocal is identical on both sides; no new measure or
normalization is introduced when removing the heat cutoff. -/
theorem scalar_expectation_eq_plaquette (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (e : PlaquetteExpression half) :
    CReal.Equiv (expectation w hw0 hw1 half (polyMul (upper e) (bulkScalar half)))
      (CReal.mul (CReal.ofQ' characterFraction)
        (expectation w hw0 hw1 half (polyMul (upper e) (lower (bulkProbe half))))) :=
  (Pivot2.mul_congr_left (scalar_numeratorLimit_eq_plaquette w hw0 hw1 half e)).trans
    (CRealAlg.cmul_assoc _ _ _)

end YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity

#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity.bulkScalarVertexImage_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity.bulkScalar_invariant_tail
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity.scalar_numerator_eq_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity.scalar_numeratorLimit_eq_plaquette
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarInteractingIdentity.scalar_expectation_eq_plaquette
