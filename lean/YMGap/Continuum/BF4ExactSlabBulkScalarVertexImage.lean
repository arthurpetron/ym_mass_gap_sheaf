/-
# The global Haar ledger has the previously computed scalar-probe image

An explicit common vertex field assigns the three added gauges to the three
non-base corners of the ORIGINAL translated probe. Applying the global
all-link ledger to the existing scalar product gives exactly the local
`bulkScalarVertexImage` whose gauge average was already computed. The source
is lifted only by adjoining the three gauge blocks, not replaced by another
observable. Equality retains coefficient probes after common carrier padding.

The full original action and observable insertion must next be carried through
this SAME ledger and through gauge averaging. Their completed scalar-test
identification and the actual-time comparison are not claimed here.
-/

import YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge
import YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals

namespace YMGap.Continuum.BF4ExactSlabBulkScalarVertexImage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals
open YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage
open YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
open YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage
open YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

private theorem lift_weight (weight : List Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum weight (liftHead p) =
      ratWeightedSum (fun m => weight (0::0::0::0::m)) p
  | [] => rfl
  | t :: rest => congrArg (fun x => t.2 * weight (0::0::0::0::t.1) + x) (lift_weight weight rest)

private theorem lift_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (liftHead p) (liftHead q) := by
  intro weight
  rw [lift_weight, lift_weight]
  exact h _

private theorem boundary_congr (n : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (liftBoundary n p) (liftBoundary n q) := by
  induction n with
  | zero => exact h
  | succ n ih => exact lift_congr ih

private theorem boundary_mul (n : Nat) (p q : RatPoly) :
    liftBoundary n (polyMul p q) = polyMul (liftBoundary n p) (liftBoundary n q) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftBoundary, ih, liftHead_mul]

private theorem lifted_scalar (q : PolyQuaternion) :
    liftBoundary 3 q.scalar = (liftThree q).scalar := rfl

private theorem probeFace_pin (half : Nat) : probeFace half = ((half,half,half,half), .p01) := by
  have h : slabPlaquetteAt 1 0 = ((0,0,0,0), .p01) := by decide +kernel
  simp only [probeFace, h, shiftFace, shiftVertex, Nat.zero_add]

/-- Three non-base corners receive g0,g1,g2; every other vertex is fixed. -/
def probeTags (half : Nat) (v : Z4Vertex) : Option (Fin 3) :=
  if v = (half+1,half,half,half) then some 0
  else if v = (half+1,half+1,half,half) then some 1
  else if v = (half,half+1,half,half) then some 2
  else none

private theorem tag_base (half : Nat) : probeTags half (probeFace half).1 = none := by
  have hn : half ≠ half + 1 := by omega
  simp only [probeFace_pin, probeTags, Prod.mk.injEq, hn,
    and_false, and_true, and_self, ite_false]

private theorem tag_first (half : Nat) :
    probeTags half (addE (probeFace half).1 (dirsOf (probeFace half).2).1) = some 0 := by
  have hn : half ≠ half + 1 := by omega
  simp only [probeFace_pin, probeTags, dirsOf, addE, Prod.mk.injEq, hn, Ne.symm hn,
    and_false, and_true, and_self, ite_false, ite_true]

private theorem tag_far (half : Nat) :
    probeTags half (addE (addE (probeFace half).1 (dirsOf (probeFace half).2).1)
      (dirsOf (probeFace half).2).2) = some 1 := by
  have hn : half ≠ half + 1 := by omega
  simp only [probeFace_pin, probeTags, dirsOf, addE, Prod.mk.injEq, Ne.symm hn,
    and_false, and_true, ite_false, ite_true]

private theorem tag_second (half : Nat) :
    probeTags half (addE (probeFace half).1 (dirsOf (probeFace half).2).2) = some 2 := by
  have hn : half ≠ half + 1 := by omega
  simp only [probeFace_pin, probeTags, dirsOf, addE, Prod.mk.injEq, hn, Ne.symm hn,
    and_true, and_self, ite_false, ite_true]

private theorem tag_far_reverse (half : Nat) :
    probeTags half (addE (addE (probeFace half).1 (dirsOf (probeFace half).2).2)
      (dirsOf (probeFace half).2).1) = some 1 := by
  have hn : half ≠ half + 1 := by omega
  simp only [probeFace_pin, probeTags, dirsOf, addE, Prod.mk.injEq, Ne.symm hn,
    and_false, and_true, ite_false, ite_true]

private abbrev source (half : Nat) (edge : Z4Plaq → Z4Link) : PolyQuaternion :=
  liftedLink (centralExtent half) (edge (probeFace half))

private theorem source_product_pin (half : Nat) :
    RatPolyCoeffEqv (liftBoundary 3 (bulkScalar half))
      (polyMul (polyMul (polyMul (source half faceLinkA).scalar (source half faceLinkB).scalar)
        (source half faceLinkC).scalar) (source half faceLinkD).scalar) := by
  have h := boundary_congr 3 (bulkScalar_product_pin half)
  conv at h => rhs; rw [boundary_mul, boundary_mul, boundary_mul]
  conv at h => rhs; rw [lifted_scalar, lifted_scalar, lifted_scalar, lifted_scalar]
  exact h

private theorem four_image {n : Nat} (hn : 0 < n) (steps : List (SelectedTranslationStep n))
    {a b c d a' b' c' d' : RatPoly}
    (ha : PaddedPolynomialCoeffEqv (n + 1) (applySelectedTranslationSteps hn steps a) a')
    (hb : PaddedPolynomialCoeffEqv (n + 1) (applySelectedTranslationSteps hn steps b) b')
    (hc : PaddedPolynomialCoeffEqv (n + 1) (applySelectedTranslationSteps hn steps c) c')
    (hd : PaddedPolynomialCoeffEqv (n + 1) (applySelectedTranslationSteps hn steps d) d') :
    PaddedPolynomialCoeffEqv (n + 1)
      (applySelectedTranslationSteps hn steps (polyMul (polyMul (polyMul a b) c) d))
      (polyMul (polyMul (polyMul a' b') c') d') :=
  (PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_mul hn steps _ d)).trans
    (((PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_mul hn steps _ c)).trans
      (((PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_mul hn steps a b)).trans
        (ha.mul hb)).mul hc)).mul hd)

/-- Global all-link substitution, with the exact local image consumed by
the 1/128 gauge-average theorem. No new state algebra or action is used. -/
theorem bulkScalar_global_vertex_image (half : Nat) :
    PaddedPolynomialCoeffEqv (linkCount (centralExtent half) + 3)
      (slabGaugePolynomial (centralExtent half) (probeTags half) (liftBoundary 3 (bulkScalar half)))
      (bulkScalarVertexImage half) := by
  unfold bulkScalarVertexImage gaugedScalarProduct
  have image (edge : Z4Plaq → Z4Link) (he : edge (probeFace half) ∈ probeLinks half) :
      PaddedPolynomialCoeffEqv (linkCount (centralExtent half) + 3)
        (slabGaugePolynomial (centralExtent half) (probeTags half) (source half edge).scalar)
        (vertexLink (centralExtent half) (probeTags half) (edge (probeFace half))).scalar :=
    (slabGauge_link (probeTags half) (probeLinks_physical he)).scalar
  have ha := image faceLinkA (by simp [probeLinks, faceLinkA, edgesOf])
  have hb := image faceLinkB (by simp [probeLinks, faceLinkB, edgesOf])
  have hc := image faceLinkC (by simp [probeLinks, faceLinkC, edgesOf])
  have hd := image faceLinkD (by simp [probeLinks, faceLinkD, edgesOf])
  have pa : PolyQuaternionCoeffEqv
      (vertexLink (centralExtent half) (probeTags half) (faceLinkA (probeFace half)))
      (PolyQuaternion.mul (source half faceLinkA) (PolyQuaternion.coordinateVariable 0)) := by
    unfold vertexLink
    rw [show (faceLinkA (probeFace half)).1 = (probeFace half).1 from rfl, tag_base]
    change PolyQuaternionCoeffEqv (gaugeLink PolyQuaternion.one _ (auxiliaryGauge
      (probeTags half (addE (probeFace half).1 (dirsOf (probeFace half).2).1)))) _
    rw [tag_first]
    exact (PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)
  have pd : PolyQuaternionCoeffEqv
      (vertexLink (centralExtent half) (probeTags half) (faceLinkD (probeFace half)))
      (PolyQuaternion.mul (source half faceLinkD) (PolyQuaternion.coordinateVariable 2)) := by
    unfold vertexLink
    rw [show (faceLinkD (probeFace half)).1 = (probeFace half).1 from rfl, tag_base]
    change PolyQuaternionCoeffEqv (gaugeLink PolyQuaternion.one _ (auxiliaryGauge
      (probeTags half (addE (probeFace half).1 (dirsOf (probeFace half).2).2)))) _
    rw [tag_second]
    exact (PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)
  have pb : vertexLink (centralExtent half) (probeTags half) (faceLinkB (probeFace half)) =
      gaugeLink (PolyQuaternion.coordinateVariable 0) (source half faceLinkB)
        (PolyQuaternion.coordinateVariable 1) := by
    unfold vertexLink
    simp only [faceLinkB, tag_first, tag_far, auxiliaryGauge]
    rfl
  have pc : vertexLink (centralExtent half) (probeTags half) (faceLinkC (probeFace half)) =
      gaugeLink (PolyQuaternion.coordinateVariable 2) (source half faceLinkC)
        (PolyQuaternion.coordinateVariable 1) := by
    unfold vertexLink
    simp only [faceLinkC, tag_second, tag_far_reverse, auxiliaryGauge]
    rfl
  rw [pb] at hb
  rw [pc] at hc
  let steps := gaugeLedger (startTag (centralExtent half) (probeTags half))
    (finishTag (centralExtent half) (probeTags half))
  have hpos : 0 < linkCount (centralExtent half) + 2 := by omega
  have hs : PaddedPolynomialCoeffEqv (linkCount (centralExtent half) + 3)
      (slabGaugePolynomial (centralExtent half) (probeTags half) (liftBoundary 3 (bulkScalar half)))
      (slabGaugePolynomial (centralExtent half) (probeTags half)
        (polyMul (polyMul (polyMul (source half faceLinkA).scalar (source half faceLinkB).scalar)
          (source half faceLinkC).scalar) (source half faceLinkD).scalar)) :=
    .of_coeff (applySelectedTranslationSteps_coeffEqv hpos steps (source_product_pin half))
  have hap := PaddedPolynomialCoeffEqv.trans ha
    (PaddedPolynomialCoeffEqv.of_coeff (blocks := linkCount (centralExtent half) + 3) pa.scalar)
  have hdp := PaddedPolynomialCoeffEqv.trans hd
    (PaddedPolynomialCoeffEqv.of_coeff (blocks := linkCount (centralExtent half) + 3) pd.scalar)
  have hfour := four_image hpos steps
    (a := (source half faceLinkA).scalar) (b := (source half faceLinkB).scalar)
    (c := (source half faceLinkC).scalar) (d := (source half faceLinkD).scalar)
    (a' := (PolyQuaternion.mul (source half faceLinkA) (PolyQuaternion.coordinateVariable 0)).scalar)
    (b' := (gaugeLink (PolyQuaternion.coordinateVariable 0) (source half faceLinkB)
      (PolyQuaternion.coordinateVariable 1)).scalar)
    (c' := (gaugeLink (PolyQuaternion.coordinateVariable 2) (source half faceLinkC)
      (PolyQuaternion.coordinateVariable 1)).scalar)
    (d' := (PolyQuaternion.mul (source half faceLinkD) (PolyQuaternion.coordinateVariable 2)).scalar)
    hap hb hc hdp
  exact PaddedPolynomialCoeffEqv.trans hs hfour

end YMGap.Continuum.BF4ExactSlabBulkScalarVertexImage

#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarVertexImage.probeTags
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarVertexImage.bulkScalar_global_vertex_image
