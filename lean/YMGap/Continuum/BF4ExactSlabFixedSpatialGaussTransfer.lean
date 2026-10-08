/-
# Actual fixed-spatial Gauss symmetry of the ORIGINAL transfer
The generator sums minus-left outgoing and plus-right incoming derivatives
over the literal baseLinks carrier, including its fringe. Its spatial-action
zero is produced from each original physical face, not inferred from the
full action. Supported placement is converted to genuine Haar equality before
differentiation. No padded equality is differentiated. All statements are
finite Haar-carrier identities; no horizontal energy, stationary vacuum,
completed/continuum gauge law, scaling estimate or gap is supplied.
-/
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingAngular
import YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.SU2QuaternionProductHeatAngularCommutation
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
namespace YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer
set_option autoImplicit false
open YMGap.Constructive YMGap.Continuum
open RingNormaliser ClusterCount4DProgress Z4HalfTimeReflectionGeometry Z4HalfTimeReflectionFaceReindex
open BF4GeometricHaarMehlerProjection BF4GeometricSpinNetworkMehler BF4CompactActionCPOrder
open BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics BF4ExactCorrectedSlabHaarNetwork
open BF4ExactPhysicalCenteredVacuumHaarResummation BF4ExactSlabAllExtentWeightedFactorization
open BF4ExactSlabAllExtentObservableHaarForm BF4ExactSlabFixedSpatialSliceCarrier BF4ExactSlabFixedSpatialSliceHeat
open BF4ExactSlabFixedSpatialTwoLayerGeometry BF4ExactSlabFixedSpatialTwoLayerGluing BF4ExactSlabFaceLinkLocality
open BF4ExactSlabFixedSpatialTransferStep BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open BF4ExactSlabVertexGaussWilsonWord BF4ExactSlabVertexGaussClosedCharacter BF4ExactSlabVertexGaussHeatAction
open SU2QuaternionPolynomialHaarCarrier SU2QuaternionArbitraryHaarRadialPositivity SU2QuaternionRatPolyDifferential
open SU2QuaternionAngularDerivative SU2QuaternionAngularSupport SU2QuaternionAngularReindex SU2QuaternionPairedFrameAt
open SU2QuaternionLeftRightAngularAction SU2QuaternionHaarAngularIBPAt SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open SU2QuaternionAuxiliaryLiftAlgebra SU2QuaternionTranslationPolynomialImages SU2QuaternionFactorizedHaarContraction
open SU2QuaternionHeadChainComposition SU2QuaternionHaarCertificateIntegration SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (carrier_extend)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open SU2QuaternionProductHeatMarginals SU2QuaternionProductHeatAngularCommutation
open QuaternionHaarAngularCarrier QuaternionHaarSquareCertificate BF4ExactSlabFixedSpatialTwoLayerBoundary BF4ExactPhysicalCenteredVacuumTransmittedMarginal
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local instance (width : Nat) (l : Z4Link) : Decidable (SliceLink width 0 l) := by
  unfold SliceLink
  infer_instance
private def term (links : List Z4Link) (v : Z4Vertex) (i : Fin 3) (l : Z4Link)
    (p : RatPoly) : RatPoly := polyAdd
  (if v=l.1 then polyNeg (frameDerivativeAt false (links.idxOf l) i p) else polyZero)
  (if v=addE l.1 l.2 then frameDerivativeAt true (links.idxOf l) i p else polyZero)
private def along (links : List Z4Link) (v : Z4Vertex) (i : Fin 3) (p : RatPoly) : RatPoly :=
  finitePolySum (fun l => term links v i l p) links
/-- The literal source-slice all-link generator, with both endpoint signs. -/
def sliceGauss (width : Nat) (v : Z4Vertex) (i : Fin 3) (p : RatPoly) : RatPoly :=
  along (baseLinks width) v i p
private theorem directions (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega
private theorem zero_supported (n : Nat) : SupportedQuaternionBlocks n polyZero :=
  fun _ h => False.elim (List.not_mem_nil h)
private theorem neg_supported {n : Nat} {p : RatPoly} (h : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact h s hs
private theorem frame_supported {n b : Nat} (right : Bool) (hb : b<n) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (frameDerivativeAt right b i p) := by
  have h (a d : Nat) (ha : a<4) (hd : d<4) :=
    angularDerivative_supported_at (by omega : 4*b+a<4*n) (by omega : 4*b+d<4*n) hp
  rcases directions i with rfl | rfl | rfl <;> cases right
  all_goals simp only [frameDerivativeAt, Bool.false_eq_true, if_false, if_true, rightDerivativeAt, pairedDerivativeAt]
  all_goals first
    | exact supported_add (h 0 1 (by decide) (by decide)) (h 2 3 (by decide) (by decide))
    | exact supported_add (h 0 1 (by decide) (by decide)) (neg_supported (h 2 3 (by decide) (by decide)))
    | exact supported_add (h 0 2 (by decide) (by decide)) (neg_supported (h 1 3 (by decide) (by decide)))
    | exact supported_add (h 0 2 (by decide) (by decide)) (h 1 3 (by decide) (by decide))
    | exact supported_add (h 0 3 (by decide) (by decide)) (h 1 2 (by decide) (by decide))
    | exact supported_add (h 0 3 (by decide) (by decide)) (neg_supported (h 1 2 (by decide) (by decide)))

private theorem sum_supported {A : Type} {n : Nat} (f : A → RatPoly) :
    ∀ xs : List A, (∀ a, a∈xs → SupportedQuaternionBlocks n (f a)) →
      SupportedQuaternionBlocks n (finitePolySum f xs)
  | [], _ => zero_supported n
  | a::xs, h => supported_add (h a List.mem_cons_self)
      (sum_supported f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))
private theorem along_supported (links : List Z4Link) (v : Z4Vertex) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks links.length p) :
    SupportedQuaternionBlocks links.length (along links v i p) := by
  apply sum_supported
  intro l hl
  have hb := List.idxOf_lt_length_of_mem hl
  unfold term
  apply supported_add
  · split
    · exact neg_supported (frame_supported false hb i hp)
    · exact zero_supported _
  · split
    · exact frame_supported true hb i hp
    · exact zero_supported _

theorem sliceGauss_supported (width : Nat) (v : Z4Vertex) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
    SupportedQuaternionBlocks (N width) (sliceGauss width v i p) := along_supported _ v i hp
private theorem frame_carrier {n b : Nat} (right : Bool) (hb : b<n) (i : Fin 3)
    {p q : RatPoly} (h : HaarCarrierEqv n p q) :
    HaarCarrierEqv n (frameDerivativeAt right b i p) (frameDerivativeAt right b i q) := by
  have hd (a d : Nat) (ha : a<4) (hh : d<4) := angularDerivative_carrier_at hb ha hh h
  rcases directions i with rfl | rfl | rfl <;> cases right
  all_goals simp only [frameDerivativeAt, Bool.false_eq_true, if_false, if_true, rightDerivativeAt, pairedDerivativeAt]
  all_goals first
    | exact HaarCarrierEqv.add (hd 0 1 (by decide) (by decide)) (hd 2 3 (by decide) (by decide))
    | exact HaarCarrierEqv.add (hd 0 1 (by decide) (by decide)) (HaarCarrierEqv.neg (hd 2 3 (by decide) (by decide)))
    | exact HaarCarrierEqv.add (hd 0 2 (by decide) (by decide)) (HaarCarrierEqv.neg (hd 1 3 (by decide) (by decide)))
    | exact HaarCarrierEqv.add (hd 0 2 (by decide) (by decide)) (hd 1 3 (by decide) (by decide))
    | exact HaarCarrierEqv.add (hd 0 3 (by decide) (by decide)) (hd 1 2 (by decide) (by decide))
    | exact HaarCarrierEqv.add (hd 0 3 (by decide) (by decide)) (HaarCarrierEqv.neg (hd 1 2 (by decide) (by decide)))

private theorem sum_carrier {A : Type} {n : Nat} (f g : A → RatPoly) :
    ∀ xs : List A, (∀ a, a∈xs → HaarCarrierEqv n (f a) (g a)) →
      HaarCarrierEqv n (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => .refl _ _
  | a::xs, h => HaarCarrierEqv.add (h a List.mem_cons_self)
      (sum_carrier f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem along_carrier (links : List Z4Link) (v : Z4Vertex) (i : Fin 3)
    {p q : RatPoly} (h : HaarCarrierEqv links.length p q) :
    HaarCarrierEqv links.length (along links v i p) (along links v i q) := by
  apply sum_carrier
  intro l hl
  have hb := List.idxOf_lt_length_of_mem hl
  unfold term
  apply HaarCarrierEqv.add
  · split
    · exact HaarCarrierEqv.neg (frame_carrier false hb i h)
    · exact .refl _ _
  · split
    · exact frame_carrier true hb i h
    · exact .refl _ _

private def E (width : Nat) : BlockEmbedding (N width) (B width) :=
  embedding (Nat.le_refl width) (Nat.zero_le width)
private theorem padded_neg {n : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv n p q) :
    PaddedPolynomialCoeffEqv n (polyNeg p) (polyNeg q) :=
  (PaddedPolynomialCoeffEqv.of_coeff (neg_smul p)).trans ((h.smul (-1)).trans (.of_coeff (neg_smul q).symm))

section FrameEmbedding
attribute [local irreducible] BlockEmbedding.polynomial
private theorem frame_embedding {source target b : Nat} (F : BlockEmbedding source target)
    (hb : b<source) (right : Bool) (i : Fin 3) (p : RatPoly) :
    PaddedPolynomialCoeffEqv target (F.polynomial (frameDerivativeAt right b i p))
      (frameDerivativeAt right (F.block b) i (F.polynomial p)) := by
  have h (a d : Nat) (ha : a<4) (hd : d<4) := F.polynomial_blockAngularDerivative hb ha hd p
  rcases directions i with rfl | rfl | rfl <;> cases right
  all_goals simp only [frameDerivativeAt, Bool.false_eq_true, if_false, if_true, rightDerivativeAt, pairedDerivativeAt,
    F.polynomial_add, F.polynomial_neg]
  · exact (h 0 1 (by decide) (by decide)).add (h 2 3 (by decide) (by decide))
  · exact (h 0 1 (by decide) (by decide)).add (padded_neg (h 2 3 (by decide) (by decide)))
  · exact (h 0 2 (by decide) (by decide)).add (padded_neg (h 1 3 (by decide) (by decide)))
  · exact (h 0 2 (by decide) (by decide)).add (h 1 3 (by decide) (by decide))
  · exact (h 0 3 (by decide) (by decide)).add (h 1 2 (by decide) (by decide))
  · exact (h 0 3 (by decide) (by decide)).add (padded_neg (h 1 2 (by decide) (by decide)))
end FrameEmbedding

private theorem padded_carrier {n : Nat} {p q : RatPoly}
    (h : PaddedPolynomialCoeffEqv n p q) (hp : SupportedQuaternionBlocks n p)
    (hq : SupportedQuaternionBlocks n q) : HaarCarrierEqv n p q :=
  carrier_of_supported hp hq (.of_padded h hp hq)

private theorem frame_image (width : Nat) (v : Z4Vertex) (i : Fin 3) (l : Z4Link)
    (hl : l∈baseLinks width) {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
    HaarCarrierEqv (B width) ((E width).polynomial (term (baseLinks width) v i l p))
      (linkGauss width v i l ((E width).polynomial p)) := by
  have hb := List.idxOf_lt_length_of_mem hl
  have he : (E width).block ((baseLinks width).idxOf l) = (boundaryCompleteSlabLinks width).idxOf l := by
    simpa only [E, timeShiftLink, timeShiftVertex, Nat.add_zero] using
      embedding_block (Nat.le_refl width) (Nat.zero_le width) hl
  have h (right : Bool) : HaarCarrierEqv (B width)
      ((E width).polynomial (frameDerivativeAt right ((baseLinks width).idxOf l) i p))
      (frameDerivativeAt right ((boundaryCompleteSlabLinks width).idxOf l) i ((E width).polynomial p)) := by
    have hpin := frame_embedding (E width) hb right i p
    rw [he] at hpin
    exact padded_carrier hpin ((E width).polynomial_supported _)
      (frame_supported right (by rw [← he]; exact (E width).block_lt hb) i ((E width).polynomial_supported p))
  unfold term linkGauss
  rw [BlockEmbedding.polynomial_add]
  apply HaarCarrierEqv.add
  · split
    · rw [BlockEmbedding.polynomial_neg]; exact HaarCarrierEqv.neg (h false)
    · exact .refl _ _
  · split
    · exact h true
    · exact .refl _ _

private theorem coeff_neg {p q : RatPoly} (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (polyNeg p) (polyNeg q) :=
  (neg_smul p).trans ((RatPolyCoeffEqv.smul (-1) h).trans (neg_smul q).symm)
private theorem frame_off {source target b : Nat} (F : BlockEmbedding source target)
    (hb : b<target) (hout : b∉F.image) (right : Bool) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks source p) :
    RatPolyCoeffEqv (frameDerivativeAt right b i (F.polynomial p)) polyZero := by
  have h (a d : Nat) (ha : a<4) (hd : d<4) :=
    F.blockAngularDerivative_offImage_zero hb hout ha hd hp
  rcases directions i with rfl | rfl | rfl <;> cases right
  all_goals simp only [frameDerivativeAt, Bool.false_eq_true, if_false, if_true, rightDerivativeAt, pairedDerivativeAt]
  all_goals first
    | exact ((h 0 1 (by decide) (by decide)).add (h 2 3 (by decide) (by decide))).trans (.add_zero _)
    | exact ((h 0 1 (by decide) (by decide)).add (coeff_neg (h 2 3 (by decide) (by decide)))).trans (.add_zero _)
    | exact ((h 0 2 (by decide) (by decide)).add (coeff_neg (h 1 3 (by decide) (by decide)))).trans (.add_zero _)
    | exact ((h 0 2 (by decide) (by decide)).add (h 1 3 (by decide) (by decide))).trans (.add_zero _)
    | exact ((h 0 3 (by decide) (by decide)).add (h 1 2 (by decide) (by decide))).trans (.add_zero _)
    | exact ((h 0 3 (by decide) (by decide)).add (coeff_neg (h 1 2 (by decide) (by decide)))).trans (.add_zero _)

private theorem omitted_link (width : Nat) (v : Z4Vertex) (i : Fin 3) (l : Z4Link)
    (hl : l∈boundaryCompleteSlabLinks width) (hout : l∉baseLinks width)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
    HaarCarrierEqv (B width) (linkGauss width v i l ((E width).polynomial p)) polyZero := by
  have hb := List.idxOf_lt_length_of_mem hl
  have ho : (boundaryCompleteSlabLinks width).idxOf l ∉ (E width).image := by
    intro hi
    have hs := (embedding_mem_iff (Nat.le_refl width) (Nat.zero_le width) hb).mp hi
    rw [BF4ExactSlabSpatialLinkReflection.correctedSlabLinkAt_idxOf hl] at hs
    exact hout ((baseLinks_mem_iff width l).mpr hs)
  have h (right : Bool) := frame_off (E width) hb ho right i hp
  unfold linkGauss
  apply (RatPolyCoeffEqv.haarCarrier ?_)
  have hleft : RatPolyCoeffEqv (if v=l.1 then polyNeg (frameDerivativeAt false
      ((boundaryCompleteSlabLinks width).idxOf l) i ((E width).polynomial p)) else polyZero) polyZero := by
    split
    · exact coeff_neg (h false)
    · exact .refl _
  have hright : RatPolyCoeffEqv (if v=addE l.1 l.2 then frameDerivativeAt true
      ((boundaryCompleteSlabLinks width).idxOf l) i ((E width).polynomial p) else polyZero) polyZero := by
    split
    · exact h true
    · exact .refl _
  exact (hleft.add hright).trans (.add_zero _)

private theorem gauss_embedding (width : Nat) (v : Z4Vertex) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
    HaarCarrierEqv (B width) ((E width).polynomial (sliceGauss width v i p))
      (vertexGauss width v i ((E width).polynomial p)) := by
  have hfilter : (boundaryCompleteSlabLinks width).filter (fun l => decide (l∈baseLinks width)) = baseLinks width := by
    change _ = (boundaryCompleteSlabLinks width).filter (fun l => decide (SliceLink width 0 l))
    apply List.filter_congr
    intro l _
    simpa only [baseLinks_mem_iff]
  have hs : ∀ xs : List Z4Link, (∀ l, l∈xs → l∈boundaryCompleteSlabLinks width) →
      HaarCarrierEqv (B width)
        ((E width).polynomial (finitePolySum (fun l => term (baseLinks width) v i l p)
          (xs.filter (fun l => decide (l∈baseLinks width)))))
        (finitePolySum (fun l => linkGauss width v i l ((E width).polynomial p)) xs) := by
    intro xs
    induction xs with
    | nil => intro _; exact .refl _ _
    | cons l xs ih =>
        intro hh
        have ht := ih (fun e he => hh e (List.mem_cons_of_mem l he))
        by_cases hl : l∈baseLinks width
        · simpa only [List.filter_cons, decide_eq_true hl, if_true, finitePolySum,
            BlockEmbedding.polynomial_add] using HaarCarrierEqv.add (frame_image width v i l hl hp) ht
        · have hz := omitted_link width v i l (hh l List.mem_cons_self) hl hp
          let rest := finitePolySum (fun l => linkGauss width v i l ((E width).polynomial p)) xs
          have hzero : HaarCarrierEqv (B width) (polyAdd (linkGauss width v i l ((E width).polynomial p)) rest) rest :=
            HaarCarrierEqv.trans (HaarCarrierEqv.add hz (.refl (B width) rest)) (RatPolyCoeffEqv.haarCarrier (.zero_add rest))
          simpa only [List.filter_cons, decide_eq_false hl, if_false, finitePolySum] using HaarCarrierEqv.trans ht (HaarCarrierEqv.symm hzero)
  have h := hs (boundaryCompleteSlabLinks width) (fun _ h => h)
  rw [hfilter] at h
  exact h

private theorem slab_product_zero {extent : Nat} (v : Z4Vertex) (i : Fin 3)
    (w : Q') (K : Nat) : ∀ ids : List Nat,
    (∀ id, id∈ids → id∈slabPhysicalFaceEdges extent) →
    PaddedPolynomialCoeffEqv (B extent)
      (vertexGauss extent v i (polynomialProduct (faceHeatPolynomial w K extent) ids)) polyZero
  | [], _ => .of_coeff (vertexGauss_one extent v i)
  | id::ids, h => PaddedPolynomialCoeffEqv.trans
      (.of_coeff (vertexGauss_mul extent v i (faceHeatPolynomial w K extent id) (polynomialProduct (faceHeatPolynomial w K extent) ids)))
      (PaddedPolynomialCoeffEqv.trans
        (((faceHeatPolynomial_gauss_zero w K (h id List.mem_cons_self) v i).mul (.refl _ _)).add
          ((PaddedPolynomialCoeffEqv.refl _ _).mul (slab_product_zero v i w K ids
            (fun a ha => h a (List.mem_cons_of_mem id ha)))))
        (.of_coeff ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.mul_zero_right _))))

/-- Every spatial face is retained; K=0, arbitrary nome and width zero remain. -/
theorem spatialWeight_gauss_zero (w : Q') (K width : Nat) (v : Z4Vertex) (i : Fin 3) :
    HaarCarrierEqv (N width) (sliceGauss width v i (spatialWeight w K width)) polyZero := by
  have hV := spatialWeight_supported w K width
  have hH := heatProduct_supported w K width (spatialIds width width 0)
  have hpin := padded_carrier (spatialWeight_pin (Nat.le_refl width) (Nat.zero_le width) w K)
    ((E width).polynomial_supported _) hH
  have hder : HaarCarrierEqv (B width)
      (vertexGauss width v i ((E width).polynomial (spatialWeight w K width))) polyZero :=
    HaarCarrierEqv.trans (along_carrier (boundaryCompleteSlabLinks width) v i hpin)
      (padded_carrier (slab_product_zero v i w K (spatialIds width width 0)
        (fun id hi => ((spatialIds_mem_iff width width 0 id).mp hi).1))
        (vertexGauss_supported width v i hH) (zero_supported _))
  have h := HaarCarrierEqv.trans (gauss_embedding width v i hV) hder
  exact carrier_of_supported (sliceGauss_supported width v i hV) (zero_supported _)
    ((E width).polynomial_supportedHaar_reflect
      (sliceGauss_supported width v i hV) (zero_supported _) (.of_carrier h))

private theorem slice_mul (width : Nat) (v : Z4Vertex) (i : Fin 3) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q) :
    HaarCarrierEqv (N width) (sliceGauss width v i (polyMul p q))
      (polyAdd (polyMul (sliceGauss width v i p) q) (polyMul p (sliceGauss width v i q))) := by
  have hs := supported_add (supported_polyMul (sliceGauss_supported width v i hp) hq)
    (supported_polyMul hp (sliceGauss_supported width v i hq))
  have h := gauss_embedding width v i (supported_polyMul hp hq)
  rw [BlockEmbedding.polynomial_mul] at h
  have hr := HaarCarrierEqv.add (HaarCarrierEqv.mul_right ((E width).polynomial q) (HaarCarrierEqv.symm (gauss_embedding width v i hp)))
    (HaarCarrierEqv.mul_left ((E width).polynomial p) (HaarCarrierEqv.symm (gauss_embedding width v i hq)))
  rw [← BlockEmbedding.polynomial_mul, ← BlockEmbedding.polynomial_mul,
    ← BlockEmbedding.polynomial_add] at hr
  exact carrier_of_supported (sliceGauss_supported width v i (supported_polyMul hp hq)) hs
    ((E width).polynomial_supportedHaar_reflect
      (sliceGauss_supported width v i (supported_polyMul hp hq)) hs
      (.of_carrier (HaarCarrierEqv.trans h (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (vertexGauss_mul width v i _ _)) hr))))

private theorem heads_zero : ∀ n, RatPolyCoeffEqv (partialHaarHeads n polyZero) polyZero
  | 0 => .refl _
  | n+1 => by simpa only [partialHaarHeads] using heads_zero n
private theorem map_zero (n : Nat) (w : Q') (K : Nat) (ids : List Nat) :
    RatPolyCoeffEqv (productMap n w K ids polyZero) polyZero :=
  (partialHaarHeads_congr n (RatPolyCoeffEqv.mul_zero_right _)).trans (heads_zero n)
private theorem map_neg (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (p : RatPoly) :
    RatPolyCoeffEqv (productMap n w K ids (polyNeg p)) (polyNeg (productMap n w K ids p)) :=
  (productMap_congr n w K ids (neg_smul p)).trans
    ((SU2QuaternionHaarKernelBound.kernelMap_smul n _ (-1) p).trans (neg_smul _).symm)

private theorem frame_map {n b : Nat} (hb : b<n) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ s, s∈ids → s<n) (right : Bool) (i : Fin 3) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    HaarCarrierEqv n (frameDerivativeAt right b i (productMap n w K ids p))
      (productMap n w K ids (frameDerivativeAt right b i p)) := by
  have h (a d : Nat) (ha : a<4) (hd : d<4) := productMap_angular_carrier n b a d hb ha hd w K ids hids p hp
  have plus (a d c e : Nat) (ha : a<4) (hd : d<4) (hc : c<4) (he : e<4) :=
    HaarCarrierEqv.trans (HaarCarrierEqv.add (h a d ha hd) (h c e hc he))
      (RatPolyCoeffEqv.haarCarrier (productMap_add n w K ids _ _).symm)
  have minus (a d c e : Nat) (ha : a<4) (hd : d<4) (hc : c<4) (he : e<4) :=
    HaarCarrierEqv.trans (HaarCarrierEqv.add (h a d ha hd) (HaarCarrierEqv.trans (HaarCarrierEqv.neg (h c e hc he))
      (RatPolyCoeffEqv.haarCarrier (map_neg n w K ids _).symm)))
      (RatPolyCoeffEqv.haarCarrier (productMap_add n w K ids _ _).symm)
  rcases directions i with rfl | rfl | rfl <;> cases right
  all_goals simp only [frameDerivativeAt, Bool.false_eq_true, if_false, if_true, rightDerivativeAt, pairedDerivativeAt]
  all_goals first
    | exact plus 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
    | exact minus 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
    | exact minus 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
    | exact plus 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
    | exact plus 0 3 1 2 (by decide) (by decide) (by decide) (by decide)
    | exact minus 0 3 1 2 (by decide) (by decide) (by decide) (by decide)

private theorem along_map (links : List Z4Link) (v : Z4Vertex) (i : Fin 3)
    (w : Q') (K : Nat) (ids : List Nat) (hids : ∀ s, s∈ids → s<links.length)
    {p : RatPoly} (hp : SupportedQuaternionBlocks links.length p) :
    HaarCarrierEqv links.length (along links v i (productMap links.length w K ids p))
      (productMap links.length w K ids (along links v i p)) := by
  have hterm : ∀ l, l∈links → HaarCarrierEqv links.length
      (term links v i l (productMap links.length w K ids p))
      (productMap links.length w K ids (term links v i l p)) := by
    intro l hl
    have h := frame_map (List.idxOf_lt_length_of_mem hl) w K ids hids
    unfold term
    have left : HaarCarrierEqv links.length
        (if v=l.1 then polyNeg (frameDerivativeAt false (links.idxOf l) i (productMap links.length w K ids p)) else polyZero)
        (productMap links.length w K ids (if v=l.1 then polyNeg (frameDerivativeAt false (links.idxOf l) i p) else polyZero)) := by
      split
      · exact HaarCarrierEqv.trans (HaarCarrierEqv.neg (h false i hp)) (RatPolyCoeffEqv.haarCarrier (map_neg _ w K ids _).symm)
      · exact RatPolyCoeffEqv.haarCarrier (map_zero _ w K ids).symm
    have right : HaarCarrierEqv links.length
        (if v=addE l.1 l.2 then frameDerivativeAt true (links.idxOf l) i (productMap links.length w K ids p) else polyZero)
        (productMap links.length w K ids (if v=addE l.1 l.2 then frameDerivativeAt true (links.idxOf l) i p else polyZero)) := by
      split
      · exact h true i hp
      · exact RatPolyCoeffEqv.haarCarrier (map_zero _ w K ids).symm
    exact HaarCarrierEqv.trans (HaarCarrierEqv.add left right) (RatPolyCoeffEqv.haarCarrier (productMap_add _ w K ids _ _).symm)
  have hs : ∀ xs : List Z4Link, (∀ l, l∈xs → l∈links) → HaarCarrierEqv links.length
      (finitePolySum (fun l => term links v i l (productMap links.length w K ids p)) xs)
      (productMap links.length w K ids (finitePolySum (fun l => term links v i l p) xs)) := by
    intro xs
    induction xs with
    | nil => intro _; exact RatPolyCoeffEqv.haarCarrier (map_zero _ w K ids).symm
    | cons l xs ih =>
        intro h
        exact HaarCarrierEqv.trans (HaarCarrierEqv.add (hterm l (h l List.mem_cons_self))
          (ih (fun a ha => h a (List.mem_cons_of_mem l ha)))) (RatPolyCoeffEqv.haarCarrier (productMap_add _ w K ids _ _).symm)
  exact hs links (fun _ h => h)

private theorem map_carrier {n : Nat} (w : Q') (K : Nat) (ids : List Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (h : HaarCarrierEqv n p q) : HaarCarrierEqv n (productMap n w K ids p) (productMap n w K ids q) :=
  partialHaarHeads_carrier (HaarCarrierEqv.mul_left (productHeat n w K ids) (carrier_extend n hp hq h))

/-- Actual ORIGINAL transfer intertwining; the spatial weight is retained. -/
theorem transferStep_gauss_intertwining (w : Q') (K width : Nat) (v : Z4Vertex) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
    HaarCarrierEqv (N width) (sliceGauss width v i (transferStep w K width p))
      (transferStep w K width (sliceGauss width v i p)) := by
  have hV := spatialWeight_supported w K width
  have hprod := HaarCarrierEqv.trans (slice_mul width v i hV hp) (HaarCarrierEqv.trans
    (HaarCarrierEqv.add (HaarCarrierEqv.mul_right p (spatialWeight_gauss_zero w K width v i)) (.refl _ _))
    (RatPolyCoeffEqv.haarCarrier (((RatPolyCoeffEqv.mul_zero_left p).add (.refl _)).trans (.zero_add _))))
  rw [transferStep_eq_productMap, transferStep_eq_productMap]
  exact HaarCarrierEqv.trans (along_map (baseLinks width) v i w K (activeBlocks width) (activeBlocks_lt width)
    (supported_polyMul hV hp))
    (map_carrier w K _ (sliceGauss_supported width v i (supported_polyMul hV hp))
      (supported_polyMul hV (sliceGauss_supported width v i hp)) hprod)

/-- Every supported signed Gauss-invariant input is preserved, including fringe. -/
theorem transferStep_gauss_zero (w : Q') (K width : Nat) (v : Z4Vertex) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i p) polyZero) :
    HaarCarrierEqv (N width) (sliceGauss width v i (transferStep w K width p)) polyZero := by
  apply HaarCarrierEqv.trans (transferStep_gauss_intertwining w K width v i hp)
  rw [transferStep_eq_productMap]
  exact HaarCarrierEqv.trans (map_carrier w K _ (supported_polyMul (spatialWeight_supported w K width)
      (sliceGauss_supported width v i hp)) (zero_supported _)
      (HaarCarrierEqv.trans (HaarCarrierEqv.mul_left _ h) (RatPolyCoeffEqv.haarCarrier (.mul_zero_right _))))
      (RatPolyCoeffEqv.haarCarrier (map_zero _ w K _))

/-! Finite original sources and messages stay in the SAME Gauss constraint.
Only literal physical spatial faces are admitted below. Rational centering
and finite reciprocal polynomials retain that constraint; no completed
generator, horizontal-energy payment or survival claim is supplied. -/
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
  (blockConditionalRatio blockReciprocal blockWindowUpper blockWindowUpper_positive)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (corrector)
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse (corrector_supported)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
  (reciprocal reciprocal_supported remainder remainder_supported scale)
attribute [local irreducible] baseLinks kineticWeight spatialWeight

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) :=
  BF4ExactSlabPlaquetteObservableAlgebra.supported_smul hp c

private theorem reflect_carrier (width : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q)
    (h : HaarCarrierEqv (B width) ((E width).polynomial p) ((E width).polynomial q)) :
    HaarCarrierEqv (N width) p q :=
  carrier_of_supported hp hq ((E width).polynomial_supportedHaar_reflect hp hq (.of_carrier h))

private theorem slice_add (width : Nat) (v : Z4Vertex) (i : Fin 3) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q) :
    HaarCarrierEqv (N width) (sliceGauss width v i (polyAdd p q))
      (polyAdd (sliceGauss width v i p) (sliceGauss width v i q)) := by
  have h := gauss_embedding width v i (supported_add hp hq)
  rw [BlockEmbedding.polynomial_add] at h
  have hr := HaarCarrierEqv.add (HaarCarrierEqv.symm (gauss_embedding width v i hp))
    (HaarCarrierEqv.symm (gauss_embedding width v i hq))
  rw [← BlockEmbedding.polynomial_add] at hr
  exact reflect_carrier width (sliceGauss_supported width v i (supported_add hp hq))
    (supported_add (sliceGauss_supported width v i hp) (sliceGauss_supported width v i hq))
    (HaarCarrierEqv.trans h (HaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier (vertexGauss_add width v i _ _)) hr))

private theorem slice_smul (width : Nat) (v : Z4Vertex) (i : Fin 3) (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    HaarCarrierEqv (N width) (sliceGauss width v i (polySmul c p))
      (polySmul c (sliceGauss width v i p)) := by
  have h := gauss_embedding width v i (support_smul hp c)
  rw [BlockEmbedding.polynomial_smul] at h
  have hr := HaarCarrierEqv.smul c (HaarCarrierEqv.symm (gauss_embedding width v i hp))
  rw [← BlockEmbedding.polynomial_smul] at hr
  exact reflect_carrier width (sliceGauss_supported width v i (support_smul hp c))
    (support_smul (sliceGauss_supported width v i hp) c)
    (HaarCarrierEqv.trans h (HaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier (vertexGauss_smul width v i c _)) hr))

private theorem reflect_gauss_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p)
    (h : HaarCarrierEqv (B width) (vertexGauss width v i ((E width).polynomial p)) polyZero) :
    HaarCarrierEqv (N width) (sliceGauss width v i p) polyZero :=
  reflect_carrier width (sliceGauss_supported width v i hp) (zero_supported _)
    (HaarCarrierEqv.trans (gauss_embedding width v i hp) h)

private theorem slice_one_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) :
    HaarCarrierEqv (N width) (sliceGauss width v i polyOne) polyZero := by
  have hp := padded_carrier (PaddedPolynomialCoeffEqv.of_prefix (E width).polynomial_one_prefix)
    ((E width).polynomial_supported polyOne) (supported_one _)
  exact reflect_gauss_zero width v i (supported_one _) (HaarCarrierEqv.trans
    (along_carrier (boundaryCompleteSlabLinks width) v i hp)
    (RatPolyCoeffEqv.haarCarrier (vertexGauss_one width v i)))

private theorem slice_zero_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) :
    HaarCarrierEqv (N width) (sliceGauss width v i polyZero) polyZero :=
  reflect_gauss_zero width v i (zero_supported _)
    (RatPolyCoeffEqv.haarCarrier (vertexGauss_zero width v i))

private theorem slice_add_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i p) polyZero)
    (h' : HaarCarrierEqv (N width) (sliceGauss width v i q) polyZero) :
    HaarCarrierEqv (N width) (sliceGauss width v i (polyAdd p q)) polyZero :=
  HaarCarrierEqv.trans (slice_add width v i hp hq)
    (HaarCarrierEqv.trans (HaarCarrierEqv.add h h') (RatPolyCoeffEqv.haarCarrier (.add_zero _)))

private theorem slice_smul_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i p) polyZero) :
    HaarCarrierEqv (N width) (sliceGauss width v i (polySmul c p)) polyZero :=
  HaarCarrierEqv.trans (slice_smul width v i c hp)
    (HaarCarrierEqv.trans (HaarCarrierEqv.smul c h) (RatPolyCoeffEqv.haarCarrier (.smul_zero c)))

private theorem slice_neg_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i p) polyZero) :
    HaarCarrierEqv (N width) (sliceGauss width v i (polyNeg p)) polyZero :=
  HaarCarrierEqv.trans (along_carrier (baseLinks width) v i (RatPolyCoeffEqv.haarCarrier (neg_smul p)))
    (slice_smul_zero width v i (-1) hp h)

private theorem slice_mul_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i p) polyZero)
    (h' : HaarCarrierEqv (N width) (sliceGauss width v i q) polyZero) :
    HaarCarrierEqv (N width) (sliceGauss width v i (polyMul p q)) polyZero :=
  HaarCarrierEqv.trans (slice_mul width v i hp hq) (HaarCarrierEqv.trans
    (HaarCarrierEqv.add (HaarCarrierEqv.mul_right q h) (HaarCarrierEqv.mul_left p h'))
    (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.mul_zero_left q).add (.mul_zero_right p))))

private theorem sourceLoop_zero (width : Nat) (loop : SourceLoop width)
    (v : Z4Vertex) (i : Fin 3) (spin : Nat) :
    HaarCarrierEqv (N width) (sliceGauss width v i (sourceCharacter width loop.edges spin)) polyZero := by
  have hp := sourceCharacter_supported width loop.edges spin
  have hq := BF4ExactSlabTemporalGaugeWilsonWord.character_supported width
    (loop.edges.map (shiftEntry 0)) spin
  have hpin := padded_carrier
    (PaddedPolynomialCoeffEqv.of_prefix (character_pin (Nat.le_refl width) (Nat.zero_le width) loop spin))
    ((E width).polynomial_supported _) hq
  exact reflect_gauss_zero width v i hp (HaarCarrierEqv.trans
    (along_carrier (boundaryCompleteSlabLinks width) v i hpin)
    (padded_carrier (placedSourceLoop_gauss_zero (Nat.le_refl width) (Nat.zero_le width) loop v i spin)
      (vertexGauss_supported width v i hq) (zero_supported _)))

private theorem spatialFace_zero (width : Nat) (face : Z4Plaq) (hf : face∈spatialFaces width)
    (v : Z4Vertex) (i : Fin 3) : HaarCarrierEqv (N width)
    (sliceGauss width v i (characterPolynomial (plaquette width face).scalar 1)) polyZero :=
  HaarCarrierEqv.trans (HaarCarrierEqv.symm (along_carrier (baseLinks width) v i
    (RatPolyCoeffEqv.haarCarrier (sourceCharacter_plaquette width face 1))))
    (sourceLoop_zero width (plaquetteLoop face hf) v i 1)

/-- Every signed physical face is retained; empty families and zero coefficients remain. -/
theorem spatialSpan_gauss_zero (width : Nat) (c : Z4Plaq → Q') (v : Z4Vertex) (i : Fin 3) :
    ∀ qs : List Z4Plaq, (∀ face, face∈qs → face∈spatialFaces width) →
      HaarCarrierEqv (N width) (sliceGauss width v i (spatialSpan width c qs)) polyZero
  | [], _ => slice_zero_zero width v i
  | face::qs, hqs => slice_add_zero width v i
      (support_smul (SU2QuaternionRelativeHeatPairGeometry.character_supported
        (BF4ExactSlabFixedSpatialSpatialOrder.plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1) (c face))
      (spatialSpan_supported width c qs)
      (slice_smul_zero width v i (c face)
        (SU2QuaternionRelativeHeatPairGeometry.character_supported
          (BF4ExactSlabFixedSpatialSpatialOrder.plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1)
        (spatialFace_zero width face (hqs face List.mem_cons_self) v i))
      (spatialSpan_gauss_zero width c v i qs (fun q hq => hqs q (List.mem_cons_of_mem face hq)))

/-- Literal rational subtraction preserves the original constraint, including OWN centers. -/
theorem shifted_gauss_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i p) polyZero) (center : Q') :
    HaarCarrierEqv (N width) (sliceGauss width v i (shifted p center)) polyZero :=
  slice_add_zero width v i (support_smul hp 1) (support_smul (supported_one _) (-center))
    (slice_smul_zero width v i 1 hp h)
    (slice_smul_zero width v i (-center) (supported_one _) (slice_one_zero width v i))

/-- Finite ORIGINAL transfer iteration preserves every supported signed input constraint. -/
theorem iterateStep_gauss_zero (w : Q') (K width : Nat) (v : Z4Vertex) (i : Fin 3) :
    ∀ count : Nat, ∀ {p : RatPoly}, SupportedQuaternionBlocks (N width) p →
      HaarCarrierEqv (N width) (sliceGauss width v i p) polyZero →
      HaarCarrierEqv (N width) (sliceGauss width v i
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) count p)) polyZero
  | 0, _, _, h => h
  | count+1, p, hp, h => iterateStep_gauss_zero w K width v i count
      (transferStep_supported w K width hp) (transferStep_gauss_zero w K width v i hp h)

/-- Every actual terminal message is invariant, not a stationary or limiting replacement. -/
theorem terminalMessage_gauss_zero (w : Q') (K width n : Nat) (v : Z4Vertex) (i : Fin 3) :
    HaarCarrierEqv (N width) (sliceGauss width v i (terminalMessage w K width n)) polyZero :=
  iterateStep_gauss_zero w K width v i n (supported_one _) (slice_one_zero width v i)

private theorem corrector_gauss_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) {R : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) R)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i R) polyZero) :
    ∀ k : Nat, HaarCarrierEqv (N width) (sliceGauss width v i (corrector R k)) polyZero
  | 0 => slice_zero_zero width v i
  | k+1 => slice_add_zero width v i (supported_one _)
      (supported_polyMul (neg_supported hp) (corrector_supported hp k)) (slice_one_zero width v i)
      (slice_mul_zero width v i (neg_supported hp) (corrector_supported hp k)
        (slice_neg_zero width v i hp h) (corrector_gauss_zero width v i hp h k))

private theorem reciprocal_gauss_zero (width : Nat) (v : Z4Vertex) (i : Fin 3) {A : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) A)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i A) polyZero)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    HaarCarrierEqv (N width) (sliceGauss width v i (reciprocal A u hu k)) polyZero := by
  have hR : HaarCarrierEqv (N width) (sliceGauss width v i (remainder A u hu)) polyZero :=
    slice_add_zero width v i (support_smul hp (scale u hu)) (neg_supported (supported_one _))
      (slice_smul_zero width v i (scale u hu) hp h)
      (slice_neg_zero width v i (supported_one _) (slice_one_zero width v i))
  exact slice_smul_zero width v i (scale u hu)
    (corrector_supported (remainder_supported hp u hu) k)
    (corrector_gauss_zero width v i (remainder_supported hp u hu) hR k)

/-- The actual finite ratio uses g_(n+t), T^t(g_n*psi) and its existing upper
window, unchanged. All auxiliary degrees and zero/fringe cases are retained;
there is no completed inverse, derivative-energy estimate or survival claim. -/
theorem blockConditionalRatio_gauss_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K)
    (n t : Nat) (v : Z4Vertex) (i : Fin 3) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi)
    (h : HaarCarrierEqv (N width) (sliceGauss width v i psi) polyZero) (k : Nat) :
    HaarCarrierEqv (N width)
      (sliceGauss width v i (blockConditionalRatio hw0 hw1 K width hK n t psi k)) polyZero := by
  have hg := terminalMessage_supported w K width n
  have hA := terminalMessage_supported w K width (n+t)
  have hnum := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t (supported_polyMul hg hp)
  exact slice_mul_zero width v i
    (reciprocal_supported hA _ _ k) hnum
    (reciprocal_gauss_zero width v i hA (terminalMessage_gauss_zero w K width (n+t) v i)
      (blockWindowUpper w K width n t) (blockWindowUpper_positive hw0 hw1 K width hK n t) k)
    (iterateStep_gauss_zero w K width v i t (supported_polyMul hg hp)
      (slice_mul_zero width v i hg hp (terminalMessage_gauss_zero w K width n v i) h))

end YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.sliceGauss
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.sliceGauss_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.spatialWeight_gauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.transferStep_gauss_intertwining
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.transferStep_gauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.spatialSpan_gauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.shifted_gauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.iterateStep_gauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.terminalMessage_gauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGaussTransfer.blockConditionalRatio_gauss_zero
